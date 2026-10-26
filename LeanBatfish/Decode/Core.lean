import Lean.Data.Json

/-!
# Strict decoding

The decoder is how LeanBatfish states which part of Batfish's IR it understands. Every
JSON object is decoded by consuming the fields we model; when the object is finished,
any field left over is an error. So an input that uses a feature we do not model is
rejected, rather than simulated as if the feature were absent.

There are two kinds of failure:

* `unsupported` — the input is well-formed Batfish JSON but uses a feature outside the
  modeled subset (an unknown field or class, or a gated field with a non-neutral value);
* `malformed` — the JSON does not have the shape we expect from Batfish, which points to
  a bug in the decoder.

Batfish omits empty and default-valued fields when it writes JSON, so most fields are
optional with a default.
-/

namespace LeanBatfish.Decode

open Lean

inductive Rejection.Kind
  | unsupported
  | malformed
  deriving DecidableEq, Inhabited, Repr

structure Rejection where
  kind : Rejection.Kind
  /-- Where in the JSON the problem is, e.g. `nodes.r1.vrfs.default.bgpProcess`. -/
  path : String
  message : String
  deriving Inhabited, Repr

instance : ToString Rejection where
  toString r :=
    let k := match r.kind with | .unsupported => "unsupported" | .malformed => "malformed"
    s!"{k} at {r.path}: {r.message}"

/-- A decoder for one JSON value. The reader context is the current JSON path. -/
abbrev DecodeM := ReaderT (Array String) (Except Rejection)

namespace DecodeM

def pathString : DecodeM String := do
  pure (".".intercalate (← read).toList)

def unsupported (msg : String) : DecodeM α := do
  throw { kind := .unsupported, path := ← pathString, message := msg }

def malformed (msg : String) : DecodeM α := do
  throw { kind := .malformed, path := ← pathString, message := msg }

/-- Decode under a deeper path. -/
def within (segment : String) (x : DecodeM α) : DecodeM α :=
  withReader (·.push segment) x

def run (x : DecodeM α) : Except Rejection α := x #[]

end DecodeM

/-- A decoder for one JSON object. The state holds the fields not yet consumed. -/
abbrev ObjM := StateT (Std.TreeMap.Raw String Json compare) DecodeM

/-- A decoder from a JSON value. -/
abbrev Decoder (α : Type) := Json → DecodeM α

open DecodeM

/-! ## Scalars -/

def str : Decoder String
  | .str s => pure s
  | j => malformed s!"expected a string, got {j.compress}"

def bool : Decoder Bool
  | .bool b => pure b
  | j => malformed s!"expected a boolean, got {j.compress}"

def nat : Decoder Nat := fun j =>
  match j.getNat? with
  | .ok n => pure n
  | .error _ => malformed s!"expected a natural number, got {j.compress}"

def int : Decoder Int := fun j =>
  match j.getInt? with
  | .ok n => pure n
  | .error _ => malformed s!"expected an integer, got {j.compress}"

/-- Decode a string with a partial parser. -/
def parsed (what : String) (parse : String → Option α) : Decoder α := fun j => do
  let s ← str j
  match parse s with
  | some a => pure a
  | none => malformed s!"expected {what}, got {s.quote}"

/-- Decode a string naming one of finitely many constants. -/
def enum (what : String) (cases : List (String × α)) : Decoder α := fun j => do
  let s ← str j
  match cases.lookup s with
  | some a => pure a
  | none => unsupported s!"{what} {s.quote} is not modeled"

/-! ## Collections -/

def array (d : Decoder α) : Decoder (Array α)
  | .arr xs => xs.mapIdxM fun i x => DecodeM.within (toString i) (d x)
  | j => malformed s!"expected an array, got {j.compress.take 80}"

/-- A JSON object used as a map from names to values, kept in key order. -/
def map (d : Decoder α) : Decoder (Array (String × α))
  | .obj kvs => kvs.foldlM (init := #[]) fun acc k v => do
      pure (acc.push (k, ← DecodeM.within k (d v)))
  | j => malformed s!"expected an object, got {j.compress.take 80}"

/-! ## Objects -/

/-- Run an object decoder. Fields it does not consume are rejected as unsupported. -/
def object (d : ObjM α) : Decoder α
  | .obj kvs => do
    let (a, rest) ← d.run kvs
    match rest.toList with
    | [] => pure a
    | (k, v) :: _ => DecodeM.within k <| unsupported s!"field is not modeled: {v.compress.take 120}"
  | j => malformed s!"expected an object, got {j.compress.take 80}"

namespace ObjM

private def take? (key : String) : ObjM (Option Json) := do
  let kvs ← get
  match kvs.get? key with
  | some v => set (kvs.erase key); pure (some v)
  | none => pure none

/-- A field that must be present. -/
def req (key : String) (d : Decoder α) : ObjM α := do
  match ← take? key with
  | some v => DecodeM.within key (d v)
  | none => malformed s!"missing field {key.quote}"

/-- An optional field. JSON `null` counts as absent. -/
def opt (key : String) (d : Decoder α) : ObjM (Option α) := do
  match ← take? key with
  | some .null | none => pure none
  | some v => some <$> DecodeM.within key (d v)

/-- A field with a default, used when Batfish omitted it. -/
def dflt (key : String) (default : α) (d : Decoder α) : ObjM α := do
  return (← opt key d).getD default

/-- A field we deliberately ignore because the simulation never reads it. -/
def ignore (key : String) : ObjM Unit := do
  discard <| take? key

/-- Several ignored fields. -/
def ignoreAll (keys : List String) : ObjM Unit :=
  keys.forM ignore

/-- A field that is only supported at its neutral value. `isNeutral` decides whether the
value present has no effect; any other value rejects the input as using `feature`. -/
def gate (key : String) (feature : String) (isNeutral : Json → Bool) : ObjM Unit := do
  match ← take? key with
  | some v =>
    unless isNeutral v do
      DecodeM.within key <| unsupported s!"{feature} is not modeled ({v.compress.take 120})"
  | none => pure ()

/-- Gate that accepts only an absent, null, empty, false or zero value. -/
def gateEmpty (key : String) (feature : String) : ObjM Unit :=
  gate key feature fun
    | .null | .bool false => true
    | .arr xs => xs.isEmpty
    | .obj kvs => kvs.isEmpty
    | .str s => s.isEmpty
    | .num n => n.mantissa == 0
    | _ => false

end ObjM

/-- Decode a polymorphic object by its `class` tag. Batfish writes the fully qualified
Java class name; `cases` maps the class name without the `org.batfish.datamodel.`
prefix to the decoder for that class. -/
def byClass (what : String) (cases : List (String × ObjM α)) : Decoder α := fun j => do
  let cls ← match j.getObjVal? "class" with
    | .ok (.str c) => pure c
    | _ => malformed s!"{what} without a class tag"
  let short := (cls.dropPrefix? "org.batfish.datamodel.").map (·.toString) |>.getD cls
  match cases.lookup short with
  | some d => object (do ObjM.ignore "class"; d) j
  | none => unsupported s!"{what} class {short} is not modeled"

end LeanBatfish.Decode
