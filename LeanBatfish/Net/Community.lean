/-!
# BGP communities

Batfish has three kinds of BGP communities: standard (RFC 1997, 32 bits), extended
(RFC 4360, a 16-bit type and a 48-bit value) and large (RFC 8092, three 32-bit numbers).
In JSON they are strings in the forms Batfish prints:

* standard: `"65000:100"`;
* extended: `"<type>:<global admin>[L]:<local admin>"` or `"0x<type>:0x<subtype>:0x<value>"`;
* large: `"large:1:2:3"`.
-/

namespace LeanBatfish

inductive Community
  /-- A standard community, as its 32-bit value (high 16 bits : low 16 bits). -/
  | standard (value : UInt32)
  /-- An extended community: the type octet, the subtype octet, and the 48-bit value. -/
  | extended (type subType : Nat) (value : Nat)
  /-- A large community. -/
  | large (globalAdmin localData1 localData2 : UInt32)
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace Community

private def parseNat? (s : String) : Option Nat := s.toNat?

private def parseHex? (s : String) : Option Nat := do
  let digits ← (s.dropPrefix? "0x").map (·.toString)
  guard (!digits.isEmpty)
  digits.foldl (init := some 0) fun acc c => do
    let d ← if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    pure ((← acc) * 16 + d)

/-- Whether an extended community of this type has a 4-byte global administrator (and a
2-byte local administrator). Types `0x00` and `0x40` have a 2-byte global administrator. -/
def extendedHasLongGlobalAdmin (type : Nat) : Bool := type != 0x00 && type != 0x40

/-- Parse a community in the form Batfish prints it. -/
def parse? (s : String) : Option Community :=
  match s.splitOn ":" with
  | [hi, lo] => do
    let hi ← parseNat? hi
    let lo ← parseNat? lo
    guard (hi < 65536 && lo < 65536)
    pure (.standard (UInt32.ofNat (hi * 65536 + lo)))
  | [t, ga, la] =>
    if t.startsWith "0x" then do
      pure (.extended (← parseHex? t) (← parseHex? ga) (← parseHex? la))
    else do
      let typeAndSub ← parseNat? t
      guard (typeAndSub < 65536)
      let type := typeAndSub / 256
      let gaLong := ga.endsWith "L"
      let ga ← parseNat? (if gaLong then (ga.dropEnd 1).toString else ga)
      let la ← parseNat? la
      let value := if extendedHasLongGlobalAdmin type then ga * 65536 + la else ga * 2^32 + la
      pure (.extended type (typeAndSub % 256) value)
  | [tag, a, b, c] => do
    guard (tag.toLower == "large")
    let a ← parseNat? a; let b ← parseNat? b; let c ← parseNat? c
    guard (a < 2^32 && b < 2^32 && c < 2^32)
    pure (.large (UInt32.ofNat a) (UInt32.ofNat b) (UInt32.ofNat c))
  | _ => none

def isStandard : Community → Bool | .standard _ => true | _ => false
def isExtended : Community → Bool | .extended .. => true | _ => false
def isLarge : Community → Bool | .large .. => true | _ => false

/-- Batfish's printed form (`Community.toString`). -/
protected def toString : Community → String
  | .standard v => s!"{v.toNat / 65536}:{v.toNat % 65536}"
  | .extended type sub value =>
    let typeAndSub := type * 256 + sub
    if extendedHasLongGlobalAdmin type then
      s!"{typeAndSub}:{value / 65536}L:{value % 65536}"
    else
      s!"{typeAndSub}:{value / 2^32}:{value % 2^32}"
  | .large a b c => s!"large:{a}:{b}:{c}"

instance : ToString Community := ⟨Community.toString⟩

end Community

end LeanBatfish
