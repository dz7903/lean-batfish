import Lean.Data.Json

/-!
# Reading a `viModel` answer

Batfish's `viModel` question answers with a JSON object whose `nodes` field maps each
hostname to that node's `Configuration`. This module unpacks that envelope. The strict
decoding of each `Configuration` into the IR lives alongside it in `LeanBatfish.Decode`.
-/

namespace LeanBatfish.Decode

open Lean

/-- The answer element of a `viModel` answer, as exported by `tools/export.py`. -/
private def answerElement (answer : Json) : Except String Json := do
  let elements ← answer.getObjValAs? (Array Json) "answerElements"
  match elements[0]? with
  | some e => pure e
  | none => throw "viModel answer has no answer element"

/-- The raw `Configuration` JSON of every node, sorted by hostname. -/
def viModelNodes (answer : Json) : Except String (Array (String × Json)) := do
  let nodes ← (← answerElement answer).getObjVal? "nodes"
  let nodes ← nodes.getObj?
  pure (nodes.foldl (fun acc k v => acc.push (k, v)) #[])

end LeanBatfish.Decode
