import LeanBatfish.Decode.Core
import LeanBatfish.Decode.Net
import LeanBatfish.Topology.Edge

/-!
# Decoding Batfish's topology answers

Reads the adjacencies from Batfish's `layer3Edges`, `ospfEdges` and `bgpEdges` answers. These are
answer tables rather than IR, so only the columns we use are read.
-/

namespace LeanBatfish.Decode

open Lean

private def rowsOf (answer : Json) : Except String (Array Json) := do
  let elems ← answer.getObjValAs? (Array Json) "answerElements"
  let some table := elems[0]? | throw "answer has no answer elements"
  table.getObjValAs? (Array Json) "rows"

private def nodeInterface (j : Json) : Except String NodeInterface := do
  pure { host := ← j.getObjValAs? String "hostname", iface := ← j.getObjValAs? String "interface" }

private def ipOf (j : Json) (key : String) : Except String Ip := do
  let s ← j.getObjValAs? String key
  match Ip.parse? s with
  | some ip => pure ip
  | none => throw s!"bad IP {s}"

def layer3Edges (answer : Json) : Except String (Array Layer3Edge) := do
  (← rowsOf answer).mapM fun row => do
    pure { tail := ← nodeInterface (← row.getObjVal? "Interface"),
           head := ← nodeInterface (← row.getObjVal? "Remote_Interface") }

def ospfEdges (answer : Json) : Except String (Array OspfEdge) := do
  (← rowsOf answer).mapM fun row => do
    pure { tail := ← nodeInterface (← row.getObjVal? "Interface"),
           head := ← nodeInterface (← row.getObjVal? "Remote_Interface") }

/-- `bgpEdges` rows give a session from `Node` (at `IP`) to `Remote_Node` (at `Remote_IP`).
Unnumbered sessions (no IPs) are not modeled. -/
def bgpEdges (answer : Json) : Except String (Array BgpEdge) := do
  (← rowsOf answer).mapM fun row => do
    pure {
      tailHost := ← (← row.getObjVal? "Node").getObjValAs? String "name"
      tailIp := ← ipOf row "IP"
      headHost := ← (← row.getObjVal? "Remote_Node").getObjValAs? String "name"
      headIp := ← ipOf row "Remote_IP" }

end LeanBatfish.Decode
