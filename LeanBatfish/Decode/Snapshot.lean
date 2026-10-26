import LeanBatfish.Decode.Announcement
import LeanBatfish.Decode.Configuration
import LeanBatfish.Decode.Topology
import LeanBatfish.IR.Snapshot

/-!
# Reading a snapshot

Reads a snapshot from the files `tools/export.py` writes for it: `viModel.json`,
`layer3Edges.json`, `ospfEdges.json`, `bgpEdges.json`, and
`external_bgp_announcements.json` when the snapshot has one.
-/

namespace LeanBatfish.Decode

open Lean

/-- Why a snapshot could not be read: it is outside the modeled subset, or a file is
missing or malformed. -/
inductive SnapshotError
  | rejected (r : Rejection)
  | failed (message : String)

instance : ToString SnapshotError where
  toString
    | .rejected r => toString r
    | .failed m => m

def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw <| .userError s!"{path}: {e}"

private def readEdges (path : System.FilePath) (decode : Json → Except String α) :
    ExceptT SnapshotError IO α := do
  if !(← path.pathExists) then throw (.failed s!"{path} is missing")
  match decode (← readJson path) with
  | .ok a => pure a
  | .error e => throw (.failed s!"{path}: {e}")

/-- Read the snapshot exported in `dir`. -/
def snapshot (dir : System.FilePath) : IO (Except SnapshotError Snapshot) := ExceptT.run do
  let configs ← match network (← readJson (dir / "viModel.json")) with
    | .ok cs => pure cs
    | .error r => throw (.rejected r)
  let layer3 ← readEdges (dir / "layer3Edges.json") layer3Edges
  let ospf ← readEdges (dir / "ospfEdges.json") ospfEdges
  let bgp ← readEdges (dir / "bgpEdges.json") bgpEdges
  let annFile := dir / "external_bgp_announcements.json"
  let announcements ← if ← annFile.pathExists then
      match Decode.announcements (← readJson annFile) with
      | .ok a => pure a
      | .error r => throw (.rejected r)
    else pure #[]
  let topology : Topology := { layer3, ospf, bgp }
  return { configs := configs.qsort (·.hostname < ·.hostname), topology, announcements }

end LeanBatfish.Decode
