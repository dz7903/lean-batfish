import LeanBatfishSim.Answer
import LeanBatfishSim.Dynamics
import LeanBatfish.Decode.Snapshot

/-!
# `lean-batfish-sim`

Command-line entry point of the simulator.
-/

open Lean LeanBatfish

namespace LeanBatfishSim

def usage : String :=
  "usage: lean-batfish-sim <command> ...\n\n" ++
  "  answer [--dynamics] <snapshot-dir> <question>...\n" ++
  "            simulate the network exported in <snapshot-dir> and print the answers to\n" ++
  "            the questions (routes, fibs, bgpRib, ipsecSessionStatus, ipsecEdges) as one\n" ++
  "            JSON object; with --dynamics,\n" ++
  "            run the declarative dynamics (LeanBatfish.Model) to a fixed point instead\n" ++
  "  check-stable <snapshot-dir>\n" ++
  "            check that the simulator's converged state is a stable state of the\n" ++
  "            declarative dynamics (LeanBatfish.Model); print the routers it is not stable at\n" ++
  "  inspect <viModel.json>\n" ++
  "            list the nodes and VRFs of a Batfish viModel export\n" ++
  "  decode <viModel.json>...\n" ++
  "            decode each export strictly; print `ok` or the reason it is rejected"

open Decode (readJson)

def inspect (path : System.FilePath) : IO UInt32 := do
  match Decode.viModelNodes (← readJson path) with
  | .error e => IO.eprintln e; pure 1
  | .ok nodes =>
    for (host, config) in nodes do
      let format := (config.getObjValAs? String "configurationFormat").toOption.getD "?"
      let vrfs := match config.getObjVal? "vrfs" >>= Json.getObj? with
        | .ok m => m.foldl (fun (acc : Array String) k _ => acc.push k) #[]
        | .error _ => #[]
      IO.println s!"{host} [{format}] vrfs: {", ".intercalate vrfs.toList}"
    pure 0

/-- Decode each file; print one line per file. Exits with 1 if any file is rejected. -/
def decode (paths : List String) : IO UInt32 := do
  let mut failed := false
  for path in paths do
    match Decode.network (← readJson path) with
    | .ok configs => IO.println s!"{path}\tok\t{configs.size} nodes"
    | .error r =>
      failed := true
      IO.println s!"{path}\t{toString r}"
  pure (if failed then 1 else 0)

/-- Simulate the snapshot exported in `dir` and print the answers to `qs`. Exits with 3 if
the network is outside the modeled subset and 4 if the simulation fails. -/
def answer (dir : System.FilePath) (qs : List String) (dynamics : Bool := false) : IO UInt32 := do
  for q in qs do
    unless questions.any (·.1 == q) do
      IO.eprintln s!"unknown question {q}; known: {", ".intercalate (questions.map (·.1))}"
      return 2
  match ← Decode.snapshot dir with
  | .error (.rejected r) => IO.println (Json.mkObj [("rejected", toString r)]).compress; pure 3
  | .error (.failed e) => throw <| .userError e
  | .ok s =>
    let dp : EvalM DataPlane := if dynamics then do
        let N ← Model.Network.build s
        let (X, _) ← runDynamics N
        dataPlaneOf N X
      else simulate s.configs s.topology s.announcements
    match dp with
    | .error e => IO.println (Json.mkObj [("failed", e)]).compress; pure 4
    | .ok dp =>
      let answers := qs.filterMap fun q => (questions.find? (·.1 == q)).map fun (_, f) => (q, f s.configs dp)
      IO.println (Json.mkObj answers).compress
      pure 0

/-- Check that the converged state is a stable state of the dynamics. Exits with 1 if not,
3 if the network is outside the modeled subset and 4 if the simulation fails. -/
def checkStable (dir : System.FilePath) : IO UInt32 := do
  match ← Decode.snapshot dir with
  | .error (.rejected r) => IO.println (Json.mkObj [("rejected", toString r)]).compress; pure 3
  | .error (.failed e) => throw <| .userError e
  | .ok s =>
    let result : EvalM _ := do
      let N ← Model.Network.build s
      unstableRouters N (← simulate s.configs s.topology s.announcements)
    match result with
    | .error e => IO.println (Json.mkObj [("failed", e)]).compress; pure 4
    | .ok unstable =>
      let rows := unstable.map fun (h, v, ts) =>
        Json.mkObj [("node", h), ("vrf", v), ("tables", toJson ts)]
      IO.println (Json.mkObj [("stable", unstable.isEmpty), ("unstable", Json.arr rows)]).compress
      pure (if unstable.isEmpty then 0 else 1)

end LeanBatfishSim

def main (args : List String) : IO UInt32 := do
  match args with
  | "answer" :: "--dynamics" :: dir :: qs@(_ :: _) => LeanBatfishSim.answer dir qs true
  | "answer" :: dir :: qs@(_ :: _) => LeanBatfishSim.answer dir qs
  | ["check-stable", dir] => LeanBatfishSim.checkStable dir
  | ["inspect", path] => LeanBatfishSim.inspect path
  | "decode" :: paths@(_ :: _) => LeanBatfishSim.decode paths
  | _ => IO.eprintln LeanBatfishSim.usage; pure 2
