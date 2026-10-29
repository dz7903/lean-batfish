import LeanBatfishSim.Engine
import LeanBatfish.Model.Network

/-!
# Running the dynamics

The declarative semantics of `LeanBatfish.Model` runs too: synchronous iteration from empty
tables, with no announcements from outside, until no router changes. The result is a stable
state of the dynamics. Answering questions from it and comparing with Batfish's answers
checks that the state Batfish converges to is a stable state of the dynamics, and that the
dynamics reaches it.
-/

namespace LeanBatfishSim

open LeanBatfish Model

/-- Iterate the dynamics synchronously from empty tables to a fixed point. -/
def runDynamics (N : Network) (maxSteps : Nat := 1000) : EvalM (Array RouterState × Nat) := do
  let mut X : Array RouterState := Array.replicate N.size {}
  for t in [0:maxSteps] do
    let get := fun k => X.getD k {}
    let mut Y := #[]
    for r in N.routers do
      Y := Y.push { ← r.step N.routers get #[] with ipsec := r.ikeStep N.routers get }
    if Y == X then return (X, t)
    X := Y
  throw "the dynamics did not converge"

/-- The data plane of routers' states, in the form the answers take. -/
def dataPlaneOf (N : Network) (X : Array RouterState) : EvalM DataPlane := do
  let mut vrfs := #[]
  let mut bgp := #[]
  for r in N.routers do
    let x := X.getD r.index {}
    let rib := Rib.ofRoutes x.main
    vrfs := vrfs.push { node := r.config.hostname, vrf := r.vrf.name, rib
                        fib := ← computeFib r.config r.vrf rib : VrfDataPlane }
    if let some p := r.bgp then
      bgp := bgp.push (r.config.hostname, r.vrf.name, exposed (Bgp.ribSettings p) x.bgp x.bgpBest)
  return { vrfs, bgp }

end LeanBatfishSim

namespace LeanBatfishSim

open LeanBatfish Model

private def sameRoutes [BEq α] (a b : Array α) : Bool := a.all b.contains && b.all a.contains

/-- The tables of two router states that hold different routes. -/
def tablesDiffering (a b : RouterState) : List String :=
  [("main", sameRoutes a.main b.main), ("ospfIntra", sameRoutes a.ospfIntra b.ospfIntra),
   ("ospfInter", sameRoutes a.ospfInter b.ospfInter), ("ospfE1", sameRoutes a.ospfE1 b.ospfE1),
   ("ospfE2", sameRoutes a.ospfE2 b.ospfE2), ("bgp", sameRoutes a.bgp b.bgp),
   ("bgpBest", sameRoutes a.bgpBest b.bgpBest), ("pathIds", sameRoutes a.pathIds b.pathIds),
   ("ipsec", sameRoutes a.ipsec b.ipsec)]
  |>.filter (!·.2) |>.map (·.1)

/-- Whether the simulator's converged tables are a stable state of the dynamics: for each
router that an update changes, the tables that change. The simulator does not compute IPsec
sessions; they are brought up on its tables first, until they settle. -/
def unstableRouters (N : Network) (dp : DataPlane) : EvalM (Array (String × String × List String)) := do
  let mut X : Array RouterState := N.routers.map fun r =>
    match dp.states.find? fun (h, v, _) => h == r.config.hostname && v == r.vrf.name with
    | some (_, _, st) => st
    | none => {}
  for _ in [0:N.size + 1] do
    let get := fun k => X.getD k {}
    let Y := N.routers.map fun r => { get r.index with ipsec := r.ikeStep N.routers get }
    if Y == X then break
    X := Y
  let get := fun k => X.getD k {}
  let mut out := #[]
  for r in N.routers do
    let y := { ← r.step N.routers get #[] with ipsec := r.ikeStep N.routers get }
    let d := tablesDiffering y (get r.index)
    if !d.isEmpty then out := out.push (r.config.hostname, r.vrf.name, d)
  return out

end LeanBatfishSim
