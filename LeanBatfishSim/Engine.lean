import LeanBatfishSim.Bgp.Process
import LeanBatfishSim.Ospf
import LeanBatfishSim.Schedule
import LeanBatfish.Model.Router

/-!
# The simulation engine

Runs a network to its converged data plane: the main RIB and the FIB of every VRF of
every node. It mirrors the phases of Batfish's IBDP engine:

1. **Local routes.** Each VRF starts from its connected, local and static routes.
2. **OSPF internal routes.** Intra-area, then inter-area routes are exchanged until no
   process changes; this does not depend on the main RIBs.
3. **The main loop**, round by round until nothing changes. A round starts with
   redistribution into OSPF and BGP from the previous round's main-RIB changes; then nodes
   are updated color class by color class (`Schedule`): static and generated routes are
   activated, OSPF external routes and BGP routes are exchanged, and the main RIB is
   updated.
4. **Forwarding.** The FIB of each VRF is computed from its main RIB.

OSPF intra- and inter-area exchanges have a single stable state, so they are computed by
synchronous iteration to a fixed point. BGP and OSPF external routes can depend on the
order in which routes arrive (BGP's `ARRIVAL_ORDER` tie breaker; see `Ospf` for external
routes), so they are run the way Batfish runs them, with each process pulling or
receiving its neighbors' changes.

Adjacencies are taken from Batfish's `ospfEdges` and `bgpEdges` answers for now.
-/

namespace LeanBatfishSim

open LeanBatfish Std

/-- The converged state of one VRF. -/
structure VrfDataPlane where
  node : String
  vrf : String
  rib : Rib
  fib : Array FibEntry

/-- The converged data plane of a network, ordered by node and then VRF. -/
structure DataPlane where
  vrfs : Array VrfDataPlane
  /-- The BGP RIB of each BGP process: node, VRF, and its routes. -/
  bgp : Array (String × String × Array Route) := #[]
  /-- The converged routing tables of each VRF (node, VRF, tables), in the form of the
  declarative dynamics' router states (`LeanBatfish.Model.RouterState`). -/
  states : Array (String × String × Model.RouterState) := #[]

/-! ## VRFs -/

/-- The routing state of a VRF during the computation. -/
structure VrfState where
  config : Configuration
  vrf : Vrf
  /-- Connected, local and unconditional static routes. -/
  base : Array Route
  statics : Array Route
  activeStatics : Array Route := #[]
  /-- Generated routes activated so far; Batfish never deactivates them. -/
  generated : Array Route := #[]
  rib : Rib := {}
  deriving Inhabited

def VrfState.init (c : Configuration) (v : Vrf) : VrfState :=
  let statics := v.staticRoutes.map (·.toRoute)
  { config := c, vrf := v, statics
    base := connectedRoutes c v.name ++ localRoutes c v.name ++
      statics.filter (!·.isConditionalStatic) }

/-- Activate static routes until nothing changes. -/
def settleStatics (c : Configuration) (v : Vrf) (statics : Array Route) (rib : Rib) :
    EvalM Rib := do
  let mut rib := rib
  for _ in [0:maxRounds] do
    let (rib', changed) ← activateStatics c v statics rib
    rib := rib'
    if !changed then return rib
  throw s!"static routes of VRF {v.name} did not converge"

/-- Recompute the main RIB of a VRF from its local routes, the given protocol routes and
the static routes that were active, then activate static routes again. -/
def VrfState.refresh (s : VrfState) (protocolRoutes : Array Route) : EvalM VrfState := do
  let rib := Rib.ofRoutes (s.base ++ protocolRoutes ++ s.activeStatics)
  let rib ← settleStatics s.config s.vrf s.statics rib
  let active := s.statics.filter fun r =>
    r.isConditionalStatic && (rib.offered.getD r.network #[]).contains r
  return { s with rib, activeStatics := active }

/-! ## BGP sessions -/

/-- The endpoint of a BGP session on `host` for the peer at `peerIp`. -/
private def bgpEndpoint (configs : HashMap String Configuration) (host : String) (peerIp : Ip) :
    EvalM Bgp.Endpoint := do
  let some c := configs[host]? | throw s!"BGP edge to unknown node {host}"
  Bgp.endpoint c peerIp

/-- A neighbor configuration's identity as Batfish orders it (`BgpPeerConfigId`): node, VRF,
type (active before passive), and the peer prefix. -/
private def peerKey (e : Bgp.Endpoint) : List (String ⊕ Nat) :=
  let (kind, addr, len) := match e.peer.remote with
    | .address ip => (0, ip.bits.toNat, 32)
    | .prefix p => (1, p.addr.bits.toNat, p.len.val)
  [.inl e.host, .inl e.vrf, .inr kind, .inr addr, .inr len]

private def lexLt : List (String ⊕ Nat) → List (String ⊕ Nat) → Bool
  | [], _ :: _ => true
  | .inl a :: as, .inl b :: bs => a < b || (a == b && lexLt as bs)
  | .inr a :: as, .inr b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

/-- Batfish's order of a process's incoming sessions (`EdgeId`): by the sender's neighbor
configuration, then by the receiver's. -/
private def edgeKey (e : InEdge) : List (String ⊕ Nat) :=
  peerKey e.session.remoteEnd ++ peerKey e.session.localEnd

private def keyLt := lexLt

/-- The BGP processes of the network with their incoming sessions. -/
def buildBgp (configs : HashMap String Configuration) (sorted : Array Configuration)
    (edges : Array BgpEdge) : EvalM (Array BgpProc) := do
  let mut procs : Array BgpProc := #[]
  for c in sorted do
    for (_, v) in c.vrfs.qsort (·.1 < ·.1) do
      if let some p := v.bgpProcess then procs := procs.push (BgpProc.init c v p)
  let find (host vrf : String) : Option Nat := procs.findIdx? fun p => p.host == host && p.vrf == vrf
  for e in edges do
    let receiver ← bgpEndpoint configs e.headHost e.tailIp
    let sender ← bgpEndpoint configs e.tailHost e.headIp
    let session ← Bgp.Session.make receiver sender e.headIp e.tailIp
    let some r := find receiver.host receiver.vrf | throw "no BGP process"
    let some t := find sender.host sender.vrf | throw "no BGP process"
    procs := procs.modify r fun p => { p with incoming := p.incoming.push { session, sender := t } }
  return procs.map fun p => { p with incoming := p.incoming.qsort fun a b => keyLt (edgeKey a) (edgeKey b) }

/-! ## The network -/

/-- The changes from one main RIB to another, as a delta: withdrawals, then additions. -/
def ribDiff (old new : Rib) : Array Advert :=
  let o := old.routes
  let n := new.routes
  (o.filter (!n.contains ·)).map ({ route := ·, reason := .withdraw }) ++
    (n.filter (!o.contains ·)).map ({ route := · })

/-- Rebuild a VRF's main RIB from its local routes, protocol routes and active statics. -/
def VrfState.rebuild (s : VrfState) (protocolRoutes : Array Route) : VrfState :=
  { s with rib := Rib.ofRoutes (s.base ++ protocolRoutes ++ s.activeStatics ++ s.generated) }

/-- Activate generated routes until no more activate (`recomputeGeneratedRoutes`). -/
def VrfState.generate (s : VrfState) : EvalM VrfState := do
  if s.vrf.generatedRoutes.isEmpty then return s
  let mut s := s
  for _ in [0:maxRounds] do
    let contributors := s.rib.routes.qsort fun a b =>
      a.network.addr.bits < b.network.addr.bits ||
        (a.network.addr.bits == b.network.addr.bits && a.network.len < b.network.len)
    let mut added := false
    for g in s.vrf.generatedRoutes do
      if let some r ← g.activate s.config contributors then
        if !s.generated.contains r then
          s := { s with generated := s.generated.push r, rib := s.rib.offer r }
          added := true
    if !added then return s
  throw "generated routes did not converge"

/-- One pass of static-route activation on the current main RIB. -/
def VrfState.activate (s : VrfState) : EvalM VrfState := do
  let (rib, _) ← activateStatics s.config s.vrf s.statics s.rib
  let active := s.statics.filter fun r =>
    r.isConditionalStatic && (rib.offered.getD r.network #[]).contains r
  return { s with rib, activeStatics := active }

/-- The routing tables of each VRF as router states of the declarative dynamics. BGP routes
are listed in the order they arrived. -/
def tables (vrfs : Array VrfState) (ospf : OspfWorld) (procs : Array BgpProc) :
    Array (String × String × Model.RouterState) :=
  vrfs.map fun s =>
    let host := s.config.hostname
    let vrf := s.vrf.name
    let o := (List.range ospf.net.procs.size).find? fun i =>
      ospf.net.procs[i]!.id.host == host && ospf.net.procs[i]!.id.vrf == vrf
    let b := procs.find? fun p => p.host == host && p.vrf == vrf
    let st : Model.RouterState := {
      main := s.rib.routes
      ospfIntra := (o.map fun i => ospf.net.states[i]!.intra.routes).getD #[]
      ospfInter := (o.map fun i => ospf.net.states[i]!.inter.routes).getD #[]
      ospfE1 := (o.map fun i => ospf.ext[i]!.e1.routes).getD #[]
      ospfE2 := (o.map fun i => ospf.ext[i]!.e2.routes).getD #[]
      bgp := (b.map fun p =>
        let kept := p.rib.tree.fold (fun acc _ rs => acc ++ rs) #[]
        kept.qsort fun x y => p.rib.arrival.getD x 0 < p.rib.arrival.getD y 0).getD #[]
      bgpBest := (b.map (·.rib.bestPathRoutes)).getD #[]
      pathIds := (b.map (·.pathIds.toArray)).getD #[] }
    (host, vrf, st)

def simulate (configs : Array Configuration) (topology : Topology)
    (announcements : Array Announcement := #[]) : EvalM DataPlane := do
  let byHost : HashMap String Configuration :=
    configs.foldl (fun m c => m.insert c.hostname c) {}
  let sorted := configs.qsort (·.hostname < ·.hostname)
  let mut vrfs : Array VrfState := #[]
  for c in sorted do
    for (_, v) in c.vrfs.qsort (·.1 < ·.1) do
      vrfs := vrfs.push (VrfState.init c v)
  let vrfIndex (host vrf : String) : Option Nat :=
    vrfs.findIdx? fun s => s.config.hostname == host && s.vrf.name == vrf
  -- IGP: OSPF internal routes, then static routes.
  let mut ospf := OspfWorld.init (← (← OspfNet.build byHost topology.ospf).internal)
  let mut next := #[]
  for s in vrfs do
    next := next.push (← s.refresh (ospf.mainRibRoutes s.config.hostname s.vrf.name))
  vrfs := next
  let ospfVrf : Array Nat := ospf.net.procs.map fun p => (vrfIndex p.id.host p.id.vrf).getD 0
  -- EGP: BGP and everything that depends on the main RIBs.
  let mut procs ← buildBgp byHost sorted topology.bgp
  let procVrf : Array Nat := procs.map fun p => (vrfIndex p.host p.vrf).getD 0
  procs := procs.mapIdx fun i p =>
    if p.exportFromBgpRib then p else { p with mainRibPrev := vrfs[procVrf[i]!]!.rib.routes }
  procs := procs.map (·.stageExternal announcements)
  -- Number the main RIB's routes for add-path sessions (`preallocatePathIdsForCurrentRoutes`).
  for i in [0:procs.size] do
    let p := procs[i]!
    if p.anyAddPath && !p.exportFromBgpRib then
      procs := procs.set! i (← p.preallocate (p.mainRibPrev.filter (!·.isBgpRoute)))
  let ospfRoutes (s : VrfState) (o : OspfWorld) := o.mainRibRoutes s.config.hostname s.vrf.name
  let bgpRoutes (ps : Array BgpProc) (k : Nat) : Array Route := Id.run do
    let mut out := #[]
    for i in [0:ps.size] do
      if procVrf[i]! == k then out := out ++ (ps[i]!.rib.routes.filter (!·.nonRouting))
    return out
  let schedule := Schedule.nodeSchedule (sorted.map (·.hostname))
    ((topology.bgp.map fun e => (e.tailHost, e.headHost)) ++
     (topology.ospf.map fun e => (e.tail.host, e.head.host)))
  let mut deltaPrev : Array (Array Advert) := vrfs.map (·.rib.routes.map ({ route := · }))
  for _ in [0:maxRounds] do
    -- Redistribution and next-hop resolution, from the previous round's changes.
    for i in [0:ospf.net.procs.size] do
      ospf ← ospf.redistribute i deltaPrev[ospfVrf[i]!]!
    for i in [0:procs.size] do
      let k := procVrf[i]!
      procs := procs.set! i (← procs[i]!.redistribute { rib := vrfs[k]!.rib } deltaPrev[k]!)
    for i in [0:procs.size] do
      let k := procVrf[i]!
      procs := procs.set! i (procs[i]!.updateResolvable { rib := vrfs[k]!.rib } deltaPrev[k]!)
    let roundStart := vrfs.map (·.rib)
    for step in schedule do
      for k in [0:vrfs.size] do
        if !step.contains vrfs[k]!.config.hostname then continue
        vrfs := vrfs.set! k (← (← vrfs[k]!.activate).generate)
        for oi in [0:ospf.net.procs.size] do
          if ospfVrf[oi]! == k then ospf ← ospf.iterate oi
        vrfs := vrfs.set! k (vrfs[k]!.rebuild (ospfRoutes vrfs[k]! ospf ++ bgpRoutes procs k))
        let some i := procVrf.findIdx? (· == k) | continue
        let mut proc := procs[i]!.startOfInnerRound
        proc ← proc.injectExternal { rib := vrfs[k]!.rib }
        for e in proc.incoming do
          let (outs, sender) ← procs[e.sender]!.outgoing vrfs[procVrf[e.sender]!]!.rib
            e.session.reverse proc.newSessions
          procs := procs.set! e.sender sender
          let outs := outs.filter (·.withdrawn) ++ outs.filter (!·.withdrawn)
          for a in outs do
            let some r ← Bgp.importRoute proc.config e.session a.route | continue
            let main : MainRibView := { rib := vrfs[k]!.rib }
            proc := if a.withdrawn then proc.removeRoute main r else proc.mergeRoute main r
        proc ← proc.aggregates { rib := vrfs[k]!.rib }
        procs := procs.set! i proc
        vrfs := vrfs.set! k (vrfs[k]!.rebuild (ospfRoutes vrfs[k]! ospf ++ bgpRoutes procs k))
        procs := procs.set! i (← procs[i]!.endOfInnerRound)
    procs := procs.map (·.endOfRound)
    vrfs := vrfs.mapIdx fun k s => s.rebuild (ospfRoutes s ospf ++ bgpRoutes procs k)
    deltaPrev := (vrfs.zip roundStart).map fun (s, old) => ribDiff old s.rib
    if deltaPrev.all (·.isEmpty) && !procs.any (·.isDirty) && !ospf.isDirty then
      let mut out := #[]
      for s in vrfs do
        out := out.push { node := s.config.hostname, vrf := s.vrf.name, rib := s.rib
                          fib := ← computeFib s.config s.vrf s.rib : VrfDataPlane }
      return { vrfs := out, bgp := procs.map fun p => (p.host, p.vrf, p.rib.routes)
               states := tables vrfs ospf procs }
  throw "the data plane did not converge"

end LeanBatfishSim
