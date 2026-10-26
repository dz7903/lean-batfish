import LeanBatfishSim.Bgp.Rib

/-!
# BGP processes

The BGP process of a VRF, as Batfish's engine runs it (`BgpRoutingProcess`). Processes do
not send messages; each pulls from its neighbors what they would send, computed from the
neighbor's changes in its previous inner round (its *previous deltas*), or from its whole
RIB when the session is new.

What a process exports on a session:

* the best paths of its BGP RIB (all paths with add-path) that are active in its main RIB,
  originated by itself, or reflectable; with `advertise-inactive`, all of them;
* for Juniper-style processes, which do not export from the BGP RIB, the non-BGP routes of
  its main RIB, through the neighbor's export policy.
-/

namespace LeanBatfishSim

open LeanBatfish Std

/-- A session on which a process receives routes. -/
structure InEdge where
  /-- The session seen from the receiver: `localEnd` is the receiving process. -/
  session : Bgp.Session
  /-- The index of the sending process. -/
  sender : Nat
  deriving Inhabited

structure BgpProc where
  host : String
  vrf : String
  config : Configuration
  process : BgpProcess
  /-- Cisco-style origination: local routes enter the BGP RIB by redistribution. -/
  exportFromBgpRib : Bool
  rib : BgpRib
  mpBuilder : Delta := {}
  bpBuilder : Delta := {}
  mpPrev : Array Advert := #[]
  bpPrev : Array Advert := #[]
  prevBest : Array Route := #[]
  /-- This round's main-RIB delta, for processes that export from the main RIB. -/
  mainRibDelta : Array Advert := #[]
  /-- The whole main RIB, sent on new sessions by processes that export from the main RIB. -/
  mainRibPrev : Array Route := #[]
  /-- Whether this round is the first on the process's sessions. -/
  newSessions : Bool := true
  incoming : Array InEdge := #[]
  /-- All routes of the RIB at the start of the inner round, kept for add-path sessions. -/
  prevAll : Array Route := #[]
  /-- The add-path path ID of each route this process has sent or will send. -/
  pathIds : HashMap Route Nat := {}
  /-- The last path ID used for each prefix. -/
  pathIdGen : HashMap Prefix Nat := {}
  /-- External announcements to inject in the first iteration. -/
  external : Array Announcement := #[]
  /-- The neighbor-specific generated routes last sent on each session, by the remote
  node and IP (`_generatedRoutesSentByEdge`). -/
  generatedSent : HashMap (String × Ip) (Array Route) := {}
  deriving Inhabited

namespace BgpProc

def settings (p : BgpProcess) : Bgp.RibSettings := Bgp.ribSettings p

def init (c : Configuration) (v : Vrf) (p : BgpProcess) : BgpProc := {
  host := c.hostname, vrf := v.name, config := c, process := p
  exportFromBgpRib := c.exportBgpFromBgpRib
  rib := { settings := settings p, networkNhTieBreaker := p.networkNextHopIpTieBreaker
           redistributeNhTieBreaker := p.redistributeNextHopIpTieBreaker } }

/-- Apply a RIB update and record its deltas. -/
def update (proc : BgpProc) (main : MainRibView) (op : BgpRib.M Deltas) : BgpProc :=
  let (d, rib) := (op.run proc.rib).run main |>.run
  { proc with rib, mpBuilder := proc.mpBuilder.append d.multipath
              bpBuilder := proc.bpBuilder.append d.bestPath }

def mergeRoute (proc : BgpProc) (main : MainRibView) (r : Route) : BgpProc :=
  proc.update main (BgpRib.merge r)

def removeRoute (proc : BgpProc) (main : MainRibView) (r : Route) : BgpProc :=
  proc.update main (BgpRib.remove r)

/-! ## Add-path path IDs -/

/-- Whether some session of this process sends all paths. -/
def anyAddPath (proc : BgpProc) : Bool := proc.incoming.any (·.session.reverse.additionalPaths)

/-- The path ID of a route, assigning the next one for its prefix if it has none
(`routesToPathIds.computeIfAbsent`). -/
def pathId (proc : BgpProc) (r : Route) : BgpProc × Nat :=
  match proc.pathIds[r]? with
  | some id => (proc, id)
  | none =>
    let id := proc.pathIdGen.getD r.network 0 + 1
    ({ proc with pathIds := proc.pathIds.insert r id,
                 pathIdGen := proc.pathIdGen.insert r.network id }, id)

/-- The Java hash code Batfish orders a route by when numbering paths: BGP routes as
themselves, other main-RIB routes annotated with their VRF. -/
def javaHash (proc : BgpProc) (r : Route) : EvalM UInt32 := do
  if r.isBgpRoute then return JavaHash.bgpv4Route r
  match JavaHash.nonBgpRoute r with
  | some h => return JavaHash.annotated h proc.vrf
  | none => throw s!"add-path numbering of {repr r.protocol} routes is not simulated yet"

/-- Assign path IDs to a batch of routes in Batfish's order: by Java hash code
(`preallocatePathIds`). -/
def preallocate (proc : BgpProc) (routes : Array Route) : EvalM BgpProc := do
  let fresh := routes.filter (!proc.pathIds.contains ·)
  let keyed ← fresh.mapM fun r => do return (JavaHash.signed (← proc.javaHash r), r)
  let sorted := keyed.qsort (fun a b => a.1 < b.1)
  return sorted.foldl (fun p (_, r) => (p.pathId r).1) proc

/-- Redistribute the main-RIB delta of the previous round (`BgpRoutingProcess.redistribute`). -/
def redistribute (proc : BgpProc) (main : MainRibView) (delta : Array Advert) :
    EvalM BgpProc := do
  let p := proc.process
  let mut proc := proc
  if !proc.exportFromBgpRib then
    proc := { proc with mainRibDelta := delta }
    if proc.anyAddPath then
      proc ← proc.preallocate ((delta.filter fun a => !a.withdrawn && !a.route.isBgpRoute).map (·.route))
  let policies : List (Option String × OriginMechanism) :=
    if proc.exportFromBgpRib then
      [(p.redistributionPolicy, .redistribute), (p.independentNetworkPolicy, .network)]
    else [(p.redistributionPolicy, .redistribute)]
  for (name, mech) in policies do
    let some policy := name.bind proc.config.routingPolicies.find? | continue
    for a in delta do
      if let some b ← Bgp.redistribute proc.config p policy mech a.route then
        proc := if a.withdrawn then proc.removeRoute main b else proc.mergeRoute main b
  return proc

/-- Re-check next-hop resolvability after main-RIB changes (`updateResolvableRoutes`). -/
def updateResolvable (proc : BgpProc) (main : MainRibView) (delta : Array Advert) : BgpProc :=
  proc.update main (BgpRib.updateActiveRoutes (delta.map (·.route.network)))

/-! ## Exporting -/

/-- What `sender` sends on a session (`getOutgoingRoutesForEdge`). `s` is the session seen
from the sender; `senderMain` the sender's main RIB. -/
def outgoing (sender : BgpProc) (senderMain : Rib) (s : Bgp.Session) (isNew : Bool) :
    EvalM (Array Advert × BgpProc) := do
  let mut sender := sender
  let mut out : Array Advert := #[]
  -- Best paths of the BGP RIB, or all paths on add-path sessions.
  let (prev, deltaPrev) := if s.additionalPaths then (sender.prevAll, sender.mpPrev)
    else (sender.prevBest, sender.bpPrev)
  let mut exports : Delta := {}
  if isNew then
    for r in prev do exports := exports.add r
  for a in deltaPrev do exports := exports.push a
  for a in exports.toArray do
    let r := a.route
    let keep := s.advertiseInactive || a.withdrawn ||
      (sender.exportFromBgpRib && (r.bgp.map (·.receivedFrom)) == some .self) ||
      Bgp.isReflectable r sender.process.clientToClientReflection s ||
      senderMain.isActive r
    if !keep then continue
    if let some r' ← Bgp.exportRoute sender.config s r then
      let r' ← if s.additionalPaths then do
          let (sender', id) := sender.pathId r
          sender := sender'
          pure (r'.modifyBgp ({ · with pathId := some id }))
        else pure r'
      let adv : Advert := { route := r', reason := if a.withdrawn then .withdraw else .add }
      if !out.contains adv then out := out.push adv
  -- Neighbor-specific generated routes: what became active is sent, what stopped being
  -- active is withdrawn.
  let mut active : Array Route := #[]
  let contributors := senderMain.routes
  for g in s.localEnd.peer.generatedRoutes do
    let some r ← g.activate sender.config contributors | continue
    let attr := g.attributePolicy.bind sender.config.routingPolicies.find?
    let b ← Bgp.fromGenerated sender.config r attr sender.process.routerId (.ip s.localIp)
    if let some r' ← Bgp.exportRoute sender.config s b then
      if !active.contains r' then active := active.push r'
  let key := (s.remoteEnd.host, s.remoteIp)
  let before := if isNew then #[] else sender.generatedSent.getD key #[]
  sender := { sender with generatedSent := sender.generatedSent.insert key active }
  let generatedAdverts : Array Advert :=
    (before.filter (!active.contains ·)).map ({ route := ·, reason := .withdraw }) ++
    (active.filter (!before.contains ·)).map ({ route := · })
  -- Main-RIB routes, for processes that do not export from the BGP RIB.
  if !sender.exportFromBgpRib then
    let candidates := (if isNew then sender.mainRibPrev.map ({ route := · }) else #[]) ++
      sender.mainRibDelta
    for a in candidates do
      if a.route.isBgpRoute then continue
      let attrPolicy (g : Route) : Option RoutingPolicy :=
        (sender.config.vrfs.find? sender.vrf).bind fun v =>
          (v.generatedRoutes.find? (·.network == g.network)).bind fun gr =>
            gr.attributePolicy.bind sender.config.routingPolicies.find?
      if let some r' ← Bgp.exportMainRibRoute sender.config s a.route attrPolicy then
        let r' ← if s.additionalPaths then do
            let (sender', id) := sender.pathId a.route
            sender := sender'
            pure (r'.modifyBgp ({ · with pathId := some id }))
          else pure r'
        out := out.push { route := r', reason := a.reason }
  return (out ++ generatedAdverts, sender)

/-! ## Aggregates -/

/-- `initBgpAggregateRoutes`: replace the aggregates in the RIB by those active now. -/
def aggregates (proc : BgpProc) (main : MainRibView) : EvalM BgpProc := do
  let p := proc.process
  if p.aggregates.isEmpty then return proc
  let c := proc.config
  let current := if c.generateBgpAggregatesFromMainRib then main.rib.routes else proc.rib.routes
  let mut delta : Delta := {}
  for r in proc.rib.routes do
    if r.protocol == .aggregate then delta := delta.remove r
  for r in ← Bgp.aggregateRoutes c p current main.rib do
    delta := delta.add r
  let mut proc := proc
  for a in delta.toArray do
    proc := if a.withdrawn then proc.removeRoute main a.route else proc.mergeRoute main a.route
  return proc

/-! ## External announcements -/

/-- The announcements this process accepts (`stageExternalAdvertisements`). -/
def stageExternal (proc : BgpProc) (all : Array Announcement) : BgpProc :=
  { proc with external := all.filter (Bgp.acceptsAnnouncement proc.config proc.process) }

/-- Inject the staged announcements (`processExternalBgpAdvertisement`). -/
def injectExternal (proc : BgpProc) (main : MainRibView) : EvalM BgpProc := do
  let mut proc := proc
  for a in proc.external do
    if let some r ← Bgp.announcementRoute proc.config proc.process a then
      proc := proc.mergeRoute main r
  return { proc with external := #[] }

/-! ## One inner round -/

/-- `startOfInnerRound`. -/
def startOfInnerRound (proc : BgpProc) : BgpProc :=
  { proc with prevBest := proc.rib.bestPathRoutes
              prevAll := if proc.anyAddPath then proc.rib.routes else #[] }

/-- `endOfInnerRound`: this round's changes become what neighbors pull next. -/
def endOfInnerRound (proc : BgpProc) : EvalM BgpProc := do
  let mp := proc.mpBuilder.toArray
  let proc ← if proc.anyAddPath then
      proc.preallocate ((mp.filter (!·.withdrawn)).map (·.route)) else pure proc
  return { proc with mpPrev := mp, bpPrev := proc.bpBuilder.toArray, mpBuilder := {}, bpBuilder := {} }

/-- `endOfRound`. -/
def endOfRound (proc : BgpProc) : BgpProc :=
  { proc with newSessions := false, mainRibPrev := #[], mainRibDelta := #[] }

/-- Whether the process still has changes to send (`isDirty`). -/
def isDirty (proc : BgpProc) : Bool := !proc.mpPrev.isEmpty || !proc.bpPrev.isEmpty

end BgpProc

end LeanBatfishSim
