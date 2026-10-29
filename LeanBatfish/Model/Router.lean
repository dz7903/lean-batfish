import LeanBatfish.Semantics.Bgp.Aggregate
import LeanBatfish.Semantics.Bgp.Announcement
import LeanBatfish.Semantics.Bgp.JavaHash
import LeanBatfish.Semantics.Bgp.Preference
import LeanBatfish.Semantics.Routing.Generated
import LeanBatfish.Semantics.Routing.Ospf

/-!
# Routers

The configuration semantics of a router, as a step of the routing dynamics
(`LeanBatfish.Theory.System`): from the current states of all routers, what one router holds
after it updates. A *router* here is one VRF of a device, since each VRF has its own routing
tables.

A router's state is its routing tables — the main RIB, the four OSPF tables, and the BGP
RIB — and the IPsec sessions it has up. This module is the routing update
(`Router.updateRoutes`); the sessions are updated in `LeanBatfish.Model.Forwarding`, which
defines the full `Router.update`. The routing update recomputes all tables from what the
neighbors hold now and from the router's own tables:

* **OSPF.** The router originates intra-area routes for its interfaces and external routes
  it redistributes from its main RIB; it receives what each adjacent process holds, sent
  over the adjacency (`Ospf.sendIntra` and the like). Each table keeps, for each prefix, the
  routes of the best metric. As in Batfish, the external routes a router offers its main
  RIB are the ones it received, not its own.
* **BGP.** The router originates routes by redistribution from its main RIB, aggregates,
  and external announcements; it receives what each neighbor exports to it
  (`Bgp.exportRoute`, then `Bgp.importRoute`), and what peers outside the network send
  (the router's *input*). Learned routes whose next hop does not resolve in the main RIB are
  left out. For each prefix the RIB keeps the routes that compare best. Where Batfish's
  comparison does not decide (the `ARRIVAL_ORDER` tie breaker, and multipath routes with
  different AS paths), the routes the RIB already has win: Batfish's outcome depends on
  the order of updates there, and the routes it ended with stay.
* **Main RIB.** For each prefix, the routes of the best administrative distance and
  metric among connected, local and static routes (those whose next hop resolves),
  generated routes, and the OSPF and BGP routes.

An update reads the router's own tables as they were before it, so it is a function of the
current states, as the dynamics require.
-/

namespace LeanBatfish.Model

/-- What a router holds: its routing tables, and the IPsec sessions it has up. -/
structure RouterState where
  /-- The main RIB: its active routes. -/
  main : Array Route := #[]
  /-- The OSPF tables: for each prefix, the routes of the best metric of each kind. -/
  ospfIntra : Array Route := #[]
  ospfInter : Array Route := #[]
  ospfE1 : Array Route := #[]
  ospfE2 : Array Route := #[]
  /-- The BGP RIB: for each prefix, the routes kept as best, in the order they arrived. -/
  bgp : Array Route := #[]
  /-- The best path of each prefix, among `bgp`. -/
  bgpBest : Array Route := #[]
  /-- The add-path identifiers the router has given the routes it sends. -/
  pathIds : Array (Route × Nat) := #[]
  /-- The IPsec links whose security associations are up (`IpsecLink.key`). -/
  ipsec : Array (String × Ip) := #[]
  deriving DecidableEq, Inhabited, Repr

/-- An OSPF adjacency on which a router receives routes. -/
structure OspfLink where
  /-- The index of the sending router. -/
  sender : Nat
  senderAbr : Bool
  adj : Ospf.Adjacency
  deriving Inhabited

/-- A BGP session on which a router receives routes from another router. -/
structure BgpLink where
  /-- The index of the sending router. -/
  sender : Nat
  /-- The session, seen from the receiving router. -/
  session : Bgp.Session
  deriving Inhabited

/-- An IPsec session a router can protect packets with: one of its peer configurations
paired with a peer that negotiates with it (`Ipsec.topology`). Whether its security
association is up is part of the router's state. -/
structure IpsecLink where
  /-- The router's peer configuration. -/
  name : String
  localAddress : Ip
  /-- The peer's address. -/
  remoteAddress : Ip
  /-- The tunnel interface (route-based VPN), or none for a crypto map. -/
  tunnelInterface : Option String
  sourceInterface : String
  /-- The crypto-map ACL selecting the packets to protect. -/
  acl : Option IpAccessList
  /-- How packets are protected: the negotiated phase-2 proposal. -/
  proposal : IpsecPhase2Proposal
  /-- The index of the peer's router. -/
  peer : Nat
  deriving Inhabited

/-- The router state names an IPsec link by its configuration and peer. -/
def IpsecLink.key (l : IpsecLink) : String × Ip := (l.name, l.remoteAddress)

/-- What peers outside the network announce to a router: each route with the address of
the peer that sends it. -/
abbrev Input := Array (Ip × Route)

/-- A router: one VRF of a device, with its configuration and adjacencies. -/
structure Router where
  /-- Its index among the routers of the network. -/
  index : Nat
  config : Configuration
  vrf : Vrf
  /-- Connected, local and unconditional static routes. -/
  base : Array Route
  /-- Static routes whose activation depends on the main RIB. -/
  conditionalStatics : Array Route
  ospf : Option OspfProcess
  ospfExport : Option RoutingPolicy
  ospfLocal : Array Route
  ospfLinks : Array OspfLink
  bgp : Option BgpProcess
  bgpLinks : Array BgpLink
  /-- Sessions with peers outside the network, by the peer's address, seen from the router. -/
  externalPeers : Array (Ip × Bgp.Session)
  /-- The external announcements (`external_bgp_announcements.json`) the router takes. -/
  announcements : Array Announcement
  /-- The sessions on which the router sends all paths (add-path), seen from the router. -/
  addPathSessions : Array Bgp.Session := #[]
  /-- Where the router's interfaces lead: interface name, a remote address on the link, and
  the router owning it. -/
  links : Array (String × Ip × Nat)
  /-- The IPsec sessions the router can have. -/
  ipsecLinks : Array IpsecLink := #[]
  deriving Inhabited

/-! ## Selecting routes -/

/-- `rs` without repeated routes, in order. -/
def dedup (rs : Array Route) : Array Route :=
  rs.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

/-- For each prefix, the routes of least `key`, without repetitions. -/
def bestBy (key : Route → Nat × Nat) (rs : Array Route) : Array Route :=
  dedup <| rs.filter fun r =>
    rs.all fun r' => r'.network != r.network || !Rib.morePreferred (key r') (key r)

/-- The main RIB from the routes offered to it: the best routes of each prefix by
administrative distance, then metric. Non-routing routes never enter it. -/
def mainRib (offered : Array Route) : Array Route :=
  bestBy Rib.mainPreference (offered.filter (!·.nonRouting))

/-- One prefix of a BGP RIB: `AbstractRib`'s merge applied to `rs` in order. A route that
compares better than the first kept route replaces the kept routes; one that compares equal
joins them. -/
def keepBest (cmp : Route → Route → Int) (rs : Array Route) : Array Route :=
  rs.foldl (init := #[]) fun kept r =>
    match kept[0]? with
    | none => #[r]
    | some first =>
      let c := cmp r first
      if c < 0 then kept
      else if c == 0 then (if kept.contains r then kept else kept.push r)
      else #[r]

/-- The best path among kept routes (`selectBestPath`). -/
def bestPath (cmp : Route → Route → Int) (kept : Array Route) : Option Route :=
  kept[0]?.map fun first => kept.foldl (fun b r => if cmp r b > 0 then r else b) first

/-- The arrival time of a route in `order`: its position, or after all of them. -/
def arrivalIn (order : Array Route) (r : Route) : Nat := (order.findIdx? (· == r)).getD order.size

/-- The candidates for prefix `p` in the order they arrived: those `old` already kept first. -/
def arrivalOrder (old cands : Array Route) (p : Prefix) : Array Route :=
  let mine := dedup (cands.filter (·.network == p))
  let incumbents := old.filter fun r => r.network == p && mine.contains r
  incumbents ++ mine.filter (!incumbents.contains ·)

/-- The BGP RIB from its candidate routes: for each prefix, the routes it keeps and its best
path. The routes `old` already kept come first, in their order, and so do their prefixes. -/
def selectBgp (st : Bgp.RibSettings) (main : Rib) (old cands : Array Route) :
    Array Route × Array Route :=
  let prefixes := (old ++ cands).foldl (init := #[]) fun ps r =>
    if !ps.contains r.network && cands.any (·.network == r.network) then ps.push r.network else ps
  prefixes.foldl (init := (#[], #[])) fun (kept, best) p =>
    let order := arrivalOrder old cands p
    let arrival := arrivalIn order
    let ks := keepBest (Bgp.comparePreference st (Bgp.igpCost main) arrival) order
    (kept ++ ks, match bestPath (Bgp.bestPathCompare st arrival) ks with
      | some b => best.push b
      | none => best)

/-- The routes a BGP RIB exposes (`BgpRib.getRoutes`): the best paths, or with multipath,
the best route of each prefix and next hop. -/
def exposed (st : Bgp.RibSettings) (kept best : Array Route) : Array Route :=
  if !st.multipath then best else
  let arrival := arrivalIn kept
  kept.foldl (init := #[]) fun acc r =>
    match acc.findIdx? fun o => o.nextHop == r.nextHop && o.network == r.network with
    | none => acc.push r
    | some i => if Bgp.bestPathCompare st arrival r acc[i]! > 0 then acc.set! i r else acc

/-- Locally originated routes compete per origin mechanism and prefix: only the first by
next-hop IP (as configured), then source protocol, enters the RIB (`addLocalRoute`). -/
def localBest (p : BgpProcess) (rs : Array Route) : Array Route :=
  rs.foldl (init := #[]) fun acc r =>
    let mech := (r.bgp.map (·.originMechanism)).getD .learned
    match acc.findIdx? fun o => o.network == r.network &&
        (o.bgp.map (·.originMechanism)).getD .learned == mech with
    | none => acc.push r
    | some i => if less mech r acc[i]! then acc.set! i r else acc
where
  key (x : Route) : Option Ip × Nat :=
    (x.nextHopIp?, match x.bgp.bind (·.srcProtocol) with
      | some q => (RoutingProtocol.names.findIdx? (·.2 == q)).getD 0
      | none => 0)
  less (mech : OriginMechanism) (a b : Route) : Bool :=
    let tie := if mech == .network then p.networkNextHopIpTieBreaker
      else p.redistributeNextHopIpTieBreaker
    match key a, key b with
    | (none, pa), (none, pb) => pa < pb
    | (none, _), (some _, _) => true
    | (some _, _), (none, _) => false
    | (some x, pa), (some y, pb) =>
      if x == y then pa < pb
      else if tie == .highestNextHopIp then y.bits < x.bits else x.bits < y.bits

/-- A route from the same neighbor with the same path ID replaces an earlier one
(`evictSamePrefixReceivedFromPathId`); locally originated routes do not replace others. -/
def evictSameSource (rs : Array Route) : Array Route :=
  rs.foldl (init := #[]) fun acc r =>
    let trackable := (r.bgp.map (·.isTrackableLocal)).getD false
    let source (x : Route) := (x.network, x.bgp.map (·.receivedFrom), x.bgp.map (·.pathId))
    if trackable then acc.push r else (acc.filter (source · != source r)).push r

/-! ## Updates -/

namespace Router

/-- The Java hash code Batfish numbers a route's path by. -/
def pathHash (r : Router) (x : Route) : EvalM UInt32 := do
  if x.isBgpRoute then return JavaHash.bgpv4Route x
  match JavaHash.nonBgpRoute x with
  | some h => return JavaHash.annotated h r.vrf.name
  | none => throw s!"no path-ID hash for {repr x.protocol} routes"

/-- Give add-path identifiers to the routes that do not have one, in the order of their
Java hash codes, numbering each prefix's paths in sequence (`preallocatePathIds`). -/
def assignPathIds (r : Router) (ids : Array (Route × Nat)) (rs : Array Route) :
    EvalM (Array (Route × Nat)) := do
  let fresh := dedup (rs.filter fun x => !ids.any (·.1 == x))
  let keyed ← fresh.mapM fun x => do return (JavaHash.signed (← r.pathHash x), x)
  let sorted := keyed.qsort (fun a b => a.1 < b.1)
  return sorted.foldl (init := ids) fun ids (_, x) =>
    let last := ids.foldl (fun m (y, id) => if y.network == x.network then max m id else m) 0
    ids.push (x, last + 1)

def withPathId (ids : Array (Route × Nat)) (original exported : Route) : EvalM Route :=
  match ids.find? (·.1 == original) with
  | some (_, id) => pure (exported.modifyBgp ({ · with pathId := some id }))
  | none => throw s!"a route sent with add-path has no path ID: {repr original.protocol} {original.network} {repr original.nextHop}"

/-- Run `f` on each element of `xs`, collecting what it produces, in order. -/
def collect (xs : List α) (f : α → EvalM (Array β)) : EvalM (Array β) :=
  match xs with
  | [] => pure #[]
  | x :: xs => do return (← f x) ++ (← collect xs f)

/-- The BGP and main-RIB routes router `k`, in state `ks`, exports over session `s` (seen
from `k`), each with the route it was exported from. -/
def exportPairs (k : Router) (ks : RouterState) (s : Bgp.Session) :
    EvalM (Array (Route × Route)) := do
  let some p := k.bgp | return #[]
  let c := k.config
  let main := Rib.ofRoutes ks.main
  let st := Bgp.ribSettings p
  -- The best paths of the BGP RIB, or all exposed routes with add-path.
  let candidates := if s.additionalPaths then exposed st ks.bgp ks.bgpBest else ks.bgpBest
  let keep (r : Route) : Bool := s.advertiseInactive ||
    (c.exportBgpFromBgpRib && (r.bgp.map (·.receivedFrom)) == some .self) ||
    Bgp.isReflectable r p.clientToClientReflection s || main.isActive r
  let fromRib ← collect candidates.toList fun r =>
    if keep r then return ((← Bgp.exportRoute c s r).map (r, ·)).toArray else pure #[]
  -- Juniper-style routers export main-RIB routes directly.
  let attrPolicy (g : Route) : Option RoutingPolicy :=
    (k.vrf.generatedRoutes.find? (·.network == g.network)).bind fun gr =>
      gr.attributePolicy.bind c.routingPolicies.find?
  let fromMain ← if c.exportBgpFromBgpRib then pure #[] else
    collect ks.main.toList fun r =>
      if r.isBgpRoute then pure #[]
      else return ((← Bgp.exportMainRibRoute c s r attrPolicy).map (r, ·)).toArray
  return fromRib ++ fromMain

/-- What router `k`, in state `ks`, sends over session `s` (seen from `k`). -/
def exports (k : Router) (ks : RouterState) (s : Bgp.Session) : EvalM (Array Route) := do
  let some p := k.bgp | return #[]
  let c := k.config
  let sent ← collect (← k.exportPairs ks s).toList fun (r, r') => do
    return #[← if s.additionalPaths then withPathId ks.pathIds r r' else pure r']
  -- Routes generated for this neighbor only, such as `default-originate`.
  let generated ← collect s.localEnd.peer.generatedRoutes.toList fun g => do
    let some gr ← g.activate c ks.main | return #[]
    let b ← Bgp.fromGenerated c gr (g.attributePolicy.bind c.routingPolicies.find?) p.routerId
      (.ip s.localIp)
    return (← Bgp.exportRoute c s b).toArray
  return generated.foldl (fun acc x => if acc.contains x then acc else acc.push x) sent

/-- The routes the adjacent OSPF processes hold in one table, as the router receives them
over each adjacency. -/
def ospfReceived (r : Router) (X : Nat → RouterState) (table : RouterState → Array Route)
    (send : OspfLink → Route → EvalM (Option Route)) : EvalM (Array Route) :=
  collect r.ospfLinks.toList fun l =>
    collect (table (X l.sender)).toList fun x => return (← send l x).toArray

/-- The external routes a router's OSPF process `p` originates: what its export policy
accepts of its main RIB and of its generated routes. -/
def ospfOwn (r : Router) (p : OspfProcess) (old : RouterState) : EvalM (Array Route) :=
  match r.ospfExport with
  | none => pure #[]
  | some pol => do
    let gens ← collect p.generatedRoutes.toList fun g =>
      return (← g.activate r.config old.main).toArray
    collect (old.main ++ gens).toList fun x => return (← Ospf.redistribute r.config p pol x).toArray

/-- The OSPF tables after an update, and the OSPF routes offered to the main RIB. -/
def ospfStep (r : Router) (X : Nat → RouterState) (old : RouterState) :
    EvalM (Array Route × Array Route × Array Route × Array Route × Array Route) := do
  let some p := r.ospf | return (#[], #[], #[], #[], #[])
  let abr := Ospf.isAbr p
  let intra := r.ospfLocal ++ (← r.ospfReceived X (·.ospfIntra) fun l x => Ospf.sendIntra l.adj p x)
  let inter := (if abr then old.ospfIntra.map Ospf.intraToInter else #[]) ++
    (← r.ospfReceived X (·.ospfInter) fun l x => Ospf.sendInter l.adj l.senderAbr abr p x)
  -- A process does not take back its own external routes (`Ospf.acceptsExternal`).
  let recv1 ← r.ospfReceived X (·.ospfE1) fun l x => do
    return (← Ospf.sendE1 l.adj p x).filter (Ospf.acceptsExternal r.config.hostname ·)
  let recv2 ← r.ospfReceived X (·.ospfE2) fun l x => do
    return (← Ospf.sendE2 l.adj p x).filter (Ospf.acceptsExternal r.config.hostname ·)
  let own ← r.ospfOwn p old
  let intraT := bestBy Ospf.metricKey intra
  let interT := bestBy Ospf.metricKey inter
  let e1 := bestBy Ospf.metricKey (own.filter (·.protocol == .ospfE1) ++ recv1)
  let e2 := bestBy Ospf.e2Key (own.filter (·.protocol == .ospfE2) ++ recv2)
  let offered := intraT ++ interT ++ bestBy Ospf.metricKey recv1 ++ bestBy Ospf.e2Key recv2
  let toMain := (bestBy (fun x => (Ospf.kindRank x.protocol, 0)) offered).filter (!·.nonRouting)
  return (intraT, interT, e1, e2, toMain)

/-- The BGP RIB after an update: kept routes and best paths. -/
def bgpStep (net : Array Router) (r : Router) (X : Nat → RouterState) (old : RouterState)
    (oldMain : Rib) (input : Input) : EvalM (Array Route × Array Route) := do
  let some p := r.bgp | return (#[], #[])
  let c := r.config
  let st := Bgp.ribSettings p
  -- Originated by redistribution from the main RIB.
  let policies : List (Option String × OriginMechanism) :=
    if c.exportBgpFromBgpRib then
      [(p.redistributionPolicy, .redistribute), (p.independentNetworkPolicy, .network)]
    else [(p.redistributionPolicy, .redistribute)]
  let originated ← collect policies fun (name, mech) =>
    match name.bind c.routingPolicies.find? with
    | none => pure #[]
    | some pol => collect old.main.toList fun x =>
      return (← Bgp.redistribute c p pol mech x).toArray
  -- Learned: external announcements, neighbors, and peers outside the network.
  let announced ← collect r.announcements.toList fun a =>
    return (← Bgp.announcementRoute c p a).toArray
  let received ← collect r.bgpLinks.toList fun l => do
    let some k := net[l.sender]? | throw "BGP session from an unknown router"
    collect (← k.exports (X l.sender) l.session.reverse).toList fun x =>
      return (← Bgp.importRoute c l.session x).toArray
  let external ← collect input.toList fun (ip, x) =>
    match r.externalPeers.find? (·.1 == ip) with
    | none => pure #[]
    | some (_, s) => return (← Bgp.importRoute c s x).toArray
  let resolved := (announced ++ received ++ external).filter fun x =>
    match x.nextHop with
    | .ip nh => x.protocol == .aggregate || Bgp.resolvable oldMain nh
    | _ => true
  -- Aggregates, from the BGP RIB or the main RIB.
  let contributors := if c.generateBgpAggregatesFromMainRib then old.main
    else exposed st old.bgp old.bgpBest
  let aggregates ← Bgp.aggregateRoutes c p contributors oldMain
  let cands := evictSameSource (localBest p originated ++ resolved ++ aggregates)
  return selectBgp st oldMain old.bgp cands

/-- The conditional static routes that are active on the main RIB `main`
(`activateStaticRoutes`). -/
def activeStatics (r : Router) (main : Rib) : EvalM (Array Route) :=
  collect r.conditionalStatics.toList fun s => do
    let active ← match s.nextHop with
      | .ip ip => do
        let res ← resolveStaticNextHopIp r.config r.vrf main ip s.recursive
        pure (shouldActivateNextHopIpRoute s ip res)
      | .iface name _ => pure (((r.config.interfaces.find? name).map (·.active)).getD false)
      | .discard => pure true
    return if active then #[s] else #[]

/-- The router's generated routes activated by the main-RIB routes `main`. -/
def generated (r : Router) (main : Array Route) : EvalM (Array Route) := do
  if r.vrf.generatedRoutes.isEmpty then return #[]
  let contributors := main.qsort fun a b =>
    a.network.addr.bits < b.network.addr.bits ||
      (a.network.addr.bits == b.network.addr.bits && a.network.len < b.network.len)
  collect r.vrf.generatedRoutes.toList fun g => return (← g.activate r.config contributors).toArray

/-- The router's state after it updates, given the current states `X` of the routers of
`net` and its input; an error if Batfish would fail. -/
def step (net : Array Router) (r : Router) (X : Nat → RouterState) (input : Input) :
    EvalM RouterState := do
  let old := X r.index
  let oldMain := Rib.ofRoutes old.main
  let (ospfIntra, ospfInter, ospfE1, ospfE2, ospfMain) ← r.ospfStep X old
  let (bgp, bgpBest) ← r.bgpStep net X old oldMain input
  let bgpExposed := match r.bgp with
    | some p => exposed (Bgp.ribSettings p) bgp bgpBest
    | none => #[]
  let main := mainRib (r.base ++ (← r.activeStatics oldMain) ++ (← r.generated old.main) ++
    ospfMain ++ bgpExposed.filter (!·.nonRouting))
  -- Number the routes the router now sends with add-path.
  let new : RouterState := { main, ospfIntra, ospfInter, ospfE1, ospfE2, bgp, bgpBest,
                             pathIds := old.pathIds }
  let sent ← collect r.addPathSessions.toList fun s => return (← r.exportPairs new s).map (·.1)
  return { new with pathIds := ← r.assignPathIds old.pathIds sent }

/-- The router's routing tables after it updates. Where Batfish would fail, the router keeps
its state. The update of IPsec sessions is `Router.update`. -/
def updateRoutes (net : Array Router) (r : Router) (X : Nat → RouterState) (input : Input) :
    RouterState :=
  match r.step net X input with
  | .ok s => s
  | .error _ => X r.index

end Router

end LeanBatfish.Model
