import LeanBatfishSim.Bgp.Delta

/-!
# The BGP RIB, as Batfish's engine maintains it

An incremental BGP RIB with Batfish's exact update rules (`AbstractRib` with backups,
`BgpRib` and `Bgpv4Rib`):

* For each prefix the RIB keeps the routes that compare best (`comparePreference`); the
  others wait as backups and are promoted when the active ones are withdrawn. The
  comparison is not symmetric for multipath RIBs (routes with different AS paths each
  lose to the other), so the result depends on the order routes arrive in.
* One of the active routes is the best path (`bestPathComparator`); with `ARRIVAL_ORDER`
  the RIB records when each route arrived.
* A multipath RIB exposes one route per next hop, the best of those with that next hop.
* Locally originated routes (network statements, redistribution) compete per mechanism
  first: only the best by next-hop IP enters the RIB.
* Learned routes whose next-hop IP does not resolve in the main RIB are tracked but kept
  out until it does.

Each update returns the delta of the exposed routes (multipath delta) and the delta of the
best paths.
-/

namespace LeanBatfishSim

open LeanBatfish Std

/-- The main RIB the BGP RIB consults for next-hop resolution and IGP costs. -/
structure MainRibView where
  rib : Rib

namespace MainRibView

def lpm (m : MainRibView) (ip : Ip) : Array Route := Bgp.lpm m.rib ip

/-- `Bgpv4Rib.isResolvable`. -/
def resolvable (m : MainRibView) (ip : Ip) : Bool := Bgp.resolvable m.rib ip

/-- `BgpRib.getIgpCostToNextHopIp`. -/
def igpCost (m : MainRibView) (r : Route) : Nat := Bgp.igpCost m.rib r

end MainRibView

/-- What a BGP RIB update produced: the multipath delta and the best-path delta. -/
structure Deltas where
  multipath : Array Advert := #[]
  bestPath : Array Advert := #[]

structure BgpRib where
  settings : Bgp.RibSettings
  networkNhTieBreaker : NextHopIpTieBreaker
  redistributeNhTieBreaker : NextHopIpTieBreaker
  tree : HashMap Prefix (Array Route) := {}
  backups : HashMap Prefix (Array Route) := {}
  bestPaths : HashMap Prefix Route := {}
  arrival : HashMap Route Nat := {}
  clock : Nat := 0
  /-- Locally originated routes by mechanism and prefix, sorted best first. -/
  localRoutes : HashMap (OriginMechanism × Prefix) (Array Route) := {}
  /-- Learned routes with a next-hop IP, by that IP (`ResolvabilityEnforcer`). -/
  byNhip : HashMap Ip (Array Route) := {}
  byPrefix : HashMap Prefix (Array Route) := {}
  unresolvable : HashSet Ip := {}
  mixed : HashSet Ip := {}
  deriving Inhabited

namespace BgpRib

abbrev M := StateT BgpRib (ReaderT MainRibView Id)

private def arrivalOf (rib : BgpRib) (r : Route) : Nat := rib.arrival.getD r rib.clock

def comparePref (r1 r2 : Route) : M Int := do
  let rib ← get
  let main ← read
  return Bgp.comparePreference rib.settings main.igpCost (arrivalOf rib) r1 r2

def compareBest (r1 r2 : Route) : M Int := do
  let rib ← get
  return Bgp.bestPathCompare rib.settings (arrivalOf rib) r1 r2

private def setInsert (xs : Array Route) (r : Route) : Array Route :=
  if xs.contains r then xs else xs.push r

/-! ## `AbstractRib` with backups -/

private def putBackup (r : Route) : M Unit :=
  modify fun rib => { rib with
    backups := rib.backups.insert r.network (setInsert (rib.backups.getD r.network #[]) r) }

private def removeBackup (r : Route) : M Unit :=
  modify fun rib => { rib with
    backups := match rib.backups[r.network]? with
      | none => rib.backups
      | some bs =>
        let bs := bs.filter (· != r)
        if bs.isEmpty then rib.backups.erase r.network else rib.backups.insert r.network bs }

private def setTree (p : Prefix) (rs : Array Route) : M Unit :=
  modify fun rib => { rib with tree := if rs.isEmpty then rib.tree.erase p else rib.tree.insert p rs }

/-- `AbstractRib.mergeRouteGetDelta`. -/
def abstractMerge (r : Route) : M (Array Advert) := do
  let cur := (← get).tree.getD r.network #[]
  let delta ← match cur[0]? with
    | none => setTree r.network #[r]; pure #[{ route := r }]
    | some old =>
      let c ← comparePref r old
      if c < 0 then pure #[]
      else if c == 0 then
        if cur.contains r then pure #[]
        else setTree r.network (cur.push r); pure #[{ route := r }]
      else
        setTree r.network #[r]
        pure (cur.map (fun o => { route := o, reason := .replace }) |>.push { route := r })
  if delta.isEmpty then
    if !((← get).tree.getD r.network #[]).contains r then putBackup r
  else
    for a in delta do
      if a.reason == .replace then putBackup a.route
  return delta

/-- `CollectionUtil.maxValues` under `comparePreference`. -/
private def maxValues (rs : Array Route) : M (Array Route) := do
  let mut best : Array Route := #[]
  for r in rs do
    match best[0]? with
    | none => best := #[r]
    | some b =>
      let c ← comparePref r b
      if c == 0 then best := best.push r
      else if c > 0 then best := #[r]
  return best

/-- `AbstractRib.removeRouteGetDelta`. -/
def abstractRemove (r : Route) : M (Array Advert) := do
  let cur := (← get).tree.getD r.network #[]
  if !cur.contains r then
    removeBackup r
    return #[]
  let rest := cur.filter (· != r)
  let removal : Advert := { route := r, reason := .withdraw }
  if !rest.isEmpty then
    setTree r.network rest
    return #[removal]
  let backups := (← get).backups.getD r.network #[]
  if backups.isEmpty then
    setTree r.network #[]
    return #[removal]
  let promoted ← maxValues backups
  setTree r.network promoted
  for b in promoted do removeBackup b
  return #[removal] ++ promoted.map ({ route := · })

/-! ## `BgpRib` -/

def isMultipath (rib : BgpRib) : Bool := rib.settings.multipath

/-- `selectBestPath`: the first route that no other active route beats. -/
private def selectBestPath (p : Prefix) : M Unit := do
  let cur := (← get).tree.getD p #[]
  match cur[0]? with
  | none => modify fun rib => { rib with bestPaths := rib.bestPaths.erase p }
  | some first =>
    let mut best := first
    for r in cur do
      if (← compareBest r best) > 0 then best := r
    modify fun rib => { rib with bestPaths := rib.bestPaths.insert p best }

/-- A sorted set under `bestPathComparator`, as Java's `TreeSet`: elements that compare
equal are the same element. -/
private def treeInsert (xs : Array Route) (r : Route) : M (Array Route) := do
  for x in xs do
    if (← compareBest x r) == 0 then return xs
  let mut out := #[]
  let mut placed := false
  for x in xs do
    if !placed && (← compareBest r x) < 0 then
      out := out.push r
      placed := true
    out := out.push x
  if !placed then out := out.push r
  return out

private def treeErase (xs : Array Route) (r : Route) : M (Array Route) := do
  let mut out := #[]
  let mut removed := false
  for x in xs do
    if !removed && (← compareBest x r) == 0 then removed := true
    else out := out.push x
  return out

/-- `uniqueNextHopPostProcessDelta`: turn a delta of active routes into a delta of the
best route per next hop. -/
private def uniqueNextHop (delta : Array Advert) (before : Array Route) : M (Array Advert) := do
  let mut byNh : HashMap NextHop (Array Route) := {}
  let mut out : Delta := {}
  for a in delta do
    let r := a.route
    let set ← match byNh[r.nextHop]? with
      | some s => pure s
      | none => before.filter (·.nextHop == r.nextHop) |>.foldlM treeInsert #[]
    if a.withdrawn then
      let oldBest := set.back?
      let set ← treeErase set r
      byNh := byNh.insert r.nextHop set
      if oldBest == some r then
        out := out.push a
        if let some nb := set.back? then out := out.add nb
    else
      match set.back? with
      | none =>
        byNh := byNh.insert r.nextHop (← treeInsert set r)
        out := out.push a
      | some oldBest =>
        let set ← treeInsert set r
        byNh := byNh.insert r.nextHop set
        if set.back? == some r then
          out := (out.remove oldBest .replace).push a
  return out.toArray

private def actionDelta (r : Route) (action : Route → M (Array Advert)) : M (Array Advert) := do
  if (← get).isMultipath then
    let before := (← get).tree.getD r.network #[]
    let d ← action r
    uniqueNextHop d before
  else action r

private def deltaPrefixes (d : Array Advert) : Array Prefix :=
  (d.map (·.route.network)).foldl (fun acc p => if acc.contains p then acc else acc.push p) #[]

/-! ## Local routes and the resolvability enforcer -/

/-- Insert into the sorted set of locally originated routes of one mechanism: by next-hop
IP (none first; highest or lowest first as configured), then by source protocol. Routes
that compare equal are the same element, as in Java's `TreeSet`. -/
private def localInsert (mech : OriginMechanism) (xs : Array Route) (r : Route) :
    M (Array Route) := do
  let rib ← get
  let tie := if mech == .network then rib.networkNhTieBreaker else rib.redistributeNhTieBreaker
  let key (x : Route) : Option Ip × Nat :=
    (x.nextHopIp?, match x.bgp.bind (·.srcProtocol) with
      | some p => (RoutingProtocol.names.findIdx? (·.2 == p)).getD 0
      | none => 0)
  let lt (a b : Route) : Bool :=
    let (ia, pa) := key a
    let (ib, pb) := key b
    match ia, ib with
    | none, some _ => true
    | some _, none => false
    | none, none => pa < pb
    | some x, some y =>
      if x == y then pa < pb
      else if tie == .highestNextHopIp then y.bits < x.bits else x.bits < y.bits
  if xs.any (fun x => !lt x r && !lt r x) then return xs
  return (xs.push r).qsort lt

private def sameSource (a b : Route) : Bool :=
  (a.bgp.map (·.receivedFrom)) == (b.bgp.map (·.receivedFrom)) &&
  (a.bgp.map (·.pathId)) == (b.bgp.map (·.pathId))

private def enforcerAdd (r : Route) : M Unit := modify fun rib =>
  let rib := match r.nextHopIp? with
    | some ip => { rib with byNhip := rib.byNhip.insert ip (setInsert (rib.byNhip.getD ip #[]) r) }
    | none => rib
  { rib with byPrefix := rib.byPrefix.insert r.network (setInsert (rib.byPrefix.getD r.network #[]) r) }

private def enforcerRemove (r : Route) : M Unit := modify fun rib =>
  let rib := match r.nextHopIp? with
    | some ip =>
      let rest := (rib.byNhip.getD ip #[]).filter (· != r)
      if rest.isEmpty then
        { rib with
          byNhip := rib.byNhip.erase ip
          unresolvable := rib.unresolvable.erase ip
          mixed := rib.mixed.erase ip }
      else { rib with byNhip := rib.byNhip.insert ip rest }
    | none => rib
  let rest := (rib.byPrefix.getD r.network #[]).filter (· != r)
  { rib with
    byPrefix := (if rest.isEmpty then rib.byPrefix.erase r.network
      else rib.byPrefix.insert r.network rest) }

private def enforcerEvict (r : Route) : M Unit := do
  match ((← get).byPrefix.getD r.network #[]).find? (sameSource · r) with
  | some old => if old != r then enforcerRemove old
  | none => pure ()

private def setResolvable (ip : Ip) (resolvable : Bool) : M Unit := modify fun rib =>
  { rib with
    unresolvable := (if resolvable then rib.unresolvable.erase ip else rib.unresolvable.insert ip)
    mixed := rib.mixed.erase ip }

private def addedRoute (ip : Ip) (resolvable : Bool) : M Unit := modify fun rib =>
  if resolvable == rib.unresolvable.contains ip then { rib with mixed := rib.mixed.insert ip } else rib

mutual

/-- `BgpRib.mergeRouteGetDelta`. -/
partial def bgpMerge (r : Route) : M (Array Advert) := do
  let trackable := (r.bgp.map (·.isTrackableLocal)).getD false
  let eviction ← if trackable then pure #[] else evictSameSource r
  let delta ← actionDelta r abstractMerge
  let rib ← get
  if rib.settings.tieBreaker == BgpTieBreaker.arrivalOrder && !rib.arrival.contains r then
    set { rib with arrival := rib.arrival.insert r rib.clock, clock := rib.clock + 1 }
  if !delta.isEmpty then
    for p in deltaPrefixes delta do selectBestPath p
  return (({} : Delta).append eviction |>.append delta).toArray

/-- Remove a route that came from the same neighbor with the same path ID
(`evictSamePrefixReceivedFromPathId`). -/
partial def evictSameSource (r : Route) : M (Array Advert) := do
  let rib ← get
  let candidates := rib.tree.getD r.network #[] ++ rib.backups.getD r.network #[]
  let same := candidates.find? fun o =>
    (o.bgp.map (·.receivedFrom)) == (r.bgp.map (·.receivedFrom)) &&
    (o.bgp.map (·.pathId)) == (r.bgp.map (·.pathId))
  match same with
  | some old => if old == r then pure #[] else v4Remove old
  | none => pure #[]

/-- `BgpRib.removeRouteGetDelta`. -/
partial def bgpRemove (r : Route) : M (Array Advert) := do
  let delta ← actionDelta r abstractRemove
  let arrival := (← get).settings.tieBreaker == BgpTieBreaker.arrivalOrder
  if arrival then modify fun rib => { rib with arrival := rib.arrival.erase r }
  if !delta.isEmpty then
    for p in deltaPrefixes delta do selectBestPath p
    if arrival then
      for a in delta do
        if a.withdrawn then modify fun rib => { rib with arrival := rib.arrival.erase a.route }
  return delta

/-- `Bgpv4Rib.mergeRouteGetDelta`. -/
partial def v4Merge (r : Route) : M (Array Advert) := do
  let trackable := (r.bgp.map (·.isTrackableLocal)).getD false
  match r.nextHop with
  | .ip nhip =>
    if r.protocol != .aggregate && !trackable then
      enforcerEvict r
      let first := !(← get).byNhip.contains nhip
      enforcerAdd r
      let resolvable := (← read).resolvable nhip
      if first then setResolvable nhip resolvable else addedRoute nhip resolvable
      if !resolvable then return #[]
      return ← bgpMerge r
  | _ => pure ()
  if trackable then addLocalRoute r else bgpMerge r

/-- `Bgpv4Rib.removeRouteGetDelta`. -/
partial def v4Remove (r : Route) : M (Array Advert) := do
  if (r.bgp.map (·.isTrackableLocal)).getD false then return ← removeLocalRoute r
  enforcerRemove r
  bgpRemove r

partial def addLocalRoute (r : Route) : M (Array Advert) := do
  let some attrs := r.bgp | return #[]
  let key := (attrs.originMechanism, r.network)
  let cur := (← get).localRoutes.getD key #[]
  let oldBest := cur[0]?
  let next ← localInsert attrs.originMechanism cur r
  modify fun rib => { rib with localRoutes := rib.localRoutes.insert key next }
  let newBest := next[0]?
  if newBest != some r || oldBest == newBest then return #[]
  let d1 ← bgpMerge r
  let d2 ← match oldBest with
    | some o => bgpRemove o
    | none => pure #[]
  return (({} : Delta).append d1 |>.append d2).toArray

partial def removeLocalRoute (r : Route) : M (Array Advert) := do
  let some attrs := r.bgp | return #[]
  let key := (attrs.originMechanism, r.network)
  let some cur := (← get).localRoutes[key]? | return #[]
  let next := cur.filter (· != r)
  modify fun rib => { rib with localRoutes := rib.localRoutes.insert key next }
  let d1 ← match next[0]? with
    | some b => bgpMerge b
    | none => pure #[]
  let d2 ← bgpRemove r
  return (({} : Delta).append d1 |>.append d2).toArray

end

/-! ## The RIB's interface to the engine -/

/-- `BgpRib.multipathMergeRouteGetDelta`. -/
def merge (r : Route) : M Deltas := do
  if !(← get).isMultipath then
    let d ← v4Merge r
    return { multipath := d, bestPath := d }
  let cur := (← get).bestPaths[r.network]?
  let d ← v4Merge r
  match cur with
  | none => return { multipath := d, bestPath := d }
  | some old =>
    if (← get).bestPaths[r.network]? == some old then return { multipath := d }
    return { multipath := d, bestPath := #[{ route := old, reason := .replace }, { route := r }] }

/-- `BgpRib.multipathRemoveRouteGetDelta`. -/
def remove (r : Route) : M Deltas := do
  if !(← get).isMultipath then
    let d ← v4Remove r
    return { multipath := d, bestPath := d }
  if (← get).bestPaths[r.network]? != some r then
    return { multipath := ← v4Remove r }
  let d ← v4Remove r
  let mut bp : Array Advert := #[{ route := r, reason := .withdraw }]
  if let some nb := (← get).bestPaths[r.network]? then bp := bp.push { route := nb }
  return { multipath := d, bestPath := bp }

/-- `Bgpv4Rib.updateActiveRoutes`: after the main RIB changed at `prefixes`, activate or
deactivate learned routes whose next hop became resolvable or unresolvable. -/
def updateActiveRoutes (prefixes : Array Prefix) : M Deltas := do
  let rib ← get
  let affected := rib.mixed.toArray ++ (rib.byNhip.toArray.map (·.1)).filter fun ip =>
    prefixes.any (·.containsIp ip)
  let affected := (affected.qsort (fun a b => a.bits < b.bits)).toList.eraseDups
  let mut mp : Delta := {}
  let mut bp : Delta := {}
  for ip in affected do
    let resolvable := (← read).resolvable ip
    let rib ← get
    if resolvable != rib.unresolvable.contains ip && !rib.mixed.contains ip then continue
    for r in rib.byNhip.getD ip #[] do
      let d ← if resolvable then merge r else do
        let d ← remove r
        enforcerAdd r
        pure d
      mp := mp.append d.multipath
      bp := bp.append d.bestPath
    setResolvable ip resolvable
  return { multipath := mp.toArray, bestPath := bp.toArray }

/-- The best paths (`getBestPathRoutes`). -/
def bestPathRoutes (rib : BgpRib) : Array Route := rib.bestPaths.toArray.map (·.2)

/-- The routes the RIB exposes (`getRoutes`): the best paths, or for a multipath RIB the
best active route per prefix and next hop. -/
def routes (rib : BgpRib) : Array Route := Id.run do
  if !rib.isMultipath then return rib.bestPathRoutes
  let arrival := fun r => rib.arrival.getD r rib.clock
  let mut best : HashMap (NextHop × Prefix) Route := {}
  for (_, rs) in rib.tree.toArray do
    for r in rs do
      match best[(r.nextHop, r.network)]? with
      | none => best := best.insert (r.nextHop, r.network) r
      | some o =>
        if Bgp.bestPathCompare rib.settings arrival r o > 0 then
          best := best.insert (r.nextHop, r.network) r
  return best.toArray.map (·.2)

end BgpRib

end LeanBatfishSim
