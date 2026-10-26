import LeanBatfish.Semantics.Routing.Rib
import LeanBatfish.IR.Bgp

/-!
# BGP route preference

How a BGP RIB compares two routes for the same prefix (Batfish's `BgpRib.comparePreference`
and `BgpRib.bestPathComparator`). A comparison returns a positive number when the first
route is preferred, a negative number when the second is, and zero when they tie.

`comparePreference` decides which routes a RIB keeps: the most preferred ones, all of them
when they tie (multipath). In a multipath RIB two routes tie only if their AS paths are
equivalent under the configured mode; otherwise the comparison returns -1 *both ways*, so
the route already in the RIB stays and the newcomer waits as a backup. `bestPathComparator`
then picks one best path among the routes kept. With the `ARRIVAL_ORDER` tie breaker, the
oldest of two eBGP routes wins, so the outcome can depend on the order routes arrived in.
-/

namespace LeanBatfish.Bgp

/-- What a BGP RIB's comparisons depend on besides the two routes. -/
structure RibSettings where
  tieBreaker : BgpTieBreaker
  /-- Whether the RIB keeps several best routes (`maxPaths` other than 1). -/
  multipath : Bool
  asPathMatch : MultipathEquivalentAsPathMatchMode
  clusterListAsIgpCost : Bool
  localOriginationTieBreaker : LocalOriginationTypeTieBreaker
  deriving Inhabited

/-- The settings of a BGP process's RIB. -/
def ribSettings (p : BgpProcess) : RibSettings := {
  tieBreaker := p.tieBreaker, multipath := p.multipathEbgp || p.multipathIbgp
  asPathMatch := p.multipathEquivalentAsPathMatchMode
  clusterListAsIgpCost := p.clusterListAsIbgpCost
  localOriginationTieBreaker := p.localOriginationTypeTieBreaker }

/-- Compare two values where larger is better. -/
def cmpHigher (a b : Nat) : Int := if a > b then 1 else if a < b then -1 else 0

/-- Compare two values where smaller is better. -/
def cmpLower (a b : Nat) : Int := - cmpHigher a b

/-- `Ip.compareTo` reversed: the lower address is preferred. -/
def cmpLowerIp (a b : Ip) : Int := cmpLower a.bits.toNat b.bits.toNat

def _root_.LeanBatfish.BgpAttrs.isTrackableLocal (a : BgpAttrs) : Bool :=
  a.originMechanism == .network || a.originMechanism == .redistribute

private def aggregatePreference (p : RoutingProtocol) : Nat := if p == .aggregate then 1 else 0

/-- Aggregates over eBGP over iBGP (`BgpRib.getTypeCost`, larger is better). -/
private def typeCost (p : RoutingProtocol) : Nat :=
  match p with
  | .aggregate => 2
  | .bgp => 1
  | _ => 0

/-- `Long.MAX_VALUE`, the IGP cost of an unresolvable next hop. -/
def unreachableCost : Nat := 2 ^ 63 - 1

/-- Longest-prefix match over the forwarding routes of a main RIB, with no restriction. -/
def lpm (main : Rib) (ip : Ip) : Array Route :=
  Id.run (main.longestPrefixMatch ip fun _ => pure true)

/-- Whether a next-hop IP resolves in the main RIB (`Bgpv4Rib.isResolvable`). -/
def resolvable (main : Rib) (ip : Ip) : Bool := !(lpm main ip).isEmpty

/-- The IGP cost to a route's next hop (`BgpRib.getIgpCostToNextHopIp`): the metric of the
interface route its next hop resolves to, following next-hop IPs. -/
def igpCost (main : Rib) (r : Route) : Nat := go r 11
where
  go (r : Route) : Nat → Nat
    | 0 => unreachableCost
    | fuel + 1 =>
      match r.nextHop with
      | .ip ip => match (lpm main ip)[0]? with
        | some r' => go r' fuel
        | none => unreachableCost
      | .iface .. => r.metric
      | .discard => unreachableCost

/-- The AS-path equivalence of multipath routes (`compareAsPath`): 0 if equivalent, else -1. -/
def compareAsPath (mode : MultipathEquivalentAsPathMatchMode) (a b : AsPath) : Int :=
  match mode with
  | .exactPath => if a == b then 0 else -1
  | .firstAs => if (a[0]?.getD ⟨#[], false⟩) == (b[0]?.getD ⟨#[], false⟩) then 0 else -1
  | .pathLength => 0

/-- The address a route was received from, for comparisons (`LegacyReceivedFromToIpConverter`):
`0.0.0.0` for locally originated routes. -/
def receivedFromIp : ReceivedFrom → Ip
  | .self => Ip.zero
  | .ip ip => ip

private def receivedFromTypePreference : ReceivedFrom → Nat
  | .self => 2
  | .ip _ => 1

/-- `BgpRib.bestPathComparator`. `arrival` gives each route's logical arrival time. -/
def bestPathCompare (st : RibSettings) (arrival : Route → Nat) (l r : Route) : Int := Id.run do
  let la := l.bgp.getD {}
  let ra := r.bgp.getD {}
  if st.tieBreaker == .arrivalOrder && l.protocol == .bgp && r.protocol == .bgp then
    let c := cmpLower (arrival l) (arrival r)
    if c != 0 then return c
  if st.tieBreaker == .clusterListLength then
    let c := cmpLower la.clusterList.size ra.clusterList.size
    if c != 0 then return c
  let c := cmpLowerIp la.originatorIp ra.originatorIp
  if c != 0 then return c
  if st.tieBreaker != .clusterListLength then
    let c := cmpLower la.clusterList.size ra.clusterList.size
    if c != 0 then return c
  let c := cmpLowerIp (receivedFromIp la.receivedFrom) (receivedFromIp ra.receivedFrom)
  if c != 0 then return c
  let c := cmpHigher (receivedFromTypePreference la.receivedFrom)
    (receivedFromTypePreference ra.receivedFrom)
  if c != 0 then return c
  match la.pathId, ra.pathId with
  | none, none => return 0
  | none, some _ => return 1
  | some _, none => return -1
  | some a, some b => return cmpLower a b

/-- `BgpRib.comparePreference`. `igpCost` gives the IGP cost to a route's next hop. -/
def comparePreference (st : RibSettings) (igpCost : Route → Nat) (arrival : Route → Nat)
    (l r : Route) : Int := Id.run do
  let la := l.bgp.getD {}
  let ra := r.bgp.getD {}
  if st.localOriginationTieBreaker != .noPreference && la.originMechanism != ra.originMechanism &&
      la.isTrackableLocal && ra.isTrackableLocal then
    if st.localOriginationTieBreaker == .preferNetwork then
      return if la.originMechanism == .network then 1 else -1
    else
      return if la.originMechanism == .redistribute then 1 else -1
  let steps : List (Unit → Int) := [
    fun _ => cmpHigher la.weight ra.weight,
    fun _ => cmpHigher la.localPreference ra.localPreference,
    fun _ => cmpHigher (aggregatePreference l.protocol) (aggregatePreference r.protocol),
    fun _ => cmpLower la.asPath.length ra.asPath.length,
    fun _ => cmpHigher la.originType.preference ra.originType.preference,
    fun _ => cmpHigher (typeCost l.protocol) (typeCost r.protocol),
    fun _ => cmpLower l.metric r.metric,
    fun _ => cmpLower (igpCost l) (igpCost r),
    fun _ => if st.clusterListAsIgpCost then cmpLower la.clusterList.size ra.clusterList.size
      else 0]
  for step in steps do
    let c := step ()
    if c != 0 then return c
  let c := compareAsPath st.asPathMatch la.asPath ra.asPath
  if c != 0 || st.multipath then return c
  return bestPathCompare st arrival l r

end LeanBatfish.Bgp
