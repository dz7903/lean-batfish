import LeanBatfish.Semantics.Bgp.Session

/-!
# How BGP routes change from router to router

A BGP route travels from the BGP RIB of one router to the BGP RIB of a neighbor in five
steps (Batfish's `BgpProtocolHelper` and `BgpRoutingProcess.transformBgpRouteOnExport`):

1. **Pre-export**: the sender rewrites protocol and administrative distance, drops
   routes it must not send (`NO_ADVERTISE`, `NO_EXPORT` on eBGP, AS-path loops toward
   the peer, routes back to their originator), and decides route reflection for iBGP.
2. **Export policy** of the sender's neighbor configuration.
3. **Post-export**: on eBGP the sender's AS is prepended; weight, local preference and
   tag are reset; communities are filtered by the send-community settings; the next hop
   is set if the policy did not set one.
4. **Import**: the receiver drops routes whose AS path contains its own AS, and records
   where the route came from.
5. **Import policy** of the receiver's neighbor configuration.

Routes also enter BGP from the main RIB: Cisco-style routers *redistribute* main-RIB
routes into their BGP RIB through a redistribution policy, Juniper-style routers export
main-RIB routes directly to each neighbor through the neighbor's export policy.
-/

namespace LeanBatfish.Bgp

/-- The well-known communities `NO_EXPORT` (65535:65281) and `NO_ADVERTISE`
(65535:65282). -/
def noExport : Community := .standard (UInt32.ofNat (65535 * 65536 + 65281))
def noAdvertise : Community := .standard (UInt32.ofNat (65535 * 65536 + 65282))

def AsSet.contains (s : AsSet) (asn : Nat) : Bool := s.asns.contains asn

def AsPath.containsAs (p : AsPath) (asn : Nat) : Bool := p.any (AsSet.contains · asn)

/-- `BgpProtocolHelper.allowAsPathOut`. -/
def allowAsPathOut (p : AsPath) (peerAs : Nat) : AllowRemoteAsOut → Bool
  | .always | .exceptReceivedFrom => true
  | .never => p.isEmpty || !AsPath.containsAs p peerAs
  | .exceptFirst => match p[0]? with
    | none => true
    | some s => !AsSet.contains s peerAs

/-- Whether an iBGP route may be reflected to the neighbor (`isReflectable`): routes from
route-reflector clients go to everyone (to other clients only with client-to-client
reflection), routes from non-clients only to clients. -/
def isReflectable (r : Route) (clientToClient : Bool) (s : Session) : Bool :=
  !s.isEbgp && r.protocol == .ibgp &&
    if (r.bgp.map (·.receivedFromRouteReflectorClient)).getD false then
      clientToClient || !s.localEnd.af.routeReflectorClient
    else s.localEnd.af.routeReflectorClient

private def sortedNats (xs : Array Nat) : Array Nat :=
  ((xs.qsort (· < ·)).toList.eraseDups).toArray

/-- Pre-export (`transformBgpRoutePreExport`). The result has no next hop yet; that is
represented by `NextHop.discard`, which post-export replaces unless the export policy set
a next hop. -/
def preExport (s : Session) (r : Route) : Option Route := do
  let attrs ← r.bgp
  let outProto : RoutingProtocol := if s.isEbgp then .bgp else .ibgp
  let originatedLocally := attrs.receivedFrom == .self
  let comms := attrs.communities
  let mode := s.localEnd.af.capabilities.allowRemoteAsOut
  guard (!comms.contains noAdvertise)
  guard (!s.isEbgp || allowAsPathOut attrs.asPath s.remoteAs mode)
  guard (!(s.isEbgp && mode == .exceptReceivedFrom && attrs.receivedFrom == .ip s.remoteIp))
  guard (!(comms.contains noExport && s.isEbgp))
  guard (s.isEbgp || s.remoteEnd.process.routerId != attrs.originatorIp)
  let originatorIp :=
    if s.isEbgp || r.protocol != .ibgp then s.localEnd.process.routerId else attrs.originatorIp
  let clusterList ← reflectedClusterList s r attrs originatedLocally
  let metric := if s.isEbgp && !originatedLocally then 0 else r.metric
  pure { r with
    nextHop := .discard, protocol := outProto, nonRouting := false, nonForwarding := false
    admin := adminCost s.remoteEnd.process outProto, tag := unsetRouteTag, metric
    bgp := some { attrs with srcProtocol := some r.protocol, originatorIp, clusterList } }
where
  /-- The cluster list to send, or `none` if route reflection forbids sending. -/
  reflectedClusterList (s : Session) (r : Route) (attrs : BgpAttrs) (originatedLocally : Bool) :
      Option (Array Nat) := do
    if !(r.protocol == .ibgp && !s.isEbgp) then return #[]
    guard (isReflectable r s.localEnd.process.clientToClientReflection s || originatedLocally)
    let receiverIds := clusterIds s.remoteEnd.process
    guard (!attrs.clusterList.any receiverIds.contains)
    if originatedLocally then return attrs.clusterList
    match s.localEnd.peer.clusterId with
    | none => return attrs.clusterList
    | some cid =>
      guard (!receiverIds.contains cid)
      return sortedNats (attrs.clusterList.push cid)

/-- Remove extended communities that are not transitive. -/
def dropNonTransitive (cs : CommunitySet) : CommunitySet := cs.filter Community.isTransitive

/-- Post-export (`transformBgpRoutePostExport`). `originalNextHopIp` is the next-hop IP of
the route before export, kept on iBGP when the policy set no next hop. -/
def postExport (s : Session) (originalNextHopIp : Option Ip) (r : Route) : Route :=
  let caps := s.localEnd.af.capabilities
  let attrs := r.bgp.getD {}
  let asPath := if s.isEbgp then #[AsSet.single s.localAs] ++ attrs.asPath else attrs.asPath
  let comms := attrs.communities
  let comms :=
    if !caps.sendCommunity then
      if caps.sendExtendedCommunity then comms.filter Community.isExtended else {}
    else if !caps.sendExtendedCommunity then comms.filter Community.isStandard
    else comms
  let comms := if s.isEbgp then dropNonTransitive comms else comms
  let nextHop := match r.nextHopIp? with
    | some _ => r.nextHop
    | none => if s.isEbgp then .ip s.localIp else .ip (originalNextHopIp.getD s.localIp)
  let protocol := if r.protocol == .aggregate then (if s.isEbgp then .bgp else .ibgp)
    else r.protocol
  { r with
    nextHop, protocol, tag := unsetRouteTag
    bgp := some { attrs with
      asPath, weight := 0, communities := comms
      localPreference := if s.isEbgp then BgpAttrs.defaultLocalPreference else attrs.localPreference
      pathId := none } }

/-- The policy context for running a neighbor policy on a BGP route. -/
def policyContext (c : Configuration) (s : Session) (dir : Policy.Direction) (original : Route) :
    Policy.Context :=
  { config := c, original, direction := dir, useOutputAttributes := Policy.useOutputAttributesFor c
    session := some s.forPolicy, outputKind := .bgp }

/-- Export a BGP route over a session (`transformBgpRouteOnExport`): pre-export, the
export policy, post-export. `c` is the sender's configuration. -/
def exportRoute (c : Configuration) (s : Session) (r : Route) : EvalM (Option Route) := do
  let some pre := preExport s r | return none
  let policyName := s.localEnd.af.exportPolicy
  let some policy := c.routingPolicies.find? policyName
    | throw s!"undefined BGP export policy {policyName}"
  let o ← Policy.process (policyContext c s .out r) policy pre
  if !o.accepted then return none
  return some (postExport s r.nextHopIp? o.output)

/-- A main-RIB route as a BGP route originated by this router
(`BgpRouteUtil.convertNonBgpRouteToBgpRoute`). -/
def fromMainRib (r : Route) (routerId : Ip) (nextHopIp : Option Ip) (admin : Nat)
    (proto : RoutingProtocol) (mechanism : OriginMechanism) : Route :=
  { network := r.network, admin, protocol := proto, metric := r.metric, tag := r.tag
    nextHop := match nextHopIp with | some ip => .ip ip | none => .discard
    bgp := some { originatorIp := routerId, srcProtocol := some r.protocol
                  originMechanism := mechanism, originType := .incomplete
                  localPreference := BgpAttrs.defaultLocalPreference, receivedFrom := .self } }

/-- A generated route as a BGP route (`BgpProtocolHelper.convertGeneratedRouteToBgp`), after
its attribute policy. -/
def fromGenerated (c : Configuration) (g : Route) (attributePolicy : Option RoutingPolicy)
    (routerId : Ip) (nextHop : NextHop) : EvalM Route := do
  let attrs := g.bgp.getD {}
  let b : Route := {
    network := g.network, nextHop, protocol := .aggregate, admin := g.admin, metric := g.metric
    bgp := some { asPath := attrs.asPath, communities := attrs.communities
                  srcProtocol := some .aggregate, localPreference := BgpAttrs.defaultLocalPreference
                  originatorIp := routerId, originMechanism := .generated
                  originType := attrs.originType, receivedFrom := .self } }
  let some policy := attributePolicy | return b
  let ctx : Policy.Context := {
    config := c, original := b, useOutputAttributes := Policy.useOutputAttributesFor c
    outputKind := .bgp }
  let o ← Policy.process ctx policy { b with nextHop := .discard }
  return { o.output with nextHop }

/-- Export a main-RIB route directly to a neighbor, as Juniper-style routers do
(`exportNonBgpRouteToBgp`). `generatedAttributePolicy` finds the attribute policy of a
generated route. -/
def exportMainRibRoute (c : Configuration) (s : Session) (r : Route)
    (generatedAttributePolicy : Route → Option RoutingPolicy := fun _ => none) :
    EvalM (Option Route) := do
  let proto : RoutingProtocol := if s.isEbgp then .bgp else .ibgp
  let b ← if r.generated then
      fromGenerated c r (generatedAttributePolicy r) s.localEnd.process.routerId (.ip s.localIp)
    else pure (fromMainRib r s.localEnd.process.routerId (some s.localIp)
      (adminCost s.localEnd.process proto) proto .redistribute)
  let policyName := s.localEnd.af.exportPolicy
  let some policy := c.routingPolicies.find? policyName
    | throw s!"undefined BGP export policy {policyName}"
  let o ← Policy.process (policyContext c s .out r) policy b
  if !o.accepted then return none
  return some (postExport s none o.output)

/-- Import a route received over a session (`transformBgpRouteOnImport` and the import
policy). `s` is the session seen from the receiver; `c` its configuration. -/
def importRoute (c : Configuration) (s : Session) (r : Route) : EvalM (Option Route) := do
  let some attrs := r.bgp | return none
  if AsPath.containsAs attrs.asPath s.localAs then return none
  let proto : RoutingProtocol := if s.isEbgp then .bgp else .ibgp
  let some nhip := r.nextHopIp? | throw "received a BGP route without a next-hop IP"
  let b : Route := { r with
    admin := adminCost s.localEnd.process proto, nextHop := .ip nhip, protocol := proto
    bgp := some { attrs with
      receivedFrom := .ip s.remoteIp, srcProtocol := some proto, originMechanism := .learned
      receivedFromRouteReflectorClient := !s.isEbgp && s.localEnd.af.routeReflectorClient } }
  match s.localEnd.af.importPolicy.bind c.routingPolicies.find? with
  | none => return some b
  | some policy =>
    let o ← Policy.process (policyContext c s .in r) policy b
    return if o.accepted then some o.output else none

/-- Redistribute a main-RIB route into the BGP RIB through `policy`, as Cisco-style routers
do (`redistributeRouteToBgpRib`). The result is non-routing: it is in the BGP RIB only to be
advertised. -/
def redistribute (c : Configuration) (p : BgpProcess) (policy : RoutingPolicy)
    (mechanism : OriginMechanism) (r : Route) : EvalM (Option Route) := do
  if r.isBgpRoute then return none
  let b := { fromMainRib r p.routerId r.nextHopIp? p.ebgpAdminCost .bgp mechanism with
    nonRouting := true }
  let ctx : Policy.Context := {
    config := c, original := r, useOutputAttributes := Policy.useOutputAttributesFor c
    outputKind := .bgp }
  let o ← Policy.process ctx policy b
  return if o.accepted then some o.output else none

end LeanBatfish.Bgp
