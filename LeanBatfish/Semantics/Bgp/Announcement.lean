import LeanBatfish.IR.Announcement
import LeanBatfish.Semantics.Bgp.Transform

/-!
# External BGP announcements

How a router takes in an announcement from `external_bgp_announcements.json`
(`stageExternalAdvertisements` and `processExternalBgpAdvertisement`). The router accepts
announcements addressed to one of its active addresses from one of its configured
neighbors; over eBGP, not if the path already contains the neighbor's local AS. A
*received* announcement enters the BGP RIB as it is; a *sent* one goes through the
neighbor's import policy first.
-/

namespace LeanBatfish.Bgp

/-- Whether router `c` with BGP process `p` takes announcement `a`. -/
def acceptsAnnouncement (c : Configuration) (p : BgpProcess) (a : Announcement) : Bool :=
  let owned (ip : Ip) := c.interfaces.any fun (_, i) =>
    i.active && i.allAddresses.any (·.ip == ip)
  a.dstNode == c.hostname && owned a.dstIp &&
  match p.neighbors.find? (·.remote == .address a.srcIp) with
  | none => false
  | some peer => !(a.type.ebgp && match peer.localAs with
      | some las => Bgp.AsPath.containsAs a.asPath las
      | none => false)

/-- The route announcement `a` puts in the BGP RIB of router `c` with process `p`, if any. -/
def announcementRoute (c : Configuration) (p : BgpProcess) (a : Announcement) :
    EvalM (Option Route) := do
  let some peer := p.neighbors.find? (·.remote == .address a.srcIp) | return none
  let proto : RoutingProtocol := if a.type.ebgp then .bgp else .ibgp
  let admin := adminCost p proto
  let attrs : BgpAttrs := {
    asPath := a.asPath, clusterList := a.clusterList, communities := .ofArray a.communities
    originatorIp := a.originatorIp.getD a.srcIp
    originMechanism := .learned, originType := a.originType, receivedFrom := .ip a.srcIp
    srcProtocol := some a.srcProtocol, weight := a.weight }
  if a.type.received then
    return some {
      network := a.network, nextHop := .ip a.nextHopIp, protocol := proto, admin
      metric := a.med, bgp := some { attrs with localPreference := a.localPreference } }
  let sent : Route := {
    network := a.network, nextHop := .ip a.nextHopIp, protocol := proto, admin := 0
    metric := a.med, bgp := some { attrs with
      localPreference := if a.type.ebgp then BgpAttrs.defaultLocalPreference
        else a.localPreference, weight := 0 } }
  let incoming : Route := { sent with
    admin, bgp := sent.bgp.map ({ · with srcProtocol := some proto }) }
  match peer.ipv4Unicast.bind (·.importPolicy) |>.bind c.routingPolicies.find? with
  | none => return some incoming
  | some pol =>
    let session : Option Policy.Session :=
      match peer.localAs, peer.localIp, peer.remote, peer.remoteAsns.included[0]? with
      | some las, some lip, .address rip, some r =>
        some { localAs := las, remoteAs := r.lo, localIp := lip, remoteIp := rip,
               isEbgp := false }
      | _, _, _, _ => none
    let ctx : Policy.Context := {
      config := c, original := sent, direction := .in
      useOutputAttributes := Policy.useOutputAttributesFor c, session
      outputKind := .bgp }
    let o ← Policy.process ctx pol incoming
    return if o.accepted then some o.output else none

end LeanBatfish.Bgp
