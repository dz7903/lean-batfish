import LeanBatfish.Decode.GeneratedRoute
import LeanBatfish.IR.Bgp

/-!
# Decoding BGP configuration

The modeled subset: active and passive neighbors with an IPv4 unicast address family.
Unnumbered neighbors, confederations, conditional advertisement,
EVPN and VRF-crossing sessions are rejected.
-/

namespace LeanBatfish.Decode

open Lean ObjM

def addressFamilyCapabilities : Decoder AddressFamilyCapabilities := object do
  gate "advertiseExternal" "advertise-external" (· == .bool false)
  gate "allowLocalAsIn" "allowas-in" (· == .bool false)
  pure {
    additionalPathsReceive := ← dflt "additionalPathsReceive" false bool
    additionalPathsSelectAll := ← dflt "additionalPathsSelectAll" false bool
    additionalPathsSend := ← dflt "additionalPathsSend" false bool
    advertiseInactive := ← dflt "advertiseInactive" false bool
    allowRemoteAsOut := ← dflt "allowRemoteAsOut" .always
      (enum "allow-remote-as-out mode" AllowRemoteAsOut.names)
    sendCommunity := ← dflt "sendCommunity" false bool
    sendExtendedCommunity := ← dflt "sendExtendedCommunity" false bool }

def ipv4UnicastAddressFamily : Decoder Ipv4UnicastAddressFamily := object do
  ignoreAll ["exportPolicySources", "importPolicySources"]
  pure {
    capabilities := ← req "addressFamilyCapabilities" addressFamilyCapabilities
    importPolicy := ← opt "importPolicy" str
    exportPolicy := ← req "exportPolicy" str
    routeReflectorClient := ← dflt "routeReflectorClient" false bool }

/-- The fields shared by active and passive neighbors. -/
private def peerFields (remote : BgpPeerRemote) : ObjM BgpPeer := do
  -- Not read by Batfish's data plane.
  ignoreAll ["authenticationSettings", "defaultMetric", "description", "enforceFirstAs",
    "group"]
  gateEmpty "appliedRibGroup" "rib groups"
  gateEmpty "confederationAs" "BGP confederations"
  gateEmpty "evpnAddressFamily" "EVPN"
  gateEmpty "replaceNonLocalAsesOnExport" "as-override"
  gateEmpty "sessionVrf" "BGP sessions across VRFs"
  pure {
      remote
      localIp := ← opt "localIp" ip
      localAs := ← opt "localAs" nat
      remoteAsns := ← dflt "remoteAsns" .empty intervalSet
      ebgpMultihop := ← dflt "ebgpMultihop" false bool
      checkLocalIpOnAccept := ← dflt "checkLocalIpOnAccept" true bool
      clusterId := ← opt "clusterId" nat
      ipv4Unicast := ← opt "ipv4UnicastAddressFamily" ipv4UnicastAddressFamily
      generatedRoutes := ← dflt "generatedRoutes" #[] (array generatedRoute) }

def bgpActivePeer : Decoder BgpPeer := byClass "BGP neighbor" [
  ("BgpActivePeerConfig", do peerFields (.address (← req "peerAddress" ip)))]

def bgpPassivePeer : Decoder BgpPeer := byClass "passive BGP neighbor" [
  ("BgpPassivePeerConfig", do peerFields (.prefix (← req "peerPrefix" «prefix»)))]

def bgpAggregate : Decoder BgpAggregate := object do
  pure {
    network := ← req "network" «prefix»
    suppressionPolicy := ← opt "suppressionPolicy" str
    generationPolicy := ← opt "generationPolicy" str
    attributePolicy := ← opt "attributePolicy" str
    asPathMode := ← dflt "asPathMode" .none
      (enum "aggregate AS-path mode" AggregateAsPathMode.names)
    installInMainRib := ← req "installInMainRib" bool }

def bgpProcess : Decoder BgpProcess := object do
  gateEmpty "confederation" "BGP confederations"
  gateEmpty "interfaceNeighbors" "unnumbered BGP neighbors"
  gateEmpty "mainRibIndependentNetworkPolicy"
    "main-RIB network statements (their prefixes are not in the JSON)"
  gateEmpty "nextHopIpResolverRestrictionPolicy" "next-hop resolver restriction"
  gateEmpty "tableMapPolicy" "table-map"
  gateEmpty "tracks" "conditional advertisement (tracks)"
  pure {
    routerId := ← req "routerId" ip
    ebgpAdminCost := ← req "ebgpAdminCost" nat
    ibgpAdminCost := ← req "ibgpAdminCost" nat
    localAdminCost := ← req "localAdminCost" nat
    clientToClientReflection := ← dflt "clientToClientReflection" true bool
    clusterListAsIbgpCost := ← dflt "clusterListAsIbgpCost" false bool
    multipathEbgp := ← dflt "multipathEbgp" false bool
    multipathIbgp := ← dflt "multipathIbgp" false bool
    -- The data plane reads a missing mode as EXACT_PATH.
    multipathEquivalentAsPathMatchMode := ← dflt "multipathEquivalentAsPathMatchMode"
      .exactPath (enum "multipath AS-path mode" MultipathEquivalentAsPathMatchMode.names)
    tieBreaker := ← dflt "tieBreaker" .arrivalOrder (enum "tie breaker" BgpTieBreaker.names)
    localOriginationTypeTieBreaker := ← req "localOriginationTypeTieBreaker"
      (enum "local origination tie breaker" LocalOriginationTypeTieBreaker.names)
    networkNextHopIpTieBreaker := ← req "networkNextHopIpTieBreaker"
      (enum "next-hop tie breaker" NextHopIpTieBreaker.names)
    redistributeNextHopIpTieBreaker := ← req "redistributeNextHopIpTieBreaker"
      (enum "next-hop tie breaker" NextHopIpTieBreaker.names)
    redistributionPolicy := ← opt "redistributionPolicy" str
    independentNetworkPolicy := ← opt "independentNetworkPolicy" str
    neighbors := (← dflt "neighbors" #[] (map bgpActivePeer)).map (·.2)
    passiveNeighbors := (← dflt "dynamicNeighbors" #[] (map bgpPassivePeer)).map (·.2)
    aggregates := ← dflt "aggregates" #[] (array bgpAggregate) }

end LeanBatfish.Decode
