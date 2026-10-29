import LeanBatfish.Decode.Acl
import LeanBatfish.Decode.Bgp
import LeanBatfish.Decode.GeneratedRoute
import LeanBatfish.Decode.Interface
import LeanBatfish.Decode.RoutingPolicy
import LeanBatfish.Decode.VIModel
import LeanBatfish.IR.Configuration

/-!
# Decoding configurations

The entry point of the strict decoder: `configuration` decodes one node's JSON, and
`network` decodes a whole `viModel` answer.
-/

namespace LeanBatfish.Decode

open Lean ObjM

def staticRoute : Decoder StaticRoute := byClass "static route" [
  ("StaticRoute", do
    gateEmpty "nextVrf" "static routes into another VRF"
    gateEmpty "track" "tracked static routes"
    let network ← req "network" «prefix»
    let ip ← opt "nextHopIp" ip
    let iface ← opt "nextHopInterface" str
    let some nextHop := NextHop.ofLegacy iface ip
      | DecodeM.malformed "static route without a next hop"
    pure {
      network, nextHop
      administrativeCost := ← req "administrativeCost" nat
      metric := ← dflt "metric" 0 nat
      tag := ← dflt "tag" (-1) int
      -- Only our patched Batfish exports these two (see `tools/batfish/`).
      recursive := ← req "recursive" bool
      nonForwarding := ← req "nonForwarding" bool })]

def vrf : Decoder Vrf := object do
  ignoreAll ["description", "routeDistinguisher", "snmpServer"]
  gateEmpty "appliedRibGroups" "rib groups"
  gateEmpty "eigrpProcesses" "EIGRP"
  gateEmpty "fibExportPolicy" "FIB export policies"
  gateEmpty "firewallSessionVrfInfo" "firewall sessions"
  gateEmpty "isisProcess" "IS-IS"
  gateEmpty "kernelRoutes" "kernel routes"
  gateEmpty "ripProcess" "RIP"
  gateEmpty "vrfLeakConfig" "VRF route leaking"
  pure {
    name := ← req "name" str
    staticRoutes := ← dflt "staticRoutes" #[] (array staticRoute)
    bgpProcess := ← opt "bgpProcess" bgpProcess
    ospfProcesses := ← dflt "ospfProcesses" #[] (map ospfProcess)
    resolutionPolicy := ← opt "resolutionPolicy" str
    generatedRoutes := ← dflt "aggregateRoutes" #[] (array generatedRoute) }

/-- The neutral values of `defaultInboundAction`. -/
private def isPermitOrNull : Json → Bool
  | .null => true
  | .str "PERMIT" => true
  | _ => false

def configuration : Decoder Configuration := object do
  -- Management-plane settings and descriptive metadata.
  ignoreAll ["authenticationKeyChains", "deviceModel", "deviceType", "dnsServers",
    "dnsSourceInterface", "domainName", "generatedReferenceBooks", "humanName",
    "ipSpaceMetadata", "loggingServers", "loggingSourceInterface", "ntpServers",
    "ntpSourceInterface", "snmpSourceInterface", "snmpTrapServers", "tacacsServers",
    "tacacsSourceInterface", "vendorFamily"]
  -- Only read together with gated features (zones, layer-1 topology).
  ignoreAll ["defaultCrossZoneAction", "disconnectAdminDownInterfaces"]
  gate "defaultInboundAction" "default-deny inbound action" isPermitOrNull
  gateEmpty "mlags" "MLAG"
  gateEmpty "packetPolicies" "policy-based routing"
  gateEmpty "trackingGroups" "tracking"
  gateEmpty "zones" "firewall zones"
  let named {α} (k : String) (d : Decoder α) : ObjM (NameMap α) := dflt k #[] (map d)
  pure {
    hostname := ← req "name" str
    configurationFormat := ← req "configurationFormat" str
    exportBgpFromBgpRib := ← dflt "exportBgpFromBgpRib" false bool
    generateBgpAggregatesFromMainRib := ← dflt "generateBgpAggregatesFromMainRib" false bool
    mainRibEnforceResolvability := ← dflt "mainRibEnforceResolvability" false bool
    interfaces := ← named "interfaces" «interface»
    vrfs := ← named "vrfs" vrf
    ipAccessLists := ← named "ipAccessLists" ipAccessList
    ipSpaces := ← named "ipSpaces" ipSpace
    routeFilterLists := ← named "routeFilterLists" routeFilterList
    routingPolicies := ← named "routingPolicies" routingPolicy
    communityMatchExprs := ← named "communityMatchExprs" communityMatchExpr
    communitySetExprs := ← named "communitySetExprs" communitySetExpr
    communitySetMatchExprs := ← named "communitySetMatchExprs" communitySetMatchExpr
    communitySets := ← named "communitySets" (array community)
    asPathAccessLists := ← named "asPathAccessLists" asPathAccessList
    asPathExprs := ← named "asPathExprs" asPathExpr
    asPathMatchExprs := ← named "asPathMatchExprs" asPathMatchExpr
    ikePhase1Keys := ← named "ikePhase1Keys" ikePhase1Key
    ikePhase1Policies := ← named "ikePhase1Policies" ikePhase1Policy
    ikePhase1Proposals := ← named "ikePhase1Proposals" ikePhase1Proposal
    ipsecPeerConfigs := ← named "ipsecPeerConfigs" ipsecPeerConfig
    ipsecPhase2Policies := ← named "ipsecPhase2Policies" ipsecPhase2Policy
    ipsecPhase2Proposals := ← named "ipsecPhase2Proposals" ipsecPhase2Proposal }

/-- Decode every node of a `viModel` answer. The first rejection stops decoding. -/
def network (answer : Json) : Except Rejection (Array Configuration) := do
  let nodes ← match viModelNodes answer with
    | .ok n => pure n
    | .error e => throw { kind := .malformed, path := "", message := e }
  nodes.mapM fun (host, j) =>
    (DecodeM.within "nodes" <| DecodeM.within host <| configuration j).run

end LeanBatfish.Decode
