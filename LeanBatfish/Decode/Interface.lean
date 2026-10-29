import LeanBatfish.Decode.Ipsec
import LeanBatfish.Decode.Ospf
import LeanBatfish.IR.Interface

/-!
# Decoding interfaces

Layer-2 settings (switchports, VLANs, port channels) are accepted but not modeled: they
only influence the layer-3 topology, which the simulator currently takes from Batfish.
Features that change forwarding or address ownership — NAT, policy-based routing,
zones, HSRP/VRRP — are rejected. Crypto maps and tunnel endpoints are read; IPsec is
decoded with the configuration (`Decode.Ipsec`).
-/

namespace LeanBatfish.Decode

open Lean ObjM

def connectedRouteMetadata : Decoder ConnectedRouteMetadata := object do
  pure {
    admin := ← opt "admin" nat
    tag := ← opt "tag" int
    generateConnectedRoute := ← opt "generateConnectedRoute" bool
    generateLocalRoutes := ← opt "generateLocalRoutes" bool
    generateLocalNullRouteIfDown := ← opt "generateLocalNullRouteIfDown" bool }

/-- The neutral value of `additionalArpIps` is the empty IP space. -/
private def isEmptyIpSpace (j : Json) : Bool :=
  j.getObjValD "class" == .str "org.batfish.datamodel.EmptyIpSpace"

def «interface» : Decoder Interface := object do
  -- Derived state (Batfish already folded it into `active`) and descriptions.
  ignoreAll ["adminUp", "lineUp", "blacklisted", "inactiveReason", "declaredNames",
    "description", "humanName", "bandwidth", "speed", "mtu", "autostate",
    "dhcpRelayAddresses", "spanningTreePortfast", "ripEnabled", "ripPassive"]
  -- Layer 2; only relevant to topology inference.
  ignoreAll ["switchport", "switchportMode", "switchportTrunkEncapsulation", "accessVlan",
    "allowedVlans", "nativeVlan", "encapsulationVlan", "vlan", "channelGroup",
    "channelGroupMembers", "mlagId"]
  gate "additionalArpIps" "additional ARP IPs" isEmptyIpSpace
  gateEmpty "eigrp" "EIGRP"
  gateEmpty "firewallSessionInterfaceInfo" "firewall sessions"
  gateEmpty "hmm" "host mobility (HMM) routes"
  gateEmpty "hsrpGroups" "HSRP"
  gateEmpty "hsrpVersion" "HSRP"
  gateEmpty "inboundFilter" "inbound (to-device) filters"
  gateEmpty "incomingTransformation" "NAT"
  gateEmpty "outgoingTransformation" "NAT"
  gateEmpty "isis" "IS-IS"
  gateEmpty "outgoingOriginalFlowFilter" "original-flow egress filters"
  gateEmpty "postTransformationIncomingFilter" "post-NAT filters"
  gateEmpty "preTransformationOutgoingFilter" "pre-NAT filters"
  gateEmpty "routingPolicy" "policy-based routing"
  gateEmpty "vrrpGroups" "VRRP"
  gateEmpty "zone" "firewall zones"
  let metadata ← dflt "addressMetadata" #[] (map connectedRouteMetadata)
  let metadata ← metadata.mapM fun (k, v) => do
    match InterfaceAddress.parse? k with
    | some a => pure (a, v)
    | none => DecodeM.malformed s!"bad address {k.quote} in addressMetadata"
  pure {
    name := ← req "name" str
    vrf := ← req "vrf" str
    active := ← req "active" bool
    type := ← dflt "type" "" str
    address := ← opt "prefix" interfaceAddress
    allAddresses := ← dflt "allPrefixes" #[] (array interfaceAddress)
    addressMetadata := metadata
    incomingFilter := ← opt "incomingFilter" str
    outgoingFilter := ← opt "outgoingFilter" str
    proxyArp := ← dflt "proxyArp" false bool
    ospf := ← opt "ospfSettings" ospfInterfaceSettings
    cryptoMap := ← opt "cryptoMap" str
    tunnelConfig := ← opt "tunnelConfig" tunnelConfiguration }

end LeanBatfish.Decode
