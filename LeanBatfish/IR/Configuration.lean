import LeanBatfish.IR.Acl
import LeanBatfish.IR.Bgp
import LeanBatfish.IR.Interface
import LeanBatfish.IR.Ipsec
import LeanBatfish.IR.NextHop
import LeanBatfish.IR.RoutingPolicy.Statement

/-!
# Configurations

A `Configuration` is one device in Batfish's vendor-independent model. Named objects
(interfaces, VRFs, ACLs, policies, ...) are kept as arrays of name/value pairs in the
order Batfish writes them, which is sorted by name.
-/

namespace LeanBatfish

/-- A configured static route (`StaticRoute`). -/
structure StaticRoute where
  network : Prefix
  nextHop : NextHop
  administrativeCost : Nat
  metric : Nat
  tag : Int
  /-- Whether the next-hop IP may resolve through routes other than connected ones (Junos
  `resolve`; on by default elsewhere). -/
  recursive : Bool
  /-- Installed in the RIB but not the FIB (Junos `no-install`). -/
  nonForwarding : Bool
  deriving Inhabited, Repr

structure Vrf where
  name : String
  staticRoutes : Array StaticRoute
  bgpProcess : Option BgpProcess
  ospfProcesses : Array (String × OspfProcess)
  /-- A policy restricting which routes may be used to resolve next hops. -/
  resolutionPolicy : Option String
  generatedRoutes : Array GeneratedRoute
  deriving Inhabited, Repr

abbrev NameMap (α : Type) := Array (String × α)

def NameMap.find? (m : NameMap α) (name : String) : Option α :=
  (Array.find? (fun (p : String × α) => p.1 == name) m).map (·.2)

structure Configuration where
  hostname : String
  /-- The vendor format Batfish parsed, e.g. `CISCO_IOS`, `JUNIPER`, `FLAT_JUNIPER`. Some
  of Batfish's semantics depend on it. -/
  configurationFormat : String
  /-- Cisco-style (`true`) or Juniper-style (`false`) origination of BGP routes. -/
  exportBgpFromBgpRib : Bool
  /-- Whether BGP aggregates are activated by main-RIB routes rather than BGP routes. -/
  generateBgpAggregatesFromMainRib : Bool
  /-- Install main-RIB routes only if their next hop resolves through routes allowed by
  the VRF's resolution policy (set by Batfish for Cisco NX-OS). -/
  mainRibEnforceResolvability : Bool
  interfaces : NameMap Interface
  vrfs : NameMap Vrf
  ipAccessLists : NameMap IpAccessList
  ipSpaces : NameMap IpSpace
  routeFilterLists : NameMap RouteFilterList
  routingPolicies : NameMap RoutingPolicy
  communityMatchExprs : NameMap CommunityMatchExpr
  communitySetExprs : NameMap CommunitySetExpr
  communitySetMatchExprs : NameMap CommunitySetMatchExpr
  communitySets : NameMap (Array Community)
  asPathAccessLists : NameMap AsPathAccessList
  asPathExprs : NameMap AsPathExpr
  asPathMatchExprs : NameMap AsPathMatchExpr
  ikePhase1Keys : NameMap IkePhase1Key := #[]
  ikePhase1Policies : NameMap IkePhase1Policy := #[]
  ikePhase1Proposals : NameMap IkePhase1Proposal := #[]
  ipsecPeerConfigs : NameMap IpsecPeerConfig := #[]
  ipsecPhase2Policies : NameMap IpsecPhase2Policy := #[]
  ipsecPhase2Proposals : NameMap IpsecPhase2Proposal := #[]
  deriving Inhabited

namespace Configuration

def isJuniper (c : Configuration) : Bool :=
  c.configurationFormat ∈ ["JUNIPER", "JUNIPER_SWITCH", "FLAT_JUNIPER"]

end Configuration

end LeanBatfish
