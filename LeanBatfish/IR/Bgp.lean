import LeanBatfish.IR.Basic
import LeanBatfish.Data.IntervalSet
import LeanBatfish.Net.Prefix
import LeanBatfish.Net.AsPath
import LeanBatfish.IR.GeneratedRoute

/-!
# BGP configuration

A BGP process per VRF, with neighbors configured by address (`BgpActivePeerConfig`) or as
passive listeners for a prefix (`BgpPassivePeerConfig`). Each neighbor has
an IPv4 unicast address family carrying its import/export policies and capabilities.
-/

namespace LeanBatfish

/-- When to send a route whose AS path contains the peer's AS (`AllowRemoteAsOutMode`). -/
inductive AllowRemoteAsOut
  | always
  | never
  /-- Allowed only if the peer's AS is the first AS of the path. -/
  | exceptFirst
  /-- Never send a route back to the AS it was received from. -/
  | exceptReceivedFrom
  deriving DecidableEq, Inhabited, Repr

def AllowRemoteAsOut.names : List (String × AllowRemoteAsOut) :=
  [("ALWAYS", .always), ("NEVER", .never), ("EXCEPT_FIRST", .exceptFirst),
   ("EXCEPT_RECEIVED_FROM", .exceptReceivedFrom)]

structure AddressFamilyCapabilities where
  additionalPathsReceive : Bool := false
  additionalPathsSelectAll : Bool := false
  additionalPathsSend : Bool := false
  advertiseExternal : Bool := false
  advertiseInactive : Bool := false
  allowLocalAsIn : Bool := false
  allowRemoteAsOut : AllowRemoteAsOut := .always
  sendCommunity : Bool := false
  sendExtendedCommunity : Bool := false
  deriving Inhabited, Repr

structure Ipv4UnicastAddressFamily where
  capabilities : AddressFamilyCapabilities
  /-- Absent means accept everything. -/
  importPolicy : Option String
  /-- Batfish's conversion always sets an export policy. -/
  exportPolicy : String
  routeReflectorClient : Bool
  deriving Inhabited, Repr

/-- Whom a neighbor configuration is for: one peer address, or any peer in a prefix that
opens a session (a passive or dynamic neighbor, e.g. Cisco's `bgp listen range`). -/
inductive BgpPeerRemote
  | address (ip : Ip)
  | «prefix» (p : Prefix)
  deriving DecidableEq, Inhabited, Repr

/-- A BGP neighbor configuration (`BgpActivePeerConfig` or `BgpPassivePeerConfig`). -/
structure BgpPeer where
  remote : BgpPeerRemote
  localIp : Option Ip
  localAs : Option Asn
  /-- The AS numbers accepted for the peer. -/
  remoteAsns : IntervalSet
  ebgpMultihop : Bool
  checkLocalIpOnAccept : Bool
  clusterId : Option Nat
  ipv4Unicast : Option Ipv4UnicastAddressFamily
  /-- Routes sent to this neighbor only, such as Cisco's `default-originate`. -/
  generatedRoutes : Array GeneratedRoute
  deriving Inhabited, Repr

/-- How to choose among locally originated routes for the same prefix. -/
inductive NextHopIpTieBreaker
  | highestNextHopIp
  | lowestNextHopIp
  deriving DecidableEq, Inhabited, Repr

def NextHopIpTieBreaker.names : List (String × NextHopIpTieBreaker) :=
  [("HIGHEST_NEXT_HOP_IP", .highestNextHopIp), ("LOWEST_NEXT_HOP_IP", .lowestNextHopIp)]

/-- The last-resort tie breaker of BGP best-path selection (`BgpTieBreaker`). -/
inductive BgpTieBreaker
  /-- Prefer the oldest eBGP route. -/
  | arrivalOrder
  | clusterListLength
  | routerId
  deriving DecidableEq, Inhabited, Repr

def BgpTieBreaker.names : List (String × BgpTieBreaker) :=
  [("ARRIVAL_ORDER", .arrivalOrder), ("CLUSTER_LIST_LENGTH", .clusterListLength),
   ("ROUTER_ID", .routerId)]

/-- How AS paths must agree for two routes to be multipath-equivalent. -/
inductive MultipathEquivalentAsPathMatchMode
  | exactPath
  | firstAs
  | pathLength
  deriving DecidableEq, Inhabited, Repr

def MultipathEquivalentAsPathMatchMode.names :
    List (String × MultipathEquivalentAsPathMatchMode) :=
  [("EXACT_PATH", .exactPath), ("FIRST_AS", .firstAs), ("PATH_LENGTH", .pathLength)]

/-- Preference between locally originated routes of different origin mechanisms. -/
inductive LocalOriginationTypeTieBreaker
  | noPreference
  | preferNetwork
  | preferRedistribute
  deriving DecidableEq, Inhabited, Repr

def LocalOriginationTypeTieBreaker.names : List (String × LocalOriginationTypeTieBreaker) :=
  [("NO_PREFERENCE", .noPreference), ("PREFER_NETWORK", .preferNetwork),
   ("PREFER_REDISTRIBUTE", .preferRedistribute)]

/-- How the AS path of a generated aggregate is derived from its contributors
(`BgpAggregate.AsPathMode`). -/
inductive AggregateAsPathMode
  /-- An empty AS path (Cisco without `as-set`). -/
  | none
  /-- The contributors' longest common leading AS sequence (Arista). -/
  | commonSequence
  deriving DecidableEq, Inhabited, Repr

def AggregateAsPathMode.names : List (String × AggregateAsPathMode) :=
  [("NONE", .none), ("COMMON_SEQUENCE", .commonSequence)]

/-- A BGP aggregate (`BgpAggregate`): a route for `network` that BGP generates while some
more specific BGP route contributes to it. -/
structure BgpAggregate where
  network : Prefix
  /-- Selects contributors whose routes are suppressed. Batfish does not implement
  suppression yet. -/
  suppressionPolicy : Option String
  /-- Selects the contributing routes; without it every more specific route contributes. -/
  generationPolicy : Option String
  /-- Sets the attributes of the generated aggregate. -/
  attributePolicy : Option String
  asPathMode : AggregateAsPathMode
  /-- Whether the aggregate is also installed in the main RIB (as a discard route). -/
  installInMainRib : Bool
  deriving Inhabited, Repr

structure BgpProcess where
  routerId : Ip
  ebgpAdminCost : Nat
  ibgpAdminCost : Nat
  localAdminCost : Nat
  clientToClientReflection : Bool
  clusterListAsIbgpCost : Bool
  multipathEbgp : Bool
  multipathIbgp : Bool
  multipathEquivalentAsPathMatchMode : MultipathEquivalentAsPathMatchMode
  tieBreaker : BgpTieBreaker
  localOriginationTypeTieBreaker : LocalOriginationTypeTieBreaker
  networkNextHopIpTieBreaker : NextHopIpTieBreaker
  redistributeNextHopIpTieBreaker : NextHopIpTieBreaker
  /-- Policy selecting main-RIB routes to redistribute into BGP. -/
  redistributionPolicy : Option String
  /-- Policy selecting main-RIB routes for `network` statements. -/
  independentNetworkPolicy : Option String
  /-- Neighbors configured by address. -/
  neighbors : Array BgpPeer
  /-- Passive neighbors, which accept sessions from a prefix. -/
  passiveNeighbors : Array BgpPeer
  aggregates : Array BgpAggregate
  deriving Inhabited, Repr

end LeanBatfish
