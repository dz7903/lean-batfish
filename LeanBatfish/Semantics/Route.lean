import LeanBatfish.IR.Basic
import LeanBatfish.IR.NextHop
import LeanBatfish.Net.AsPath
import LeanBatfish.Net.Community

/-!
# Routes

A `Route` is an entry of a routing table, the counterpart of Batfish's `AbstractRoute`
and its subclasses. The fields every route has come first; the attributes only BGP routes
have are grouped in `BgpAttrs`.

Two routes are equal when all their fields are equal, as for Batfish's route classes, so
a routing table holding a set of routes keeps distinct copies only when they differ in
some attribute.
-/

namespace LeanBatfish

/-! ## Community sets -/

namespace Community

/-- Batfish's `Community.asBigInt`, which orders communities (`Community.compareTo`). The
type and subtype octets of extended communities are signed Java bytes. -/
def toInt : Community → Int
  | .standard v => v.toNat
  | .extended t s v =>
    let signed (b : Nat) : Int := if b ≥ 128 then (b : Int) - 256 else b
    signed t * 2 ^ 56 + signed s * 2 ^ 48 + v
  | .large a b c => a.toNat * 2 ^ 64 + b.toNat * 2 ^ 32 + c.toNat

end Community

/-- A set of communities (`CommunitySet`), kept sorted by `Community.toInt` and without
duplicates, so that equal sets have equal representations. -/
structure CommunitySet where
  toArray : Array Community := #[]
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace CommunitySet

def empty : CommunitySet := {}

def ofArray (cs : Array Community) : CommunitySet :=
  let sorted := cs.qsort (fun a b => a.toInt < b.toInt)
  ⟨sorted.foldl (fun acc c => if acc.back? == some c then acc else acc.push c) #[]⟩

def contains (s : CommunitySet) (c : Community) : Bool := s.toArray.contains c

def size (s : CommunitySet) : Nat := s.toArray.size

def union (a b : CommunitySet) : CommunitySet := ofArray (a.toArray ++ b.toArray)

def filter (s : CommunitySet) (p : Community → Bool) : CommunitySet := ⟨s.toArray.filter p⟩

end CommunitySet

/-! ## BGP attributes -/

/-- How a BGP route came to exist (`OriginMechanism`). -/
inductive OriginMechanism
  | generated
  | learned
  | network
  | redistribute
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- Where a BGP route was received from (`ReceivedFrom`). -/
inductive ReceivedFrom
  /-- Originated by this router. -/
  | self
  | ip (ip : Ip)
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- The attributes only BGP routes carry (`BgpRoute`, `Bgpv4Route`). The MED is the
route's `metric`. -/
structure BgpAttrs where
  asPath : AsPath := #[]
  communities : CommunitySet := {}
  localPreference : Nat := 100
  weight : Nat := 0
  originType : OriginType := .igp
  originatorIp : Ip := Ip.zero
  /-- Cluster IDs, sorted and without duplicates. -/
  clusterList : Array Nat := #[]
  receivedFrom : ReceivedFrom := .self
  receivedFromRouteReflectorClient : Bool := false
  /-- The protocol of the route this one was redistributed from, if any. -/
  srcProtocol : Option RoutingProtocol := none
  originMechanism : OriginMechanism := .learned
  /-- The add-path path ID, if any. -/
  pathId : Option Nat := none
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- `BgpRoute.DEFAULT_LOCAL_PREFERENCE`. -/
def BgpAttrs.defaultLocalPreference : Nat := 100

/-- `BgpRoute.MAX_LOCAL_PREFERENCE`. -/
def BgpAttrs.maxLocalPreference : Nat := 2 ^ 32 - 1

/-! ## OSPF attributes -/

/-- The attributes only OSPF routes carry (`OspfRoute` and subclasses). -/
structure OspfAttrs where
  /-- The area the route belongs to; `none` is Batfish's `NO_AREA`, for external routes
  not yet sent into an area. -/
  area : Option Nat := none
  /-- For external routes: the cost to reach the router that redistributed them. -/
  costToAdvertiser : Nat := 0
  /-- For external routes: the hostname of the router that redistributed them. -/
  advertiser : String := ""
  /-- For external routes: the metric they were redistributed with. -/
  lsaMetric : Nat := 0
  deriving DecidableEq, Hashable, Inhabited, Repr

/-! ## Routes -/

/-- `Route.UNSET_ROUTE_TAG`. -/
def unsetRouteTag : Int := -1

structure Route where
  network : Prefix
  nextHop : NextHop
  protocol : RoutingProtocol
  admin : Nat
  metric : Nat := 0
  tag : Int := unsetRouteTag
  /-- Kept out of the main RIB (`nonRouting`). -/
  nonRouting : Bool := false
  /-- Kept out of the FIB (`nonForwarding`). -/
  nonForwarding : Bool := false
  /-- For static routes: whether the next-hop IP may resolve through non-connected
  routes. -/
  recursive : Bool := true
  /-- For local routes: the length of the interface prefix the address came from. -/
  sourcePrefixLength : Nat := 0
  bgp : Option BgpAttrs := none
  /-- For OSPF external routes: E1 or E2. -/
  ospfMetricType : Option OspfMetricType := none
  ospf : Option OspfAttrs := none
  /-- A generated (aggregate) route (`GeneratedRoute`): it carries BGP-like attributes in
  `bgp` but is not a BGP route. -/
  generated : Bool := false
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace Route

def nextHopIp? (r : Route) : Option Ip :=
  match r.nextHop with
  | .ip ip => some ip
  | .iface _ ip => ip
  | .discard => none

/-- The next-hop interface, or Batfish's `"dynamic"` placeholder when there is none. -/
def nextHopInterface (r : Route) : String :=
  match r.nextHop with
  | .iface name _ => name
  | .discard => NextHop.nullInterfaceName
  | .ip _ => NextHop.unsetInterfaceName

def localPreference (r : Route) : Nat := (r.bgp.map (·.localPreference)).getD 0

def asPath (r : Route) : AsPath := (r.bgp.map (·.asPath)).getD #[]

def communities (r : Route) : CommunitySet := (r.bgp.map (·.communities)).getD {}

/-- Whether this is a BGP route (Batfish's `BgpRoute`). -/
def isBgpRoute (r : Route) : Bool := r.bgp.isSome && !r.generated

def ospfArea (r : Route) : Option Nat := r.ospf.bind (·.area)

/-- Update the BGP attributes, if this is a BGP route. -/
def modifyBgp (r : Route) (f : BgpAttrs → BgpAttrs) : Route :=
  { r with bgp := r.bgp.map f }

end Route

end LeanBatfish
