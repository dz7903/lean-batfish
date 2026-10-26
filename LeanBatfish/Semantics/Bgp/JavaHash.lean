import LeanBatfish.Semantics.Route

/-!
# Java hash codes of BGP routes

With add-path, Batfish numbers the paths it sends for each prefix, and it assigns numbers to
a batch of routes in the order of their Java `hashCode()` (`PATH_ID_ROUTE_COMPARATOR`). The
numbers are visible in answers and break ties in best-path selection, so LeanBatfish
computes the same hash codes. They follow Batfish's `hashCode` methods of `Bgpv4Route` and
the objects it contains; all are deterministic (Batfish uses fixed constants for singletons
such as `NextHopDiscard` and `ReceivedFromSelf`).

Java `int` arithmetic is 32-bit two's complement, modeled with `UInt32`.
-/

namespace LeanBatfish.JavaHash

/-- `Long.hashCode`. -/
def long (v : Int) : UInt32 :=
  let u : UInt64 := UInt64.ofInt v
  (u ^^^ (u >>> 32)).toUInt32

def bool (b : Bool) : UInt32 := if b then 1231 else 1237

def ip (i : Ip) : UInt32 := i.bits

/-- `Prefix.hashCode`. -/
def «prefix» (p : Prefix) : UInt32 := 31 + 31 * long p.addr.bits.toNat + p.len.val.toUInt32

/-- `String.hashCode` (over UTF-16 code units; configuration names are ASCII). -/
def string (s : String) : UInt32 :=
  s.foldl (fun h c => h * 31 + c.toNat.toUInt32) 0

def nextHop : NextHop → UInt32
  | .discard => 856925083
  | .ip i => ip i
  | .iface name none => string name
  | .iface name (some i) => string name + 31 * ip i

def receivedFrom : ReceivedFrom → UInt32
  | .self => 0x631AFA34
  | .ip i => ip i

/-- `List.hashCode` of the AS sets; each `AsSet` hashes its sorted ASNs and its flag. -/
def asPath (p : AsPath) : UInt32 :=
  p.foldl (fun h s =>
    let arr := s.asns.foldl (fun (a : UInt32) (n : Nat) => 31 * a + long n) 1
    31 * h + (arr * 31 + bool s.confederation)) 1

def community : Community → UInt32
  | .standard v => long v.toNat
  | .extended t sub value => 31 * 31 * long value + 31 * t.toUInt32 + sub.toUInt32
  | .large a b c =>
    -- `Objects.hash(Long, Long, Long)`.
    [a, b, c].foldl (fun h x => 31 * h + long x.toNat) 1

/-- `Set.hashCode`: the sum of the elements' hash codes. -/
def communities (cs : CommunitySet) : UInt32 := cs.toArray.foldl (fun h c => h + community c) 0

def clusterList (cl : Array Nat) : UInt32 := cl.foldl (fun (h : UInt32) (c : Nat) => h + long c) 0

private def ordinal (p : RoutingProtocol) : UInt32 :=
  ((RoutingProtocol.names.findIdx? (·.2 == p)).getD 0).toUInt32

private def originMechanism : OriginMechanism → UInt32
  | .generated => 0 | .learned => 1 | .network => 2 | .redistribute => 3

private def originType : OriginType → UInt32
  | .egp => 0 | .igp => 1 | .incomplete => 2

/-- `BgpRouteAttributes.hashCode`. -/
def attributes (r : Route) (a : BgpAttrs) : UInt32 := Id.run do
  let mut h := asPath a.asPath
  h := h * 31 + clusterList a.clusterList
  h := h * 31 + communities a.communities
  h := h * 31 + a.localPreference.toUInt32
  h := h * 31 + r.metric.toUInt32
  h := h * 31 + ip a.originatorIp
  h := h * 31 + originMechanism a.originMechanism
  h := h * 31 + originType a.originType
  h := h * 31 + ordinal r.protocol
  h := h * 31 + bool a.receivedFromRouteReflectorClient
  h := h * 31 + (match a.srcProtocol with | some p => ordinal p | none => (0 : UInt32) - 1)
  h := h * 31 + 0
  h := h * 31 + a.weight.toUInt32
  return h

/-- `Bgpv4Route.hashCode`. -/
def bgpv4Route (r : Route) : UInt32 := Id.run do
  let a := r.bgp.getD {}
  let mut h := long r.admin
  h := h * 31 + attributes r a
  h := h * 31 + receivedFrom a.receivedFrom
  h := h * 31 + «prefix» r.network
  h := h * 31 + nextHop r.nextHop
  h := h * 31 + (a.pathId.getD 0).toUInt32
  h := h * 31 + bool r.nonForwarding
  h := h * 31 + bool r.nonRouting
  h := h * 31 + long r.tag
  return h

/-- `Objects.hash`: `Arrays.hashCode` of the boxed arguments' hash codes. -/
def objects (hs : List UInt32) : UInt32 := hs.foldl (fun h x => 31 * h + x) 1

private def area (r : Route) : UInt32 :=
  long (match r.ospfArea with | some a => (a : Int) | none => -1)

/-- The hash code of a main-RIB route that is not a BGP route, as Batfish's route class
computes it, or `none` for classes not ported. -/
def nonBgpRoute (r : Route) : Option UInt32 :=
  match r.protocol with
  | .connected => some (objects [«prefix» r.network, long r.admin, bool r.nonRouting,
      bool r.nonForwarding, nextHop r.nextHop, long r.tag])
  | .local => some (objects [«prefix» r.network, long r.admin, bool r.nonRouting,
      bool r.nonForwarding, nextHop r.nextHop, r.sourcePrefixLength.toUInt32, long r.tag])
  | .static => some (objects [«prefix» r.network, long r.admin, bool r.nonForwarding,
      bool r.nonRouting, long r.metric, nextHop r.nextHop, long r.tag, bool r.recursive, 0])
  | .ospf | .ospfIa => some (Id.run do
      let mut h := «prefix» r.network
      h := 31 * h + long r.admin
      h := 31 * h + area r
      h := 31 * h + long r.metric
      h := 31 * h + nextHop r.nextHop
      h := 31 * h + bool r.nonForwarding
      h := 31 * h + bool r.nonRouting
      h := 31 * h + long r.tag
      return h)
  | .ospfE1 | .ospfE2 => some (Id.run do
      let a := r.ospf.getD {}
      let mut h := «prefix» r.network
      h := 31 * h + long r.admin
      h := 31 * h + long r.metric
      h := 31 * h + nextHop r.nextHop
      h := 31 * h + bool r.nonRouting
      h := 31 * h + bool r.nonForwarding
      h := 31 * h + long r.tag
      h := 31 * h + area r
      h := 31 * h + string a.advertiser
      h := 31 * h + long a.costToAdvertiser
      h := 31 * h + long a.lsaMetric
      return h)
  | _ => none

/-- `AnnotatedRoute.hashCode`: a main-RIB route with the name of its VRF. -/
def annotated (routeHash : UInt32) (vrf : String) : UInt32 := 31 * routeHash + string vrf

/-- A Java `int` as a signed integer, for `Comparator.comparingInt`. -/
def signed (h : UInt32) : Int := if h.toNat ≥ 2 ^ 31 then h.toNat - 2 ^ 32 else h.toNat

end LeanBatfish.JavaHash
