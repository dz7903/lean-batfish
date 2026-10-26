import LeanBatfish.Semantics.Policy.Eval
import LeanBatfish.Topology.Edge
import LeanBatfish.IR.Configuration

/-!
# BGP sessions

A BGP session between two configured neighbors, seen in one direction: routes flow from the
*local* side to the *remote* side (Batfish's `BgpSessionProperties` for an edge). Which
sessions exist comes from the topology; their properties come from the two neighbors'
configurations.
-/

namespace LeanBatfish.Bgp

/-- One end of a session: a node, a VRF, its BGP process and the neighbor configuration
for the other end. -/
structure Endpoint where
  host : String
  vrf : String
  process : BgpProcess
  peer : BgpPeer
  /-- The neighbor's IPv4 unicast address family. -/
  af : Ipv4UnicastAddressFamily
  deriving Inhabited

/-- A session in the direction from `local` to `remote`. -/
structure Session where
  localEnd : Endpoint
  remoteEnd : Endpoint
  localAs : Nat
  remoteAs : Nat
  localIp : Ip
  remoteIp : Ip
  isEbgp : Bool
  /-- Whether the local side sends all paths, not just best paths (add-path). -/
  additionalPaths : Bool
  /-- Whether the local side advertises BGP routes that are not active in its main RIB. -/
  advertiseInactive : Bool
  deriving Inhabited

namespace Session

/-- The session in the other direction. -/
def reverse (s : Session) : Session :=
  { localEnd := s.remoteEnd, remoteEnd := s.localEnd, localAs := s.remoteAs, remoteAs := s.localAs
    localIp := s.remoteIp, remoteIp := s.localIp, isEbgp := s.isEbgp
    additionalPaths := !s.isEbgp && s.localEnd.af.capabilities.additionalPathsReceive &&
      s.remoteEnd.af.capabilities.additionalPathsSend &&
      s.remoteEnd.af.capabilities.additionalPathsSelectAll
    advertiseInactive := s.remoteEnd.af.capabilities.advertiseInactive }

/-- What routing policies see of the session. -/
def forPolicy (s : Session) : Policy.Session :=
  { localAs := s.localAs, remoteAs := s.remoteAs, localIp := s.localIp, remoteIp := s.remoteIp
    isEbgp := s.isEbgp }

/-- The session from `local` (at `localIp`) to `remote` (at `remoteIp`), from the two
neighbor configurations (`BgpSessionProperties.from`). Without confederations, a session
is eBGP when the two local AS numbers differ. -/
def make (l r : Endpoint) (localIp remoteIp : Ip) : Except String Session := do
  let some localAs := l.peer.localAs | throw s!"BGP neighbor {remoteIp} on {l.host} has no local AS"
  let some remoteAs := r.peer.localAs | throw s!"BGP neighbor {localIp} on {r.host} has no local AS"
  let isEbgp := localAs != remoteAs
  return {
    localEnd := l, remoteEnd := r, localAs, remoteAs, localIp, remoteIp, isEbgp
    additionalPaths := !isEbgp && r.af.capabilities.additionalPathsReceive &&
      l.af.capabilities.additionalPathsSend && l.af.capabilities.additionalPathsSelectAll
    advertiseInactive := l.af.capabilities.advertiseInactive }

end Session

/-- The endpoint of a session on router `c` for the peer at `peerIp`: the VRF and neighbor
configured for it, either by address or, failing that, as a passive neighbor whose prefix
contains it (the most specific such prefix). -/
def endpoint (c : Configuration) (peerIp : Ip) : Except String Endpoint := do
  let host := c.hostname
  let mut passive : Option (Vrf × BgpProcess × BgpPeer × Nat) := none
  for (_, v) in c.vrfs do
    let some p := v.bgpProcess | continue
    if let some peer := p.neighbors.find? (·.remote == .address peerIp) then
      let some af := peer.ipv4Unicast | throw s!"BGP neighbor {peerIp} on {host} has no IPv4 unicast"
      return { host, vrf := v.name, process := p, peer, af }
    for peer in p.passiveNeighbors do
      let .prefix q := peer.remote | continue
      let better : Bool := match passive with
        | some (_, _, _, len) => decide (len < q.len.val)
        | none => true
      if q.containsIp peerIp && better then
        passive := some (v, p, peer, q.len.val)
  match passive with
  | some (v, p, peer, _) =>
    let some af := peer.ipv4Unicast | throw s!"BGP neighbor for {peerIp} on {host} has no IPv4 unicast"
    return { host, vrf := v.name, process := p, peer, af }
  | none => throw s!"no BGP neighbor {peerIp} on {host}"

/-- `BgpProcess.getAdminCost`. -/
def adminCost (p : BgpProcess) (proto : RoutingProtocol) : Nat :=
  if proto == .ibgp then p.ibgpAdminCost else p.ebgpAdminCost

/-- `BgpProcess.getClusterIds`: the cluster IDs configured on the process's neighbors. -/
def clusterIds (p : BgpProcess) : Array Nat :=
  p.neighbors.filterMap (·.clusterId)

end LeanBatfish.Bgp
