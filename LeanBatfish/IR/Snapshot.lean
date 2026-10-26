import LeanBatfish.IR.Announcement
import LeanBatfish.IR.Configuration
import LeanBatfish.Topology.Edge

/-!
# Snapshots

A snapshot is what Batfish analyzes: the configurations of the network's devices, plus
inputs from outside them. LeanBatfish reads it as Batfish exports it: the
vendor-independent configurations, the adjacencies Batfish computed (layer-3 edges, OSPF
adjacencies, BGP sessions), and the external BGP announcements, if any.
-/

namespace LeanBatfish

structure Snapshot where
  /-- The configurations, sorted by hostname. -/
  configs : Array Configuration
  topology : Topology
  announcements : Array Announcement := #[]
  deriving Inhabited

end LeanBatfish
