import LeanBatfish.Net.Ip

/-!
# Edges

The adjacencies the routing protocols and forwarding run over. Batfish computes them from the
configurations (layer-3 edges from shared subnets, OSPF adjacencies from compatible
interface settings, BGP sessions from compatible peer settings and reachability). For
now LeanBatfish takes them from Batfish's `layer3Edges`, `ospfEdges` and `bgpEdges` answers; computing
them in Lean is a later step of the plan.

Edges are directed. An edge from `tail` to `head` carries routes from `tail` to `head`.
-/

namespace LeanBatfish

/-- An interface of a node. -/
structure NodeInterface where
  host : String
  iface : String
  deriving DecidableEq, Hashable, Inhabited, Repr

instance : ToString NodeInterface := ⟨fun n => s!"{n.host}[{n.iface}]"⟩

/-- An OSPF adjacency: `tail` and `head` are the two interfaces. -/
structure OspfEdge where
  tail : NodeInterface
  head : NodeInterface
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- An established BGP session, seen from `tail`'s side: routes flow from `tail` to `head`.
Each session appears in both directions. -/
structure BgpEdge where
  tailHost : String
  tailIp : Ip
  headHost : String
  headIp : Ip
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- A layer-3 edge: `tail` and `head` are interfaces in a shared subnet, so `tail` can send
packets to the addresses of `head`. Each link appears in both directions. -/
structure Layer3Edge where
  tail : NodeInterface
  head : NodeInterface
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- The adjacencies of a network. -/
structure Topology where
  ospf : Array OspfEdge := #[]
  bgp : Array BgpEdge := #[]
  layer3 : Array Layer3Edge := #[]
  deriving Inhabited

end LeanBatfish
