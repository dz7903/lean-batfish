import LeanBatfish.Net.Prefix

/-!
# Next hops

Where a route sends traffic (`route.nh.NextHop`). Batfish's JSON for static routes gives
the next hop as a pair of optional fields, `nextHopIp` and `nextHopInterface`, decoded by
`NextHop.ofLegacy` exactly as Batfish's `NextHop.legacyConverter` does.
-/

namespace LeanBatfish

inductive NextHop
  /-- Drop the traffic (`NextHopDiscard`, the `null_interface`). -/
  | discard
  /-- Resolve this IP recursively through the RIB (`NextHopIp`). -/
  | ip (ip : Ip)
  /-- Send out of this interface, to the destination itself or to `ip` if given
  (`NextHopInterface`). -/
  | iface (name : String) (ip : Option Ip)
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace NextHop

/-- Batfish's name for the discard interface. -/
def nullInterfaceName : String := "null_interface"

/-- Batfish's name for an unset next-hop interface. -/
def unsetInterfaceName : String := "dynamic"

def ofLegacy (iface : Option String) (ip : Option Ip) : Option NextHop :=
  match iface with
  | some name =>
    if name == unsetInterfaceName then ip.map .ip
    else if name == nullInterfaceName then some .discard
    else some (.iface name ip)
  | none => ip.map .ip

end NextHop

end LeanBatfish
