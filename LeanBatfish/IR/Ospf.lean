import LeanBatfish.IR.Basic
import LeanBatfish.Net.Prefix
import LeanBatfish.IR.GeneratedRoute
import Lean.Data.Json.Basic

/-!
# OSPF configuration

The OSPF parts of the IR: per-VRF processes with their areas, and per-interface settings.
The modeled subset is plain (non-stub, non-NSSA) areas without summarization; the decoder
rejects the rest.
-/

namespace LeanBatfish

inductive OspfNetworkType
  | broadcast
  | pointToPoint
  deriving DecidableEq, Inhabited, Repr

def OspfNetworkType.names : List (String × OspfNetworkType) :=
  [("BROADCAST", .broadcast), ("POINT_TO_POINT", .pointToPoint)]

structure OspfInterfaceSettings where
  enabled : Bool
  passive : Bool
  /-- The OSPF process (by process id) this interface belongs to. -/
  process : Option String
  area : Option Nat
  cost : Option Nat
  networkType : Option OspfNetworkType
  helloInterval : Nat
  deadInterval : Nat
  deriving Inhabited, Repr

structure OspfArea where
  name : Nat
  /-- Interfaces in the area. -/
  interfaces : Array String
  injectDefaultRoute : Bool
  metricOfDefaultRoute : Nat
  deriving Inhabited, Repr

structure OspfProcess where
  processId : String
  routerId : Ip
  /-- In bits per second, as Batfish writes it (a decimal number). -/
  referenceBandwidth : Lean.JsonNumber
  /-- Administrative distance per OSPF route type (`ospf`, `ospfIA`, `ospfE1`, ...). -/
  adminCosts : Array (RoutingProtocol × Nat)
  areas : Array OspfArea
  /-- The policy deciding which routes are redistributed into OSPF. -/
  exportPolicy : Option String
  summaryAdminCost : Nat
  /-- Routes the process originates as externals, such as Cisco's `default-information
  originate`. -/
  generatedRoutes : Array GeneratedRoute
  deriving Inhabited, Repr

end LeanBatfish
