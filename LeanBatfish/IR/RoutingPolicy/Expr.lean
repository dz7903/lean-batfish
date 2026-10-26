import LeanBatfish.IR.RoutingPolicy.PrefixSet
import LeanBatfish.Net.AsPath

/-!
# Routing-policy value expressions

The non-boolean expressions of Batfish's routing-policy language: numbers, AS numbers,
next hops, origins and prefixes. Expressions that read policy variables (`Var*`) are not
part of the IR we model; Batfish's concrete evaluator rejects them too.
-/

namespace LeanBatfish

/-- `IntExpr`: only literals (`LiteralInt`). -/
abbrev IntExpr := Int

inductive IntMatchExpr
  | comparison (comparator : IntComparator) (expr : IntExpr)
  | all (exprs : Array IntMatchExpr)
  deriving Inhabited, Repr

/-- An AS number computed from the route or session (`AsExpr`). -/
inductive AsExpr
  | explicit (asn : Asn)
  /-- The local AS of the BGP session (`AutoAs`, `LocalAs` differ in corner cases). -/
  | autoAs
  | localAs
  | remoteAs
  /-- The last (originating) AS of the route's AS path. -/
  | lastAs
  deriving Inhabited, Repr

/-- `LongExpr`. -/
inductive LongExpr
  | literal (value : Int)
  /-- The original route's metric plus `addend`, at most `2^32 - 1` (`IncrementMetric`). -/
  | incrementMetric (addend : Nat)
  /-- The original route's metric minus `subtrahend`, at least 0 (`DecrementMetric`). -/
  | decrementMetric (subtrahend : Nat)
  /-- The local preference plus `addend` (`IncrementLocalPreference`). -/
  | incrementLocalPreference (addend : Nat)
  /-- The local preference minus `subtrahend`, at least 0 (`DecrementLocalPreference`). -/
  | decrementLocalPreference (subtrahend : Nat)
  /-- An AS number as a long (`AsnValue`). -/
  | asnValue (asExpr : AsExpr)
  /-- `(high << 16) | low` (`Uint32HighLowExpr`). -/
  | uint32HighLow (high low : IntExpr)
  deriving Inhabited, Repr

inductive LongMatchExpr
  | comparison (comparator : IntComparator) (expr : LongExpr)
  | all (exprs : Array LongMatchExpr)
  deriving Inhabited, Repr

/-- A list of AS numbers to prepend or exclude (`AsPathListExpr`). -/
inductive AsPathListExpr
  | literal (list : Array AsExpr)
  /-- `expr` repeated `number` times (`MultipliedAs`). -/
  | multiplied (expr : AsExpr) (number : IntExpr)
  deriving Inhabited, Repr

/-- The next hop to set (`NextHopExpr`). -/
inductive NextHopExpr
  | discard
  /-- One IP, or several for ECMP; Batfish uses only a single IP here. -/
  | ip (ips : Array Ip)
  /-- The local IP of the BGP session. -/
  | self
  /-- Keep the next hop the route arrived with. -/
  | unchanged
  /-- The IP of the BGP peer the route was received from. -/
  | bgpPeerAddress
  deriving Inhabited, Repr

/-- `PrefixSetExpr`. -/
inductive PrefixSetExpr
  | explicit (prefixSpace : PrefixSpace)
  /-- A route-filter list of the configuration. -/
  | named (name : String)
  deriving Inhabited, Repr

end LeanBatfish
