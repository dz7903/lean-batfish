import LeanBatfish.IR.RoutingPolicy.Expr

/-!
# AS-path expressions

Two generations of AS-path matching coexist in Batfish:

* the structured language of `routing_policy.as_path` (`MatchAsPath` with an
  `AsPathExpr` and an `AsPathMatchExpr`, named ones in `asPathExprs` and
  `asPathMatchExprs`);
* the legacy `AsPathAccessList`s (`asPathAccessLists`), used by `LegacyMatchAsPath`.

Both match regular expressions against the rendered AS path (`AsPath.render`), using
Java's unanchored `find()`.
-/

namespace LeanBatfish

/-- Computes an AS path (`AsPathExpr`). -/
inductive AsPathExpr
  /-- The AS path of the route being processed. -/
  | input
  /-- `expr` with consecutive duplicate ASes removed. -/
  | deduped (expr : AsPathExpr)
  | reference (name : String)
  deriving Inhabited, Repr

/-- A predicate on an AS path (`AsPathMatchExpr`). -/
inductive AsPathMatchExpr
  | regex (regex : String)
  | any (disjuncts : Array AsPathMatchExpr)
  | hasLength (comparator : IntComparator) (length : IntExpr)
  | reference (name : String)
  deriving Inhabited, Repr

structure AsPathAccessListLine where
  action : LineAction
  regex : String
  deriving Inhabited, Repr

/-- A legacy AS-path access list: the first line whose regex matches decides; no match
means deny. -/
structure AsPathAccessList where
  name : String
  lines : Array AsPathAccessListLine
  deriving Inhabited, Repr

end LeanBatfish
