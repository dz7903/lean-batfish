import LeanBatfish.IR.RoutingPolicy.Expr
import LeanBatfish.Net.Community

/-!
# Community expressions

Batfish's community language (`routing_policy.communities`) has four sorts:

* `CommunityMatchExpr` — a predicate on a single community;
* `CommunitySetExpr` — computes a set of communities (e.g. the route's input
  communities, a literal, a union, a difference);
* `CommunitySetMatchExpr` — a predicate on a set of communities;
* renderings — how communities are turned into strings for regex matching.

Named expressions live in the configuration's `communityMatchExprs`,
`communitySetExprs`, `communitySetMatchExprs` and `communitySets` maps.
-/

namespace LeanBatfish

/-- How a single community is rendered for `CommunityMatchRegex`. -/
inductive CommunityRendering
  /-- `"65000:100"`, the usual printed form. -/
  | colonSeparated
  /-- The community's numeric value. -/
  | integerValue
  /-- Fixed strings for some communities, `fallback` for the rest. -/
  | specialCases (fallback : CommunityRendering) (specialCases : Array (Community × String))
  deriving Inhabited, Repr

/-- How a community set is rendered for `CommunitySetMatchRegex`: standard, then
extended, then large communities, each ascending and rendered by `rendering`, separated
by spaces (`TypesFirstAscendingSpaceSeparated`). -/
structure CommunitySetRendering where
  rendering : CommunityRendering
  deriving Inhabited, Repr

/-- A community built from expressions (`CommunityExpr`). -/
inductive CommunityExpr
  | standardHighLow (high low : IntExpr)
  | routeTarget (globalAdmin localAdmin : LongExpr)
  deriving Inhabited, Repr

mutual

/-- A predicate on one community. -/
inductive CommunityMatchExpr
  | is (community : Community)
  | inSet (set : CommunitySetExpr)
  | matchAll (exprs : Array CommunityMatchExpr)
  | matchAny (exprs : Array CommunityMatchExpr)
  | not (expr : CommunityMatchExpr)
  | regex (rendering : CommunityRendering) (regex : String)
  | reference (name : String)
  | allStandard
  | allExtended
  | allLarge
  /-- First-match lines; no matching line means no match. -/
  | acl (lines : Array (LineAction × CommunityMatchExpr))
  | standardHigh (expr : IntMatchExpr)
  | standardLow (expr : IntMatchExpr)
  | routeTargetExtended
  | siteOfOriginExtended
  | vpnDistinguisherExtended
  | opaqueExtended (transitive : Bool) (subType : Nat)
  | extendedGlobalAdmin (expr : LongMatchExpr)
  | extendedGlobalAdminHigh (expr : IntMatchExpr)
  | extendedGlobalAdminLow (expr : IntMatchExpr)
  | extendedLocalAdmin (expr : LongMatchExpr)

/-- An expression computing a set of communities. -/
inductive CommunitySetExpr
  /-- The communities of the route being processed. -/
  | input
  | literal (communities : Array Community)
  | union (exprs : Array CommunitySetExpr)
  /-- `initial` minus the communities matching `removalCriterion`. -/
  | difference (initial : CommunitySetExpr) (removalCriterion : CommunityMatchExpr)
  /-- A named `CommunitySetExpr` of the configuration. -/
  | exprReference (name : String)
  /-- A named literal `CommunitySet` of the configuration. -/
  | setReference (name : String)
  | ofExprs (exprs : Array CommunityExpr)

end

instance : Inhabited CommunityMatchExpr := ⟨.allStandard⟩
instance : Inhabited CommunitySetExpr := ⟨.input⟩

/-- A predicate on a set of communities. -/
inductive CommunitySetMatchExpr
  /-- Some community of the set satisfies `expr`. -/
  | hasCommunity (expr : CommunityMatchExpr)
  | hasSize (expr : IntMatchExpr)
  | matchAll (exprs : Array CommunitySetMatchExpr)
  | matchAny (exprs : Array CommunitySetMatchExpr)
  | not (expr : CommunitySetMatchExpr)
  | regex (rendering : CommunitySetRendering) (regex : String)
  | reference (name : String)
  /-- First-match lines; no matching line means no match. -/
  | acl (lines : Array (LineAction × CommunitySetMatchExpr))
  deriving Inhabited

end LeanBatfish
