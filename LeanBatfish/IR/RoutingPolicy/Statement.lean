import LeanBatfish.IR.RoutingPolicy.Community
import LeanBatfish.IR.RoutingPolicy.AsPath

/-!
# Routing policies

A `RoutingPolicy` is a list of statements run against a route. Statements and boolean
expressions are mutually recursive: `If` tests a boolean expression, and some boolean
expressions (`CallExpr`, `FirstMatchChain`, `WithEnvironmentExpr`) run statements.

The constructors follow Batfish's classes in `routing_policy.statement` and
`routing_policy.expr`; the comment on each names the class.
-/

namespace LeanBatfish

/-- The parameterless statements of `Statements.StaticStatement`. -/
inductive StaticStatementType
  | defaultAction
  | exitAccept
  | exitReject
  | fallThrough
  | removePrivateAs
  | «return»
  | returnFalse
  | returnLocalDefaultAction
  | returnTrue
  | setDefaultActionAccept
  | setDefaultActionReject
  | setLocalDefaultActionAccept
  | setLocalDefaultActionReject
  | setReadIntermediateBgpAttributes
  | setWriteIntermediateBgpAttributes
  | suppress
  | unsetWriteIntermediateBgpAttributes
  | unsuppress
  deriving DecidableEq, Inhabited, Repr

def StaticStatementType.names : List (String × StaticStatementType) := [
  ("DefaultAction", .defaultAction), ("ExitAccept", .exitAccept),
  ("ExitReject", .exitReject), ("FallThrough", .fallThrough),
  ("RemovePrivateAs", .removePrivateAs), ("Return", .return),
  ("ReturnFalse", .returnFalse), ("ReturnLocalDefaultAction", .returnLocalDefaultAction),
  ("ReturnTrue", .returnTrue), ("SetDefaultActionAccept", .setDefaultActionAccept),
  ("SetDefaultActionReject", .setDefaultActionReject),
  ("SetLocalDefaultActionAccept", .setLocalDefaultActionAccept),
  ("SetLocalDefaultActionReject", .setLocalDefaultActionReject),
  ("SetReadIntermediateBgpAttributes", .setReadIntermediateBgpAttributes),
  ("SetWriteIntermediateBgpAttributes", .setWriteIntermediateBgpAttributes),
  ("Suppress", .suppress),
  ("UnsetWriteIntermediateBgpAttributes", .unsetWriteIntermediateBgpAttributes),
  ("Unsuppress", .unsuppress)]

/-- The parameterless boolean expressions of `BooleanExprs.StaticBooleanExpr`. -/
inductive StaticBooleanType
  | callExprContext
  | callStatementContext
  | «false»
  | «true»
  deriving DecidableEq, Inhabited, Repr

def StaticBooleanType.names : List (String × StaticBooleanType) := [
  ("CallExprContext", .callExprContext), ("CallStatementContext", .callStatementContext),
  ("False", .false), ("True", .true)]

/-- `AdministrativeCostExpr`. -/
inductive AdminCostExpr
  | literal (value : Nat)
  | increment (addend max : Nat)
  | decrement (subtrahend min : Nat)
  deriving Inhabited, Repr

mutual

inductive BooleanExpr
  /-- `StaticBooleanExpr`. -/
  | static (type : StaticBooleanType)
  /-- `CallExpr`: run another policy as a boolean subroutine. -/
  | call (policyName : String)
  | conjunction (conjuncts : Array BooleanExpr)
  | disjunction (disjuncts : Array BooleanExpr)
  /-- `ConjunctionChain`: Juniper policy chains joined by `&&`. -/
  | conjunctionChain (subroutines : Array BooleanExpr)
  /-- `FirstMatchChain`: Juniper policy chains, the first to accept or reject decides. -/
  | firstMatchChain (subroutines : Array BooleanExpr)
  | not (expr : BooleanExpr)
  /-- `WithEnvironmentExpr`: evaluate `expr` with intermediate BGP attributes enabled,
  running the given statements around it. -/
  | withEnvironment (expr : BooleanExpr) (preStatements postStatements postTrueStatements :
      Array Statement)
  /-- `MatchPrefixSet` on the route's destination network (`DestinationNetwork`). -/
  | matchPrefixSet (prefixSet : PrefixSetExpr)
  | matchProtocol (protocols : Array RoutingProtocol)
  | matchSourceProtocol (protocols : Array RoutingProtocol)
  | matchTag (comparator : IntComparator) (tag : LongExpr)
  | matchMetric (comparator : IntComparator) (metric : LongExpr)
  | matchLocalPreference (comparator : IntComparator) (localPreference : LongExpr)
  | matchBgpSessionType (types : Array BgpSessionType)
  | matchCommunities (communitySetExpr : CommunitySetExpr)
      (communitySetMatchExpr : CommunitySetMatchExpr)
  /-- `MatchAsPath` (structured AS-path matching). -/
  | matchAsPath (asPathExpr : AsPathExpr) (asPathMatchExpr : AsPathMatchExpr)
  /-- `LegacyMatchAsPath` with a `NamedAsPathSet`: an AS-path access list. -/
  | legacyMatchAsPath (asPathAccessList : String)
  /-- `MatchInterface`: the route's next-hop interface is one of these. -/
  | matchInterface (interfaces : Array String)
  /-- `MatchPeerAddress`: the route was received from one of these peers. -/
  | matchPeerAddress (peers : Array Ip)
  | matchProcessAsn (asn : Asn)
  | matchClusterListLength (comparator : IntComparator) (length : IntExpr)
  | matchIpv4
  | routeIsClassful

inductive Statement
  /-- `Statements.StaticStatement`. -/
  | static (type : StaticStatementType)
  | ifThen (guard : BooleanExpr) (trueStatements falseStatements : Array Statement)
  /-- `CallStatement`. -/
  | call (policyName : String)
  /-- `Comment`: no effect. -/
  | comment
  | setDefaultPolicy (policyName : String)
  | setLocalPreference (localPreference : LongExpr)
  | setMetric (metric : LongExpr)
  | setTag (tag : LongExpr)
  | setDefaultTag (tag : LongExpr)
  | setWeight (weight : IntExpr)
  | setOrigin (origin : OriginType)
  | setNextHop (expr : NextHopExpr)
  | setAdministrativeCost (admin : AdminCostExpr)
  | setOspfMetricType (metricType : OspfMetricType)
  | setCommunities (communitySetExpr : CommunitySetExpr)
  | prependAsPath (expr : AsPathListExpr)
  | excludeAsPath (expr : AsPathListExpr)
  /-- `TraceableStatement`: runs its inner statements; the trace element is only for
  presentation. -/
  | traceable (innerStatements : Array Statement)

end

instance : Inhabited BooleanExpr := ⟨.static .true⟩
instance : Inhabited Statement := ⟨.comment⟩

structure RoutingPolicy where
  name : String
  statements : Array Statement
  deriving Inhabited

end LeanBatfish
