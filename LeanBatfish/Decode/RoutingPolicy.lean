import LeanBatfish.Decode.Net
import LeanBatfish.IR.RoutingPolicy.Statement

/-!
# Decoding routing policies

Decoders for Batfish's routing-policy language: statements, boolean expressions, value
expressions, communities and AS paths. Classes outside the modeled language are rejected
by `byClass`. A few classes are known but rejected on purpose:

* `Var*` expressions, `HasRoute` and `MatchColor`, which Batfish's concrete evaluator
  does not support either.
-/

namespace LeanBatfish.Decode

open Lean ObjM

private def stmt (name : String) (d : ObjM α) : String × ObjM α :=
  ("routing_policy.statement." ++ name, do ignore "comment"; d)
private def expr (name : String) (d : ObjM α) : String × ObjM α :=
  ("routing_policy.expr." ++ name, do ignore "comment"; d)
private def comm (name : String) (d : ObjM α) : String × ObjM α :=
  ("routing_policy.communities." ++ name, d)
private def asp (name : String) (d : ObjM α) : String × ObjM α :=
  ("routing_policy.as_path." ++ name, d)
/-- Statements and boolean expressions outside the `statement`/`expr` packages, which
carry a `comment` like all statements and boolean expressions do. -/
private def commented (c : String × ObjM α) : String × ObjM α :=
  (c.1, do ignore "comment"; c.2)

/-! ## Value expressions -/

def intExpr : Decoder IntExpr := byClass "int expression" [
  expr "LiteralInt" (req "value" int)]

def asExpr : Decoder AsExpr := byClass "AS expression" [
  expr "ExplicitAs" (.explicit <$> req "as" nat),
  expr "AutoAs" (pure .autoAs),
  expr "LocalAs" (pure .localAs),
  expr "RemoteAs" (pure .remoteAs),
  expr "LastAs" (pure .lastAs)]

def longExpr : Decoder LongExpr := byClass "long expression" [
  expr "LiteralLong" (.literal <$> req "value" int),
  expr "IncrementMetric" (.incrementMetric <$> req "addend" nat),
  expr "DecrementMetric" (.decrementMetric <$> req "subtrahend" nat),
  expr "IncrementLocalPreference" (.incrementLocalPreference <$> req "addend" nat),
  expr "DecrementLocalPreference" (.decrementLocalPreference <$> req "subtrahend" nat),
  expr "AsnValue" (.asnValue <$> req "as" asExpr),
  expr "Uint32HighLowExpr" (.uint32HighLow <$> req "highExpr" intExpr <*> req "lowExpr" intExpr)]

partial def intMatchExpr : Decoder IntMatchExpr := byClass "int match expression" [
  expr "IntComparison" (.comparison <$> req "comparator" intComparator <*> req "expr" intExpr),
  expr "IntMatchAll" (.all <$> dflt "exprs" #[] (array intMatchExpr))]

partial def longMatchExpr : Decoder LongMatchExpr := byClass "long match expression" [
  expr "LongComparison" (.comparison <$> req "comparator" intComparator <*> req "expr" longExpr),
  expr "LongMatchAll" (.all <$> dflt "exprs" #[] (array longMatchExpr))]

def asPathListExpr : Decoder AsPathListExpr := byClass "AS list expression" [
  expr "LiteralAsList" (.literal <$> dflt "list" #[] (array asExpr)),
  expr "MultipliedAs" (.multiplied <$> req "expr" asExpr <*> req "number" intExpr)]

def nextHopExpr : Decoder NextHopExpr := byClass "next-hop expression" [
  expr "DiscardNextHop" (pure .discard),
  expr "IpNextHop" (.ip <$> dflt "ips" #[] (array ip)),
  expr "SelfNextHop" (pure .self),
  expr "UnchangedNextHop" (pure .unchanged),
  expr "BgpPeerAddressNextHop" (pure .bgpPeerAddress)]

def originExpr : Decoder OriginType := byClass "origin expression" [
  -- `asNum` is never read by Batfish's evaluation.
  expr "LiteralOrigin" (do ignore "asNum"; req "originType" originType)]

def prefixRange : Decoder PrefixRange := parsed "a prefix range" fun s =>
  match s.splitOn ":" with
  | [p] => (Prefix.parse? p).map fun p => ⟨p, .singleton p.len⟩
  | [p, r] => do pure ⟨← Prefix.parse? p, ← SubRange.parse? r⟩
  | _ => none

def prefixSetExpr : Decoder PrefixSetExpr := byClass "prefix set expression" [
  expr "ExplicitPrefixSet" (.explicit <$> dflt "prefixSpace" #[] (array prefixRange)),
  expr "NamedPrefixSet" (.named <$> req "name" str)]

def adminCostExpr : Decoder AdminCostExpr := byClass "administrative cost expression" [
  expr "LiteralAdministrativeCost" (.literal <$> req "value" nat),
  expr "IncrementAdministrativeCost" (.increment <$> req "addend" nat <*> req "max" nat),
  expr "DecrementAdministrativeCost" (.decrement <$> req "subtrahend" nat <*> req "min" nat)]

/-! ## Communities -/

partial def communityRendering : Decoder CommunityRendering := byClass "community rendering" [
  comm "ColonSeparatedRendering" (pure .colonSeparated),
  comm "IntegerValueRendering" (pure .integerValue),
  comm "SpecialCasesRendering" do
    let fallback ← req "fallbackRendering" communityRendering
    let cases ← dflt "specialCases" #[] (map str)
    let cases ← cases.mapM fun (k, v) => do
      match Community.parse? k with
      | some c => pure (c, v)
      | none => DecodeM.malformed s!"bad community key {k.quote}"
    pure (.specialCases fallback cases)]

def communitySetRendering : Decoder CommunitySetRendering := byClass "community set rendering" [
  comm "TypesFirstAscendingSpaceSeparated"
    (CommunitySetRendering.mk <$> req "communityRendering" communityRendering)]

def communityExpr : Decoder CommunityExpr := byClass "community expression" [
  comm "StandardCommunityHighLowExprs"
    (.standardHighLow <$> req "highExpr" intExpr <*> req "lowExpr" intExpr),
  comm "RouteTargetExtendedCommunityExpr"
    (.routeTarget <$> req "gaExpr" longExpr <*> req "laExpr" longExpr)]

mutual

partial def communityMatchExpr : Decoder CommunityMatchExpr := byClass "community match" [
  comm "CommunityIs" (.is <$> req "community" community),
  comm "CommunityIn" (.inSet <$> req "communitySetExpr" communitySetExpr),
  comm "CommunityMatchAll" (.matchAll <$> dflt "exprs" #[] (array communityMatchExpr)),
  comm "CommunityMatchAny" (.matchAny <$> dflt "exprs" #[] (array communityMatchExpr)),
  comm "CommunityNot" (.not <$> req "expr" communityMatchExpr),
  comm "CommunityMatchRegex"
    (.regex <$> req "communityRendering" communityRendering <*> req "regex" str),
  comm "CommunityMatchExprReference" (.reference <$> req "name" str),
  comm "AllStandardCommunities" (pure .allStandard),
  comm "AllExtendedCommunities" (pure .allExtended),
  comm "AllLargeCommunities" (pure .allLarge),
  comm "CommunityAcl" (.acl <$> dflt "lines" #[] (array (object do
    ignore "class"
    pure (← req "action" lineAction, ← req "communityMatchExpr" communityMatchExpr)))),
  comm "StandardCommunityHighMatch" (.standardHigh <$> req "expr" intMatchExpr),
  comm "StandardCommunityLowMatch" (.standardLow <$> req "expr" intMatchExpr),
  comm "RouteTargetExtendedCommunities" (pure .routeTargetExtended),
  comm "SiteOfOriginExtendedCommunities" (pure .siteOfOriginExtended),
  comm "VpnDistinguisherExtendedCommunities" (pure .vpnDistinguisherExtended),
  comm "OpaqueExtendedCommunities"
    (.opaqueExtended <$> req "transitive" bool <*> req "subType" nat),
  comm "ExtendedCommunityGlobalAdministratorMatch"
    (.extendedGlobalAdmin <$> req "expr" longMatchExpr),
  comm "ExtendedCommunityGlobalAdministratorHighMatch"
    (.extendedGlobalAdminHigh <$> req "expr" intMatchExpr),
  comm "ExtendedCommunityGlobalAdministratorLowMatch"
    (.extendedGlobalAdminLow <$> req "expr" intMatchExpr),
  comm "ExtendedCommunityLocalAdministratorMatch"
    (.extendedLocalAdmin <$> req "expr" longMatchExpr)]

partial def communitySetExpr : Decoder CommunitySetExpr := byClass "community set expression" [
  comm "InputCommunities" (pure .input),
  comm "LiteralCommunitySet" (.literal <$> dflt "communitySet" #[] (array community)),
  comm "CommunitySetUnion" (.union <$> dflt "exprs" #[] (array communitySetExpr)),
  comm "CommunitySetDifference" (.difference <$> req "initial" communitySetExpr
    <*> req "removalCriterion" communityMatchExpr),
  comm "CommunitySetExprReference" (.exprReference <$> req "name" str),
  comm "CommunitySetReference" (.setReference <$> req "name" str),
  comm "CommunityExprsSet" (.ofExprs <$> dflt "exprs" #[] (array communityExpr))]

end

partial def communitySetMatchExpr : Decoder CommunitySetMatchExpr :=
  byClass "community set match" [
  comm "HasCommunity" (.hasCommunity <$> req "expr" communityMatchExpr),
  comm "HasSize" (.hasSize <$> req "expr" intMatchExpr),
  comm "CommunitySetMatchAll" (.matchAll <$> dflt "exprs" #[] (array communitySetMatchExpr)),
  comm "CommunitySetMatchAny" (.matchAny <$> dflt "exprs" #[] (array communitySetMatchExpr)),
  comm "CommunitySetNot" (.not <$> req "expr" communitySetMatchExpr),
  comm "CommunitySetMatchRegex"
    (.regex <$> req "communityRendering" communitySetRendering <*> req "regex" str),
  comm "CommunitySetMatchExprReference" (.reference <$> req "name" str),
  comm "CommunitySetAcl" (.acl <$> dflt "lines" #[] (array (object do
    ignore "class"
    pure (← req "action" lineAction, ← req "communitySetMatchExpr" communitySetMatchExpr))))]

/-! ## AS paths -/

partial def asPathExpr : Decoder AsPathExpr := byClass "AS-path expression" [
  asp "InputAsPath" (pure .input),
  asp "DedupedAsPath" (.deduped <$> req "asPathExpr" asPathExpr),
  asp "AsPathExprReference" (.reference <$> req "name" str)]

def intComparison : Decoder (IntComparator × IntExpr) := byClass "int comparison" [
  expr "IntComparison" (Prod.mk <$> req "comparator" intComparator <*> req "expr" intExpr)]

partial def asPathMatchExpr : Decoder AsPathMatchExpr := byClass "AS-path match" [
  asp "AsPathMatchRegex" (.regex <$> req "regex" str),
  asp "AsPathMatchAny" (.any <$> dflt "disjuncts" #[] (array asPathMatchExpr)),
  asp "HasAsPathLength" (do
    let (c, n) ← req "comparison" intComparison
    pure (.hasLength c n)),
  asp "AsPathMatchExprReference" (.reference <$> req "name" str)]

def asPathAccessList : Decoder AsPathAccessList := object do
  pure {
    name := ← req "name" str
    lines := ← dflt "lines" #[] (array (object do
      pure { action := ← req "action" lineAction, regex := ← req "regex" str })) }

def asPathSetName : Decoder String := byClass "AS-path set" [
  expr "NamedAsPathSet" (req "name" str)]

/-! ## Statements and boolean expressions -/

mutual

partial def booleanExpr : Decoder BooleanExpr := byClass "boolean expression" [
  expr "BooleanExprs$StaticBooleanExpr"
    (.static <$> req "type" (enum "static boolean" StaticBooleanType.names)),
  expr "CallExpr" (.call <$> req "calledPolicyName" str),
  expr "Conjunction" (.conjunction <$> dflt "conjuncts" #[] (array booleanExpr)),
  expr "Disjunction" (.disjunction <$> dflt "disjuncts" #[] (array booleanExpr)),
  expr "ConjunctionChain" (.conjunctionChain <$> dflt "subroutines" #[] (array booleanExpr)),
  expr "FirstMatchChain" (.firstMatchChain <$> dflt "subroutines" #[] (array booleanExpr)),
  expr "Not" (.not <$> req "expr" booleanExpr),
  expr "WithEnvironmentExpr" (.withEnvironment <$> req "expr" booleanExpr
    <*> dflt "preStatements" #[] (array statement)
    <*> dflt "postStatements" #[] (array statement)
    <*> dflt "postTrueStatements" #[] (array statement)),
  expr "MatchPrefixSet" (do
    req "prefix" (byClass "prefix expression" [expr "DestinationNetwork" (pure ())])
    .matchPrefixSet <$> req "prefixSet" prefixSetExpr),
  expr "MatchProtocol" (.matchProtocol <$> dflt "protocols" #[] (array routingProtocol)),
  expr "MatchSourceProtocol"
    (.matchSourceProtocol <$> dflt "protocols" #[] (array routingProtocol)),
  expr "MatchTag" (.matchTag <$> req "cmp" intComparator <*> req "tag" longExpr),
  expr "MatchMetric" (.matchMetric <$> req "comparator" intComparator <*> req "metric" longExpr),
  expr "MatchLocalPreference"
    (.matchLocalPreference <$> req "comparator" intComparator <*> req "metric" longExpr),
  expr "MatchBgpSessionType" (.matchBgpSessionType <$> dflt "types" #[] (array bgpSessionType)),
  commented <| comm "MatchCommunities" (.matchCommunities <$> req "communitySetExpr" communitySetExpr
    <*> req "communitySetMatchExpr" communitySetMatchExpr),
  commented <| asp "MatchAsPath"
    (.matchAsPath <$> req "asPathExpr" asPathExpr <*> req "asPathMatchExpr" asPathMatchExpr),
  expr "LegacyMatchAsPath" (.legacyMatchAsPath <$> req "expr" asPathSetName),
  expr "MatchInterface" (.matchInterface <$> dflt "interfaces" #[] (array str)),
  expr "MatchPeerAddress" (.matchPeerAddress <$> dflt "peers" #[] (array ip)),
  expr "MatchProcessAsn" (.matchProcessAsn <$> req "asn" nat),
  expr "MatchClusterListLength"
    (.matchClusterListLength <$> req "comparator" intComparator <*> req "rhs" intExpr),
  expr "MatchIpv4" (pure .matchIpv4),
  expr "RouteIsClassful" (pure .routeIsClassful)]

partial def statement : Decoder Statement := byClass "statement" [
  stmt "Statements$StaticStatement"
    (.static <$> req "type" (enum "static statement" StaticStatementType.names)),
  stmt "If" (.ifThen <$> req "guard" booleanExpr
    <*> dflt "trueStatements" #[] (array statement)
    <*> dflt "falseStatements" #[] (array statement)),
  stmt "CallStatement" (.call <$> req "calledPolicyName" str),
  stmt "Comment" (do ignore "text"; pure .comment),
  stmt "SetDefaultPolicy" (.setDefaultPolicy <$> req "defaultPolicy" str),
  stmt "SetLocalPreference" (.setLocalPreference <$> req "localPreference" longExpr),
  stmt "SetMetric" (.setMetric <$> req "metric" longExpr),
  stmt "SetTag" (.setTag <$> req "tag" longExpr),
  stmt "SetDefaultTag" (.setDefaultTag <$> req "tag" longExpr),
  stmt "SetWeight" (.setWeight <$> req "weight" intExpr),
  stmt "SetOrigin" (.setOrigin <$> req "originType" originExpr),
  stmt "SetNextHop" (.setNextHop <$> req "expr" nextHopExpr),
  stmt "SetAdministrativeCost" (.setAdministrativeCost <$> req "admin" adminCostExpr),
  stmt "SetOspfMetricType"
    (.setOspfMetricType <$> req "metricType" ospfMetricType),
  commented <| comm "SetCommunities" (.setCommunities <$> req "communitySetExpr" communitySetExpr),
  stmt "PrependAsPath" (.prependAsPath <$> req "expr" asPathListExpr),
  stmt "ExcludeAsPath" (.excludeAsPath <$> req "expr" asPathListExpr),
  stmt "TraceableStatement" (do
    ignore "traceElement"
    .traceable <$> dflt "innerStatements" #[] (array statement))]

end

def routingPolicy : Decoder RoutingPolicy := object do
  pure { name := ← req "name" str, statements := ← dflt "statements" #[] (array statement) }

def routeFilterList : Decoder RouteFilterList := object do
  ignore "vendorStructureId"
  pure {
    name := ← req "name" str
    lines := ← dflt "lines" #[] (array (object do
      pure {
        action := ← req "action" lineAction
        ipWildcard := ← req "ipWildcard" ipWildcard
        lengthRange := ← req "lengthRange" subRange })) }

end LeanBatfish.Decode
