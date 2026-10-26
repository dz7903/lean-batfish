import LeanBatfish.Data.Regex
import LeanBatfish.IR.Configuration
import LeanBatfish.Semantics.Route

/-!
# Matching prefixes, communities and AS paths

The predicates routing policies use on route attributes, as pure functions: prefix
spaces and route-filter lists, the community language of `routing_policy.communities`,
and the AS-path language of `routing_policy.as_path` and AS-path access lists.

Named expressions are looked up in the configuration. Lookups can in principle refer to
each other in a cycle, so evaluation takes a `fuel` bound and fails when it runs out;
Batfish would overflow its stack instead.
-/

namespace LeanBatfish

/-- Evaluation of routing policies fails with a message when Batfish itself would throw,
or when a regex is outside the supported syntax. -/
abbrev EvalM := Except String

/-- The default recursion bound for policy evaluation. -/
def policyFuel : Nat := 256

/-! ## Prefixes -/

namespace PrefixRange

/-- Whether `p` is in the range: it lies under the range's prefix, and its length is in
the length range (`PrefixSpace.containsPrefix`). -/
def containsPrefix (r : PrefixRange) (p : Prefix) : Bool :=
  r.prefix.containsPrefix p && r.lengthRange.contains p.len

end PrefixRange

def PrefixSpace.containsPrefix (s : PrefixSpace) (p : Prefix) : Bool :=
  s.any (·.containsPrefix p)

/-- The first line whose wildcard contains the prefix's address and whose length range
contains its length decides; no match denies (`RouteFilterList.permits`). -/
def RouteFilterList.permits (l : RouteFilterList) (p : Prefix) : Bool :=
  match l.lines.find? (fun line => line.ipWildcard.containsIp p.addr &&
      line.lengthRange.contains p.len) with
  | some line => line.action == .permit
  | none => false

/-! ## Numbers -/

def IntMatchExpr.matches : IntMatchExpr → Int → Bool
  | .comparison c e, v => c.apply v e
  | .all es, v => es.attach.all fun ⟨e, _⟩ => e.matches v

/-! ## Communities -/

namespace Community

/-- The global administrator of an extended community; opaque communities have none
(`ExtendedCommunity.getGlobalAdministrator` throws). -/
def globalAdministrator? : Community → Option Nat
  | .extended t _ v =>
    if t == 0x03 || t == 0x43 then none
    else if t == 0x00 || t == 0x40 then some (v / 2 ^ 32) else some (v / 2 ^ 16)
  | _ => none

def localAdministrator? : Community → Option Nat
  | .extended t _ v =>
    if t == 0x03 || t == 0x43 then none
    else if t == 0x00 || t == 0x40 then some (v % 2 ^ 32) else some (v % 2 ^ 16)
  | _ => none

def isRouteTarget : Community → Bool
  | .extended t s _ => (t == 0 || t == 1 || t == 2) && s == 2
  | _ => false

def isRouteOrigin : Community → Bool
  | .extended t s _ => (t == 0 || t == 1 || t == 2) && s == 3
  | _ => false

def isVpnDistinguisher : Community → Bool
  | .extended t s _ => (t == 0 || t == 1) && s == 0x10
  | _ => false

/-- Whether a community is transitive. Extended communities are transitive unless bit
`0x40` of the type is set; standard and large communities always are. -/
def isTransitive : Community → Bool
  | .extended t _ _ => t &&& 0x40 == 0
  | _ => true

/-- The string `CommunityMatchRegex` matches against (`CommunityToRegexInputString`). -/
def regexInput (r : CommunityRendering) (c : Community) : String :=
  match r with
  | .colonSeparated =>
    match c with
    | .standard _ => c.toString
    | .extended .. => ""
    | .large a b c => s!"{a}:{b}:{c}"
  | .integerValue => toString c.toInt
  | .specialCases fallback cases =>
    match cases.find? (·.1 == c) with
    | some (_, s) => s
    | none =>
      match fallback with
      | .colonSeparated => regexInput .colonSeparated c
      | .integerValue => regexInput .integerValue c
      | .specialCases .. => regexInput .colonSeparated c

/-- Standard first, then extended, then large (`TYPES_FIRST_ASCENDING_COMPARATOR`). -/
def typePriority : Community → Nat
  | .standard _ => 0
  | .extended .. => 1
  | .large .. => 2

end Community

/-- The string `CommunitySetMatchRegex` matches against: the communities ordered by type
and then value, rendered and joined by spaces. -/
def CommunitySet.regexInput (r : CommunitySetRendering) (s : CommunitySet) : String :=
  let sorted := s.toArray.qsort fun a b =>
    a.typePriority < b.typePriority || (a.typePriority == b.typePriority && a.toInt < b.toInt)
  " ".intercalate (sorted.toList.map (Community.regexInput r.rendering))

def regexFind (regex : String) (input : String) : EvalM Bool := do
  match Regex.parse regex with
  | .ok r => pure (r.find input)
  | .error e => throw s!"regex {regex.quote}: {e}"

def LongMatchExpr.matches : LongMatchExpr → Int → EvalM Bool
  | .comparison c (.literal n), v => pure (c.apply v n)
  | .comparison _ _, _ => throw "only literal values are supported in long match expressions"
  | .all es, v => es.attach.allM fun ⟨e, _⟩ => e.matches v

/-- What community expressions read: the configuration's named expressions and the input
community set. -/
structure CommunityContext where
  config : Configuration
  input : CommunitySet

def CommunityExpr.eval : CommunityExpr → EvalM Community
  | .standardHighLow hi lo =>
    if 0 ≤ hi && hi < 65536 && 0 ≤ lo && lo < 65536 then
      pure (.standard (UInt32.ofNat (hi.toNat * 65536 + lo.toNat)))
    else throw "standard community half out of range"
  | .routeTarget (.literal ga) (.literal la) =>
    if 0 ≤ ga && ga < 2 ^ 32 && 0 ≤ la && la < 2 ^ 16 then
      -- `ExtendedCommunity.target`: type 0x02 (4-byte AS) unless both halves are small.
      if ga < 2 ^ 16 then pure (.extended 0x00 0x02 (ga.toNat * 2 ^ 32 + la.toNat))
      else pure (.extended 0x02 0x02 (ga.toNat * 2 ^ 16 + la.toNat))
    else throw "route-target community value out of range"
  | .routeTarget .. => throw "only literal route-target values are supported"

mutual

def CommunityMatchExpr.eval (ctx : CommunityContext) (fuel : Nat) (e : CommunityMatchExpr)
    (c : Community) : EvalM Bool :=
  match fuel with
  | 0 => throw "community expressions nest too deeply"
  | fuel + 1 =>
    match e with
    | .is c' => pure (c == c')
    | .inSet s => do return (← s.eval ctx fuel).contains c
    | .matchAll es => es.allM fun e => e.eval ctx fuel c
    | .matchAny es => es.anyM fun e => e.eval ctx fuel c
    | .not e => do return !(← e.eval ctx fuel c)
    | .regex r re => regexFind re (c.regexInput r)
    | .reference name =>
      match ctx.config.communityMatchExprs.find? name with
      | some e => e.eval ctx fuel c
      | none => throw s!"undefined community match expression {name}"
    | .allStandard => pure c.isStandard
    | .allExtended => pure c.isExtended
    | .allLarge => pure c.isLarge
    | .acl lines => do
      for (action, e) in lines do
        if ← e.eval ctx fuel c then return action == .permit
      return false
    | .standardHigh m =>
      match c with
      | .standard v => pure (m.matches (v.toNat / 65536))
      | _ => pure false
    | .standardLow m =>
      match c with
      | .standard v => pure (m.matches (v.toNat % 65536))
      | _ => pure false
    | .routeTargetExtended => pure c.isRouteTarget
    | .siteOfOriginExtended => pure c.isRouteOrigin
    | .vpnDistinguisherExtended => pure c.isVpnDistinguisher
    | .opaqueExtended transitive subType =>
      match c with
      | .extended t s _ => pure ((t == 0x03 || t == 0x43) && transitive == c.isTransitive &&
          s == subType)
      | _ => pure false
    | .extendedGlobalAdmin m => adminMatch c.isExtended c.globalAdministrator? (m.matches ·)
    | .extendedGlobalAdminHigh m =>
      adminMatch c.isExtended c.globalAdministrator? fun ga => pure (m.matches (ga / 65536))
    | .extendedGlobalAdminLow m =>
      adminMatch c.isExtended c.globalAdministrator? fun ga => pure (m.matches (ga % 65536))
    | .extendedLocalAdmin m => adminMatch c.isExtended c.localAdministrator? (m.matches ·)
where
  /-- Non-extended communities do not match; opaque ones make Batfish throw. -/
  adminMatch (isExtended : Bool) (value : Option Nat) (f : Int → EvalM Bool) : EvalM Bool :=
    if !isExtended then pure false
    else match value with
      | some v => f v
      | none => throw "opaque extended community has no administrator fields"

def CommunitySetExpr.eval (ctx : CommunityContext) (fuel : Nat) (e : CommunitySetExpr) :
    EvalM CommunitySet :=
  match fuel with
  | 0 => throw "community expressions nest too deeply"
  | fuel + 1 =>
    match e with
    | .input => pure ctx.input
    | .literal cs => pure (.ofArray cs)
    | .union es => do
      let sets ← es.mapM (·.eval ctx fuel)
      pure (.ofArray (sets.foldl (· ++ ·.toArray) #[]))
    | .difference initial criterion => do
      let s ← initial.eval ctx fuel
      let kept ← s.toArray.filterM fun c => do return !(← criterion.eval ctx fuel c)
      pure ⟨kept⟩
    | .exprReference name =>
      match ctx.config.communitySetExprs.find? name with
      | some e => e.eval ctx fuel
      | none => throw s!"undefined community set expression {name}"
    | .setReference name =>
      match ctx.config.communitySets.find? name with
      | some cs => pure (.ofArray cs)
      | none => throw s!"undefined community set {name}"
    | .ofExprs es => do return .ofArray (← es.mapM (·.eval))

end

def CommunitySetMatchExpr.eval (ctx : CommunityContext) (fuel : Nat) (e : CommunitySetMatchExpr)
    (s : CommunitySet) : EvalM Bool :=
  match fuel with
  | 0 => throw "community expressions nest too deeply"
  | fuel + 1 =>
    match e with
    | .hasCommunity m => s.toArray.anyM fun c => m.eval ctx fuel c
    | .hasSize m => pure (m.matches s.size)
    | .matchAll es => es.allM fun e => e.eval ctx fuel s
    | .matchAny es => es.anyM fun e => e.eval ctx fuel s
    | .not e => do return !(← e.eval ctx fuel s)
    | .regex r re => regexFind re (s.regexInput r)
    | .reference name =>
      match ctx.config.communitySetMatchExprs.find? name with
      | some e => e.eval ctx fuel s
      | none => throw s!"undefined community set match expression {name}"
    | .acl lines => do
      for (action, e) in lines do
        if ← e.eval ctx fuel s then return action == .permit
      return false

/-! ## AS paths -/

def AsPathExpr.eval (config : Configuration) (input : AsPath) (fuel : Nat) :
    AsPathExpr → EvalM AsPath
  | .input => pure input
  | .deduped e => match fuel with
    | 0 => throw "AS-path expressions nest too deeply"
    | fuel + 1 => do
      let p ← e.eval config input fuel
      pure (p.foldl (fun acc s => if acc.back? == some s then acc else acc.push s) #[])
  | .reference name => match fuel with
    | 0 => throw "AS-path expressions nest too deeply"
    | fuel + 1 =>
      match config.asPathExprs.find? name with
      | some e => e.eval config input fuel
      | none => throw s!"undefined AS-path expression {name}"

def AsPathMatchExpr.eval (config : Configuration) (fuel : Nat) (e : AsPathMatchExpr)
    (p : AsPath) : EvalM Bool :=
  match fuel with
  | 0 => throw "AS-path expressions nest too deeply"
  | fuel + 1 =>
    match e with
    | .regex r => regexFind r p.render
    | .any es => es.anyM fun e => e.eval config fuel p
    | .hasLength c n => pure (c.apply p.length n)
    | .reference name =>
      match config.asPathMatchExprs.find? name with
      | some e => e.eval config fuel p
      | none => throw s!"undefined AS-path match expression {name}"

/-- The first line whose regex is found in the rendered path decides; no match denies
(`AsPathAccessList.permits`). -/
def AsPathAccessList.permits (l : AsPathAccessList) (p : AsPath) : EvalM Bool := do
  let s := p.render
  for line in l.lines do
    if ← regexFind line.regex s then return line.action == .permit
  return false

end LeanBatfish
