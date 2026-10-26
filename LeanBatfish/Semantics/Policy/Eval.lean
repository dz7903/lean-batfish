import LeanBatfish.Semantics.Policy.Match

/-!
# Evaluating routing policies

A routing policy runs against an input route (the *original* route) and writes the
attributes of an *output* route. It answers whether the route is accepted. This follows
Batfish's `RoutingPolicy.process` and the `execute`/`evaluate` methods of its statements
and expressions.

Three details of Batfish's evaluation are visible in the result and modeled here:

* **Which attributes are read.** Juniper policies read the attributes of the output route,
  so that an earlier `then` clause affects later matches; other vendors read the original
  route (`Environment.useOutputAttributes`). Juniper policy chains can also read and write
  a separate set of *intermediate* BGP attributes.
* **Which attributes can be written.** The output route has a kind (BGP, OSPF external,
  or other), and statements that set attributes the kind lacks do nothing.
* **Control flow.** Statements return a `Result` with flags for exit, return and fall
  through, which `If`, calls and policy chains interpret as in Batfish.
-/

namespace LeanBatfish.Policy

/-- The direction a policy is applied in (`Environment.Direction`). -/
inductive Direction
  | «in»
  | out
  deriving DecidableEq, Inhabited, Repr

/-- The BGP session a policy runs for (`BgpSessionProperties`), seen from this router. -/
structure Session where
  localAs : Nat
  remoteAs : Nat
  localIp : Ip
  remoteIp : Ip
  isEbgp : Bool
  deriving Inhabited, Repr

/-- The kind of route a policy writes: Batfish's output route builder class. -/
inductive OutputKind
  | bgp
  | ospfExternal
  /-- A generated (aggregate) route: it has BGP-like attributes (AS path, communities,
  local preference, origin, weight) but is not a BGP route. -/
  | generated
  | other
  deriving DecidableEq, Inhabited, Repr

/-- Whether the output route has an AS path, communities, local preference, origin type and
weight that policies can read and write. -/
def OutputKind.hasBgpAttributes : OutputKind → Bool
  | .bgp | .generated => true
  | _ => false

/-- What stays fixed while a policy runs. -/
structure Context where
  config : Configuration
  original : Route
  direction : Direction := .out
  useOutputAttributes : Bool
  session : Option Session := none
  outputKind : OutputKind
  deriving Inhabited

/-- What a policy changes as it runs: the output route and the flags of Batfish's
`Environment`. -/
structure State where
  output : Route
  /-- The intermediate BGP attributes, once created by `SetWriteIntermediateBgpAttributes`. -/
  intermediate : Option Route := none
  defaultAction : Bool := false
  localDefaultAction : Bool := false
  defaultPolicy : Option String := none
  callExprContext : Bool := false
  callStatementContext : Bool := false
  readFromIntermediate : Bool := false
  writeToIntermediate : Bool := false
  tagExplicitlySet : Bool := false
  suppressed : Option Bool := none
  /-- Set when a policy refers to an undefined policy or route-filter list. -/
  error : Bool := false
  deriving Inhabited

/-- The outcome of a statement or boolean expression (`routing_policy.Result`). -/
structure Result where
  value : Bool := false
  exit : Bool := false
  fallThrough : Bool := false
  ret : Bool := false
  deriving DecidableEq, Inhabited, Repr

abbrev PolicyM := ReaderT Context (StateT State EvalM)

def liftEval (x : EvalM α) : PolicyM α := monadLift x

/-! ## Reading attributes -/

/-- The intermediate attributes. Batfish only reads them after creating them. -/
def intermediate : PolicyM Route := do
  match (← get).intermediate with
  | some r => pure r
  | none => throw "intermediate BGP attributes read before they were set"

def readTag : PolicyM Int := do
  if (← read).useOutputAttributes then return (← get).output.tag
  if (← get).readFromIntermediate then return (← intermediate).tag
  return (← read).original.tag

def readMetric : PolicyM Nat := do
  if (← read).useOutputAttributes then return (← get).output.metric
  if (← get).readFromIntermediate then return (← intermediate).metric
  return (← read).original.metric

/-- The local preference to match on, or `none` if the route has none. -/
def readLocalPreference : PolicyM (Option Nat) := do
  let ctx ← read
  if ctx.useOutputAttributes && ctx.outputKind == .bgp then
    return some (← get).output.localPreference
  if (← get).readFromIntermediate then return some (← intermediate).localPreference
  return if ctx.original.isBgpRoute then ctx.original.bgp.map (·.localPreference) else none

/-- The communities to match on (`CommunityContext.fromEnvironment`). -/
def readCommunities : PolicyM CommunitySet := do
  let ctx ← read
  if ctx.useOutputAttributes && ctx.outputKind.hasBgpAttributes then
    return (← get).output.communities
  if (← get).readFromIntermediate then return (← intermediate).communities
  return ctx.original.communities

/-- The AS path to match on (`AsPathContext.fromEnvironment`), if the route has one. -/
def readAsPath : PolicyM (Option AsPath) := do
  let ctx ← read
  if ctx.useOutputAttributes && ctx.outputKind.hasBgpAttributes then
    return some (← get).output.asPath
  if (← get).readFromIntermediate then return some (← intermediate).asPath
  return ctx.original.bgp.map (·.asPath)

/-! ## Writing attributes -/

/-- Apply `f` to the output route, and to the intermediate attributes when writing to
them. -/
def write (f : Route → Route) : PolicyM Unit :=
  modify fun s => { s with
    output := f s.output
    intermediate := if s.writeToIntermediate then s.intermediate.map f else s.intermediate }

/-- Like `write`, but only for output routes with BGP attributes. -/
def writeBgp (f : BgpAttrs → BgpAttrs) : PolicyM Unit := do
  if (← read).outputKind.hasBgpAttributes then write (·.modifyBgp f)

/-! ## Value expressions -/

def session : PolicyM Session := do
  match (← read).session with
  | some s => pure s
  | none => throw "expected BGP session properties"

/-- The first AS of a path; Batfish takes the lowest AS of the first segment. -/
def firstAs? (p : AsPath) : Option Nat := do
  let s ← p[0]?
  s.asns[0]?

def evalAs : AsExpr → PolicyM Nat
  | .explicit asn => pure asn
  | .localAs => do return (← session).localAs
  | .remoteAs => do return (← session).remoteAs
  | .autoAs => do
    if (← read).direction == .out then return (← session).localAs
    let path ← match ← readAsPath with
      | some p => pure p
      | none => throw "AutoAs on a route without an AS path"
    match firstAs? path with
    | some asn => pure asn
    | none => return (← session).remoteAs
  | .lastAs => do
    let path ← match ← readAsPath with
      | some p => pure p
      | none => throw "LastAs on a route without an AS path"
    match firstAs? path with
    | some asn => pure asn
    | none => throw "LastAs on an empty AS path"

def evalLong : LongExpr → PolicyM Int
  | .literal v => pure v
  | .incrementMetric addend => do
    return min ((← read).original.metric + addend) (2 ^ 32 - 1)
  | .decrementMetric subtrahend => do
    return ((← read).original.metric : Int) - subtrahend |>.toNat
  | .incrementLocalPreference addend => do
    return min ((← oldLocalPreference) + addend) BgpAttrs.maxLocalPreference
  | .decrementLocalPreference subtrahend => do
    return ((← oldLocalPreference : Int) - subtrahend).toNat
  | .asnValue e => do return (← evalAs e)
  | .uint32HighLow .. => throw "Uint32HighLowExpr cannot be evaluated"
where
  oldLocalPreference : PolicyM Nat := do
    if (← get).readFromIntermediate then return (← intermediate).localPreference
    return (← read).original.localPreference

def evalAsList : AsPathListExpr → PolicyM (Array Nat)
  | .literal es => es.mapM evalAs
  | .multiplied e n => do
    let asn ← evalAs e
    return Array.replicate n.toNat asn

/-- The next hop a `SetNextHop` writes, or `none` to leave it unchanged. -/
def evalNextHop : NextHopExpr → PolicyM (Option NextHop)
  | .discard => pure (some .discard)
  | .ip ips =>
    if h : ips.size = 1 then pure (some (.ip ips[0]))
    else throw "setting more than one next-hop IP is not supported"
  | .self => do return (← read).session.map (.ip ·.localIp)
  | .unchanged => do
    let ctx ← read
    if !ctx.original.isBgpRoute then return none
    match ctx.session with
    | some s => if s.isEbgp then return ctx.original.nextHopIp?.map .ip else return none
    | none => return none
  | .bgpPeerAddress => do return some (.ip (← session).remoteIp)

def evalAdmin : AdminCostExpr → PolicyM Nat
  | .literal v => pure v
  | .increment addend max => do
    let old := (← read).original.admin
    return if old + addend > max then max else old + addend
  | .decrement subtrahend min => do
    let old := (← read).original.admin
    return if old < min + subtrahend then min else old - subtrahend

/-- Batfish stores BGP local preference, MED and weight in 32 bits. -/
def toU32 (v : Int) : Nat := (v % 2 ^ 32).toNat

def communityContext : PolicyM CommunityContext := do
  return { config := (← read).config, input := ← readCommunities }

/-! ## Statements and boolean expressions -/

/-- `SetWriteIntermediateBgpAttributes`: start writing to the intermediate attributes,
creating them from the original route's metric, tag, AS path and communities. -/
def startWritingIntermediate : PolicyM Unit := do
  let ctx ← read
  if ctx.outputKind != .bgp then return
  let s ← get
  let inter := s.intermediate.getD {
    network := ctx.original.network, nextHop := ctx.original.nextHop, protocol := .bgp,
    admin := 0, metric := ctx.original.metric, tag := ctx.original.tag,
    bgp := some { asPath := ctx.original.asPath, communities := ctx.original.communities,
                  localPreference := 0 } }
  set { s with writeToIntermediate := true, intermediate := some inter }

def staticStatement : StaticStatementType → PolicyM Result
  | .defaultAction => do return { exit := true, value := (← get).defaultAction }
  | .exitAccept => pure { exit := true, value := true }
  | .exitReject => pure { exit := true, value := false }
  | .fallThrough => pure { ret := true, fallThrough := true }
  | .return => pure { ret := true }
  | .returnFalse => pure { ret := true, value := false }
  | .returnTrue => pure { ret := true, value := true }
  | .returnLocalDefaultAction => do return { ret := true, value := (← get).localDefaultAction }
  | .removePrivateAs => do
    let strip (p : AsPath) : AsPath :=
      (p.map fun s => { asns := s.asns.filter (!isPrivateAs ·) }).filter (!·.asns.isEmpty)
    if (← read).outputKind.hasBgpAttributes then
      modify fun s => { s with
        output := s.output.modifyBgp fun b => { b with asPath := strip b.asPath }
        intermediate := if s.writeToIntermediate then
            s.intermediate.map (·.modifyBgp fun b => { b with asPath := strip b.asPath })
          else s.intermediate }
    return {}
  | .setDefaultActionAccept => do modify ({ · with defaultAction := true }); return {}
  | .setDefaultActionReject => do modify ({ · with defaultAction := false }); return {}
  | .setLocalDefaultActionAccept => do modify ({ · with localDefaultAction := true }); return {}
  | .setLocalDefaultActionReject => do modify ({ · with localDefaultAction := false }); return {}
  | .setReadIntermediateBgpAttributes => do
    if (← read).outputKind == .bgp then modify ({ · with readFromIntermediate := true })
    return {}
  | .setWriteIntermediateBgpAttributes => do startWritingIntermediate; return {}
  | .unsetWriteIntermediateBgpAttributes => do
    modify ({ · with writeToIntermediate := false }); return {}
  | .suppress => do modify ({ · with suppressed := some true }); return {}
  | .unsuppress => do modify ({ · with suppressed := some false }); return {}
where
  /-- `AsPath.isPrivateAs`. -/
  isPrivateAs (asn : Nat) : Bool :=
    (64512 ≤ asn && asn ≤ 65534) || (4200000000 ≤ asn && asn ≤ 4294967294)

/-- The network size of an address's class (`Ip.getClassNetworkSize`); `-1` for class D
and E addresses. -/
def classSize (ip : Ip) : Int :=
  let first := ip.bits >>> 24
  if first ≤ 127 then 8 else if first ≤ 191 then 16 else if first ≤ 223 then 24 else -1

def lookupPolicy (name : String) : PolicyM (Option RoutingPolicy) := do
  return (← read).config.routingPolicies.find? name

mutual

/-- Run statements in order, stopping at the first that exits or returns. -/
def execAll (fuel : Nat) (stmts : Array Statement) : PolicyM (Option Result) :=
  match fuel with
  | 0 => throw "routing policy evaluation nests too deeply"
  | fuel + 1 => do
    for st in stmts do
      let r ← exec fuel st
      if r.exit || r.ret then return some r
    return none

/-- `RoutingPolicy.call`: run a policy's statements; falling off the end yields the
default action. -/
def callPolicy (fuel : Nat) (p : RoutingPolicy) : PolicyM Result :=
  match fuel with
  | 0 => throw "routing policy evaluation nests too deeply"
  | fuel + 1 => do
    for st in p.statements do
      let r ← exec fuel st
      if r.exit then return r
      if r.ret then return { r with ret := false }
    return { fallThrough := true, value := (← get).defaultAction }

def exec (fuel : Nat) (st : Statement) : PolicyM Result :=
  match fuel with
  | 0 => throw "routing policy evaluation nests too deeply"
  | fuel + 1 =>
    match st with
    | .static t => staticStatement t
    | .ifThen guard ts fs => do
      let g ← eval fuel guard
      if g.exit then return g
      match ← execAll fuel (if g.value then ts else fs) with
      | some r => pure r
      | none => pure { fallThrough := true }
    | .call name => do
      match ← lookupPolicy name with
      | none => modify ({ · with error := true }); return { value := false }
      | some p =>
        let old := (← get).callStatementContext
        modify ({ · with callStatementContext := true })
        let r ← callPolicy fuel p
        modify ({ · with callStatementContext := old })
        return { r with ret := false }
    | .comment => pure {}
    | .setDefaultPolicy name => do modify ({ · with defaultPolicy := some name }); return {}
    | .setLocalPreference e => do
      let v ← evalLong e
      writeBgp ({ · with localPreference := toU32 v })
      return {}
    | .setMetric e => do
      let v ← evalLong e
      write ({ · with metric := v.toNat })
      return {}
    | .setTag e => do
      let v ← evalLong e
      write ({ · with tag := v })
      modify ({ · with tagExplicitlySet := true })
      return {}
    | .setDefaultTag e => do
      if !(← get).tagExplicitlySet then
        let v ← evalLong e
        write ({ · with tag := v })
      return {}
    | .setWeight w => do
      writeBgp ({ · with weight := toU32 w })
      return {}
    | .setOrigin o => do
      writeBgp ({ · with originType := o })
      return {}
    | .setNextHop e => do
      if (← read).outputKind == .bgp then
        if let some nh ← evalNextHop e then write ({ · with nextHop := nh })
      return {}
    | .setAdministrativeCost e => do
      let v ← evalAdmin e
      write ({ · with admin := v })
      return {}
    | .setOspfMetricType t => do
      if (← read).outputKind == .ospfExternal then
        modify fun s => { s with output := { s.output with ospfMetricType := some t } }
      return {}
    | .setCommunities e => do
      if (← read).outputKind.hasBgpAttributes then
        let cs ← liftEval ((e.eval (← communityContext) policyFuel))
        writeBgp ({ · with communities := cs })
      return {}
    | .prependAsPath e => do
      if (← read).outputKind.hasBgpAttributes then
        let asns ← evalAsList e
        let s ← get
        let base ← if s.readFromIntermediate then do pure (← intermediate).asPath
          else pure s.output.asPath
        let path := asns.map AsSet.single ++ base
        writeBgp ({ · with asPath := path })
      return {}
    | .excludeAsPath e => do
      if (← read).outputKind.hasBgpAttributes then
        let asns ← evalAsList e
        let strip (p : AsPath) : AsPath :=
          (p.map fun s => { asns := s.asns.filter (!asns.contains ·) }).filter
            (!·.asns.isEmpty)
        writeBgp fun b => { b with asPath := strip b.asPath }
      return {}
    | .traceable inner => do
      match ← execAll fuel inner with
      | some r => pure r
      | none => pure { fallThrough := true }

def eval (fuel : Nat) (e : BooleanExpr) : PolicyM Result :=
  match fuel with
  | 0 => throw "routing policy evaluation nests too deeply"
  | fuel + 1 =>
    match e with
    | .static t => do
      let s ← get
      return { value := match t with
        | .callExprContext => s.callExprContext
        | .callStatementContext => s.callStatementContext
        | .false => false
        | .true => true }
    | .call name => do
      match ← lookupPolicy name with
      | none => modify ({ · with error := true }); return { value := false }
      | some p =>
        let s ← get
        modify ({ · with callExprContext := true })
        let r ← callPolicy fuel p
        modify ({ · with callExprContext := s.callExprContext,
                         localDefaultAction := s.localDefaultAction })
        return { r with ret := false }
    | .conjunction es => do
      for c in es do
        let r ← eval fuel c
        if r.exit then return r
        if !r.value then return { r with ret := false }
      return { value := true }
    | .disjunction es => do
      for d in es do
        let r ← eval fuel d
        if r.exit then return r
        if r.value then return { r with ret := false }
      return { value := false }
    | .not e => do
      let r ← eval fuel e
      return if r.exit then r else { value := !r.value }
    | .conjunctionChain subs => do
      let mut last : Result := { fallThrough := true }
      for sub in subs do
        last ← eval fuel sub
        if last.exit then return last
        if !last.fallThrough && !last.value then return { last with ret := false }
      if !last.fallThrough then return { last with ret := false }
      callDefaultPolicy fuel
    | .firstMatchChain subs => do
      for sub in subs do
        let r ← eval fuel sub
        if r.exit then return r
        if !r.fallThrough then return { r with ret := false }
      callDefaultPolicy fuel
    | .withEnvironment e pre post postTrue => do
      for st in pre do discard <| exec fuel st
      let r ← eval fuel e
      for st in post do discard <| exec fuel st
      if r.value then
        for st in postTrue do discard <| exec fuel st
      return r
    | .matchPrefixSet ps => do
      let ctx ← read
      let p := ctx.original.network
      match ps with
      | .explicit space => return { value := space.containsPrefix p }
      | .named name =>
        match ctx.config.routeFilterLists.find? name with
        | some l => return { value := l.permits p }
        | none => modify ({ · with error := true }); return { value := false }
    | .matchProtocol ps => do return { value := ps.contains (← read).original.protocol }
    | .matchSourceProtocol ps => do
      let src := (← read).original.bgp.bind (·.srcProtocol)
      return { value := match src with | some p => ps.contains p | none => false }
    | .matchTag c e => do
      let lhs ← readTag
      return { value := c.apply lhs (← evalLong e) }
    | .matchMetric c e => do
      let lhs ← readMetric
      if lhs ≥ 2 ^ 31 then throw "metric does not fit in a Java int"
      return { value := c.apply lhs (← evalLong e) }
    | .matchLocalPreference c e => do
      match ← readLocalPreference with
      | some lp => return { value := c.apply lp (← evalLong e) }
      | none => return { value := false }
    | .matchBgpSessionType types => do
      match (← read).session with
      | none => return { value := false }
      | some s => return { value := types.any fun t =>
          if s.isEbgp then t != .ibgp && t != .ibgpUnnumbered
          else t == .ibgp || t == .ibgpUnnumbered }
    | .matchCommunities se me => do
      let ctx ← communityContext
      let set ← liftEval (se.eval ctx policyFuel)
      return { value := ← liftEval (me.eval ctx policyFuel set) }
    | .matchAsPath pe me => do
      match ← readAsPath with
      | none => return { value := false }
      | some input =>
        let config := (← read).config
        let p ← liftEval (pe.eval config input policyFuel)
        return { value := ← liftEval (me.eval config policyFuel p) }
    | .legacyMatchAsPath name => do
      let ctx ← read
      match ctx.config.asPathAccessLists.find? name with
      | none => modify ({ · with error := true }); return { value := false }
      | some l =>
        let s ← get
        let path ← if ctx.useOutputAttributes then
            pure (if ctx.outputKind.hasBgpAttributes then s.output.asPath else #[])
          else if s.readFromIntermediate then do pure (← intermediate).asPath
          else pure ctx.original.asPath
        return { value := ← liftEval (l.permits path) }
    | .matchInterface names => do
      let ctx ← read
      let s ← get
      let iface := if ctx.useOutputAttributes then s.output.nextHopInterface
        else ctx.original.nextHopInterface
      return { value := iface != NextHop.unsetInterfaceName && names.contains iface }
    | .matchPeerAddress peers => do
      match (← read).session with
      | none => return { value := false }
      | some s => return { value := peers.contains s.remoteIp }
    | .matchProcessAsn _ => return { value := false }
    | .matchClusterListLength c n => do
      let ctx ← read
      let s ← get
      let len := if ctx.useOutputAttributes && ctx.outputKind == .bgp then
          (s.output.bgp.map (·.clusterList.size)).getD 0
        else (ctx.original.bgp.map (·.clusterList.size)).getD 0
      return { value := c.apply len n }
    | .matchIpv4 => return { value := true }
    | .routeIsClassful => do
      let p := (← read).original.network
      return { value := (p.len.val : Int) ≤ classSize p.addr }

/-- Call the policy set by `SetDefaultPolicy`, as policy chains do when no policy in the
chain decides. -/
def callDefaultPolicy (fuel : Nat) : PolicyM Result :=
  match fuel with
  | 0 => throw "routing policy evaluation nests too deeply"
  | fuel + 1 => do
    match (← get).defaultPolicy with
    | none => throw "default policy is not set"
    | some name => do
      let r ← eval fuel (.call name)
      return { r with ret := false }

end

/-- Juniper policies read the output route's attributes
(`Environment.useOutputAttributesFor`). -/
def useOutputAttributesFor (c : Configuration) : Bool :=
  c.configurationFormat ∈ ["JUNIPER", "JUNIPER_SWITCH", "FLAT_JUNIPER"]

/-- The outcome of running a policy: whether it accepts the route, and the output route.
-/
structure Outcome where
  accepted : Bool
  output : Route
  deriving Inhabited

/-- `RoutingPolicy.process`: run `policy` on the context's original route, starting from
the output route `output`. The route is accepted if the policy's result is true and it
did not suppress the route. -/
def process (ctx : Context) (policy : RoutingPolicy) (output : Route) : EvalM Outcome := do
  let (r, s) ← (callPolicy policyFuel policy).run ctx |>.run { output }
  pure { accepted := r.value && s.suppressed != some true, output := s.output }

/-- `RoutingPolicy.processReadOnly`: whether `policy` accepts `route`, reading the
route's own attributes and discarding any writes. Batfish uses this for resolution
policies and FIB export policies. -/
def accepts (config : Configuration) (policy : RoutingPolicy) (route : Route) : EvalM Bool := do
  let ctx : Context :=
    { config := config, original := route, useOutputAttributes := false, outputKind := .bgp }
  let attrs : BgpAttrs := { localPreference := 0 }
  let output : Route :=
    { network := route.network, nextHop := route.nextHop, protocol := .bgp, admin := 0,
      bgp := some attrs }
  return (← process ctx policy output).accepted

end LeanBatfish.Policy
