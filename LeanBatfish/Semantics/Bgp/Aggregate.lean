import Std.Data.HashMap
import LeanBatfish.Semantics.Routing.Rib
import LeanBatfish.Semantics.Policy.Eval

/-!
# BGP aggregates

A BGP process activates an aggregate (Cisco `aggregate-address`, Junos BGP aggregates) when
a more specific route contributes to it (`BgpRoutingProcess.initBgpAggregateRoutes`). Each
route contributes to the most specific aggregate that strictly contains it, if it passes the
aggregate's generation policy. Aggregates are activated most specific first, and an
activated aggregate contributes in turn to a more general one.

The contributors are the BGP RIB's routes, or the main RIB's when the configuration says so
(`generateBgpAggregatesFromMainRib`); in that case an aggregate is not activated if the main
RIB already has a better route for its prefix.
-/

namespace LeanBatfish.Bgp

open Std

/-- The longest common leading AS sequence of the contributors (`AsPath.aggregateContributors`). -/
def commonLeadingAsns (paths : Array AsPath) : AsPath := Id.run do
  let some first := paths[0]? | return #[]
  let mut out : AsPath := #[]
  for i in [0:first.size] do
    let some s := first[i]? | break
    if s.asns.size != 1 || s.confederation then break
    if paths.all (fun p => p[i]? == some s) then out := out.push s else break
  return out

/-- The aggregates process `p` activates, most specific first, from the routes that may
contribute (`current`) and the main RIB. -/
def aggregateRoutes (c : Configuration) (p : BgpProcess) (current : Array Route) (main : Rib) :
    EvalM (Array Route) := do
  -- The most specific aggregate strictly containing a prefix.
  let mostSpecific (q : Prefix) : Option BgpAggregate :=
    if q.len.val == 0 then none
    else (p.aggregates.filter fun a => a.network.len < q.len && a.network.containsPrefix q)
      |>.foldl (fun best a => match best with
        | some b => if a.network.len > b.network.len then some a else best
        | none => some a) none
  let mut contributors : HashMap Prefix (Array Route) := {}
  for r in current do
    if r.protocol == .aggregate then continue
    if let some a := mostSpecific r.network then
      contributors := contributors.insert a.network ((contributors.getD a.network #[]).push r)
  -- Most specific first, then by address.
  let ordered := p.aggregates.toList.mergeSort fun a b =>
    a.network.len > b.network.len || (a.network.len == b.network.len &&
      a.network.addr.bits ≤ b.network.addr.bits)
  let mut out := #[]
  for agg in ordered do
    let cs := contributors.getD agg.network #[]
    let gen := agg.generationPolicy.bind c.routingPolicies.find?
    let mut activated := false
    let mut paths : Array AsPath := #[]
    for r in cs do
      let ok ← match gen with
        | none => pure true
        | some pol => Policy.accepts c pol r
      if ok then
        activated := true
        if r.isBgpRoute then paths := paths.push r.asPath
    let mut route : Option Route := none
    if activated then
      let asPath := if agg.asPathMode == .commonSequence then commonLeadingAsns paths else #[]
      let base : Route := {
        network := agg.network, nextHop := .discard, protocol := .aggregate
        admin := p.localAdminCost, metric := 0, nonRouting := !agg.installInMainRib
        bgp := some { asPath, localPreference := BgpAttrs.defaultLocalPreference
                      srcProtocol := some .aggregate, originatorIp := p.routerId
                      originMechanism := .generated, originType := .igp
                      receivedFrom := .self, weight := 32768 } }
      let r ← match agg.attributePolicy.bind c.routingPolicies.find? with
        | none => pure base
        | some pol =>
          let ctx : Policy.Context := {
            config := c, original := base, useOutputAttributes := Policy.useOutputAttributesFor c
            outputKind := .bgp }
          pure (← Policy.process ctx pol base).output
      if c.generateBgpAggregatesFromMainRib then
        match (main.routesAt agg.network)[0]? with
        | some m => if Rib.morePreferred (Rib.mainPreference m) (Rib.mainPreference r) then
            route := none else route := some r
        | none => route := some r
      else route := some r
    if let some r := route then out := out.push r
    if let some general := mostSpecific agg.network then
      let more := cs ++ (match route with | some r => #[r] | none => #[])
      contributors := contributors.insert general.network
        ((contributors.getD general.network #[]) ++ more)
  return out

end LeanBatfish.Bgp
