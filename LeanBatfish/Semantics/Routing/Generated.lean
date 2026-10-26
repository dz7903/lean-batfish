import LeanBatfish.Semantics.Routing.Static

/-!
# Generated routes

Generated routes (Junos aggregate and generate routes) are activated by main-RIB routes
that pass their generation policy (`GeneratedRouteHelper.activateGeneratedRoute`). The
policy runs on a contributing route and writes the generated route, so it can set the
generated route's attributes; a generated route that does not discard traffic forwards to
the contributor's next hop.
-/

namespace LeanBatfish

/-- A generated route before activation. -/
def GeneratedRoute.toRoute (g : GeneratedRoute) : Route := {
  network := g.network, nextHop := .discard, protocol := .aggregate
  admin := g.administrativeCost, metric := g.metric, tag := g.tag, generated := true
  bgp := some { communities := .ofArray g.communities, localPreference := g.localPreference
                originType := g.originType, weight := g.weight } }

/-- The active form of a generated route, given the main-RIB routes that may contribute (in
order): without a generation policy it is always active; otherwise the first contributor
the policy accepts activates it. -/
def GeneratedRoute.activate (c : Configuration) (g : GeneratedRoute) (contributors : Array Route) :
    EvalM (Option Route) := do
  let base := g.toRoute
  let some name := g.generationPolicy | return some base
  let some policy := c.routingPolicies.find? name
    | throw s!"undefined generation policy {name}"
  for r in contributors do
    let ctx : Policy.Context := {
      config := c, original := r, useOutputAttributes := Policy.useOutputAttributesFor c
      outputKind := .generated }
    let o ← Policy.process ctx policy base
    if o.accepted then
      let out := o.output
      return some (if g.discard then out else
        { out with nextHop := match r.nextHopIp? with | some ip => .ip ip | none => .discard })
  return none

end LeanBatfish
