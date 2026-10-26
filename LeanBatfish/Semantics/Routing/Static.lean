import LeanBatfish.Semantics.Routing.Rib
import LeanBatfish.Semantics.Policy.Eval

/-!
# Connected, local and static routes

The routes a VRF has before any routing protocol runs (Batfish's `VirtualRouter`):

* a **connected** route for each address of each active interface in the VRF;
* a **local** route, the `/32` of the address itself, for addresses shorter than `/32`;
* the VRF's **static** routes. A static route with a next-hop IP is active only while that
  IP resolves through the main RIB; one with a next-hop interface only while the
  interface is active; others are always active.

Next hops resolve through routes accepted by the VRF's *resolution policy*, if it has
one. Cisco configurations use it to keep the default route from resolving next hops.
-/

namespace LeanBatfish

/-! ## Connected and local routes -/

private def metadataOf (i : Interface) (a : InterfaceAddress) : Option ConnectedRouteMetadata :=
  (i.addressMetadata.find? (·.1 == a)).map (·.2)

/-- Connected routes of the active interfaces in `vrf` (`generateConnectedRoutes`). -/
def connectedRoutes (c : Configuration) (vrf : String) : Array Route := Id.run do
  let mut out := #[]
  for (_, i) in c.interfaces do
    if !i.active || i.vrf != vrf then continue
    for a in i.allAddresses do
      let md := metadataOf i a
      if (md.bind (·.generateConnectedRoute)).getD true then
        out := out.push {
          network := a.prefix, nextHop := .iface i.name none, protocol := .connected
          admin := (md.bind (·.admin)).getD 0, tag := (md.bind (·.tag)).getD unsetRouteTag }
  return out

/-- Local routes of the interfaces in `vrf` (`generateLocalRoutes`): for active interfaces,
the `/32` of each address shorter than `/32` unless metadata says otherwise; for inactive
ones, a discard route if the metadata asks for it. -/
def localRoutes (c : Configuration) (vrf : String) : Array Route := Id.run do
  let mut out := #[]
  for (_, i) in c.interfaces do
    if i.vrf != vrf then continue
    for a in i.allAddresses do
      let md := metadataOf i a
      let route (nh : NextHop) : Route := {
        network := Prefix.make a.ip 32, nextHop := nh, protocol := .local
        admin := (md.bind (·.admin)).getD 0, tag := (md.bind (·.tag)).getD unsetRouteTag
        sourcePrefixLength := a.len }
      if i.active then
        if (md.bind (·.generateLocalRoutes)).getD (a.len.val < 32) then
          out := out.push (route (.iface i.name none))
      else if (md.bind (·.generateLocalNullRouteIfDown)).getD false then
        out := out.push (route .discard)
  return out

/-! ## Static routes -/

def StaticRoute.toRoute (s : StaticRoute) : Route := {
  network := s.network, nextHop := s.nextHop, protocol := .static
  admin := s.administrativeCost, metric := s.metric, tag := s.tag
  recursive := s.recursive, nonForwarding := s.nonForwarding }

/-- Whether a route may be used to resolve next hops: it passes the VRF's resolution
policy, if there is one. -/
def resolutionAllowed (c : Configuration) (v : Vrf) (r : Route) : EvalM Bool :=
  match v.resolutionPolicy with
  | none => pure true
  | some name =>
    match c.routingPolicies.find? name with
    | some p => Policy.accepts c p r
    | none => throw s!"undefined resolution policy {name}"

/-- The routes a static route's next-hop IP resolves through
(`StaticRouteHelper.resolveStaticNextHopIp`): the longest match among connected routes
and, for recursive static routes, routes allowed by the resolution policy. -/
def resolveStaticNextHopIp (c : Configuration) (v : Vrf) (rib : Rib) (ip : Ip)
    (recursive : Bool) : EvalM (Array Route) :=
  rib.longestPrefixMatch ip fun r =>
    if r.protocol == .connected then pure true
    else if !recursive then pure false
    else resolutionAllowed c v r

/-- Whether a static route with a next-hop IP may be active, given what its next hop
resolves through (`StaticRouteHelper.shouldActivateNextHopIpRoute`). A route whose own
network contains its next hop needs a more specific route to it, or it would resolve
through itself. -/
def shouldActivateNextHopIpRoute (route : Route) (nextHop : Ip) (resolution : Array Route) :
    Bool :=
  if !route.network.containsIp nextHop then !resolution.isEmpty
  else resolution.any (·.network.len > route.network.len)

/-- Whether a static route's activation depends on the RIB or the interfaces
(`isConditionalStaticRoute`). -/
def Route.isConditionalStatic (r : Route) : Bool :=
  match r.nextHop with
  | .ip _ | .iface .. => true
  | .discard => false

/-- One pass of static-route activation (`VirtualRouter.activateStaticRoutes`): routes with
a next-hop IP, grouped by that IP in ascending order, then routes with a next-hop
interface. Within a group the resolution is computed once per recursiveness, from the RIB
as it is when first needed. Returns the new RIB and whether anything changed. -/
def activateStatics (c : Configuration) (v : Vrf) (statics : Array Route) (rib : Rib) :
    EvalM (Rib × Bool) := do
  let conditional := statics.filter (·.isConditionalStatic)
  let withIp := conditional.filterMap fun r =>
    match r.nextHop with | .ip ip => some (ip, r) | _ => none
  let ips := (withIp.map (·.1)).qsort (· < ·) |>.toList.eraseDups
  let groups := ips.map fun ip => (withIp.filter (·.1 == ip)).map (·.2)
  let withoutIp := conditional.filter fun r => match r.nextHop with | .ip _ => false | _ => true
  let mut rib := rib
  let mut changed := false
  for group in groups do
    let mut recursiveRes : Option (Array Route) := none
    let mut nonRecursiveRes : Option (Array Route) := none
    for r in group do
      let .ip ip := r.nextHop | continue
      let res ← if r.recursive then do
          match recursiveRes with
          | some res => pure res
          | none =>
            let res ← resolveStaticNextHopIp c v rib ip true
            recursiveRes := some res
            pure res
        else do
          match nonRecursiveRes with
          | some res => pure res
          | none =>
            let res ← resolveStaticNextHopIp c v rib ip false
            nonRecursiveRes := some res
            pure res
      (rib, changed) := update rib changed r (shouldActivateNextHopIpRoute r ip res)
  for r in withoutIp do
    let active := match r.nextHop with
      | .iface name _ => ((c.interfaces.find? name).map (·.active)).getD false
      | _ => true
    (rib, changed) := update rib changed r active
  return (rib, changed)
where
  update (rib : Rib) (changed : Bool) (r : Route) (activate : Bool) : Rib × Bool :=
    let offered := (rib.offered.getD r.network #[]).contains r
    if activate && !offered then (rib.offer r, true)
    else if !activate && offered then (rib.withdraw r, true)
    else (rib, changed)

end LeanBatfish
