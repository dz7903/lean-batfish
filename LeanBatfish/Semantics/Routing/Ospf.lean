import Std.Data.HashMap
import LeanBatfish.Semantics.Routing.Static
import LeanBatfish.Topology.Edge

/-!
# OSPF

Batfish computes OSPF as a distance-vector exchange between adjacent processes (its
`OspfRoutingProcess`), not by running SPF over a link-state database. Each process keeps
four tables, one per kind of route, each holding for every prefix the routes of lowest
metric:

* **intra-area** routes start from the process's own interfaces and travel within an
  area, adding the cost of the receiving interface at each hop;
* **inter-area** routes are intra-area routes that an area border router (ABR) passes
  between areas; non-ABRs pass them on within the area, never back to the router they
  came from (split horizon);
* **external** routes (E1 and E2) are main-RIB routes that a process redistributes
  through its export policy. E1 routes add each hop's cost to their metric; E2 routes keep
  their metric and add the cost to a separate cost-to-advertiser, which breaks ties.

The routes a process puts into the main RIB are, for each prefix, those of the most
preferred kind: intra-area, then inter-area, then E1, then E2.

Every hop adds a positive cost, so each kind of route is a strictly increasing routing
algebra in the sense of `LeanBatfish.Theory`: the exchange has exactly one stable state,
whatever order messages are processed in. This module gives the functions that define
that state (what a process originates, and how a route changes when sent over an
adjacency); the simulator computes the state by iterating them to a fixed point.
-/

namespace LeanBatfish.Ospf

open Std

/-- An OSPF process: its node, VRF and process ID. -/
structure ProcId where
  host : String
  vrf : String
  proc : String
  deriving DecidableEq, Hashable, Inhabited, Repr

instance : ToString ProcId := ⟨fun p => s!"{p.host}:{p.vrf}:ospf {p.proc}"⟩

/-- An adjacency, as used to send routes from `sender` to `receiver`. -/
structure Adjacency where
  sender : ProcId
  receiver : ProcId
  /-- The receiving interface. -/
  receiverIface : String
  senderIp : Ip
  receiverIp : Ip
  area : Nat
  /-- The OSPF cost of the receiving interface, added to routes on receipt. -/
  cost : Nat
  deriving Inhabited, Repr

/-- A table of OSPF routes of one kind: for each prefix, the routes of the best metric. -/
abbrev Table := HashMap Prefix (Array Route)

/-- The four tables of a process. -/
structure ProcState where
  intra : Table := {}
  inter : Table := {}
  e1 : Table := {}
  e2 : Table := {}
  deriving Inhabited

/-! ## Configuration lookups -/

def adminCost (p : OspfProcess) (proto : RoutingProtocol) : EvalM Nat :=
  match p.adminCosts.find? (·.1 == proto) with
  | some (_, v) => pure v
  | none => throw s!"OSPF process {p.processId} has no admin cost for {repr proto}"

/-- `Interface.getOspfCost`. Batfish fills in interface costs when it converts the
configuration. A zero cost would make the exchange not strictly increasing, and is not
modeled. -/
def ifaceCost (i : Interface) : EvalM Nat :=
  match i.ospf.bind (·.cost) with
  | some 0 => throw s!"interface {i.name} has OSPF cost 0"
  | some c => pure c
  | none => throw s!"interface {i.name} has no OSPF cost"

/-- `OspfProcess.isAreaBorderRouter`: the process is in area 0 and in another area. -/
def isAbr (p : OspfProcess) : Bool :=
  p.areas.any (·.name == 0) && p.areas.size > 1

/-! ## Tables -/

/-- Keep, for each prefix, the routes with the least `key`, without duplicates. -/
def Table.ofRoutes (key : Route → Nat × Nat) (routes : Array Route) : Table := Id.run do
  let mut t : Table := {}
  for r in routes do
    match t[r.network]? with
    | none => t := t.insert r.network #[r]
    | some cur =>
      let k := key r
      let k' := key cur[0]!
      if k.1 < k'.1 || (k.1 == k'.1 && k.2 < k'.2) then t := t.insert r.network #[r]
      else if k == k' && !cur.contains r then t := t.insert r.network (cur.push r)
  return t

def Table.routes (t : Table) : Array Route := t.fold (fun acc _ rs => acc ++ rs) #[]

/-- Two tables hold the same routes. -/
def Table.same (a b : Table) : Bool :=
  a.size == b.size && a.fold (fun ok p rs => ok && match b[p]? with
    | some rs' => rs.size == rs'.size && rs.all rs'.contains
    | none => false) true

/-- Intra-area, inter-area and E1 tables prefer the lowest metric. -/
def metricKey (r : Route) : Nat × Nat := (r.metric, 0)

/-- E2 tables prefer the lowest metric, then the lowest cost to the advertiser. -/
def e2Key (r : Route) : Nat × Nat := (r.metric, (r.ospf.map (·.costToAdvertiser)).getD 0)

/-! ## Origination -/

/-- The intra-area routes a process originates from its interfaces
(`initializeRoutesByArea`): one per address of each active, OSPF-enabled interface in an
area, or the `/32` of each address for loopbacks not in point-to-point mode. They are
non-routing: the connected routes already cover them locally. -/
def localIntraRoutes (c : Configuration) (p : OspfProcess) : EvalM (Array Route) := do
  let admin ← adminCost p .ospf
  let mut out := #[]
  for area in p.areas do
    for name in area.interfaces do
      let some i := c.interfaces.find? name | continue
      let some s := i.ospf | continue
      if !i.active || !s.enabled then continue
      let loopbackHosts := i.type == "LOOPBACK" && i.address.isSome &&
        s.networkType != some .pointToPoint
      let cost ← ifaceCost i
      for a in i.allAddresses do
        out := out.push {
          network := if loopbackHosts then Prefix.make a.ip 32 else a.prefix
          nextHop := .ip a.ip, protocol := .ospf, admin, metric := cost, nonRouting := true
          ospf := some { area := some area.name } }
  return out

/-- An ABR keeps each intra-area route as a non-routing inter-area route too, to pass it
into its other areas (`OspfInterAreaRoute.builder(intraAreaRoute)`). -/
def intraToInter (r : Route) : Route := { r with protocol := .ospfIa, nonRouting := true }

/-- The external route a process originates from a main-RIB route, if its export policy
accepts it (`convertToExternalRoute`). The policy must set the metric type. -/
def redistribute (c : Configuration) (p : OspfProcess) (exportPolicy : RoutingPolicy)
    (r : Route) : EvalM (Option Route) := do
  let ctx : Policy.Context := {
    config := c, original := r, useOutputAttributes := Policy.useOutputAttributesFor c
    outputKind := .ospfExternal }
  let start : Route := { network := r.network, nextHop := .discard, protocol := .ospfE2, admin := 0 }
  let o ← Policy.process ctx exportPolicy start
  if !o.accepted then return none
  let some t := o.output.ospfMetricType
    | throw s!"OSPF export policy {exportPolicy.name} did not set a metric type"
  let proto : RoutingProtocol := if t == .e1 then .ospfE1 else .ospfE2
  return some { o.output with
    network := r.network, protocol := proto, admin := ← adminCost p proto, nonRouting := true
    ospf := some { area := none, costToAdvertiser := 0, advertiser := c.hostname,
                   lsaMetric := o.output.metric } }

/-! ## Sending routes over an adjacency -/

def inTransit (adj : Adjacency) (r : Route) : Route :=
  { r with nextHop := .ip adj.senderIp, nonRouting := true }

def received (adj : Adjacency) (admin : Nat) (r : Route) : Route :=
  { r with nextHop := .iface adj.receiverIface (some adj.senderIp), admin
           nonRouting := false, nonForwarding := false }

/-- An intra-area route as the receiver gets it: only routes of the adjacency's area are
sent, and the receiver adds its interface cost. -/
def sendIntra (adj : Adjacency) (receiver : OspfProcess) (r : Route) : EvalM (Option Route) := do
  if r.ospfArea != some adj.area then return none
  let r := inTransit adj r
  return some { received adj (← adminCost receiver .ospf) r with metric := r.metric + adj.cost }

/-- An inter-area route as the receiver gets it. A non-ABR sends routes of the adjacency's
area; an ABR sends routes of other areas, relabelled with the adjacency's area. Neither
sends a route back to the router it came from. An ABR does not accept a default route,
since ABRs originate it. -/
def sendInter (adj : Adjacency) (senderAbr receiverAbr : Bool) (receiver : OspfProcess)
    (r : Route) : EvalM (Option Route) := do
  if r.nextHopIp? == some adj.receiverIp then return none
  let r ← if senderAbr then
      if r.ospfArea == some adj.area then return none
      pure { r with ospf := r.ospf.map ({ · with area := some adj.area }) }
    else
      if r.ospfArea != some adj.area then return none
      pure r
  if receiverAbr && r.network.len.val == 0 then return none
  let r := inTransit adj r
  return some { received adj (← adminCost receiver .ospfIa) r with metric := r.metric + adj.cost }

/-- An E1 route as the receiver gets it. Routes cross between areas only through area 0;
both the metric and the cost to the advertiser grow by the receiver's interface cost. -/
def sendE1 (adj : Adjacency) (receiver : OspfProcess) (r : Route) : EvalM (Option Route) := do
  let area := r.ospfArea
  unless area == some 0 || adj.area == 0 || area == some adj.area || area == none do
    return none
  let attrs := (r.ospf.getD {})
  let r := { inTransit adj r with ospf := some { attrs with area := some adj.area } }
  return some { received adj (← adminCost receiver .ospfE1) r with
    metric := r.metric + adj.cost
    ospf := some { attrs with area := some adj.area,
                              costToAdvertiser := attrs.costToAdvertiser + adj.cost } }

/-- An E2 route as the receiver gets it: the metric stays, the cost to the advertiser
grows by the receiver's interface cost. -/
def sendE2 (adj : Adjacency) (receiver : OspfProcess) (r : Route) : EvalM (Option Route) := do
  let attrs := (r.ospf.getD {})
  let area := attrs.area <|> some adj.area
  let r := { inTransit adj r with ospf := some { attrs with area } }
  return some { received adj (← adminCost receiver .ospfE2) r with
    ospf := some { attrs with area, costToAdvertiser := attrs.costToAdvertiser + adj.cost } }

/-- Whether a process keeps an external route it receives: not its own E1 routes coming
back, nor its own E2 routes coming back from elsewhere (`OspfExternalType1Rib`,
`OspfExternalType2Rib`). -/
def acceptsExternal (host : String) (r : Route) : Bool :=
  let attrs := r.ospf.getD {}
  if attrs.advertiser != host then true
  else if r.protocol == .ospfE1 then r.nonRouting
  else attrs.costToAdvertiser == 0

/-! ## Into the main RIB -/

/-- `OspfRib`: routes of a more preferred kind displace the others. -/
def kindRank : RoutingProtocol → Nat
  | .ospf => 0
  | .ospfIs => 1
  | .ospfIa => 2
  | .ospfE1 => 3
  | _ => 4

/-- The routes a process offers the main RIB: for each prefix, the routes of the most
preferred kind, without the non-routing ones. -/
def mainRibRoutes (s : ProcState) : Array Route := Id.run do
  let mut best : HashMap Prefix (Array Route) := {}
  for r in s.intra.routes ++ s.inter.routes ++ s.e1.routes ++ s.e2.routes do
    match best[r.network]? with
    | none => best := best.insert r.network #[r]
    | some cur =>
      let k := kindRank r.protocol
      let k' := kindRank cur[0]!.protocol
      if k < k' then best := best.insert r.network #[r]
      else if k == k' && !cur.contains r then best := best.insert r.network (cur.push r)
  return (Table.routes best).filter (!·.nonRouting)

end LeanBatfish.Ospf
