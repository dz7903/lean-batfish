import LeanBatfishSim.Bgp.Delta

/-!
# OSPF in the engine

Intra-area and inter-area routes form strictly increasing exchanges with a single stable
state, which the engine computes by synchronous iteration before the main loop, as Batfish
does in its IGP phase.

External routes are different, because of how Batfish wires them to the main RIB. A process
puts its own redistributed routes into its E1/E2 tables and sends them out, but changes
those cause in its tables (a received route displaced by a better own route) are not
passed to the process's main-RIB view: only changes from received messages are. So what a
router installs depends on the order in which its own and received routes arrived. The
engine therefore runs external routes the way Batfish does: per round and per node in the
schedule, with message queues on each adjacency, tables that keep backups, and a main-RIB
view fed only by received changes.
-/

namespace LeanBatfishSim

open LeanBatfish Std

/-- An upper bound on rounds of any exchange; reaching it means no convergence. -/
def maxRounds : Nat := 10000

/-! ## Processes and adjacencies -/

/-- An OSPF process with what the engine needs about it. -/
structure OspfProc where
  id : Ospf.ProcId
  config : Configuration
  process : OspfProcess
  exportPolicy : Option RoutingPolicy
  localIntra : Array Route
  deriving Inhabited

/-- The OSPF part of the computation: processes, adjacencies into each process, and
the state of each process. -/
structure OspfNet where
  procs : Array OspfProc
  /-- For each process (by index), the adjacencies on which it receives routes, with the
  index of the sending process. -/
  incoming : Array (Array (Nat × Ospf.Adjacency))
  states : Array Ospf.ProcState
  deriving Inhabited

private def findProc (procs : Array OspfProc) (id : Ospf.ProcId) : Option Nat :=
  procs.findIdx? (·.id == id)

/-- The process and IP of an interface on an OSPF adjacency. -/
private def endpoint (configs : HashMap String Configuration) (ni : NodeInterface) :
    EvalM (Ospf.ProcId × Interface × Ip) := do
  let some c := configs[ni.host]? | throw s!"OSPF edge to unknown node {ni.host}"
  let some i := c.interfaces.find? ni.iface | throw s!"OSPF edge to unknown interface {ni}"
  let some s := i.ospf | throw s!"OSPF edge on {ni} without OSPF settings"
  let some proc := s.process | throw s!"OSPF edge on {ni} without an OSPF process"
  let some a := i.address | throw s!"OSPF edge on {ni} without an address"
  return ({ host := ni.host, vrf := i.vrf, proc }, i, a.ip)

def OspfNet.build (configs : HashMap String Configuration) (edges : Array OspfEdge) :
    EvalM OspfNet := do
  let mut procs := #[]
  for c in (configs.toArray.map (·.2)).qsort (·.hostname < ·.hostname) do
    for (_, v) in c.vrfs do
      for (name, p) in v.ospfProcesses do
        let exportPolicy := p.exportPolicy.bind c.routingPolicies.find?
        procs := procs.push {
          id := { host := c.hostname, vrf := v.name, proc := name }, config := c, process := p
          exportPolicy, localIntra := ← Ospf.localIntraRoutes c p }
  let mut incoming := Array.replicate procs.size #[]
  for e in edges do
    let (tailId, _, tailIp) ← endpoint configs e.tail
    let (headId, headIface, headIp) ← endpoint configs e.head
    let some t := findProc procs tailId | throw s!"no OSPF process {tailId}"
    let some h := findProc procs headId | throw s!"no OSPF process {headId}"
    let some area := headIface.ospf.bind (·.area) | throw s!"no OSPF area on {e.head}"
    let adj : Ospf.Adjacency := {
      sender := tailId, receiver := headId, receiverIface := headIface.name
      senderIp := tailIp, receiverIp := headIp, area, cost := ← Ospf.ifaceCost headIface }
    incoming := incoming.modify h (·.push (t, adj))
  return { procs, incoming, states := Array.replicate procs.size {} }

/-- Iterate one kind of exchange to its fixed point. `origin i` gives what process `i`
originates, `send` how a route crosses an adjacency, and `get`/`set` select the table. -/
def OspfNet.exchange (net : OspfNet) (name : String) (key : Route → Nat × Nat)
    (origin : Nat → EvalM (Array Route))
    (send : Ospf.Adjacency → Nat → Nat → Route → EvalM (Option Route))
    (accept : Nat → Route → Bool)
    (get : Ospf.ProcState → Ospf.Table)
    (set : Ospf.ProcState → Ospf.Table → Ospf.ProcState) : EvalM OspfNet := do
  let mut states := net.states
  for _ in [0:maxRounds] do
    let mut next := states
    let mut changed := false
    for i in [0:net.procs.size] do
      let mut routes ← origin i
      for (j, adj) in net.incoming[i]! do
        for r in (get states[j]!).routes do
          if let some r' ← send adj j i r then
            if accept i r' then routes := routes.push r'
      let t := Ospf.Table.ofRoutes key routes
      if !(get states[i]!).same t then changed := true
      next := next.modify i (set · t)
    states := next
    if !changed then return { net with states }
  throw s!"OSPF {name} routes did not converge"

def OspfNet.isAbr (net : OspfNet) (i : Nat) : Bool := Ospf.isAbr net.procs[i]!.process

/-- Intra-area, then inter-area routes. -/
def OspfNet.internal (net : OspfNet) : EvalM OspfNet := do
  let net ← net.exchange "intra-area" Ospf.metricKey
    (fun i => pure net.procs[i]!.localIntra)
    (fun adj _ i r => Ospf.sendIntra adj net.procs[i]!.process r)
    (fun _ _ => true) (·.intra) ({ · with intra := · })
  net.exchange "inter-area" Ospf.metricKey
    (fun i => pure (if net.isAbr i then
      (net.states[i]!.intra.routes.map Ospf.intraToInter) else #[]))
    (fun adj j i r => Ospf.sendInter adj (net.isAbr j) (net.isAbr i) net.procs[i]!.process r)
    (fun _ _ => true) (·.inter) ({ · with inter := · })


/-! ## Tables with Batfish's update rules -/

/-- A routing table under `AbstractRib`'s rules for a fixed preference `cmp` (positive when
the first route is preferred), optionally keeping backups. -/
structure SimpleRib where
  withBackups : Bool
  tree : HashMap Prefix (Array Route) := {}
  backups : HashMap Prefix (Array Route) := {}
  deriving Inhabited

namespace SimpleRib

private def putBackup (rib : SimpleRib) (r : Route) : SimpleRib :=
  if !rib.withBackups then rib else
  let bs := rib.backups.getD r.network #[]
  { rib with backups := rib.backups.insert r.network (if bs.contains r then bs else bs.push r) }

private def dropBackup (rib : SimpleRib) (r : Route) : SimpleRib :=
  match rib.backups[r.network]? with
  | none => rib
  | some bs =>
    let bs := bs.filter (· != r)
    { rib with backups := if bs.isEmpty then rib.backups.erase r.network
        else rib.backups.insert r.network bs }

def merge (cmp : Route → Route → Int) (rib : SimpleRib) (r : Route) : SimpleRib × Array Advert :=
  let cur := rib.tree.getD r.network #[]
  match cur[0]? with
  | none => ({ rib with tree := rib.tree.insert r.network #[r] }, #[{ route := r }])
  | some old =>
    let c := cmp r old
    if c < 0 then (if cur.contains r then rib else rib.putBackup r, #[])
    else if c == 0 then
      if cur.contains r then (rib, #[])
      else ({ rib with tree := rib.tree.insert r.network (cur.push r) }, #[{ route := r }])
    else
      let rib := cur.foldl putBackup { rib with tree := rib.tree.insert r.network #[r] }
      (rib, cur.map ({ route := ·, reason := .replace }) |>.push { route := r })

def remove (cmp : Route → Route → Int) (rib : SimpleRib) (r : Route) : SimpleRib × Array Advert :=
  let cur := rib.tree.getD r.network #[]
  if !cur.contains r then (rib.dropBackup r, #[]) else
  let rest := cur.filter (· != r)
  let removal : Advert := { route := r, reason := .withdraw }
  if !rest.isEmpty then ({ rib with tree := rib.tree.insert r.network rest }, #[removal]) else
  let bs := rib.backups.getD r.network #[]
  let promoted := bs.foldl (fun best b => match best[0]? with
    | none => #[b]
    | some x => let c := cmp b x; if c == 0 then best.push b else if c > 0 then #[b] else best) #[]
  let tree := if promoted.isEmpty then rib.tree.erase r.network else rib.tree.insert r.network promoted
  let rib := promoted.foldl dropBackup { rib with tree }
  (rib, #[removal] ++ promoted.map ({ route := · }))

def apply (cmp : Route → Route → Int) (rib : SimpleRib) (a : Advert) : SimpleRib × Array Advert :=
  if a.withdrawn then rib.remove cmp a.route else rib.merge cmp a.route

def routes (rib : SimpleRib) : Array Route := rib.tree.fold (fun acc _ rs => acc ++ rs) #[]

end SimpleRib

/-! ## External routes, incrementally -/

def cmpE1 (a b : Route) : Int := if a.metric < b.metric then 1 else if a.metric > b.metric then -1 else 0

def cmpE2 (a b : Route) : Int :=
  let ca := (a.ospf.map (·.costToAdvertiser)).getD 0
  let cb := (b.ospf.map (·.costToAdvertiser)).getD 0
  if a.metric != b.metric then cmpE1 a b
  else if ca < cb then 1 else if ca > cb then -1 else 0

/-- `OspfRib`: preference by kind of route only. -/
def cmpKind (a b : Route) : Int :=
  let ka := Ospf.kindRank a.protocol
  let kb := Ospf.kindRank b.protocol
  if ka < kb then 1 else if ka > kb then -1 else 0

/-- The external-route state of one process. -/
structure ExtState where
  e1 : SimpleRib := { withBackups := true }
  e2 : SimpleRib := { withBackups := true }
  /-- What the process offers its main RIB (`OspfRib`). -/
  view : SimpleRib := { withBackups := false }
  /-- Messages waiting on each incoming adjacency (by position in `incoming`). -/
  queues : Array (Array Advert) := #[]
  /-- Own redistributed and generated routes, not yet sent. -/
  pending : Array Advert := #[]
  deriving Inhabited

/-- Merge a route of either type into the matching table (`OspfExternalType1Rib`/`...2Rib`
reject the process's own routes coming back). -/
def ExtState.mergeOwn (host : String) (s : ExtState) (r : Route) : ExtState × Array Advert :=
  if !Ospf.acceptsExternal host r then (s, #[]) else
  if r.protocol == .ospfE1 then
    let (e1, d) := s.e1.merge cmpE1 r
    ({ s with e1 }, d)
  else
    let (e2, d) := s.e2.merge cmpE2 r
    ({ s with e2 }, d)

def ExtState.applyReceived (host : String) (s : ExtState) (a : Advert) : ExtState × Array Advert :=
  if a.withdrawn then
    if a.route.protocol == .ospfE1 then
      let (e1, d) := s.e1.remove cmpE1 a.route
      ({ s with e1 }, d)
    else
      let (e2, d) := s.e2.remove cmpE2 a.route
      ({ s with e2 }, d)
  else s.mergeOwn host a.route

/-- The OSPF part of the network. -/
structure OspfWorld where
  net : OspfNet
  ext : Array ExtState
  deriving Inhabited

def OspfWorld.init (net : OspfNet) : OspfWorld := Id.run do
  let mut ext := #[]
  for i in [0:net.procs.size] do
    -- Intra-area and inter-area routes enter the view first (Batfish's IGP phase).
    let st := net.states[i]!
    let view := (st.intra.routes ++ st.inter.routes).foldl
      (fun v r => (v.merge cmpKind r).1) ({ withBackups := false } : SimpleRib)
    ext := ext.push { view, queues := Array.replicate net.incoming[i]!.size #[] }
  return { net, ext }

/-- Redistribute at the start of a round (`OspfRoutingProcess.redistribute`): main-RIB routes
of the previous round's delta (withdrawn ones too: Batfish never withdraws them) through the
export policy, and generated routes activated by those routes. -/
def OspfWorld.redistribute (w : OspfWorld) (i : Nat) (delta : Array Advert) : EvalM OspfWorld := do
  let p := w.net.procs[i]!
  let some policy := p.exportPolicy | return w
  let host := p.id.host
  let mut s := w.ext[i]!
  let routes := delta.map (·.route)
  let mut candidates := routes
  for g in p.process.generatedRoutes do
    if let some r ← g.activate p.config routes then candidates := candidates.push r
  for r in candidates do
    if let some e ← Ospf.redistribute p.config p.process policy r then
      let (s', d) := s.mergeOwn host e
      s := { s' with pending := s'.pending ++ d }
  return { w with ext := w.ext.set! i s }

/-- Send adverts from process `i` to its neighbors' queues. -/
private def OspfWorld.send (w : OspfWorld) (i : Nat) (adverts : Array Advert) : OspfWorld :=
  if adverts.isEmpty then w else Id.run do
  let mut ext := w.ext
  for r in [0:w.net.procs.size] do
    let inc := w.net.incoming[r]!
    for q in [0:inc.size] do
      if inc[q]!.1 == i then
        ext := ext.modify r fun s => { s with queues := s.queues.modify q (· ++ adverts) }
  return { w with ext }

/-- One OSPF iteration of process `i` (`OspfRoutingProcess.executeIteration`, external part):
send pending own routes, process received messages, send the resulting changes, and pass
those changes (only those) to the main-RIB view. -/
def OspfWorld.iterate (w : OspfWorld) (i : Nat) : EvalM OspfWorld := do
  let p := w.net.procs[i]!
  let host := p.id.host
  let pending := w.ext[i]!.pending
  let mut w := w.send i pending
  w := { w with ext := w.ext.modify i ({ · with pending := #[] }) }
  let mut s := w.ext[i]!
  let mut delta : Array Advert := #[]
  let inc := w.net.incoming[i]!
  for q in [0:inc.size] do
    let (_, adj) := inc[q]!
    for a in s.queues[q]! do
      let r ← if a.route.protocol == .ospfE1 then Ospf.sendE1 adj p.process a.route
        else Ospf.sendE2 adj p.process a.route
      let some r := r | continue
      let (s', d) := s.applyReceived host { a with route := r }
      s := s'
      delta := delta ++ d
    s := { s with queues := s.queues.set! q #[] }
  let mut view := s.view
  for a in delta do
    view := (view.apply cmpKind a).1
  w := { w with ext := w.ext.set! i { s with view } }
  -- Routes go out as this process holds them; each receiver applies its adjacency's
  -- transformation (`sendE1`/`sendE2`) when it processes its queue.
  return w.send i delta

/-- The OSPF routes each VRF offers its main RIB. -/
def OspfWorld.mainRibRoutes (w : OspfWorld) (host vrf : String) : Array Route := Id.run do
  let mut out := #[]
  for i in [0:w.net.procs.size] do
    let p := w.net.procs[i]!
    if p.id.host == host && p.id.vrf == vrf then
      out := out ++ (w.ext[i]!.view.routes.filter (!·.nonRouting))
  return out

def OspfWorld.isDirty (w : OspfWorld) : Bool :=
  w.ext.any fun s => !s.pending.isEmpty || s.queues.any (!·.isEmpty)

end LeanBatfishSim
