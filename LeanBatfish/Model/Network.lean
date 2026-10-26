import LeanBatfish.IR.Snapshot
import LeanBatfish.Model.Router
import LeanBatfish.Semantics.Forwarding.Fib
import LeanBatfish.Theory.DataPlane

/-!
# The network of a snapshot

A snapshot as a routing system (`LeanBatfish.Theory.System`) with a data plane. Its routers
are the VRFs of the modeled devices; their adjacencies are the layer-3 edges, OSPF
adjacencies and BGP sessions Batfish computed.

**The environment.** Some BGP peers are outside the network: neighbors configured on a
modeled router whose device is not modeled, or that are not in the snapshot at all. Such
a peer may send anything, at any time: what it sends is the router's input. Choosing which
devices to model therefore chooses what the environment controls; leaving out a device
makes its announcements arbitrary.

**The data plane.** A router forwards a packet by its destination address: it accepts
packets for its own addresses, and otherwise looks up its FIB, computed from its main RIB as
Batfish does. A packet sent out of an interface goes to the router on the link that owns
the address it is sent to; if no modeled router owns it, the packet leaves the network.
Packet filters (ACLs) are not modeled yet.
-/

namespace LeanBatfish.Model

structure Network where
  routers : Array Router
  deriving Inhabited

namespace Network

/-- The number of routers. -/
abbrev size (N : Network) : Nat := N.routers.size

/-- The router for a VRF of a device. -/
def find? (N : Network) (host : String) (vrf : String := "default") : Option (Fin N.size) :=
  (N.routers.findIdx? fun r => r.config.hostname == host && r.vrf.name == vrf).bind fun i =>
    if h : i < N.size then some ⟨i, h⟩ else none

/-- The routers' states as `Router.update` reads them. -/
def states (N : Network) (X : Fin N.size → RouterState) (k : Nat) : RouterState :=
  if h : k < N.size then X ⟨k, h⟩ else {}

/-- The network as a routing system. -/
def system (N : Network) : Theory.System N.size where
  State := RouterState
  Input := Input
  update i X x := N.routers[i].update N.routers (N.states X) x

/-- Every router starts with empty tables. -/
def init (N : Network) : Fin N.size → RouterState := fun _ => {}

/-- No announcements from outside. -/
def quiet (N : Network) : Fin N.size → Input := fun _ => #[]

/-! ## Forwarding -/

/-- Whether `ip` is an address of an active interface of the router. -/
def _root_.LeanBatfish.Model.Router.owns (r : Router) (ip : Ip) : Bool :=
  r.config.interfaces.any fun (_, i) =>
    i.active && i.vrf == r.vrf.name && i.allAddresses.any (·.ip == ip)

/-- The FIB actions for destination `dst` in a main RIB: those of the longest-matching
forwarding routes. -/
def fibActions (r : Router) (main : Array Route) (dst : Ip) : EvalM (Array FibAction) := do
  let rib := Rib.ofRoutes main
  let mut out := #[]
  for route in Bgp.lpm rib dst do
    for a in ← resolveActions r.config r.vrf rib route none [] 0 do
      if !out.contains a then out := out.push a
  return out

/-- What router `i` in state `x` does with a packet to `dst`. -/
def forward (N : Network) (i : Fin N.size) (x : RouterState) (dst : Ip) :
    List (Theory.Hop N.size) :=
  let r := N.routers[i]
  if r.owns dst then [.accept] else
  match fibActions r x.main dst with
  | .error _ => [.drop]
  | .ok actions =>
    if actions.isEmpty then [.drop] else
    actions.toList.map fun (a : FibAction) => match a with
      | .discard => .drop
      | .forward iface arpIp =>
        let target := arpIp.getD dst
        match r.links.find? fun (name, ip, _) => name == iface && ip == target with
        | some (_, _, j) => if h : j < N.size then .forward ⟨j, h⟩ else .exit
        | none => .exit

/-- The data plane of states `X`. -/
def dataPlane (N : Network) (X : Fin N.size → RouterState) : Theory.DataPlane N.size Ip :=
  N.system.dataPlane N.forward X

/-- In states `X`, a packet to `dst` sent by device `src` can be accepted by device `tgt`
(default VRFs). -/
def Delivers (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src tgt : String) : Prop :=
  ∃ i j, N.find? src = some i ∧ N.find? tgt = some j ∧ (N.dataPlane X).Delivers dst i j

/-- In states `X`, no packet to `dst` sent by device `src` is accepted by device `tgt`. -/
def Isolated (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src tgt : String) : Prop :=
  ∀ i j, N.find? src = some i → N.find? tgt = some j → ¬ (N.dataPlane X).Delivers dst i j

/-- In states `X`, a packet to `dst` sent by device `src` can leave the network. -/
def Exits (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src : String) : Prop :=
  ∃ i, N.find? src = some i ∧ (N.dataPlane X).Exits dst i

/-- A check of `Exits` by computation. -/
def checkExits (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src : String) : Bool :=
  match N.find? src with
  | some i => (N.dataPlane X).canExit dst i
  | none => false

theorem exits_of_check {N : Network} {X : Fin N.size → RouterState} {dst : Ip} {src : String}
    (h : N.checkExits X dst src = true) : N.Exits X dst src := by
  unfold checkExits at h
  split at h
  · rename_i i hi
    exact ⟨i, hi, Theory.DataPlane.exits_of_canExit _ h⟩
  · cases h

/-- A check of `Delivers` by computation. -/
def checkDelivers (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src tgt : String) : Bool :=
  match N.find? src, N.find? tgt with
  | some i, some j => (N.dataPlane X).canDeliver dst i j
  | _, _ => false

/-- A check of `Isolated` by computation. -/
def checkIsolated (N : Network) (X : Fin N.size → RouterState) (dst : Ip) (src tgt : String) : Bool :=
  match N.find? src, N.find? tgt with
  | some i, some j => (N.dataPlane X).cannotDeliver dst i j
  | _, _ => true

theorem delivers_of_check {N : Network} {X : Fin N.size → RouterState} {dst : Ip}
    {src tgt : String} (h : N.checkDelivers X dst src tgt = true) : N.Delivers X dst src tgt := by
  unfold checkDelivers at h
  split at h
  · rename_i i j hi hj
    exact ⟨i, j, hi, hj, Theory.DataPlane.delivers_of_canDeliver _ h⟩
  · cases h

theorem isolated_of_check {N : Network} {X : Fin N.size → RouterState} {dst : Ip}
    {src tgt : String} (h : N.checkIsolated X dst src tgt = true) : N.Isolated X dst src tgt := by
  intro i j hi hj
  unfold checkIsolated at h
  rw [hi, hj] at h
  exact Theory.DataPlane.not_delivers_of_cannotDeliver _ h

/-! ## Building the network of a snapshot -/

/-- A session with a peer outside the network, from the router's neighbor configuration:
the peer's AS is the first one the configuration accepts. -/
def externalSession (l : Bgp.Endpoint) (remoteIp : Ip) : Option Bgp.Session := do
  let remoteAs ← (l.peer.remoteAsns.included[0]?).map (·.lo)
  let remote : Bgp.Endpoint := { host := "", vrf := "", process := default, af := default
                                 peer := { (default : BgpPeer) with localAs := some remoteAs } }
  (Bgp.Session.make l remote (l.peer.localIp.getD Ip.zero) remoteIp).toOption

private def routerOf (index : Nat) (c : Configuration) (v : Vrf) (announcements : Array Announcement) :
    EvalM Router := do
  let statics := v.staticRoutes.map (·.toRoute)
  let (ospf, ospfExport, ospfLocal) ← match v.ospfProcesses.toList with
    | [] => pure (none, none, #[])
    | [(_, p)] => pure (some p, p.exportPolicy.bind c.routingPolicies.find?,
        ← Ospf.localIntraRoutes c p)
    | _ => throw s!"{c.hostname} has several OSPF processes in VRF {v.name}"
  return {
    index, config := c, vrf := v
    base := connectedRoutes c v.name ++ localRoutes c v.name ++
      statics.filter (!·.isConditionalStatic)
    conditionalStatics := statics.filter (·.isConditionalStatic)
    ospf, ospfExport, ospfLocal, ospfLinks := #[]
    bgp := v.bgpProcess, bgpLinks := #[], externalPeers := #[]
    announcements := match v.bgpProcess with
      | some p => announcements.filter (Bgp.acceptsAnnouncement c p)
      | none => #[]
    links := #[] }

/-- The network of snapshot `s`, modeling the devices that `modeled` selects (all by
default). -/
def build (s : Snapshot) (modeled : String → Bool := fun _ => true) : EvalM Network := do
  let configs := s.configs.filter (modeled ·.hostname)
  let mut routers : Array Router := #[]
  for c in configs do
    for (_, v) in c.vrfs.qsort (·.1 < ·.1) do
      routers := routers.push (← routerOf routers.size c v s.announcements)
  let indexOf (host vrf : String) : Option Nat :=
    routers.findIdx? fun r => r.config.hostname == host && r.vrf.name == vrf
  let config? (host : String) : Option Configuration := configs.find? (·.hostname == host)
  let iface? (ni : NodeInterface) : Option Interface := (config? ni.host).bind (·.interfaces.find? ni.iface)
  -- Forwarding: where each interface leads.
  for e in s.topology.layer3 do
    let (some ti, some hi) := (iface? e.tail, iface? e.head) | continue
    let (some t, some h) := (indexOf e.tail.host ti.vrf, indexOf e.head.host hi.vrf) | continue
    for a in hi.allAddresses do
      routers := routers.modify t fun r => { r with links := r.links.push (ti.name, a.ip, h) }
  -- OSPF adjacencies.
  for e in s.topology.ospf do
    let (some ti, some hi) := (iface? e.tail, iface? e.head) | continue
    let (some t, some h) := (indexOf e.tail.host ti.vrf, indexOf e.head.host hi.vrf) | continue
    let (some tp, some hp) := ((routers[t]!).ospf, (routers[h]!).ospf) | continue
    let (some ta, some ha) := (ti.address, hi.address) | throw s!"OSPF edge {e.tail} without an address"
    let some area := hi.ospf.bind (·.area) | throw s!"no OSPF area on {e.head}"
    let adj : Ospf.Adjacency := {
      sender := { host := e.tail.host, vrf := ti.vrf, proc := tp.processId }
      receiver := { host := e.head.host, vrf := hi.vrf, proc := hp.processId }
      receiverIface := hi.name, senderIp := ta.ip, receiverIp := ha.ip, area
      cost := ← Ospf.ifaceCost hi }
    routers := routers.modify h fun r =>
      { r with ospfLinks := r.ospfLinks.push { sender := t, senderAbr := Ospf.isAbr tp, adj } }
  -- BGP sessions, between modeled routers or from a peer that is not modeled.
  for e in s.topology.bgp do
    let some hc := config? e.headHost | continue
    let receiver ← Bgp.endpoint hc e.tailIp
    let some h := indexOf e.headHost receiver.vrf | continue
    match config? e.tailHost with
    | some tc =>
      let sender ← Bgp.endpoint tc e.headIp
      let session ← Bgp.Session.make receiver sender e.headIp e.tailIp
      let some t := indexOf e.tailHost sender.vrf | continue
      routers := routers.modify h fun r =>
        { r with bgpLinks := r.bgpLinks.push { sender := t, session } }
    | none =>
      let sender ← Bgp.endpoint (s.configs.find? (·.hostname == e.tailHost)).get! e.headIp
      let session ← Bgp.Session.make receiver sender e.headIp e.tailIp
      routers := routers.modify h fun r =>
        { r with externalPeers := r.externalPeers.push (e.tailIp, session) }
  for r in routers do
    for l in r.bgpLinks do
      let out := l.session.reverse
      if out.additionalPaths then
        routers := routers.modify l.sender fun k =>
          { k with addPathSessions := k.addPathSessions.push out }
  -- Configured neighbors with no session in the snapshot are peers outside it.
  for i in [0:routers.size] do
    let r := routers[i]!
    let some p := r.bgp | continue
    for peer in p.neighbors do
      let .address ip := peer.remote | continue
      let known := r.bgpLinks.any (·.session.remoteIp == ip) || r.externalPeers.any (·.1 == ip)
      if known then continue
      let some af := peer.ipv4Unicast | continue
      let l : Bgp.Endpoint := { host := r.config.hostname, vrf := r.vrf.name, process := p, peer, af }
      if let some session := externalSession l ip then
        routers := routers.modify i fun r => { r with externalPeers := r.externalPeers.push (ip, session) }
  return { routers }

/-- The network of snapshot `s`, or the empty network if it cannot be built. -/
def ofSnapshot (s : Snapshot) (modeled : String → Bool := fun _ => true) : Network :=
  match build s modeled with
  | .ok n => n
  | .error _ => default

end Network

end LeanBatfish.Model

namespace LeanBatfish.Model.Network

/-! ## Synchronous iteration on arrays

`System.iterate` is a function of functions, which evaluation recomputes over and over.
These versions keep the states in an array, and equal it. -/

/-- One synchronous step on states kept in an array. -/
def stepArray (N : Network) (e : Fin N.size → Input) (X : Array RouterState) :
    Array RouterState :=
  N.routers.mapFinIdx fun i r _ => r.update N.routers (fun k => X.getD k {}) (e ⟨i, by simpa⟩)

/-- `t` synchronous steps from empty tables, on arrays. -/
def iterateArray (N : Network) (e : Fin N.size → Input) : Nat → Array RouterState
  | 0 => Array.replicate N.size {}
  | t + 1 => N.stepArray e (N.iterateArray e t)

/-- The states an array holds. -/
def ofArray (N : Network) (X : Array RouterState) : Fin N.size → RouterState :=
  fun i => X.getD i {}

theorem size_iterateArray (N : Network) (e : Fin N.size → Input) :
    ∀ t, (N.iterateArray e t).size = N.size
  | 0 => by simp [iterateArray]
  | t + 1 => by simp [iterateArray, stepArray]

/-- The array iteration is the synchronous iteration of the system. -/
theorem ofArray_iterateArray (N : Network) (e : Fin N.size → Input) :
    ∀ t, N.ofArray (N.iterateArray e t) = N.system.iterate e N.init t := by
  intro t
  induction t with
  | zero =>
    funext i
    simp [ofArray, iterateArray, init, Theory.System.iterate, Array.getD]
  | succ t ih =>
    show _ = N.system.step (N.system.iterate e N.init t) e
    rw [← ih]
    funext i
    have hsize := N.size_iterateArray e t
    have hstates : N.states (N.ofArray (N.iterateArray e t)) =
        fun k => (N.iterateArray e t).getD k {} := by
      funext k
      simp only [states, ofArray]
      split
      · rfl
      · simp [Array.getD]; omega
    simp only [Theory.System.step, ofArray, iterateArray, stepArray, Array.getD_eq_getD_getElem?,
      Array.getElem?_mapFinIdx]
    simp [system, hstates, Array.getD_eq_getD_getElem?]

/-- Iterate synchronously from empty tables until no router changes, for at most `fuel`
steps. -/
def converge (N : Network) (e : Fin N.size → Input) (fuel : Nat := 1000) : Array RouterState :=
  go (Array.replicate N.size {}) fuel
where
  go (X : Array RouterState) : Nat → Array RouterState
    | 0 => X
    | fuel + 1 => let Y := N.stepArray e X; if Y == X then X else go Y fuel

/-- What `converge` reaches is a state of the synchronous iteration. -/
theorem converge_eq_iterate (N : Network) (e : Fin N.size → Input) (fuel : Nat) :
    ∃ t, N.ofArray (N.converge e fuel) = N.system.iterate e N.init t := by
  suffices h : ∀ fuel t, ∃ t', N.ofArray (converge.go N e (N.iterateArray e t) fuel) =
      N.system.iterate e N.init t' by
    obtain ⟨t', h⟩ := h fuel 0
    exact ⟨t', h⟩
  intro fuel
  induction fuel with
  | zero => intro t; exact ⟨t, ofArray_iterateArray N e t⟩
  | succ fuel ih =>
    intro t
    simp only [converge.go]
    split
    · exact ⟨t, ofArray_iterateArray N e t⟩
    · exact ih (t + 1)

instance (N : Network) : DecidableEq N.system.State := inferInstanceAs (DecidableEq RouterState)

instance (N : Network) (e : Fin N.size → Input) (X : Fin N.size → RouterState) :
    Decidable (N.system.Stable e X) :=
  decidable_of_iff (∀ i, (N.routers[i].update N.routers (N.states X) (e i) : RouterState) = X i) <| by
    constructor
    · intro h; funext i; exact h i
    · intro h i; exact congrFun h i

end LeanBatfish.Model.Network
