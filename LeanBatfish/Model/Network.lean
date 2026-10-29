import LeanBatfish.IR.Snapshot
import LeanBatfish.Model.Forwarding
import LeanBatfish.Semantics.Ipsec
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

**The data plane.** A router forwards a packet as `Router.forward` says: by its
destination, through its FIB, wrapping and unwrapping tunneled packets. Packet filters
(ACLs) are not modeled yet.

**Tunnels.** Batfish's layer-3 edges between tunnel interfaces are left out: a tunnel is
not a link here, but packets wrapped and routed through the underlay. The IPsec sessions a
router can have are those Batfish's negotiation establishes in both directions (or with a
dynamic responder); whether each is up is the router's state. Routing protocols over
tunnels are not modeled yet, nor IPsec whose tunnel interface is in another VRF than its
source interface.
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

/-- A router's action as a hop of the network's data plane: a packet sent to a router
that is not in the network leaves it. -/
def hop (N : Network) : Out → Theory.Hop N.size Packet
  | .send j q => if h : j < N.size then .forward ⟨j, h⟩ q else .exit
  | .accept => .accept
  | .drop => .drop
  | .exit => .exit

/-- What router `i` in state `x` does with packet `p`. -/
def forward (N : Network) (i : Fin N.size) (x : RouterState) (p : Packet) :
    List (Theory.Hop N.size Packet) :=
  (N.routers[i].forward x p).map N.hop

/-- The data plane of states `X`. -/
def dataPlane (N : Network) (X : Fin N.size → RouterState) : Theory.DataPlane N.size Packet :=
  N.system.dataPlane N.forward X

/-- In states `X`, packet `p` sent by device `src` can be accepted by device `tgt`
(default VRFs). -/
def Delivers (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src tgt : String) : Prop :=
  ∃ i j, N.find? src = some i ∧ N.find? tgt = some j ∧ (N.dataPlane X).Delivers p i j

/-- In states `X`, packet `p` sent by device `src` is never accepted by device `tgt`. -/
def Isolated (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src tgt : String) : Prop :=
  ∀ i j, N.find? src = some i → N.find? tgt = some j → ¬ (N.dataPlane X).Delivers p i j

/-- In states `X`, packet `p` sent by device `src` can leave the network. -/
def Exits (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src : String) : Prop :=
  ∃ i, N.find? src = some i ∧ (N.dataPlane X).Exits p i

/-- A check of `Exits` by computation. -/
def checkExits (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src : String) : Bool :=
  match N.find? src with
  | some i => (N.dataPlane X).canExit p i
  | none => false

theorem exits_of_check {N : Network} {X : Fin N.size → RouterState} {p : Packet} {src : String}
    (h : N.checkExits X p src = true) : N.Exits X p src := by
  unfold checkExits at h
  split at h
  · rename_i i hi
    exact ⟨i, hi, Theory.DataPlane.exits_of_canExit _ h⟩
  · cases h

/-- A check of `Delivers` by computation. -/
def checkDelivers (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src tgt : String) : Bool :=
  match N.find? src, N.find? tgt with
  | some i, some j => (N.dataPlane X).canDeliver p i j
  | _, _ => false

/-- A check of `Isolated` by computation. -/
def checkIsolated (N : Network) (X : Fin N.size → RouterState) (p : Packet) (src tgt : String) : Bool :=
  match N.find? src, N.find? tgt with
  | some i, some j => (N.dataPlane X).cannotDeliver p i j
  | _, _ => true

theorem delivers_of_check {N : Network} {X : Fin N.size → RouterState} {p : Packet}
    {src tgt : String} (h : N.checkDelivers X p src tgt = true) : N.Delivers X p src tgt := by
  unfold checkDelivers at h
  split at h
  · rename_i i j hi hj
    exact ⟨i, j, hi, hj, Theory.DataPlane.delivers_of_canDeliver _ h⟩
  · cases h

theorem isolated_of_check {N : Network} {X : Fin N.size → RouterState} {p : Packet}
    {src tgt : String} (h : N.checkIsolated X p src tgt = true) : N.Isolated X p src tgt := by
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
  -- Tunnel interfaces, which wrap packets instead of leading somewhere.
  let isTunnel (ni : NodeInterface) : Bool :=
    (iface? ni).any (fun i => i.type == "TUNNEL" || i.tunnelConfig.isSome) ||
      (config? ni.host).any (·.ipsecPeerConfigs.any (·.2.tunnelInterface == some ni.iface))
  -- Forwarding: where each interface leads.
  for e in s.topology.layer3 do
    if isTunnel e.tail || isTunnel e.head then continue
    let (some ti, some hi) := (iface? e.tail, iface? e.head) | continue
    let (some t, some h) := (indexOf e.tail.host ti.vrf, indexOf e.head.host hi.vrf) | continue
    for a in hi.allAddresses do
      routers := routers.modify t fun r => { r with links := r.links.push (ti.name, a.ip, h) }
  -- OSPF adjacencies.
  for e in s.topology.ospf do
    if isTunnel e.tail || isTunnel e.head then throw s!"OSPF over the tunnel {e.tail} is not modeled"
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
    let owner := Array.find? (fun (p : String × Interface) => p.2.allAddresses.any (·.ip == e.headIp))
      hc.interfaces
    if let some (name, _) := owner then
      if isTunnel ⟨e.headHost, name⟩ then throw s!"BGP over the tunnel {e.headHost}[{name}] is not modeled"
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
  -- IPsec sessions: Batfish's negotiation must succeed both ways, or with a dynamic
  -- responder for a crypto map. A route-based session needs tunnel interfaces on both ends.
  let ipsec := Ipsec.topology configs
  let peer? (id : Ipsec.PeerId) : Option (Configuration × IpsecPeerConfig) := do
    let c ← config? id.host
    return (c, ← c.ipsecPeerConfigs.find? id.name)
  let routerOf (c : Configuration) (p : IpsecPeerConfig) : EvalM (Option Nat) := do
    let some src := c.interfaces.find? p.sourceInterface | return none
    if let some t := p.tunnelInterface.bind c.interfaces.find? then
      if t.vrf != src.vrf then
        throw s!"IPsec on {c.hostname}[{t.name}] with its source in another VRF is not modeled"
    return indexOf c.hostname src.vrf
  let link (p : IpsecPeerConfig) (name : String) (remote : Ip) (proposal : IpsecPhase2Proposal)
      (peer : Nat) : IpsecLink :=
    { name, localAddress := p.localAddress, remoteAddress := remote
      tunnelInterface := p.tunnelInterface, sourceInterface := p.sourceInterface
      acl := p.policyAccessList, proposal, peer }
  for e in ipsec do
    let some proposal := e.session.established | continue
    let (some (ic, i), some (rc, r)) := (peer? e.initiator, peer? e.responder) | continue
    let (some ti, some tr) := (← routerOf ic i, ← routerOf rc r) | continue
    match r.kind with
    | .static .. =>
      let back := ipsec.any fun f => f.initiator == e.responder && f.responder == e.initiator &&
        f.session.established.isSome
      if back then
        let l := link i e.initiator.name r.localAddress proposal tr
        routers := routers.modify ti fun x => { x with ipsecLinks := x.ipsecLinks.push l }
    | .dynamic _ =>
      if i.tunnelInterface.isNone then
        let l := link i e.initiator.name r.localAddress proposal tr
        let l' := link r e.responder.name i.localAddress proposal ti
        routers := routers.modify ti fun x => { x with ipsecLinks := x.ipsecLinks.push l }
        routers := routers.modify tr fun x => { x with ipsecLinks := x.ipsecLinks.push l' }
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
