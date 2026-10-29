import LeanBatfish.Reasoning.Confinement

/-!
# Forwarding at any time

The data plane changes as routers update. To prove something of every packet at every time,
whatever the schedule and whatever peers outside the network announce, it is enough to know
every way each router may forward at any time, and to check the property on those ways: a
data plane that may do all of them has every path the real one has
(`Theory.DataPlane.Path.mono`).

Two kinds of routers make those ways few:

* A *static* router (no OSPF, no BGP) computes its main RIB from its own previous main RIB
  alone. From empty tables it goes through a few RIBs and then stays: its *orbit*. At any time
  it holds one of them, with any of its IPsec sessions up or down.
* About any other router nothing is assumed: it may send a packet to any neighbor, accept it,
  drop it or send it out of the network. It must have no tunnels, so that it never changes a
  packet.

`Network.anyTime` is the data plane that does all of that, and `anyTimeCheck` checks that the
routers are of those kinds. Then `along_always` turns a check of a property on `anyTime`
(`Theory.DataPlane.checkAlong`) into the property at every time.
-/

namespace LeanBatfish.Model

/-- A static router's main RIB after an update from main RIB `old`: `Router.step` without
OSPF and BGP. -/
def Router.staticMain (r : Router) (old : Array Route) : EvalM (Array Route) := do
  let stat ← r.activeStatics (Rib.ofRoutes old)
  let gens ← r.generated old
  return mainRib (r.base ++ stat ++ gens ++ #[] ++ (#[] : Array Route).filter (!·.nonRouting))

/-- The main RIBs a static router goes through from empty tables, until one repeats. -/
def Router.orbit (r : Router) (fuel : Nat := 16) : Array (Array Route) :=
  go fuel #[#[]] #[]
where
  go : Nat → Array (Array Route) → Array Route → Array (Array Route)
    | 0, seen, _ => seen
    | fuel + 1, seen, m =>
      match r.staticMain m with
      | .ok m' => if seen.contains m' then seen else go fuel (seen.push m') m'
      | .error _ => seen

/-- Whether the main RIBs `O` include empty tables and whatever an update makes of them. -/
def Router.closedUnder (r : Router) (O : Array (Array Route)) : Bool :=
  O.contains #[] && O.all fun m =>
    match r.staticMain m with
    | .ok m' => O.contains m'
    | .error _ => true

/-- Whether a router never changes a packet: no IPsec sessions and no GRE tunnels. -/
def Router.plain (r : Router) : Bool :=
  r.ipsecLinks.isEmpty && r.config.interfaces.all fun (_, i) => i.tunnelConfig.isNone

/-- The sublists of a list: the ways to keep some of its elements. -/
def sublists : List α → List (List α)
  | [] => [[]]
  | a :: l => (sublists l).map (a :: ·) ++ sublists l

theorem filter_mem_sublists (f : α → Bool) : ∀ l : List α, l.filter f ∈ sublists l
  | [] => by simp [sublists]
  | a :: l => by
    simp only [List.filter_cons, sublists, List.mem_append, List.mem_map]
    split
    · exact Or.inl ⟨_, filter_mem_sublists f l, rfl⟩
    · exact Or.inr (filter_mem_sublists f l)

namespace Network

/-- What router `i` may do with packet `p` at any time. A router `static` selects holds a RIB of
its orbit and any of its IPsec sessions; any other router may forward the packet unchanged to
any neighbor, accept it, drop it or send it out. -/
def anyTime (N : Network) (static : Nat → Bool) : Theory.DataPlane N.size Packet := fun i p =>
  let r := N.routers[i]
  if static i then
    r.orbit.toList.flatMap fun m => (sublists r.ipsecLinks.toList).flatMap fun live =>
      (r.forwardOn m live.toArray wrapFuel p).map N.hop
  else
    r.links.toList.filterMap (fun (_, _, j) =>
      if h : j < N.size then some (.forward ⟨j, h⟩ p) else none) ++ [.accept, .drop, .exit]

/-- The routers `static` selects route statically and stay in their orbits; the others never
change packets. -/
def anyTimeCheck (N : Network) (static : Nat → Bool) : Bool :=
  (List.range N.size).all fun i =>
    match N.routers[i]? with
    | some r => r.index == i &&
      if static i then r.ospf.isNone && r.bgp.isNone && r.closedUnder r.orbit else r.plain
    | none => true

end Network

/-! ## Static routers stay in their orbits -/

theorem staticMain_of_step {net : Array Router} {r : Router} {X : Nat → RouterState}
    {input : Input} {s : RouterState} (ho : r.ospf = none) (hb : r.bgp = none)
    (h : r.step net X input = .ok s) : r.staticMain (X r.index).main = .ok s.main := by
  unfold Router.step at h
  simp only [Router.ospfStep, Router.bgpStep, ho, hb, pure_bind] at h
  obtain ⟨stat, hstat, h⟩ := bind_ok h
  obtain ⟨gens, hgens, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp [Router.staticMain, hstat, hgens, bind, Except.bind, pure, Except.pure]

/-! ## Routers without tunnels never change packets -/

namespace Router

theorem hasGre_of_plain {r : Router} (hp : r.plain = true) (a b : Ip) : r.hasGre a b = false := by
  simp only [plain, Bool.and_eq_true, Array.all_eq_true'] at hp
  simp only [hasGre, Array.any_eq_false']
  intro x hx
  have := hp.2 x hx
  simp_all

theorem greTunnel?_of_plain {r : Router} (hp : r.plain = true) (iface : String) :
    r.greTunnel? iface = none := by
  simp only [plain, Bool.and_eq_true, Array.all_eq_true'] at hp
  simp only [greTunnel?, NameMap.find?]
  cases hf : Array.find? (fun (q : String × Interface) => q.1 == iface) r.config.interfaces with
  | none => rfl
  | some x =>
    have := hp.2 x (Array.mem_of_find?_eq_some hf)
    simp_all

theorem sendOut_cases (r : Router) (iface : String) (arpIp : Option Ip) (p : Packet) :
    r.sendOut iface arpIp p = .exit ∨
      ∃ name ip j, (name, ip, j) ∈ r.links ∧ r.sendOut iface arpIp p = .send j p := by
  unfold sendOut
  simp only []
  cases hf : Array.find? (fun (x : String × Ip × Nat) => x.1 == iface && x.2.1 == arpIp.getD p.dst)
      r.links with
  | none => left; rfl
  | some x =>
    obtain ⟨name, ip, j⟩ := x
    right
    exact ⟨name, ip, j, Array.mem_of_find?_eq_some hf, rfl⟩

/-- A router with no IPsec sessions and no GRE tunnels sends packets on unchanged, to a
router on one of its links. -/
theorem forwardOn_plain {r : Router} (hp : r.plain = true) {main : Array Route} {fuel : Nat}
    {p : Packet} {o : Out} (ho : o ∈ r.forwardOn main #[] fuel p) :
    o = .accept ∨ o = .drop ∨ o = .exit ∨ ∃ name ip j, (name, ip, j) ∈ r.links ∧ o = .send j p := by
  have hl : r.ipsecLinks = #[] := by
    simp only [plain, Bool.and_eq_true, Array.isEmpty_iff] at hp; exact hp.1
  cases fuel with
  | zero => simp [forwardOn] at ho; exact Or.inr (Or.inl ho)
  | succ fuel =>
    unfold forwardOn at ho
    split at ho
    · split at ho
      · simp at ho; exact Or.inl ho
      · simp [hasGre_of_plain hp] at ho; exact Or.inr (Or.inl ho)
      · simp at ho; exact Or.inr (Or.inl ho)
    · split at ho
      · simp at ho; exact Or.inr (Or.inl ho)
      · split at ho
        · simp at ho; exact Or.inr (Or.inl ho)
        · simp only [List.mem_flatMap] at ho
          obtain ⟨a, _, ho⟩ := ho
          cases a with
          | discard => simp at ho; exact Or.inr (Or.inl ho)
          | forward iface arpIp =>
            simp only [greTunnel?_of_plain hp, Option.isSome_none, Bool.false_eq_true,
              ↓reduceIte] at ho
            split at ho
            · -- Out of a tunnel interface, with no session up: dropped.
              right; left
              split at ho
              · simp only [List.find?_toArray, List.find?_nil] at ho; simpa using ho
              · simpa using ho
            · simp only [hl, cryptoEntry?, List.find?_toArray, List.find?_nil] at ho
              have hs : o = r.sendOut iface arpIp p := by
                split at ho <;> simp_all
              rcases sendOut_cases r iface arpIp p with h | ⟨name, ip, j, hj, h⟩
              · exact Or.inr (Or.inr (Or.inl (hs.trans h)))
              · exact Or.inr (Or.inr (Or.inr ⟨name, ip, j, hj, hs.trans h⟩))

end Router

/-! ## Every way to forward, at any time -/

namespace Network

variable {N : Network} {static : Nat → Bool}

/-- What `anyTimeCheck` says of a router. -/
theorem check_router (hc : N.anyTimeCheck static = true) (i : Fin N.size) :
    N.routers[i].index = i ∧
      (static i = true → N.routers[i].ospf = none ∧ N.routers[i].bgp = none ∧
        N.routers[i].closedUnder N.routers[i].orbit = true) ∧
      (static i = false → N.routers[i].plain = true) := by
  have := List.all_eq_true.mp hc i (List.mem_range.mpr i.isLt)
  simp only [Array.getElem?_eq_getElem i.isLt, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨hidx, h⟩ := this
  refine ⟨hidx, fun hs => ?_, fun hs => ?_⟩
  · simp only [hs, ↓reduceIte, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · simpa [hs] using h

/-- A static router holds a main RIB of its orbit. -/
def InOrbit (N : Network) (static : Nat → Bool) (i : Fin N.size) (x : RouterState) : Prop :=
  static i = true → N.routers[i].orbit.contains x.main = true

theorem inOrbit_update (hc : N.anyTimeCheck static = true) (i : Fin N.size)
    (Y : Fin N.size → RouterState) (x : Input) (hY : ∀ k, N.InOrbit static k (Y k)) :
    N.InOrbit static i (N.system.update i Y x) := by
  intro hs
  obtain ⟨hidx, hstatic, _⟩ := check_router hc i
  obtain ⟨ho, hb, hclosed⟩ := hstatic hs
  have hold : N.states Y N.routers[i].index = Y i := by
    rw [hidx]; simp [states]
  have hin := hY i hs
  show N.routers[i].orbit.contains (N.routers[i].updateRoutes N.routers (N.states Y) x).main = true
  unfold Router.updateRoutes
  split
  · rename_i st hst
    have hm := staticMain_of_step ho hb hst
    rw [hold] at hm
    simp only [Router.closedUnder, Bool.and_eq_true, Array.all_eq_true'] at hclosed
    have := hclosed.2 _ (Array.mem_of_contains_eq_true hin)
    rw [hm] at this
    exact this
  · rw [hold]; exact hin

/-- At any time, the static routers hold main RIBs of their orbits. -/
theorem inOrbit_run (hc : N.anyTimeCheck static = true) (ψ : Theory.Schedule N.size)
    (env : N.system.Env) (t : Nat) (i : Fin N.size) :
    N.InOrbit static i (N.system.run ψ env N.init t i) := by
  refine Theory.System.run_invariant _ (N.InOrbit static) N.init ?_
    (fun i Y x hY => inOrbit_update hc i Y x hY) ψ env t i
  intro i hs
  obtain ⟨_, hstatic, _⟩ := check_router hc i
  obtain ⟨_, _, hclosed⟩ := hstatic hs
  simp only [Router.closedUnder, Bool.and_eq_true] at hclosed
  exact hclosed.1

theorem mem_map_hop {outs : List Out} {h : Theory.Hop N.size Packet} (hh : h ∈ outs.map N.hop) :
    ∃ o ∈ outs, N.hop o = h := by
  simpa using hh

/-- When the static routers are in their orbits, `anyTime` may do whatever the data plane
does. -/
theorem hop_anyTime (hc : N.anyTimeCheck static = true) {Y : Fin N.size → RouterState}
    (hY : ∀ i, N.InOrbit static i (Y i)) (i : Fin N.size) (p : Packet)
    {h : Theory.Hop N.size Packet} (hh : h ∈ N.dataPlane Y i p) : h ∈ N.anyTime static i p := by
  obtain ⟨_, _, hplain⟩ := check_router hc i
  change h ∈ (N.routers[i].forwardOn (Y i).main (N.routers[i].live (Y i)) wrapFuel p).map N.hop at hh
  unfold anyTime
  cases hs : static i
  · -- A router that never changes packets.
    have hp := hplain hs
    have hlive : N.routers[i].live (Y i) = #[] := by
      have h1 : N.routers[i].ipsecLinks = #[] := by
        simp only [Router.plain, Bool.and_eq_true, Array.isEmpty_iff] at hp; exact hp.1
      unfold Router.live; rw [h1]; rfl
    rw [hlive] at hh
    obtain ⟨o, ho, rfl⟩ := mem_map_hop hh
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_filterMap,
      List.mem_cons, List.not_mem_nil, or_false]
    rcases Router.forwardOn_plain hp ho with rfl | rfl | rfl | ⟨name, ip, j, hj, rfl⟩
    · simp [hop]
    · simp [hop]
    · simp [hop]
    · by_cases hjn : j < N.size
      · left
        exact ⟨(name, ip, j), Array.mem_toList_iff.mpr hj, by simp [hjn, hop]⟩
      · right; simp [hop, hjn]
  · -- A static router: one RIB of its orbit, some of its sessions up.
    simp only [↓reduceIte, List.mem_flatMap]
    refine ⟨(Y i).main, ?_, (N.routers[i].live (Y i)).toList, ?_, ?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_of_contains_eq_true (hY i hs))
    · simp only [Router.live, Array.toList_filter]
      exact filter_mem_sublists _ _
    · simpa using hh

/-- A property checked on `anyTime` holds at every time, for every schedule and environment:
of everything a packet `p` sent by router `i` becomes, and of every hop it takes. -/
theorem along_always (hc : N.anyTimeCheck static = true) {Q : Fin N.size → Packet → Bool}
    {E : Fin N.size → Packet → Fin N.size → Packet → Bool} {i : Fin N.size} {p : Packet} {k : Nat}
    (hcheck : (N.anyTime static).checkAlong Q E i p k = true)
    (ψ : Theory.Schedule N.size) (env : N.system.Env) (t : Nat) {j : Fin N.size} {q : Packet}
    (hpath : (N.dataPlane (N.system.run ψ env N.init t)).Path i p j q) :
    Q j q = true ∧ ∀ j' q', .forward j' q' ∈ N.dataPlane (N.system.run ψ env N.init t) j q →
      E j q j' q' = true := by
  have hY := inOrbit_run hc ψ env t
  have hpath' := hpath.mono (fun i p j q hf => hop_anyTime hc hY i p hf)
  obtain ⟨hQ, hE⟩ := (N.anyTime static).along_of_checkAlong hcheck hpath'
  exact ⟨hQ, fun j' q' hf => hE j' q' (hop_anyTime hc hY j q hf)⟩

end Network

end LeanBatfish.Model
