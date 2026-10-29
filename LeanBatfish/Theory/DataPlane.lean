import LeanBatfish.Theory.Dynamics

/-!
# Data planes

The control plane computes routes so that routers can forward packets. How a router
forwards depends only on its own state (its forwarding table, and the tunnels it has up),
so the routers' states at a time determine the *data plane* at that time, and a run of a
routing system gives a data plane that changes over time.

A router may rewrite the packets it forwards: a tunnel wraps a packet in an outer header,
and the router at the other end unwraps it. So a hop says both where the packet goes and
what it is when it gets there, and a path follows a packet through its changes.

A packet crosses the data plane of one time: forwarding tables do not change while a
packet is in flight. Isolation *at any time* then says that no packet is ever delivered
whatever the schedule and environment; reachability *at convergence* is about the data
plane of a stable state.
-/

namespace LeanBatfish.Theory

/-- What a router can do with a packet. -/
inductive Hop (n : Nat) (Packet : Type)
  /-- Send packet `p` to router `j`: the packet received, or what the router made of it. -/
  | forward (j : Fin n) (p : Packet)
  /-- Accept it: the packet is addressed to this router. -/
  | accept
  /-- Drop it: there is no route, or the route discards. -/
  | drop
  /-- Send it out of the network, to a host or router that is not modeled. -/
  | exit
  deriving DecidableEq, Repr

/-- A data plane: what each router can do with each packet. Several hops mean the router
may use any of them (equal-cost multipath). -/
abbrev DataPlane (n : Nat) (Packet : Type) := Fin n → Packet → List (Hop n Packet)

namespace DataPlane

variable {n : Nat} {Packet : Type} (F : DataPlane n Packet)

/-- `F.Path i p j q`: packet `p` at router `i` can arrive at router `j` as packet `q`. -/
inductive Path : Fin n → Packet → Fin n → Packet → Prop
  | refl (i : Fin n) (p : Packet) : Path i p i p
  | step {i j k : Fin n} {p q r : Packet} : .forward j q ∈ F i p → Path j q k r → Path i p k r

/-- Packet `p`, starting at router `i`, can be accepted by router `j`. -/
def Delivers (p : Packet) (i j : Fin n) : Prop := ∃ q, F.Path i p j q ∧ .accept ∈ F j q

/-- Packet `p`, starting at router `i`, can leave the network. -/
def Exits (p : Packet) (i : Fin n) : Prop := ∃ j q, F.Path i p j q ∧ .exit ∈ F j q

variable {F}

theorem Path.snoc {i j k : Fin n} {p q r : Packet} (h : F.Path i p j q)
    (hk : .forward k r ∈ F j q) : F.Path i p k r := by
  induction h with
  | refl => exact .step hk (.refl _ _)
  | step hj _ ih => exact .step hj (ih hk)

/-- A property of routers and packets that forwarding preserves holds all along a path. -/
theorem Path.closed {R : Fin n → Packet → Prop}
    (hR : ∀ i p j q, R i p → .forward j q ∈ F i p → R j q) {i j : Fin n} {p q : Packet}
    (h : F.Path i p j q) (hi : R i p) : R j q := by
  induction h with
  | refl => exact hi
  | step hj _ ih => exact ih (hR _ _ _ _ hi hj)

/-- A data plane that may do whatever `F` does has every path `F` has. -/
theorem Path.mono {G : DataPlane n Packet} (hFG : ∀ i p j q, .forward j q ∈ F i p → .forward j q ∈ G i p)
    {i j : Fin n} {p q : Packet} (h : F.Path i p j q) : G.Path i p j q := by
  induction h with
  | refl => exact .refl _ _
  | step hj _ ih => exact .step (hFG _ _ _ _ hj) ih

/-! ## Checking forwarding by computation -/

variable (F)

/-- Where router `i` can send packet `p`, and as what. -/
def next (i : Fin n) (p : Packet) : List (Fin n × Packet) :=
  (F i p).filterMap fun | .forward j q => some (j, q) | _ => none

theorem mem_next {i j : Fin n} {p q : Packet} : (j, q) ∈ F.next i p ↔ .forward j q ∈ F i p := by
  simp only [next, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp at he
    obtain ⟨rfl, rfl⟩ := he
    exact hh
  · intro h; exact ⟨_, h, rfl⟩

/-- The routers and packets a packet can reach from `(i, p)` in at most `k` hops. -/
def reachWithin [DecidableEq Packet] (i : Fin n) (p : Packet) : Nat → List (Fin n × Packet)
  | 0 => [(i, p)]
  | k + 1 =>
    let s := reachWithin i p k
    s ++ (s.flatMap fun x => F.next x.1 x.2).filter (· ∉ s)

theorem path_of_mem_reachWithin [DecidableEq Packet] {i : Fin n} {p : Packet} :
    ∀ {k x}, x ∈ F.reachWithin i p k → F.Path i p x.1 x.2 := by
  intro k
  induction k with
  | zero => intro x h; simp [reachWithin] at h; subst h; exact .refl _ _
  | succ k ih =>
    intro x h
    simp only [reachWithin, List.mem_append, List.mem_filter, List.mem_flatMap] at h
    rcases h with h | ⟨⟨y, hy, hx⟩, _⟩
    · exact ih h
    · exact (ih hy).snoc (F.mem_next.mp hx)

theorem mem_reachWithin_self [DecidableEq Packet] {i : Fin n} {p : Packet} :
    ∀ k, (i, p) ∈ F.reachWithin i p k
  | 0 => by simp [reachWithin]
  | k + 1 => List.mem_append_left _ (mem_reachWithin_self k)

/-- Whether `p`, from router `i`, is accepted by router `j` within `n` hops. -/
def canDeliver [DecidableEq Packet] (p : Packet) (i j : Fin n) : Bool :=
  (F.reachWithin i p n).any fun x => decide (x.1 = j) && decide (.accept ∈ F x.1 x.2)

theorem delivers_of_canDeliver [DecidableEq Packet] {p : Packet} {i j : Fin n}
    (h : F.canDeliver p i j = true) : F.Delivers p i j := by
  simp only [canDeliver, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨x, hx, rfl, hacc⟩ := h
  exact ⟨x.2, F.path_of_mem_reachWithin hx, hacc⟩

/-- Whether `p`, from router `i`, can leave the network within `n` hops. -/
def canExit [DecidableEq Packet] (p : Packet) (i : Fin n) : Bool :=
  (F.reachWithin i p n).any fun x => decide (.exit ∈ F x.1 x.2)

theorem exits_of_canExit [DecidableEq Packet] {p : Packet} {i : Fin n}
    (h : F.canExit p i = true) : F.Exits p i := by
  simp only [canExit, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨x, hx, he⟩ := h
  exact ⟨x.1, x.2, F.path_of_mem_reachWithin hx, he⟩

/-- Whether everything `p` can become, from router `i`, is within `k` hops: what is reached
in `k` hops only forwards to what is reached in `k` hops. -/
def closedWithin [DecidableEq Packet] (i : Fin n) (p : Packet) (k : Nat) : Bool :=
  let R := F.reachWithin i p k
  decide (∀ x ∈ R, ∀ y ∈ F.next x.1 x.2, y ∈ R)

/-- What a closed reach set holds is all a packet can become. -/
theorem mem_reachWithin_of_path [DecidableEq Packet] {i : Fin n} {p : Packet} {k : Nat}
    (hc : F.closedWithin i p k = true) {j : Fin n} {q : Packet} (h : F.Path i p j q) :
    (j, q) ∈ F.reachWithin i p k := by
  simp only [closedWithin, decide_eq_true_eq] at hc
  exact h.closed (R := fun j q => (j, q) ∈ F.reachWithin i p k)
    (fun _ _ _ _ hx hy => hc _ hx _ (F.mem_next.mpr hy)) (F.mem_reachWithin_self k)

/-- Whether `p`, from router `i`, can never be accepted by router `j`: what it can reach is
closed within `n` hops, and nothing of it is accepted by `j`. -/
def cannotDeliver [DecidableEq Packet] (p : Packet) (i j : Fin n) : Bool :=
  F.closedWithin i p n &&
    (F.reachWithin i p n).all fun x => decide (x.1 ≠ j) || decide (.accept ∉ F x.1 x.2)

theorem not_delivers_of_cannotDeliver [DecidableEq Packet] {p : Packet} {i j : Fin n}
    (h : F.cannotDeliver p i j = true) : ¬ F.Delivers p i j := by
  simp only [cannotDeliver, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨hc, hall⟩ := h
  rintro ⟨q, hp, hacc⟩
  rcases hall _ (F.mem_reachWithin_of_path hc hp) with h | h
  · exact h rfl
  · exact h hacc

/-- Whether everything `p` can become from router `i` satisfies `Q`, and every hop it can
take satisfies `E`, checked on the reach set within `k` hops, which must be closed. -/
def checkAlong [DecidableEq Packet] (Q : Fin n → Packet → Bool)
    (E : Fin n → Packet → Fin n → Packet → Bool) (i : Fin n) (p : Packet) (k : Nat) : Bool :=
  F.closedWithin i p k && (F.reachWithin i p k).all fun x =>
    Q x.1 x.2 && (F.next x.1 x.2).all fun y => E x.1 x.2 y.1 y.2

theorem along_of_checkAlong [DecidableEq Packet] {Q : Fin n → Packet → Bool}
    {E : Fin n → Packet → Fin n → Packet → Bool} {i : Fin n} {p : Packet} {k : Nat}
    (h : F.checkAlong Q E i p k = true) {j : Fin n} {q : Packet} (hp : F.Path i p j q) :
    Q j q = true ∧ ∀ j' q', .forward j' q' ∈ F j q → E j q j' q' = true := by
  simp only [checkAlong, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hall⟩ := h
  have := hall _ (F.mem_reachWithin_of_path hc hp)
  exact ⟨this.1, fun j' q' hf => this.2 (j', q') (F.mem_next.mpr hf)⟩

end DataPlane

/-! ## The data plane of a routing system -/

namespace System

variable {n : Nat} (S : System n) {Packet : Type}

/-- The data plane of states `X`, when router `i` in state `x` forwards by `fwd i x`. -/
def dataPlane (fwd : Fin n → S.State → Packet → List (Hop n Packet)) (X : S.States) :
    DataPlane n Packet :=
  fun i => fwd i (X i)

/-- `Q` holds of the data plane at every time, from initial states `X`, for every schedule
and environment. -/
def Always (fwd : Fin n → S.State → Packet → List (Hop n Packet)) (X : S.States)
    (Q : DataPlane n Packet → Prop) : Prop :=
  ∀ ψ env t, Q (S.dataPlane fwd (S.run ψ env X t))

/-- A per-router invariant that guarantees `Q` of the data plane makes `Q` hold at any
time. -/
theorem always_of_invariant (fwd : Fin n → S.State → Packet → List (Hop n Packet))
    (P : Fin n → S.State → Prop) (X : S.States) (hX : ∀ i, P i (X i))
    (hupdate : ∀ i (Y : S.States) x, (∀ k, P k (Y k)) → P i (S.update i Y x))
    (Q : DataPlane n Packet → Prop)
    (hQ : ∀ Y : S.States, (∀ i, P i (Y i)) → Q (S.dataPlane fwd Y)) :
    S.Always fwd X Q :=
  fun ψ env t => hQ _ (fun i => S.run_invariant P X hX hupdate ψ env t i)

/-- What holds of the data plane of a stable state holds forever once the network is
there, whatever the schedule. -/
theorem stable_dataPlane (fwd : Fin n → S.State → Packet → List (Hop n Packet))
    (e : Fin n → S.Input) (X : S.States) (hX : S.Stable e X) (Q : DataPlane n Packet → Prop)
    (hQ : Q (S.dataPlane fwd X)) (ψ : Schedule n) (t : Nat) :
    Q (S.dataPlane fwd (S.run ψ (fun _ => e) X t)) := by
  rw [S.run_stable e X hX ψ t]; exact hQ

end System

end LeanBatfish.Theory
