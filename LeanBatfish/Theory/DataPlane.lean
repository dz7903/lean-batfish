import LeanBatfish.Theory.Dynamics

/-!
# Data planes

The control plane computes routes so that routers can forward packets. How a router
forwards depends only on its own state (its forwarding table), so the routers' states at
a time determine the *data plane* at that time, and a run of a routing system gives a
data plane that changes over time.

A packet crosses the data plane of one time: forwarding tables do not change while a
packet is in flight. Isolation *at any time* then says that no packet is ever delivered
whatever the schedule and environment; reachability *at convergence* is about the data
plane of a stable state.
-/

namespace LeanBatfish.Theory

/-- What a router can do with a packet. -/
inductive Hop (n : Nat)
  /-- Send it to router `j`. -/
  | forward (j : Fin n)
  /-- Accept it: the packet is addressed to this router. -/
  | accept
  /-- Drop it: there is no route, or the route discards. -/
  | drop
  /-- Send it out of the network, to a host or router that is not modeled. -/
  | exit
  deriving DecidableEq, Repr

/-- A data plane: what each router can do with each packet. Several hops mean the router
may use any of them (equal-cost multipath). -/
abbrev DataPlane (n : Nat) (Packet : Type) := Fin n → Packet → List (Hop n)

namespace DataPlane

variable {n : Nat} {Packet : Type} (F : DataPlane n Packet)

/-- `F.Path p i j`: packet `p` can get from router `i` to router `j`. -/
inductive Path (p : Packet) : Fin n → Fin n → Prop
  | refl (i : Fin n) : Path p i i
  | step {i j k : Fin n} : .forward j ∈ F i p → Path p j k → Path p i k

/-- Packet `p`, starting at router `i`, can be accepted by router `j`. -/
def Delivers (p : Packet) (i j : Fin n) : Prop := F.Path p i j ∧ .accept ∈ F j p

/-- Packet `p`, starting at router `i`, can leave the network. -/
def Exits (p : Packet) (i : Fin n) : Prop := ∃ j, F.Path p i j ∧ .exit ∈ F j p

variable {F}

theorem Path.snoc {p : Packet} {i j k : Fin n} (h : F.Path p i j) (hk : .forward k ∈ F j p) :
    F.Path p i k := by
  induction h with
  | refl i => exact .step hk (.refl k)
  | step hj _ ih => exact .step hj (ih hk)

/-- A set of routers that forwards a packet only among itself keeps the packet. -/
theorem Path.closed {p : Packet} {R : Fin n → Prop}
    (hR : ∀ i j, R i → .forward j ∈ F i p → R j) {i j : Fin n} (h : F.Path p i j) (hi : R i) :
    R j := by
  induction h with
  | refl => exact hi
  | step hj _ ih => exact ih (hR _ _ hi hj)

/-! ## Checking forwarding by computation -/

variable (F)

/-- The routers a packet can be forwarded to by router `i`. -/
def next (p : Packet) (i : Fin n) : List (Fin n) :=
  (F i p).filterMap fun | .forward j => some j | _ => none

theorem mem_next {p : Packet} {i j : Fin n} : j ∈ F.next p i ↔ .forward j ∈ F i p := by
  simp only [next, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp at he
    subst he; exact hh
  · intro h; exact ⟨_, h, rfl⟩

/-- The routers a packet can reach from `i` in at most `k` hops (with repetitions). -/
def reachWithin (p : Packet) (i : Fin n) : Nat → List (Fin n)
  | 0 => [i]
  | k + 1 =>
    let s := reachWithin p i k
    s ++ (s.flatMap (F.next p)).filter (· ∉ s)

theorem path_of_mem_reachWithin {p : Packet} {i : Fin n} :
    ∀ {k j}, j ∈ F.reachWithin p i k → F.Path p i j := by
  intro k
  induction k with
  | zero => intro j h; simp [reachWithin] at h; subst h; exact .refl _
  | succ k ih =>
    intro j h
    simp only [reachWithin, List.mem_append, List.mem_filter, List.mem_flatMap] at h
    rcases h with h | ⟨⟨x, hx, hj⟩, _⟩
    · exact ih h
    · exact (ih hx).snoc (F.mem_next.mp hj)

/-- Whether `p`, from router `i`, is accepted by router `j` within `n` hops. -/
def canDeliver [DecidableEq Packet] (p : Packet) (i j : Fin n) : Bool :=
  decide (j ∈ F.reachWithin p i n) && decide (.accept ∈ F j p)

theorem delivers_of_canDeliver [DecidableEq Packet] {p : Packet} {i j : Fin n}
    (h : F.canDeliver p i j = true) : F.Delivers p i j := by
  simp only [canDeliver, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨F.path_of_mem_reachWithin h.1, h.2⟩

/-- No router in `R` accepts `p`, and `R` is closed under forwarding `p`: then a packet
from a router in `R` is never delivered. -/
theorem not_delivers_of_closed {p : Packet} (R : List (Fin n))
    (hclosed : ∀ x ∈ R, ∀ j ∈ F.next p x, j ∈ R) (hacc : ∀ x ∈ R, .accept ∉ F x p)
    {i j : Fin n} (hi : i ∈ R) : ¬ F.Delivers p i j := by
  rintro ⟨hp, hj⟩
  have := hp.closed (R := (· ∈ R)) (fun x y hx hy => hclosed x hx y (F.mem_next.mpr hy)) hi
  exact hacc j this hj

/-- Whether `p`, from router `i`, can leave the network within `n` hops. -/
def canExit [DecidableEq Packet] (p : Packet) (i : Fin n) : Bool :=
  (F.reachWithin p i n).any fun j => decide (.exit ∈ F j p)

theorem exits_of_canExit [DecidableEq Packet] {p : Packet} {i : Fin n}
    (h : F.canExit p i = true) : F.Exits p i := by
  simp only [canExit, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨j, hj, he⟩ := h
  exact ⟨j, F.path_of_mem_reachWithin hj, he⟩

theorem mem_reachWithin_self {p : Packet} {i : Fin n} : ∀ k, i ∈ F.reachWithin p i k
  | 0 => by simp [reachWithin]
  | k + 1 => List.mem_append_left _ (mem_reachWithin_self k)

/-- Whether `p`, from router `i`, can never be accepted by router `j`: the routers it can
reach in `n` hops are closed under forwarding, and `j` is not one of them or does not
accept it. -/
def cannotDeliver [DecidableEq Packet] (p : Packet) (i j : Fin n) : Bool :=
  let R := F.reachWithin p i n
  decide (∀ x ∈ R, ∀ y ∈ F.next p x, y ∈ R) && (decide (j ∉ R) || decide (.accept ∉ F j p))

theorem not_delivers_of_cannotDeliver [DecidableEq Packet] {p : Packet} {i j : Fin n}
    (h : F.cannotDeliver p i j = true) : ¬ F.Delivers p i j := by
  simp only [cannotDeliver, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hclosed, hj⟩ := h
  rintro ⟨hp, hacc⟩
  have hi : i ∈ F.reachWithin p i n := F.mem_reachWithin_self n
  have := hp.closed (R := (· ∈ F.reachWithin p i n))
    (fun x y hx hy => hclosed x hx y (F.mem_next.mpr hy)) hi
  rcases hj with hj | hj
  · exact hj this
  · exact hj hacc

end DataPlane

/-! ## The data plane of a routing system -/

namespace System

variable {n : Nat} (S : System n) {Packet : Type}

/-- The data plane of states `X`, when router `i` in state `x` forwards by `fwd i x`. -/
def dataPlane (fwd : Fin n → S.State → Packet → List (Hop n)) (X : S.States) :
    DataPlane n Packet :=
  fun i => fwd i (X i)

/-- `Q` holds of the data plane at every time, from initial states `X`, for every schedule
and environment. -/
def Always (fwd : Fin n → S.State → Packet → List (Hop n)) (X : S.States)
    (Q : DataPlane n Packet → Prop) : Prop :=
  ∀ ψ env t, Q (S.dataPlane fwd (S.run ψ env X t))

/-- A per-router invariant that guarantees `Q` of the data plane makes `Q` hold at any
time. -/
theorem always_of_invariant (fwd : Fin n → S.State → Packet → List (Hop n))
    (P : Fin n → S.State → Prop) (X : S.States) (hX : ∀ i, P i (X i))
    (hupdate : ∀ i (Y : S.States) x, (∀ k, P k (Y k)) → P i (S.update i Y x))
    (Q : DataPlane n Packet → Prop) (hQ : ∀ Y : S.States, (∀ i, P i (Y i)) → Q (S.dataPlane fwd Y)) :
    S.Always fwd X Q :=
  fun ψ env t => hQ _ (fun i => S.run_invariant P X hX hupdate ψ env t i)

/-- What holds of the data plane of a stable state holds forever once the network is
there, whatever the schedule. -/
theorem stable_dataPlane (fwd : Fin n → S.State → Packet → List (Hop n))
    (e : Fin n → S.Input) (X : S.States) (hX : S.Stable e X) (Q : DataPlane n Packet → Prop)
    (hQ : Q (S.dataPlane fwd X)) (ψ : Schedule n) (t : Nat) :
    Q (S.dataPlane fwd (S.run ψ (fun _ => e) X t)) := by
  rw [S.run_stable e X hX ψ t]; exact hQ

end System

end LeanBatfish.Theory
