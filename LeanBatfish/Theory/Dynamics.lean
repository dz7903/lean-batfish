import LeanBatfish.Theory.Schedule

/-!
# Routing dynamics

A network of `n` routers, each holding a *state* (its routing tables). A router changes
its state only when it updates, and an update looks at the states of the routers (in
practice its neighbors' and its own) and at what the router receives from outside the
network at that time (its *input*: announcements from external peers, for instance).
This is the setting of Daggitt and Griffin, with Üresin and Dubois's asynchronous
iterations, generalized from routing algebras over adjacency matrices (see
`AlgebraDynamics`) to any per-router update; the states of real protocols, such as a
router's OSPF, BGP and main routing tables, fit it directly.

The behavior of the network is then fixed by three things: the initial states, the
schedule (who updates when, on which information), and the environment (the input each
router gets at each time). A property that holds *at any time* holds for every schedule
and every environment; *converged* properties are about stable states, which no update
changes.
-/

namespace LeanBatfish.Theory

/-- A routing system of `n` routers. -/
structure System (n : Nat) where
  /-- What one router holds. -/
  State : Type
  /-- What one router receives from outside the network at one time. -/
  Input : Type
  /-- Router `i`'s new state, from the current states of the routers and its input. -/
  update : Fin n → (Fin n → State) → Input → State

namespace System

variable {n : Nat} (S : System n)

/-- The states of all routers. -/
abbrev States := Fin n → S.State

/-- An environment: the input of each router at each time. -/
abbrev Env := Nat → Fin n → S.Input

/-- One synchronous step: every router updates on the current states, with input `e`. -/
def step (X : S.States) (e : Fin n → S.Input) : S.States := fun i => S.update i X (e i)

/-- A stable state for a constant input `e`: no update changes any router. -/
def Stable (e : Fin n → S.Input) (X : S.States) : Prop := S.step X e = X

/-- `t` synchronous steps with constant input `e`. -/
def iterate (e : Fin n → S.Input) (X : S.States) : Nat → S.States
  | 0 => X
  | t + 1 => S.step (iterate e X t) e

/-- The states at time `t`, from initial states `X`, under schedule `ψ` and environment
`env`. A router that is not active keeps its state. -/
def run (ψ : Schedule n) (env : S.Env) (X : S.States) : Nat → S.States
  | 0 => X
  | t + 1 => fun i =>
    if ψ.active (t + 1) i then
      S.update i (fun k => run ψ env X (ψ.dataTime (t + 1) i k) k) (env (t + 1) i)
    else run ψ env X t i
termination_by t => t
decreasing_by
  · exact Nat.lt_succ_of_le (ψ.causal _ _ _)
  · exact Nat.lt_succ_self _

/-- The run from `X` under `ψ` and `env` reaches `Y` and stays there. -/
def ConvergesTo (ψ : Schedule n) (env : S.Env) (X Y : S.States) : Prop :=
  ∃ t₀, ∀ t, t₀ ≤ t → S.run ψ env X t = Y

/-- *Absolute convergence* for a constant input `e`: from any states, under any fair
schedule, the network reaches the same stable state. -/
def AbsolutelyConvergent (e : Fin n → S.Input) : Prop :=
  ∃ Y, ∀ ψ : Schedule n, ψ.Fair → ∀ X, S.ConvergesTo ψ (fun _ => e) X Y

/-! ## Results -/

/-- Under the synchronous schedule, the run is the synchronous iteration. -/
theorem run_synchronous (e : Fin n → S.Input) (X : S.States) :
    ∀ t, S.run (Schedule.synchronous n) (fun _ => e) X t = S.iterate e X t := by
  intro t
  induction t with
  | zero => rw [run]; rfl
  | succ t ih =>
    funext i
    rw [run]
    show S.update i (fun k => S.run _ _ X t k) (e i) = S.iterate e X (t + 1) i
    rw [ih]
    rfl

/-- A stable state is absorbing: started there, the network stays there under every
schedule. -/
theorem run_stable (e : Fin n → S.Input) (X : S.States) (hX : S.Stable e X)
    (ψ : Schedule n) : ∀ t, S.run ψ (fun _ => e) X t = X := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    match t with
    | 0 => rw [run]
    | t + 1 =>
      funext i
      rw [run]
      dsimp only
      split
      · have : (fun k => S.run ψ (fun _ => e) X (ψ.dataTime (t + 1) i k) k) = X := by
          funext k
          rw [ih _ (Nat.lt_succ_of_le (ψ.causal t i k))]
        rw [this]
        exact congrFun hX i
      · rw [ih t (Nat.lt_succ_self t)]

/-- If the synchronous iteration reaches a state that one more step leaves unchanged,
that state is stable and the iteration stays there. -/
theorem iterate_stable (e : Fin n → S.Input) (X : S.States) (t : Nat)
    (h : S.step (S.iterate e X t) e = S.iterate e X t) :
    S.Stable e (S.iterate e X t) ∧ ∀ s, t ≤ s → S.iterate e X s = S.iterate e X t := by
  refine ⟨h, fun s hs => ?_⟩
  induction s with
  | zero => have : t = 0 := by omega
            subst this; rfl
  | succ s ih =>
    rcases Nat.lt_or_ge s t with hlt | hge
    · have : t = s + 1 := by omega
      subst this; rfl
    · show S.step (S.iterate e X s) e = _
      rw [ih hge, h]

/-- *Invariants hold at any time.* If every router's initial state satisfies `P`, and an
update keeps `P` whenever all routers satisfy it, whatever the input, then `P` holds of
every router at every time, for every schedule and every environment.

The invariant must be a property of each router separately: an update may combine
states from different times, so a property relating several routers' states at the same
time is not preserved in general. -/
theorem run_invariant (P : Fin n → S.State → Prop) (X : S.States) (hX : ∀ i, P i (X i))
    (hupdate : ∀ i (Y : S.States) x, (∀ k, P k (Y k)) → P i (S.update i Y x))
    (ψ : Schedule n) (env : S.Env) : ∀ t i, P i (S.run ψ env X t i) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    match t with
    | 0 => intro i; rw [run]; exact hX i
    | t + 1 =>
      intro i
      rw [run]
      dsimp only
      split
      · exact hupdate i _ _ fun k => ih _ (Nat.lt_succ_of_le (ψ.causal t i k)) k
      · exact ih t (Nat.lt_succ_self t) i

end System

end LeanBatfish.Theory
