/-!
# Schedules

Üresin and Dubois's model of asynchrony, which Daggitt and Griffin use for routing
protocols. Time is discrete. At each time `t` some routers update (`active t i`), and an
update of router `i` uses what each router `k` held at some earlier time
(`dataTime t i k`): messages are delayed, and may be reordered or lost, as long as
information never comes from the future.
-/

namespace LeanBatfish.Theory

/-- An asynchronous schedule for `n` routers. -/
structure Schedule (n : Nat) where
  /-- The routers that update at time `t`. -/
  active : Nat → Fin n → Bool
  /-- `dataTime t i k`: the time of the state of `k` that router `i` uses when it updates
  at time `t`. -/
  dataTime : Nat → Fin n → Fin n → Nat
  causal : ∀ t i k, dataTime (t + 1) i k ≤ t

namespace Schedule

variable {n : Nat}

/-- Every router updates at every time, using the states of the previous time. -/
def synchronous (n : Nat) : Schedule n :=
  { active := fun _ _ => true, dataTime := fun t _ _ => t - 1
    causal := fun t _ _ => by simp }

/-- A fair schedule: every router updates infinitely often, and eventually only uses
information that is arbitrarily recent (Üresin and Dubois's conditions). -/
def Fair (ψ : Schedule n) : Prop :=
  (∀ i t, ∃ t', t < t' ∧ ψ.active t' i = true) ∧
  (∀ i k t, ∃ t', ∀ s, t' ≤ s → t ≤ ψ.dataTime s i k)

end Schedule

end LeanBatfish.Theory
