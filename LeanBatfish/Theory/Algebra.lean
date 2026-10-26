/-!
# Routing algebras

The algebraic model of routing used by Sobrinho and by Daggitt and Griffin ("Rigorous,
executable, ... routing algebras"; "Formally verified convergence of policy-rich DBF
routing protocols"). A routing algebra has

* a set of routes `S`,
* a *choice* operator `x ⊕ y` picking the preferred of two routes,
* *policies* `f ▷ x` applied to a route as it crosses an edge,
* a *trivial* route `0` (the route from a node to itself) and an *invalid* route `∞`
  (no route).

The laws below are the ones Daggitt and Griffin require of a routing algebra; the
properties after them (increasing, strictly increasing, distributive) are the conditions
under which they prove convergence.
-/

namespace LeanBatfish.Theory

/-- The data of a routing algebra, without laws (a *raw* routing algebra). -/
structure RawAlgebra where
  Route : Type
  /-- Labels of edges; each names a policy. -/
  Policy : Type
  choose : Route → Route → Route
  extend : Policy → Route → Route
  trivial : Route
  invalid : Route

namespace RawAlgebra

variable (A : RawAlgebra)

/-- `x ≤ y`: `x` is preferred to (or as good as) `y`. -/
def Le (x y : A.Route) : Prop := A.choose x y = x

/-- `x < y`: `x` is strictly preferred to `y`. -/
def Lt (x y : A.Route) : Prop := A.Le x y ∧ x ≠ y

end RawAlgebra

/-- The laws of a routing algebra. -/
class IsRoutingAlgebra (A : RawAlgebra) : Prop where
  /-- Choice picks one of its arguments. -/
  choose_sel : ∀ x y, A.choose x y = x ∨ A.choose x y = y
  choose_comm : ∀ x y, A.choose x y = A.choose y x
  choose_assoc : ∀ x y z, A.choose (A.choose x y) z = A.choose x (A.choose y z)
  /-- The trivial route is preferred to every route. -/
  trivial_choose : ∀ x, A.choose A.trivial x = A.trivial
  /-- Every route is preferred to the invalid route. -/
  invalid_choose : ∀ x, A.choose A.invalid x = x
  /-- Extending the invalid route gives the invalid route. -/
  extend_invalid : ∀ f, A.extend f A.invalid = A.invalid

namespace RawAlgebra

variable (A : RawAlgebra)

/-- Policies never make a route better (`x ≤ f ▷ x`). -/
def Increasing : Prop := ∀ f x, A.Le x (A.extend f x)

/-- Policies make every valid route strictly worse. Daggitt and Griffin prove that
distance-vector protocols over finite, strictly increasing algebras converge to a unique
stable state from any starting state, under any fair asynchronous schedule. -/
def StrictlyIncreasing : Prop := ∀ f x, x ≠ A.invalid → A.Lt x (A.extend f x)

/-- Policies distribute over choice. Distributive algebras compute globally optimal routes
(the classic Bellman-Ford setting); BGP's policies are not distributive. -/
def Distributive : Prop := ∀ f x y, A.extend f (A.choose x y) = A.choose (A.extend f x) (A.extend f y)

end RawAlgebra

section Laws

variable {A : RawAlgebra} [IsRoutingAlgebra A]

theorem le_refl (x : A.Route) : A.Le x x := by
  unfold RawAlgebra.Le
  rcases IsRoutingAlgebra.choose_sel (A := A) x x with h | h <;> exact h

theorem le_total (x y : A.Route) : A.Le x y ∨ A.Le y x := by
  unfold RawAlgebra.Le
  rcases IsRoutingAlgebra.choose_sel (A := A) x y with h | h
  · exact Or.inl h
  · right; rw [IsRoutingAlgebra.choose_comm]; exact h

theorem le_antisymm {x y : A.Route} (h₁ : A.Le x y) (h₂ : A.Le y x) : x = y := by
  unfold RawAlgebra.Le at h₁ h₂
  rw [IsRoutingAlgebra.choose_comm] at h₂
  exact h₁.symm.trans h₂

theorem le_trans {x y z : A.Route} (h₁ : A.Le x y) (h₂ : A.Le y z) : A.Le x z := by
  unfold RawAlgebra.Le at *
  calc A.choose x z = A.choose (A.choose x y) z := by rw [h₁]
    _ = A.choose x (A.choose y z) := IsRoutingAlgebra.choose_assoc x y z
    _ = A.choose x y := by rw [h₂]
    _ = x := h₁

theorem trivial_le (x : A.Route) : A.Le A.trivial x := IsRoutingAlgebra.trivial_choose x

theorem le_invalid (x : A.Route) : A.Le x A.invalid := by
  unfold RawAlgebra.Le
  rw [IsRoutingAlgebra.choose_comm]
  exact IsRoutingAlgebra.invalid_choose x

/-- The choice of two routes is preferred to the first. -/
theorem choose_le_left (x y : A.Route) : A.Le (A.choose x y) x := by
  unfold RawAlgebra.Le
  rw [IsRoutingAlgebra.choose_assoc, IsRoutingAlgebra.choose_comm y x,
    ← IsRoutingAlgebra.choose_assoc]
  rcases IsRoutingAlgebra.choose_sel (A := A) x x with h | h <;> rw [h]

theorem choose_le_right (x y : A.Route) : A.Le (A.choose x y) y := by
  rw [IsRoutingAlgebra.choose_comm]; exact choose_le_left y x

end Laws

end LeanBatfish.Theory
