import LeanBatfish.Theory.AlgebraDynamics

/-!
# The shortest-path algebra

Routes are distances (`none` is no route), choice takes the shorter, and an edge adds its
cost. This is the algebra of each kind of OSPF route in Batfish's computation (intra-area,
inter-area, E1); with positive costs it is strictly increasing, which is what makes the
OSPF exchange converge to the same state whatever the order of updates.
-/

namespace LeanBatfish.Theory

/-- Shortest paths with costs in `Nat`. -/
def shortestPath : RawAlgebra where
  Route := Option Nat
  Policy := Nat
  choose x y := match x, y with
    | none, y => y
    | x, none => x
    | some a, some b => some (min a b)
  extend w x := x.map (· + w)
  trivial := some 0
  invalid := none

instance : IsRoutingAlgebra shortestPath where
  choose_sel x y := by
    cases x <;> cases y <;> simp [shortestPath]
    rename_i a b
    by_cases h : a ≤ b
    · left; exact Nat.min_eq_left h
    · right; exact Nat.min_eq_right (by omega)
  choose_comm x y := by
    cases x <;> cases y <;> simp [shortestPath, Nat.min_comm]
  choose_assoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [shortestPath, Nat.min_assoc]
  trivial_choose x := by
    cases x <;> simp [shortestPath]
  invalid_choose x := by
    cases x <;> simp [shortestPath]
  extend_invalid _ := rfl

theorem shortestPath_increasing : shortestPath.Increasing := by
  intro w x
  cases x <;> simp [RawAlgebra.Le, shortestPath]
  omega

/-- With positive costs, every edge makes a route strictly worse. -/
theorem shortestPath_strictlyIncreasing (w : Nat) (hw : 0 < w) (x : shortestPath.Route)
    (hx : x ≠ shortestPath.invalid) :
    shortestPath.Lt x (shortestPath.extend w x) := by
  cases x with
  | none => exact absurd rfl hx
  | some a =>
    constructor
    · simp [RawAlgebra.Le, shortestPath]
    · simp [shortestPath]; omega

/-! ## Checking stability -/

/-- Whether `X` is a fixed point of `σ` is decidable when routes have decidable equality
and there are finitely many destinations: compare `σ X` with `X` entry by entry. -/
instance {A : RawAlgebra} [DecidableEq A.Route] {n m : Nat} (N : Network A n)
    (O X : RoutingState A n (Fin m)) : Decidable (sigma N O X = X) :=
  decidable_of_iff (∀ i : Fin n, ∀ d : Fin m, sigma N O X i d = X i d) <| by
    constructor
    · intro h; funext i d; exact h i d
    · intro h i d; rw [h]

instance : DecidableEq shortestPath.Route := inferInstanceAs (DecidableEq (Option Nat))

/-- A three-router line `0 — 1 — 2` with unit costs, routing to each router. -/
private def line : Network shortestPath 3 :=
  { adj := fun i k => if (i.val + 1 == k.val) || (k.val + 1 == i.val)
      then some (show shortestPath.Policy from (1 : Nat)) else none }

private def lineDistances : RoutingState shortestPath 3 (Fin 3) :=
  fun i d => some (if i.val ≤ d.val then d.val - i.val else i.val - d.val)

example : sigma line (identity shortestPath 3) lineDistances = lineDistances := by decide

example : sigma line (identity shortestPath 3) (identity shortestPath 3) ≠
    identity shortestPath 3 := by decide

/-- Two synchronous steps from the identity reach the distances, which are stable. -/
example : (line.system (identity shortestPath 3)).iterate (fun _ => ())
    (identity shortestPath 3) 2 = lineDistances := by
  show sigma line _ (sigma line _ (identity shortestPath 3)) = lineDistances
  funext i d; revert i d; decide

end LeanBatfish.Theory
