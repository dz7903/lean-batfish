import LeanBatfish.Theory.Algebra
import LeanBatfish.Theory.Dynamics

/-!
# Dynamics over a routing algebra

Daggitt and Griffin's model of distance-vector and path-vector protocols, as a routing
system (`System`).

**Routing states.** A routing state `X` gives, for every router `i` and destination `d`,
the route `X i d` that `i` selects. Daggitt and Griffin take the destinations to be the
routers, with router `d` originating the trivial route to itself (the identity matrix).
Batfish routes to prefixes, which several routers may originate, so here the
destinations are any type, and an origination matrix `O` says what each router
originates for each destination; Daggitt and Griffin's setting is `O = identity`.

**The update `σ`.** A router chooses the best of what it originates and what each
neighbor offers through the policy on the edge:

    σ(X) i d = (⨁ₖ A i k ▷ X k d) ⊕ O i d

**Dynamic networks.** Links and routers come and go: the network is that of the current
*epoch*, which the environment gives as each router's input.
-/

namespace LeanBatfish.Theory

variable {A : RawAlgebra} {n : Nat} {Dest : Type}

/-- A network: for each ordered pair of routers, the policy on the edge from the second to
the first (the route `k` offers is extended by `adj i k` when `i` receives it), or `none`
when there is no edge. -/
structure Network (A : RawAlgebra) (n : Nat) where
  adj : Fin n → Fin n → Option A.Policy

/-- A routing state: the route each router selects for each destination. -/
abbrev RoutingState (A : RawAlgebra) (n : Nat) (Dest : Type) := Fin n → Dest → A.Route

/-- Daggitt and Griffin's origination: router `d` originates the trivial route to itself. -/
def identity (A : RawAlgebra) (n : Nat) : RoutingState A n (Fin n) :=
  fun i d => if i = d then A.trivial else A.invalid

/-- The route offered to `i` by `k` over their edge, or invalid without an edge. -/
def offer (N : Network A n) (i k : Fin n) (x : A.Route) : A.Route :=
  match N.adj i k with
  | some f => A.extend f x
  | none => A.invalid

/-- The best of `m` routes (`⨁`), invalid if there are none. -/
def bigChoose (A : RawAlgebra) : (m : Nat) → (Fin m → A.Route) → A.Route
  | 0, _ => A.invalid
  | m + 1, f => A.choose (f 0) (bigChoose A m (fun k => f k.succ))

/-- The update `σ`. -/
def sigma (N : Network A n) (O : RoutingState A n Dest) (X : RoutingState A n Dest) :
    RoutingState A n Dest :=
  fun i d => A.choose (bigChoose A n (fun k => offer N i k (X k d))) (O i d)

/-- The network as a routing system: a router's state is its row of the routing state,
and it has no input. -/
def Network.system (N : Network A n) (O : RoutingState A n Dest) : System n where
  State := Dest → A.Route
  Input := Unit
  update i X _ := sigma N O X i

/-- A stable state is a fixed point of `σ`. -/
theorem Network.stable_iff (N : Network A n) (O X : RoutingState A n Dest) :
    (N.system O).Stable (fun _ => ()) X ↔ sigma N O X = X := Iff.rfl

/-- A dynamic network: the network and its participating routers in each epoch. -/
structure DynamicNetwork (A : RawAlgebra) (n : Nat) where
  Epoch : Type
  network : Epoch → Network A n
  participates : Epoch → Fin n → Bool

/-- The network of an epoch restricted to its participants. -/
def DynamicNetwork.restricted (D : DynamicNetwork A n) (e : D.Epoch) : Network A n :=
  { adj := fun i k =>
      if D.participates e i && D.participates e k then (D.network e).adj i k else none }

/-- A dynamic network as a routing system whose input is the current epoch. A router that
does not participate falls back to its own originations when it updates. -/
def DynamicNetwork.system (D : DynamicNetwork A n) (O : RoutingState A n Dest) : System n where
  State := Dest → A.Route
  Input := D.Epoch
  update i X e := if D.participates e i then sigma (D.restricted e) O X i else O i

end LeanBatfish.Theory
