/-!
# Sets of natural numbers as unions of intervals

Batfish describes ports, ICMP codes, AS numbers and similar values with `SubRange`
(one closed interval) and `IntegerSpace` / `LongSpace` (a set of numbers written as a
comma-separated list such as `"1,5-10,!7"`). Both are represented here by
`IntervalSet`: a list of closed intervals to include and a list to exclude.
-/

namespace LeanBatfish

/-- A closed interval `[lo, hi]` of natural numbers. Batfish calls this a `SubRange`. -/
structure SubRange where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Hashable, Inhabited, Repr, Ord

namespace SubRange

def contains (r : SubRange) (n : Nat) : Bool := r.lo ≤ n && n ≤ r.hi

def singleton (n : Nat) : SubRange := ⟨n, n⟩

/-- Parse `"a-b"` or `"a"`. -/
def parse? (s : String) : Option SubRange :=
  match (s.trimAscii.toString.splitOn "-").map (·.trimAscii.toString.toNat?) with
  | [some a] => some ⟨a, a⟩
  | [some a, some b] => if a ≤ b then some ⟨a, b⟩ else none
  | _ => none

instance : ToString SubRange where
  toString r := if r.lo == r.hi then toString r.lo else s!"{r.lo}-{r.hi}"

end SubRange

/-- A set of natural numbers: those in some `included` interval and in no `excluded`
interval. -/
structure IntervalSet where
  included : Array SubRange := #[]
  excluded : Array SubRange := #[]
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace IntervalSet

def empty : IntervalSet := {}

def ofRange (r : SubRange) : IntervalSet := { included := #[r] }

def singleton (n : Nat) : IntervalSet := ofRange (.singleton n)

def contains (s : IntervalSet) (n : Nat) : Bool :=
  s.included.any (·.contains n) && !s.excluded.any (·.contains n)

def isEmpty (s : IntervalSet) : Bool := s.included.isEmpty

/-- Parse Batfish's `NumberSpace` string format: comma-separated atoms `a`, `a-b`, or
`!a-b` for exclusion. The empty string is the empty set. -/
def parse? (s : String) : Option IntervalSet := do
  let s := s.trimAscii.toString
  if s.isEmpty then return {}
  (s.splitOn ",").foldlM (init := {}) fun acc atom => do
    let atom := atom.trimAscii.toString
    if atom.startsWith "!" then
      let r ← SubRange.parse? (atom.drop 1).toString
      pure { acc with excluded := acc.excluded.push r }
    else
      let r ← SubRange.parse? atom
      pure { acc with included := acc.included.push r }

end IntervalSet

end LeanBatfish
