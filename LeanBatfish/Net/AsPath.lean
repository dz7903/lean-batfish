/-!
# AS paths

A BGP AS path is a sequence of segments. Batfish represents each segment as an `AsSet`:
a sorted set of AS numbers plus a flag saying whether it is a confederation segment.
An ordinary AS_SEQUENCE hop is an `AsSet` with a single AS.
-/

namespace LeanBatfish

/-- An AS number (32 bits in practice; Batfish uses Java `long`). -/
abbrev Asn := Nat

structure AsSet where
  /-- The AS numbers, sorted ascending. -/
  asns : Array Asn
  confederation : Bool := false
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace AsSet

def single (asn : Asn) : AsSet := ⟨#[asn], false⟩

/-- Batfish's rendering (`AsSet.toString`), used as input to AS-path regexes:
`65000`, `{1,2}`, `(65000)` for a confederation hop, `[1,2]` for a confederation set. -/
protected def toString (s : AsSet) : String :=
  let body := ",".intercalate (s.asns.toList.map toString)
  match s.confederation, s.asns.size with
  | false, 1 => body
  | false, _ => "{" ++ body ++ "}"
  | true, 1 => "(" ++ body ++ ")"
  | true, _ => "[" ++ body ++ "]"

instance : ToString AsSet := ⟨AsSet.toString⟩

end AsSet

abbrev AsPath := Array AsSet

namespace AsPath

/-- Path length as used in best-path selection and `HasAsPathLength`: the number of
segments, not counting confederation segments (`AsPath.length`). -/
def length (p : AsPath) : Nat := (p.filter (!·.confederation)).size

/-- Batfish's rendering (`AsPath.getAsPathString`): segments separated by spaces. -/
def render (p : AsPath) : String := " ".intercalate (p.toList.map toString)

end AsPath

end LeanBatfish
