import LeanBatfish.Semantics.Policy.Match

/-!
# Ranges of networks

A *network range* is a set of prefixes given by an IP wildcard on the address and an
interval of lengths, like a line of a route-filter list. Finite lists of ranges describe the
sets of networks that analyses compute (the networks a policy may accept) and that
properties state (the networks a router may hold). Inclusion of ranges is checked by
computation; the bit-level facts behind it are proved bit by bit.

A *bound* is an optional list of ranges: `none` bounds nothing, and `some rs` says that the
network is in one of the ranges `rs`.
-/

namespace LeanBatfish

/-- The prefixes whose address the wildcard contains and whose length is in the interval. -/
structure NetRange where
  wild : IpWildcard
  lens : SubRange
  deriving DecidableEq, Repr, Inhabited

/-! ## Two facts about masks -/

/-- If `x` agrees with `a₁` outside mask `m₁`, `m₁ ⊆ m₂`, and `a₁` agrees with `a₂` outside
`m₂`, then `x` agrees with `a₂` outside `m₂`. -/
theorem UInt32.or_mask_subset (x a1 a2 m1 m2 : UInt32) (h1 : (x ||| m1) = (a1 ||| m1))
    (hm : m1 &&& ~~~m2 = 0) (ha : (a1 ||| m2) = (a2 ||| m2)) : (x ||| m2) = (a2 ||| m2) := by
  rw [← ha]
  apply UInt32.toBitVec_inj.mp
  have h1 := congrArg UInt32.toBitVec h1
  have hm := congrArg UInt32.toBitVec hm
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_not, UInt32.toBitVec_zero] at *
  ext i hi
  have e1 := congrArg (·.getLsbD i) h1
  have e2 := congrArg (·.getLsbD i) hm
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi,
    decide_true, Bool.true_and] at *
  cases hx : x.toBitVec.getLsbD i <;> cases ha1 : a1.toBitVec.getLsbD i <;>
    cases hm1 : m1.toBitVec.getLsbD i <;> cases hm2 : m2.toBitVec.getLsbD i <;> simp_all

/-- Agreeing with `p` under mask `nm` is agreeing with `p` outside `~nm`. -/
theorem UInt32.or_mask_of_and (x p nm : UInt32) (h : (x &&& nm) = p) :
    (x ||| ~~~nm) = ((p &&& ~~~(~~~nm)) ||| ~~~nm) := by
  rw [← h]
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_not, BitVec.getElem_or,
    BitVec.getElem_and, BitVec.getElem_not]
  cases x.toBitVec[i] <;> cases nm.toBitVec[i] <;> simp

namespace NetRange

def mem (r : NetRange) (n : Prefix) : Bool := r.wild.containsIp n.addr && r.lens.contains n.len

/-- The prefix `p`, up to host bits. -/
def ofPrefix (p : Prefix) : NetRange := ⟨IpWildcard.ofPrefix p, ⟨p.len, p.len⟩⟩

/-- The prefixes under `p` with lengths from `lo` to `hi`. -/
def under (p : Prefix) (lo hi : Nat) : NetRange := ⟨IpWildcard.ofPrefix p, ⟨max lo p.len, hi⟩⟩

/-- A sufficient condition for `r ⊆ s`: `s` ignores at least the bits `r` ignores, agrees
with `r` on the others, and allows at least `r`'s lengths. -/
def subset (r s : NetRange) : Bool :=
  r.wild.wildcardMask &&& ~~~s.wild.wildcardMask == 0 &&
  (r.wild.ip.bits ||| s.wild.wildcardMask) == (s.wild.ip.bits ||| s.wild.wildcardMask) &&
  s.lens.lo ≤ r.lens.lo && r.lens.hi ≤ s.lens.hi

theorem mem_of_subset {r s : NetRange} {n : Prefix} (hr : r.mem n = true)
    (h : r.subset s = true) : s.mem n = true := by
  simp only [mem, subset, IpWildcard.containsIp, SubRange.contains, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at *
  obtain ⟨hx, hl1, hl2⟩ := hr
  obtain ⟨⟨⟨hm, ha⟩, hlo⟩, hhi⟩ := h
  exact ⟨UInt32.or_mask_subset _ _ _ _ _ hx hm ha, by omega, by omega⟩

end NetRange

/-- A bound on networks: `none` bounds nothing; `some rs` says the network is in one of `rs`. -/
abbrev Bound := Option (List NetRange)

namespace Bound

def holds : Bound → Prefix → Prop
  | none, _ => True
  | some rs, n => ∃ r ∈ rs, r.mem n = true

/-- Nothing satisfies it. -/
def never : Bound := some []

/-- A network satisfying either bound. -/
def or : Bound → Bound → Bound
  | some a, some b => some (a ++ b.filter (!a.contains ·))
  | _, _ => none

/-- A network satisfying both bounds. -/
def and : Bound → Bound → Bound
  | some a, _ => some a
  | none, b => b

def anyOf (bs : List Bound) : Bound := bs.foldr or never

def allOf (bs : List Bound) : Bound := bs.foldr and none

theorem not_never {n : Prefix} : ¬ never.holds n := by simp [never, holds]

theorem holds_or_left {a b : Bound} {n : Prefix} (h : a.holds n) : (a.or b).holds n := by
  cases a <;> cases b <;> simp_all [or, holds]
  rename_i h; obtain ⟨r, hr, hm⟩ := h; exact ⟨r, Or.inl hr, hm⟩

theorem holds_or_right {a b : Bound} {n : Prefix} (h : b.holds n) : (a.or b).holds n := by
  cases a <;> cases b <;> simp_all [or, holds]
  rename_i a b; obtain ⟨r, hr, hm⟩ := h
  by_cases hra : r ∈ a
  · exact ⟨r, Or.inl hra, hm⟩
  · exact ⟨r, Or.inr ⟨hr, hra⟩, hm⟩

theorem holds_and {a b : Bound} {n : Prefix} (ha : a.holds n) (hb : b.holds n) :
    (a.and b).holds n := by
  cases a <;> simp_all [and]

theorem holds_anyOf {bs : List Bound} {b : Bound} {n : Prefix} (hb : b ∈ bs) (h : b.holds n) :
    (anyOf bs).holds n := by
  induction bs with
  | nil => cases hb
  | cons x xs ih =>
    simp only [anyOf, List.foldr_cons] at *
    rcases List.mem_cons.mp hb with rfl | hb
    · exact holds_or_left h
    · exact holds_or_right (ih hb)

theorem holds_allOf {bs : List Bound} {n : Prefix} (h : ∀ b ∈ bs, b.holds n) :
    (allOf bs).holds n := by
  induction bs with
  | nil => simp [allOf, holds]
  | cons x xs ih =>
    simp only [allOf, List.foldr_cons] at *
    exact holds_and (h x (by simp)) (ih fun b hb => h b (by simp [hb]))

@[simp] theorem holds_never {n : Prefix} : never.holds n ↔ False := by simp [never, holds]

@[simp] theorem holds_none {n : Prefix} : Bound.holds none n ↔ True := by simp [holds]

@[simp] theorem holds_or {a b : Bound} {n : Prefix} : (a.or b).holds n ↔ a.holds n ∨ b.holds n := by
  constructor
  · intro h
    cases a <;> cases b <;> simp_all [or, holds]
    rename_i h; obtain ⟨r, hr, hm⟩ := h
    rcases hr with hr | ⟨hr, _⟩
    · exact Or.inl ⟨r, hr, hm⟩
    · exact Or.inr ⟨r, hr, hm⟩
  · rintro (h | h)
    · exact holds_or_left h
    · exact holds_or_right h

@[simp] theorem holds_anyOf_iff {bs : List Bound} {n : Prefix} :
    (anyOf bs).holds n ↔ ∃ b ∈ bs, b.holds n := by
  induction bs with
  | nil => simp [anyOf]
  | cons x xs ih => simp only [anyOf, List.foldr_cons] at *; simp [ih]

/-- Every network the bound allows is in one of `known`, by range inclusion. -/
def within (b : Bound) (known : List NetRange) : Bool :=
  match b with
  | none => false
  | some rs => rs.all fun r => known.any r.subset

theorem holds_within {b : Bound} {known : List NetRange} {n : Prefix} (h : b.holds n)
    (hw : b.within known = true) : ∃ k ∈ known, k.mem n = true := by
  cases b with
  | none => simp [within] at hw
  | some rs =>
    obtain ⟨r, hr, hm⟩ := h
    simp only [within, List.all_eq_true, List.any_eq_true] at hw
    obtain ⟨k, hk, hs⟩ := hw r hr
    exact ⟨k, hk, NetRange.mem_of_subset hm hs⟩

end Bound

/-! ## Prefix sets as bounds -/

/-- The ranges of the permit lines of a route-filter list. -/
def RouteFilterList.permitRanges (l : RouteFilterList) : List NetRange :=
  (l.lines.toList.filter (·.action == .permit)).map fun line => ⟨line.ipWildcard, line.lengthRange⟩

theorem RouteFilterList.permits_bound {l : RouteFilterList} {n : Prefix} (h : l.permits n = true) :
    ∃ r ∈ l.permitRanges, r.mem n = true := by
  unfold permits at h
  split at h
  · rename_i line hfind
    have hmem := Array.mem_of_find?_eq_some hfind
    have hmatch := Array.find?_some hfind
    refine ⟨⟨line.ipWildcard, line.lengthRange⟩, ?_, ?_⟩
    · simp only [permitRanges, List.mem_map, List.mem_filter]
      exact ⟨line, ⟨Array.mem_toList_iff.mpr hmem, h⟩, rfl⟩
    · simpa [NetRange.mem] using hmatch
  · cases h

/-- A prefix range as a network range. -/
def PrefixRange.toNetRange (r : PrefixRange) : NetRange :=
  ⟨IpWildcard.ofPrefix r.prefix, ⟨max r.lengthRange.lo r.prefix.len, r.lengthRange.hi⟩⟩

theorem PrefixRange.toNetRange_mem {r : PrefixRange} {n : Prefix}
    (h : r.containsPrefix n = true) : r.toNetRange.mem n = true := by
  simp only [containsPrefix, Prefix.containsPrefix, Prefix.containsIp, SubRange.contains,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hip⟩, hlo, hhi⟩ := h
  simp only [toNetRange, NetRange.mem, IpWildcard.ofPrefix, IpWildcard.make,
    IpWildcard.containsIp, SubRange.contains, Bool.and_eq_true, beq_iff_eq]
  have hlen' : r.prefix.len.val ≤ n.len.val := hlen
  refine ⟨?_, decide_eq_true (by show max _ _ ≤ _; omega), decide_eq_true hhi⟩
  exact UInt32.or_mask_of_and _ _ _ hip

/-- The bound a prefix set gives on the networks it matches, in configuration `c`. -/
def PrefixSetExpr.bound (c : Configuration) : PrefixSetExpr → Bound
  | .explicit space => some (space.toList.map PrefixRange.toNetRange)
  | .named name => match c.routeFilterLists.find? name with
    | some l => some l.permitRanges
    | none => Bound.never

end LeanBatfish

namespace LeanBatfish

theorem PrefixSetExpr.bound_explicit {c : Configuration} {space : PrefixSpace} {n : Prefix}
    (h : space.containsPrefix n = true) : (PrefixSetExpr.bound c (.explicit space)).holds n := by
  simp only [PrefixSpace.containsPrefix, Array.any_eq_true] at h
  obtain ⟨i, hi, hr⟩ := h
  exact ⟨_, List.mem_map.mpr ⟨space[i], by simp, rfl⟩, PrefixRange.toNetRange_mem hr⟩

theorem PrefixSetExpr.bound_named {c : Configuration} {name : String} {l : RouteFilterList}
    {n : Prefix} (hl : c.routeFilterLists.find? name = some l) (h : l.permits n = true) :
    (PrefixSetExpr.bound c (.named name)).holds n := by
  simp only [PrefixSetExpr.bound, hl]
  exact RouteFilterList.permits_bound h

end LeanBatfish
