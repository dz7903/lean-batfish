import LeanBatfish.Model.Router

/-!
# Selecting routes keeps routes

The functions that choose routes for a table (`bestBy`, `keepBest`, `selectBgp`, ...) only
choose among the routes they are given. So whatever holds of all candidate routes holds of
the table.
-/

namespace LeanBatfish.Model

/-- A fold that, at each step, keeps some of its routes and possibly adds the element, only
holds routes from its start and the elements. -/
theorem mem_foldl_of_step {α : Type} {f : Array Route → α → Array Route} {g : α → Route}
    (hf : ∀ acc a x, x ∈ f acc a → x ∈ acc ∨ x = g a) :
    ∀ (l : List α) (init : Array Route) x, x ∈ l.foldl f init → x ∈ init ∨ ∃ a ∈ l, x = g a := by
  intro l
  induction l with
  | nil => intro init x h; exact Or.inl h
  | cons a as ih =>
    intro init x h
    rcases ih (f init a) x h with h | ⟨b, hb, rfl⟩
    · rcases hf init a x h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, rfl⟩
    · exact Or.inr ⟨b, by simp [hb], rfl⟩

theorem mem_dedup {rs : Array Route} {x : Route} (h : x ∈ dedup rs) : x ∈ rs := by
  unfold dedup at h
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_of_step (g := id) (fun acc a x hx => by
      split at hx
      · exact Or.inl hx
      · rcases Array.mem_push.mp hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr hx) rs.toList #[] x h with h | ⟨a, ha, rfl⟩
  · simp at h
  · exact Array.mem_toList_iff.mp ha

theorem mem_bestBy {key : Route → Nat × Nat} {rs : Array Route} {x : Route}
    (h : x ∈ bestBy key rs) : x ∈ rs :=
  (Array.mem_filter.mp (mem_dedup h)).1

theorem mem_mainRib {rs : Array Route} {x : Route} (h : x ∈ mainRib rs) : x ∈ rs :=
  (Array.mem_filter.mp (mem_bestBy h)).1

theorem mem_keepBest {cmp : Route → Route → Int} {rs : Array Route} {x : Route}
    (h : x ∈ keepBest cmp rs) : x ∈ rs := by
  unfold keepBest at h
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_of_step (g := id) (fun kept r x hx => by
      try simp only [] at hx
      repeat' split at hx
      all_goals first
        | exact Or.inl hx
        | (simp at hx; exact Or.inr hx)
        | (rcases Array.mem_push.mp hx with hx | hx
           · exact Or.inl hx
           · exact Or.inr hx)) rs.toList #[] x h with h | ⟨a, ha, rfl⟩
  · simp at h
  · exact Array.mem_toList_iff.mp ha

theorem mem_bestPath {cmp : Route → Route → Int} {kept : Array Route} {b : Route}
    (h : bestPath cmp kept = some b) : b ∈ kept := by
  unfold bestPath at h
  cases hk : kept[0]? with
  | none => simp [hk] at h
  | some first =>
    simp only [hk, Option.map_some, Option.some.injEq] at h
    subst h
    rw [← Array.foldl_toList]
    have hfirst : first ∈ kept := Array.mem_of_getElem? hk
    suffices ∀ (l : List Route) (b : Route), b ∈ kept → (∀ x ∈ l, x ∈ kept) →
        l.foldl (fun b r => if cmp r b > 0 then r else b) b ∈ kept from
      this _ _ hfirst fun x hx => Array.mem_toList_iff.mp hx
    intro l
    induction l with
    | nil => intro b hb _; exact hb
    | cons a as ih =>
      intro b hb hl
      simp only [List.foldl_cons]
      apply ih
      · split
        · exact hl a (by simp)
        · exact hb
      · exact fun x hx => hl x (by simp [hx])

theorem mem_push_step {acc : Array Route} {r x : Route} (h : x ∈ acc.push r) : x ∈ acc ∨ x = r :=
  Array.mem_push.mp h

theorem mem_set_step {acc : Array Route} {r x : Route} {i : Nat} (h : x ∈ acc.set! i r) :
    x ∈ acc ∨ x = r := by
  simp only [Array.set!_eq_setIfInBounds] at h
  exact Array.mem_or_eq_of_mem_setIfInBounds h

theorem mem_exposed {st : Bgp.RibSettings} {kept best : Array Route} {x : Route}
    (h : x ∈ exposed st kept best) : x ∈ kept ∨ x ∈ best := by
  unfold exposed at h
  split at h
  · exact Or.inr h
  · rw [← Array.foldl_toList] at h
    rcases mem_foldl_of_step (g := id) (fun acc r x hx => by
        try simp only [] at hx
        repeat' split at hx
        all_goals first
          | exact Or.inl hx
          | exact mem_push_step hx
          | exact mem_set_step hx) kept.toList #[] x h with h | ⟨a, ha, rfl⟩
    · simp at h
    · exact Or.inl (Array.mem_toList_iff.mp ha)

theorem mem_localBest {p : BgpProcess} {rs : Array Route} {x : Route} (h : x ∈ localBest p rs) :
    x ∈ rs := by
  unfold localBest at h
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_of_step (g := id) (fun acc r x hx => by
      try simp only [] at hx
      repeat' split at hx
      all_goals first
        | exact Or.inl hx
        | exact mem_push_step hx
        | exact mem_set_step hx) rs.toList #[] x h with h | ⟨a, ha, rfl⟩
  · simp at h
  · exact Array.mem_toList_iff.mp ha

theorem mem_evictSameSource {rs : Array Route} {x : Route} (h : x ∈ evictSameSource rs) :
    x ∈ rs := by
  unfold evictSameSource at h
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_of_step (g := id) (fun acc r x hx => by
      try simp only [] at hx
      repeat' split at hx
      all_goals first
        | exact mem_push_step hx
        | (rcases Array.mem_push.mp hx with hx | hx
           · exact Or.inl (Array.mem_filter.mp hx).1
           · exact Or.inr hx)) rs.toList #[] x h with h | ⟨a, ha, rfl⟩
  · simp at h
  · exact Array.mem_toList_iff.mp ha

/-- A fold over pairs of route arrays that only adds routes from `S`. -/
theorem mem_foldl_pair {α : Type} {S : Route → Prop}
    {f : Array Route × Array Route → α → Array Route × Array Route}
    (hf : ∀ acc a y, y ∈ (f acc a).1 ∨ y ∈ (f acc a).2 → y ∈ acc.1 ∨ y ∈ acc.2 ∨ S y) :
    ∀ (l : List α) init y, y ∈ (l.foldl f init).1 ∨ y ∈ (l.foldl f init).2 →
      y ∈ init.1 ∨ y ∈ init.2 ∨ S y := by
  intro l
  induction l with
  | nil =>
    intro init y h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | cons a as ih =>
    intro init y h
    rcases ih (f init a) y h with h | h | h
    · exact hf init a y (Or.inl h)
    · exact hf init a y (Or.inr h)
    · exact Or.inr (Or.inr h)

theorem mem_selectBgp {st : Bgp.RibSettings} {main : Rib} {old cands : Array Route} {x : Route}
    (h : x ∈ (selectBgp st main old cands).1 ∨ x ∈ (selectBgp st main old cands).2) :
    x ∈ cands := by
  unfold selectBgp at h
  simp only [] at h
  rw [← Array.foldl_toList] at h
  have := mem_foldl_pair (S := (· ∈ cands)) ?_ _ _ x h
  · simpa using this
  · intro acc p y hy
    -- A route the step adds is among the prefix's candidates.
    have hks : ∀ cmp z, z ∈ keepBest cmp (arrivalOrder old cands p) → z ∈ cands := fun _ z hz => by
      have hz := mem_keepBest hz
      unfold arrivalOrder at hz
      rcases Array.mem_append.mp hz with hz | hz
      · have hz := (Array.mem_filter.mp hz).2
        simp only [Bool.and_eq_true, Array.contains_iff_mem] at hz
        exact (Array.mem_filter.mp (mem_dedup hz.2)).1
      · exact (Array.mem_filter.mp (mem_dedup (Array.mem_filter.mp hz).1)).1
    simp only at hy
    rcases hy with hy | hy
    · rcases Array.mem_append.mp hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inr (hks _ y hy))
    · split at hy
      · rename_i b hb
        rcases Array.mem_push.mp hy with hy | rfl
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (hks _ _ (mem_bestPath hb)))
      · exact Or.inr (Or.inl hy)

end LeanBatfish.Model
