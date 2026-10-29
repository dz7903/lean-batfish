import LeanBatfish.Model.Network
import LeanBatfish.Reasoning.Selection
import LeanBatfish.Reasoning.Transfer

/-!
# Confinement: which prefixes a part of the network can ever hold

A *region* of routers is confined to a list of network ranges when, whatever the schedule of
updates and whatever peers outside the network announce, its routers only ever hold routes
for networks in those ranges. `confined_always` proves this from a check computed on the
network (`confinementCheck`): every route a router of the region can originate is in the
ranges, OSPF only reaches it from inside the region, and each BGP session from outside the
region (or from a peer outside the network) passes routes through a policy whose analysis
(`LeanBatfish.Policy.accCall`) bounds them to the ranges.
-/

namespace LeanBatfish.Model

open Reasoning Policy Std.Do

/-- Network `n` is in one of the ranges. -/
def Known (known : List NetRange) (n : Prefix) : Prop := ∃ k ∈ known, k.mem n = true

def knownB (known : List NetRange) (n : Prefix) : Bool := known.any (·.mem n)

theorem knownB_iff {known : List NetRange} {n : Prefix} : knownB known n = true ↔ Known known n := by
  simp [knownB, Known]

/-- The routes of a router's tables. -/
def RouterState.routes (x : RouterState) : Array Route :=
  x.main ++ x.ospfIntra ++ x.ospfInter ++ x.ospfE1 ++ x.ospfE2 ++ x.bgp ++ x.bgpBest

/-- Every route the router holds is for a known network. -/
def Confined (known : List NetRange) (x : RouterState) : Prop :=
  ∀ r ∈ x.routes, Known known r.network

/-! ## Helpers -/

theorem mem_ret_toArray {β : Type} {m : EvalM (Option β)} {ws : Array β} {y : β}
    (h : (do return (← m).toArray : EvalM (Array β)) = .ok ws) (hy : y ∈ ws) : m = .ok (some y) := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok o =>
    rw [hm] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases o <;> simp_all

theorem collect_spec {α β : Type} (xs : List α) (f : α → EvalM (Array β)) :
    ⦃⌜True⌝⦄ Router.collect xs f ⦃⇓? ys => ⌜∀ y ∈ ys, ∃ x ∈ xs, ∃ zs, f x = .ok zs ∧ y ∈ zs⌝⦄ :=
  except_spec fun _ h _ hy => mem_collect h hy

set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- All routes of `rs` are for known networks. -/
def AllKnown (known : List NetRange) (rs : Array Route) : Prop := ∀ y ∈ rs, Known known y.network

namespace AllKnown

variable {known : List NetRange}

@[simp] theorem append {a b : Array Route} :
    AllKnown known (a ++ b) ↔ AllKnown known a ∧ AllKnown known b := by
  simp only [AllKnown, Array.mem_append]
  exact ⟨fun h => ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩,
    fun h y hy => hy.elim (h.1 y) (h.2 y)⟩

@[simp] theorem empty : AllKnown known #[] := by simp [AllKnown]

theorem bestBy {key : Route → Nat × Nat} {rs : Array Route} (h : AllKnown known rs) :
    AllKnown known (Model.bestBy key rs) := fun y hy => h y (mem_bestBy hy)

theorem filter {p : Route → Bool} {rs : Array Route} (h : AllKnown known rs) :
    AllKnown known (rs.filter p) := fun y hy => h y (Array.mem_filter.mp hy).1

theorem mainRib {rs : Array Route} (h : AllKnown known rs) : AllKnown known (Model.mainRib rs) :=
  fun y hy => h y (mem_mainRib hy)

theorem ite {c : Prop} [Decidable c] {a b : Array Route} (ha : AllKnown known a)
    (hb : AllKnown known b) : AllKnown known (if c then a else b) := by
  split <;> assumption

theorem intraToInter {rs : Array Route} (h : AllKnown known rs) :
    AllKnown known (rs.map Ospf.intraToInter) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hy
  exact h x hx

theorem ofConfined {x : RouterState} (h : Confined known x) :
    AllKnown known x.main ∧ AllKnown known x.ospfIntra ∧ AllKnown known x.ospfInter ∧
      AllKnown known x.ospfE1 ∧ AllKnown known x.ospfE2 ∧ AllKnown known x.bgp ∧
      AllKnown known x.bgpBest := by
  have : AllKnown known x.routes := h
  simp only [RouterState.routes, AllKnown.append, and_assoc] at this
  exact this

end AllKnown

/-- Closes goals made of `AllKnown` facts about tables built from known routes. -/
macro "all_known" : tactic => `(tactic|
  repeat' (first
    | with_reducible assumption
    | with_reducible apply And.intro
    | with_reducible rw [AllKnown.append]
    | with_reducible apply AllKnown.bestBy
    | with_reducible apply AllKnown.filter
    | with_reducible apply AllKnown.mainRib
    | with_reducible apply AllKnown.ite
    | with_reducible apply AllKnown.intraToInter
    | with_reducible exact AllKnown.empty))

/-! ## OSPF -/

/-- Routes received over OSPF adjacencies keep their networks, so what neighbors with known
routes send is known. -/
theorem ospfReceived_spec {known : List NetRange} {r : Router} {X : Nat → RouterState}
    {table : RouterState → Array Route} {send : OspfLink → Route → EvalM (Option Route)}
    (hsend : ∀ l x y, send l x = .ok (some y) → y.network = x.network)
    (htable : ∀ l ∈ r.ospfLinks, AllKnown known (table (X l.sender))) :
    ⦃⌜True⌝⦄ r.ospfReceived X table send ⦃⇓? rs => ⌜AllKnown known rs⌝⦄ := by
  refine except_spec fun rs h y hy => ?_
  obtain ⟨l, hl, zs, hzs, hy⟩ := mem_collect h hy
  obtain ⟨x, hx, ws, hws, hy⟩ := mem_collect hzs hy
  rw [hsend l x y (mem_ret_toArray hws hy)]
  exact htable l (Array.mem_toList_iff.mp hl) x (Array.mem_toList_iff.mp hx)

theorem ospfOwn_spec {known : List NetRange} {r : Router} {p : OspfProcess} {old : RouterState}
    (hgen : ∀ g ∈ p.generatedRoutes, Known known g.network) (hold : AllKnown known old.main) :
    ⦃⌜True⌝⦄ r.ospfOwn p old ⦃⇓? rs => ⌜AllKnown known rs⌝⦄ := by
  refine except_spec fun rs h y hy => ?_
  unfold Router.ospfOwn at h
  split at h
  · simp [pure, Except.pure] at h; subst h; simp at hy
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i gens hgens
      obtain ⟨x, hx, ws, hws, hy⟩ := mem_collect h hy
      have := ospfRedistribute_network (mem_ret_toArray hws hy) y rfl
      rw [this]
      have hx : x ∈ old.main ∨ x ∈ gens := by simpa using hx
      rcases hx with hx | hx
      · exact hold x hx
      · obtain ⟨g, hg, zs, hzs, hx⟩ := mem_collect hgens hx
        rw [activate_network (mem_ret_toArray hzs hx)]
        exact hgen g (by simpa using hg)

theorem ospfStep_known {known : List NetRange} {r : Router} {X : Nat → RouterState}
    {old : RouterState} {res : Array Route × Array Route × Array Route × Array Route × Array Route}
    (h : r.ospfStep X old = .ok res)
    (hlocal : AllKnown known r.ospfLocal)
    (hgen : ∀ p, r.ospf = some p → ∀ g ∈ p.generatedRoutes, Known known g.network)
    (hold : Confined known old) (hlinks : ∀ l ∈ r.ospfLinks, Confined known (X l.sender)) :
    AllKnown known res.1 ∧ AllKnown known res.2.1 ∧ AllKnown known res.2.2.1 ∧
      AllKnown known res.2.2.2.1 ∧ AllKnown known res.2.2.2.2 := by
  have hold' := AllKnown.ofConfined hold
  have hl := fun l hl => AllKnown.ofConfined (hlinks l hl)
  cases hp : r.ospf with
  | none =>
    simp only [Router.ospfStep, hp, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | some p =>
    have hIntra := ospfReceived_spec (X := X) (table := (·.ospfIntra))
      (send := fun l x => Ospf.sendIntra l.adj p x) (fun _ _ _ h => sendIntra_network h _ rfl)
      (fun l h => (hl l h).2.1)
    have hInter := ospfReceived_spec (X := X) (table := (·.ospfInter))
      (send := fun l x => Ospf.sendInter l.adj l.senderAbr (Ospf.isAbr p) p x)
      (fun _ _ _ h => sendInter_network h _ rfl) (fun l h => (hl l h).2.2.1)
    have hE1 := ospfReceived_spec (X := X) (table := (·.ospfE1))
      (send := fun l x => do
        return (← Ospf.sendE1 l.adj p x).filter (Ospf.acceptsExternal r.config.hostname ·))
      (fun l x y h => by
        cases he : Ospf.sendE1 l.adj p x with
        | error e => simp [he, bind, Except.bind] at h
        | ok o =>
          simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          exact sendE1_network he y (Option.eq_some_of_filter_eq_some h ▸ by
            cases o <;> simp_all [Option.filter])) (fun l h => (hl l h).2.2.2.1)
    have hE2 := ospfReceived_spec (X := X) (table := (·.ospfE2))
      (send := fun l x => do
        return (← Ospf.sendE2 l.adj p x).filter (Ospf.acceptsExternal r.config.hostname ·))
      (fun l x y h => by
        cases he : Ospf.sendE2 l.adj p x with
        | error e => simp [he, bind, Except.bind] at h
        | ok o =>
          simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          exact sendE2_network he y (Option.eq_some_of_filter_eq_some h ▸ by
            cases o <;> simp_all [Option.filter])) (fun l h => (hl l h).2.2.2.2.1)
    have hOwn := ospfOwn_spec (r := r) (old := old) (hgen p hp) hold'.1
    refine except_result (Q := fun res => AllKnown known res.1 ∧ AllKnown known res.2.1 ∧
      AllKnown known res.2.2.1 ∧ AllKnown known res.2.2.2.1 ∧ AllKnown known res.2.2.2.2) ?_ h
    unfold Router.ospfStep
    simp only [hp]
    mvcgen [hIntra, hInter, hE1, hE2, hOwn]
    obtain ⟨_, _, _, _, _, _, _⟩ := hold'
    all_known

/-! ## BGP -/

theorem bind_ok {α β : Type} {x : EvalM α} {f : α → EvalM β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- The analysis bounds the networks policy `name` of `c` accepts to `known`. The policy must
exist: an undefined export policy makes the export fail, but an undefined import policy
accepts everything. -/
def policyWithin (c : Configuration) (name : String) (known : List NetRange) : Bool :=
  match c.routingPolicies.find? name with
  | some P => (accCall c policyFuel P).safe && (accCall c policyFuel P).accepted.within known
  | none => false

theorem known_of_policyWithin {c : Configuration} {name : String} {known : List NetRange}
    {n : Prefix} (hb : PolicyBound c name n) (hw : policyWithin c name known = true) :
    Known known n := by
  unfold policyWithin at hw
  split at hw
  · rename_i P hP
    simp only [Bool.and_eq_true] at hw
    exact Bound.holds_within (hb P hP hw.1) hw.2
  · cases hw

/-- How the routes a router sends over a session are known: the router holds only known
routes and generates only known ones, or its export policy bounds them. -/
def ExportKnown (known : List NetRange) (k : Router) (ks : RouterState) (s : Bgp.Session) : Prop :=
  (Confined known ks ∧ ∀ g ∈ s.localEnd.peer.generatedRoutes, Known known g.network) ∨
    policyWithin k.config s.localEnd.af.exportPolicy known = true

theorem exportPairs_known {known : List NetRange} {k : Router} {ks : RouterState}
    {s : Bgp.Session} {ps : Array (Route × Route)} (h : k.exportPairs ks s = .ok ps)
    (hk : ExportKnown known k ks s) : ∀ q ∈ ps, Known known q.2.network := by
  intro q hq
  unfold Router.exportPairs at h
  split at h
  case h_2 => simp [pure, Except.pure] at h; subst h; simp at hq
  case h_1 p _ =>
    obtain ⟨fromRib, hrib, h⟩ := bind_ok h
    -- What the main RIB contributes: nothing, or the routes its export collects.
    have hmain : ∃ fromMain, ps = fromRib ++ fromMain ∧ (fromMain = #[] ∨
        Router.collect ks.main.toList (fun r =>
          if r.isBgpRoute = true then pure #[]
          else do
            let o ← Bgp.exportMainRibRoute k.config s r fun g =>
              (Array.find? (fun x => x.network == g.network) k.vrf.generatedRoutes).bind fun gr =>
                gr.attributePolicy.bind k.config.routingPolicies.find?
            pure (Option.map (fun x => (r, x)) o).toArray) = .ok fromMain) := by
      simp only [] at h
      split at h
      · simp [bind, Except.bind, pure, Except.pure] at h
        exact ⟨#[], by simp [h], Or.inl rfl⟩
      · obtain ⟨fromMain, hm, h⟩ := bind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨fromMain, h.symm, Or.inr hm⟩
    obtain ⟨fromMain, rfl, hmain⟩ := hmain
    rcases Array.mem_append.mp hq with hq | hq
    · obtain ⟨r, hr, zs, hzs, hq⟩ := mem_collect hrib hq
      split at hzs
      · obtain ⟨o, ho, hzs⟩ := bind_ok hzs
        simp only [pure, Except.pure, Except.ok.injEq] at hzs
        subst hzs
        cases o with
        | none => simp at hq
        | some r' =>
          simp at hq; subst hq
          obtain ⟨hnet, hb⟩ := exportRoute_network ho
          rw [hnet]
          rcases hk with ⟨hc, _⟩ | hw
          · have := AllKnown.ofConfined hc
            have hr := Array.mem_toList_iff.mp hr
            split at hr
            · rcases mem_exposed hr with hr | hr
              · exact this.2.2.2.2.2.1 r hr
              · exact this.2.2.2.2.2.2 r hr
            · exact this.2.2.2.2.2.2 r hr
          · exact known_of_policyWithin hb hw
      · simp [pure, Except.pure] at hzs; subst hzs; simp at hq
    · rcases hmain with rfl | hmain
      · simp at hq
      · obtain ⟨r, hr, zs, hzs, hq⟩ := mem_collect hmain hq
        split at hzs
        · simp [pure, Except.pure] at hzs; subst hzs; simp at hq
        · obtain ⟨o, ho, hzs⟩ := bind_ok hzs
          simp only [pure, Except.pure, Except.ok.injEq] at hzs
          subst hzs
          cases o with
          | none => simp at hq
          | some r' =>
            simp at hq; subst hq
            obtain ⟨hnet, hb⟩ := exportMainRibRoute_network ho
            rw [hnet]
            rcases hk with ⟨hc, _⟩ | hw
            · exact (AllKnown.ofConfined hc).1 r (Array.mem_toList_iff.mp hr)
            · exact known_of_policyWithin hb hw

theorem mem_dedupInto {sent extra : Array Route} {y : Route}
    (h : y ∈ extra.foldl (fun acc x => if acc.contains x then acc else acc.push x) sent) :
    y ∈ sent ∨ y ∈ extra := by
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_of_step (g := id) (fun acc a x hx => by
      split at hx
      · exact Or.inl hx
      · exact mem_push_step hx) extra.toList sent y h with h | ⟨a, ha, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Array.mem_toList_iff.mp ha)

theorem exports_known {known : List NetRange} {k : Router} {ks : RouterState} {s : Bgp.Session}
    {ys : Array Route} (h : k.exports ks s = .ok ys) (hk : ExportKnown known k ks s) :
    AllKnown known ys := by
  intro y hy
  unfold Router.exports at h
  split at h
  case h_2 => simp [pure, Except.pure] at h; subst h; simp at hy
  case h_1 p _ =>
    obtain ⟨pairs, hpairs, h⟩ := bind_ok h
    obtain ⟨sent, hsent, h⟩ := bind_ok h
    obtain ⟨gens, hgens, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases mem_dedupInto hy with hy | hy
    · obtain ⟨⟨r, r'⟩, hq, zs, hzs, hy⟩ := mem_collect hsent hy
      have hr' := exportPairs_known hpairs hk _ (Array.mem_toList_iff.mp hq)
      simp only [] at hzs
      split at hzs
      · obtain ⟨w, hw, hzs⟩ := bind_ok hzs
        simp only [pure, Except.pure, Except.ok.injEq] at hzs
        subst hzs
        simp at hy; subst hy
        rw [withPathId_network hw]; exact hr'
      · simp [bind, Except.bind, pure, Except.pure] at hzs
        subst hzs
        simp at hy; subst hy
        exact hr'
    · obtain ⟨g, hg, zs, hzs, hy⟩ := mem_collect hgens hy
      obtain ⟨ogr, hgr, hzs⟩ := bind_ok hzs
      cases ogr with
      | none => simp [pure, Except.pure] at hzs; subst hzs; simp at hy
      | some gr =>
        simp only [] at hzs
        obtain ⟨b, hb, hzs⟩ := bind_ok hzs
        obtain ⟨o, ho, hzs⟩ := bind_ok hzs
        simp only [pure, Except.pure, Except.ok.injEq] at hzs
        subst hzs
        cases o with
        | none => simp at hy
        | some y' =>
          simp at hy; subst hy
          obtain ⟨hnet, hbound⟩ := exportRoute_network ho
          rw [hnet, fromGenerated_network hb, activate_network hgr]
          rcases hk with ⟨_, hgk⟩ | hw
          · exact hgk g (Array.mem_toList_iff.mp hg)
          · have := known_of_policyWithin hbound hw
            rwa [fromGenerated_network hb, activate_network hgr] at this

/-- A session with a peer outside the network passes routes through an import policy whose
analysis bounds them to `known`. -/
def ImportKnown (known : List NetRange) (c : Configuration) (s : Bgp.Session) : Prop :=
  ∃ name, s.localEnd.af.importPolicy = some name ∧ policyWithin c name known = true

theorem bgpStep_known {known : List NetRange} {net : Array Router} {r : Router}
    {X : Nat → RouterState} {old : RouterState} {oldMain : Rib} {input : Input}
    {res : Array Route × Array Route} (h : r.bgpStep net X old oldMain input = .ok res)
    (hold : Confined known old)
    (hann : ∀ a ∈ r.announcements, Known known a.network)
    (hagg : ∀ p, r.bgp = some p → ∀ a ∈ p.aggregates, Known known a.network)
    (hlinks : ∀ l ∈ r.bgpLinks, ∀ k, net[l.sender]? = some k →
      ExportKnown known k (X l.sender) l.session.reverse)
    (hext : ∀ e ∈ r.externalPeers, ImportKnown known r.config e.2) :
    AllKnown known res.1 ∧ AllKnown known res.2 := by
  have hold' := AllKnown.ofConfined hold
  unfold Router.bgpStep at h
  split at h
  case h_2 => simp [pure, Except.pure] at h; subst h; simp
  case h_1 p hp =>
    obtain ⟨originated, horig, h⟩ := bind_ok h
    obtain ⟨announced, hannd, h⟩ := bind_ok h
    obtain ⟨received, hrecv, h⟩ := bind_ok h
    obtain ⟨external, hextl, h⟩ := bind_ok h
    obtain ⟨aggs, haggs, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- Every candidate is for a known network.
    have horig' : AllKnown known originated := by
      intro y hy
      obtain ⟨⟨name, mech⟩, _, zs, hzs, hy⟩ := mem_collect horig hy
      simp only [] at hzs
      split at hzs
      · simp [pure, Except.pure] at hzs; subst hzs; simp at hy
      · obtain ⟨x, hx, ws, hws, hy⟩ := mem_collect hzs hy
        rw [redistribute_network (mem_ret_toArray hws hy)]
        exact hold'.1 x (Array.mem_toList_iff.mp hx)
    have hannd' : AllKnown known announced := by
      intro y hy
      obtain ⟨a, ha, zs, hzs, hy⟩ := mem_collect hannd hy
      rw [announcementRoute_network (mem_ret_toArray hzs hy)]
      exact hann a (Array.mem_toList_iff.mp ha)
    have hrecv' : AllKnown known received := by
      intro y hy
      obtain ⟨l, hl, zs, hzs, hy⟩ := mem_collect hrecv hy
      split at hzs
      · rename_i k hk
        obtain ⟨xs, hxs, hzs⟩ := bind_ok hzs
        obtain ⟨x, hx, ws, hws, hy⟩ := mem_collect hzs hy
        rw [(importRoute_network (mem_ret_toArray hws hy)).1]
        exact exports_known hxs (hlinks l (Array.mem_toList_iff.mp hl) k hk) x
          (Array.mem_toList_iff.mp hx)
      · simp [throw, throwThe, MonadExceptOf.throw] at hzs
    have hextl' : AllKnown known external := by
      intro y hy
      obtain ⟨⟨ip, x⟩, he, zs, hzs, hy⟩ := mem_collect hextl hy
      simp only [] at hzs
      split at hzs
      · simp [pure, Except.pure] at hzs; subst hzs; simp at hy
      · rename_i e he'
        have hmem := Array.mem_of_find?_eq_some he'
        obtain ⟨name, hname, hw⟩ := hext _ hmem
        obtain ⟨hnet, hb⟩ := importRoute_network (mem_ret_toArray hzs hy)
        rw [hnet]
        exact known_of_policyWithin (hb name hname) hw
    have haggs' : AllKnown known aggs := by
      intro y hy
      obtain ⟨a, ha, hnet⟩ := aggregateRoutes_network haggs y hy
      rw [hnet]; exact hagg p hp a ha
    -- The RIB keeps only candidates.
    have hcands : AllKnown known (evictSameSource (localBest p originated ++
        (announced ++ received ++ external).filter (fun x => match x.nextHop with
          | .ip nh => x.protocol == .aggregate || Bgp.resolvable oldMain nh
          | _ => true) ++ aggs)) := by
      intro y hy
      have hy := mem_evictSameSource hy
      simp only [Array.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact horig' y (mem_localBest hy)
      · have hy := (Array.mem_filter.mp hy).1
        simp only [Array.mem_append] at hy
        rcases hy with (hy | hy) | hy
        · exact hannd' y hy
        · exact hrecv' y hy
        · exact hextl' y hy
      · exact haggs' y hy
    exact ⟨fun y hy => hcands y (mem_selectBgp (Or.inl hy)),
      fun y hy => hcands y (mem_selectBgp (Or.inr hy))⟩

/-! ## A router's update -/

/-- What the confinement of a router's update needs of the router itself. -/
structure RouterKnown (known : List NetRange) (r : Router) : Prop where
  base : AllKnown known r.base
  statics : AllKnown known r.conditionalStatics
  generated : ∀ g ∈ r.vrf.generatedRoutes, Known known g.network
  ospfLocal : AllKnown known r.ospfLocal
  ospfGenerated : ∀ p, r.ospf = some p → ∀ g ∈ p.generatedRoutes, Known known g.network
  announcements : ∀ a ∈ r.announcements, Known known a.network
  aggregates : ∀ p, r.bgp = some p → ∀ a ∈ p.aggregates, Known known a.network
  external : ∀ e ∈ r.externalPeers, ImportKnown known r.config e.2

theorem activeStatics_known {known : List NetRange} {r : Router} {main : Rib} {ys : Array Route}
    (h : r.activeStatics main = .ok ys) (hs : AllKnown known r.conditionalStatics) :
    AllKnown known ys := by
  intro y hy
  obtain ⟨x, hx, zs, hzs, hy⟩ := mem_collect h hy
  -- Each static route contributes itself or nothing.
  have : y = x := by
    simp only [] at hzs
    split at hzs
    · obtain ⟨_, _, hzs⟩ := bind_ok hzs
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hzs
      subst hzs; split at hy <;> simp_all
    all_goals
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hzs
      subst hzs; split at hy <;> simp_all
  subst this
  exact hs y (Array.mem_toList_iff.mp hx)

theorem generated_known {known : List NetRange} {r : Router} {main ys : Array Route}
    (h : r.generated main = .ok ys) (hg : ∀ g ∈ r.vrf.generatedRoutes, Known known g.network) :
    AllKnown known ys := by
  intro y hy
  unfold Router.generated at h
  split at h
  · simp [pure, Except.pure] at h; subst h; simp at hy
  · obtain ⟨g, hgm, zs, hzs, hy⟩ := mem_collect h hy
    rw [activate_network (mem_ret_toArray hzs hy)]
    exact hg g (Array.mem_toList_iff.mp hgm)

theorem step_known {known : List NetRange} {net : Array Router} {r : Router}
    {X : Nat → RouterState} {input : Input} {st : RouterState}
    (h : r.step net X input = .ok st) (hr : RouterKnown known r)
    (hold : Confined known (X r.index))
    (hospf : ∀ l ∈ r.ospfLinks, Confined known (X l.sender))
    (hbgp : ∀ l ∈ r.bgpLinks, ∀ k, net[l.sender]? = some k →
      ExportKnown known k (X l.sender) l.session.reverse) :
    Confined known st := by
  unfold Router.step at h
  obtain ⟨⟨oi, oe, e1, e2, om⟩, hospfStep, h⟩ := bind_ok h
  have ho := ospfStep_known hospfStep hr.ospfLocal hr.ospfGenerated hold hospf
  simp only [] at h
  obtain ⟨⟨kept, best⟩, hbgpStep, h⟩ := bind_ok h
  have hb := bgpStep_known hbgpStep hold hr.announcements hr.aggregates hbgp hr.external
  simp only [] at h
  obtain ⟨stat, hstat, h⟩ := bind_ok h
  obtain ⟨gens, hgens, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hstat' := activeStatics_known hstat hr.statics
  have hgens' := generated_known hgens hr.generated
  have hbase := hr.base
  obtain ⟨h1, h2, h3, h4, h5⟩ := ho
  obtain ⟨h6, h7⟩ := hb
  show AllKnown known (_ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _)
  all_known
  all_goals
    split
    · intro y hy
      rcases mem_exposed hy with hy | hy
      · exact h6 y hy
      · exact h7 y hy
    · simp

/-! ## The network -/

/-- The checks on a router of the region: what it originates is known, OSPF reaches it only
from the region, and each BGP session into it passes only known routes, because the sender
is in the region or because the sender's export policy (or, for peers outside the network,
the router's import policy) bounds them. -/
def Network.routerCheck (N : Network) (region : Nat → Bool) (known : List NetRange) (r : Router) : Bool :=
  let isKnown (n : Prefix) := knownB known n
  r.base.all (isKnown ·.network) && r.conditionalStatics.all (isKnown ·.network) &&
  r.vrf.generatedRoutes.all (isKnown ·.network) && r.ospfLocal.all (isKnown ·.network) &&
  (match r.ospf with
    | some p => p.generatedRoutes.all (isKnown ·.network)
    | none => true) &&
  r.ospfLinks.all (region ·.sender) &&
  r.announcements.all (isKnown ·.network) &&
  (match r.bgp with
    | some p => p.aggregates.all (isKnown ·.network)
    | none => true) &&
  r.externalPeers.all (fun e => match e.2.localEnd.af.importPolicy with
    | some name => policyWithin r.config name known
    | none => false) &&
  r.bgpLinks.all fun l =>
    match N.routers[l.sender]? with
    | some k =>
      (region l.sender && l.session.reverse.localEnd.peer.generatedRoutes.all (isKnown ·.network)) ||
        policyWithin k.config l.session.reverse.localEnd.af.exportPolicy known
    | none => true

/-- The region of routers selected by `region` is confined to `known` (see `confined_always`). -/
def Network.confinementCheck (N : Network) (region : Nat → Bool) (known : List NetRange) : Bool :=
  (List.range N.size).all fun i =>
    match N.routers[i]? with
    | some r => r.index == i && (!region i || N.routerCheck region known r)
    | none => true

theorem confined_empty {known : List NetRange} : Confined known {} := by
  intro r hr; simp [RouterState.routes] at hr

theorem routerKnown_of_check {N : Network} {region : Nat → Bool} {known : List NetRange}
    {r : Router} (h : N.routerCheck region known r = true) : RouterKnown known r := by
  simp only [Network.routerCheck, Bool.and_eq_true, Array.all_eq_true', knownB_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, hstat⟩, hgen⟩, hlocal⟩, hogen⟩, _⟩, hann⟩, hagg⟩, hext⟩, _⟩ := h
  refine ⟨fun y hy => hbase y hy, fun y hy => hstat y hy, hgen, fun y hy => hlocal y hy, ?_, hann,
    ?_, ?_⟩
  · intro p hp g hg; rw [hp] at hogen; simp only [Array.all_eq_true', knownB_iff] at hogen
    exact hogen g hg
  · intro p hp a ha; rw [hp] at hagg; simp only [Array.all_eq_true', knownB_iff] at hagg
    exact hagg a ha
  · intro e he
    have := hext e he
    split at this
    · exact ⟨_, by assumption, this⟩
    · cases this

/-- **Confinement at any time.** If the check passes, then whatever the schedule and whatever
peers outside the network announce, every router of the region holds only routes for
networks in `known`, at every time. -/
theorem confined_always (N : Network) (region : Nat → Bool) (known : List NetRange)
    (hc : N.confinementCheck region known = true) (ψ : Theory.Schedule N.size)
    (env : N.system.Env) (t : Nat) (i : Fin N.size) (hi : region i = true) :
    Confined known (N.system.run ψ env N.init t i) := by
  refine N.system.run_invariant (fun i x => region i = true → Confined known x) N.init
    (fun _ _ => confined_empty) ?_ ψ env t i hi
  intro j Y x hY hj
  -- The states as routers read them are confined in the region.
  have hstates : ∀ k, region k = true → Confined known (N.states Y k) := by
    intro k hk
    by_cases hks : k < N.size
    · have e : N.states Y k = Y ⟨k, hks⟩ := dite_eq_left_of_eq_true (eq_true hks)
      rw [e]; exact hY _ hk
    · have e : N.states Y k = {} := dite_eq_right_of_eq_false (eq_false hks)
      rw [e]; exact confined_empty
  have hcj : N.routers[j].index = j ∧ (region j = false ∨ N.routerCheck region known N.routers[j]) := by
    have hc' : ∀ x, x < N.size → (match N.routers[x]? with
        | some r => r.index == x && (!region x || N.routerCheck region known r)
        | none => true) = true := by simpa [Network.confinementCheck] using hc
    have := hc' j j.isLt
    simp only [Array.getElem?_eq_getElem j.isLt, Bool.and_eq_true, beq_iff_eq,
      Bool.or_eq_true, Bool.not_eq_true'] at this
    exact this
  obtain ⟨hidx, hcheck⟩ := hcj
  have hcheck : N.routerCheck region known N.routers[j] = true := by
    rcases hcheck with h | h
    · rw [h] at hj; cases hj
    · exact h
  -- IPsec sessions do not hold routes: what counts is the routing update.
  show Confined known (N.routers[j].updateRoutes N.routers (N.states Y) x)
  unfold Router.updateRoutes
  split
  · rename_i st hst
    refine step_known hst (routerKnown_of_check hcheck) ?_ ?_ ?_
    · rw [hidx]; exact hstates j hj
    · intro l hl
      simp only [Network.routerCheck, Bool.and_eq_true, Array.all_eq_true'] at hcheck
      exact hstates _ (hcheck.1.1.1.1.2 l hl)
    · intro l hl k hk
      simp only [Network.routerCheck, Bool.and_eq_true, Array.all_eq_true'] at hcheck
      have := hcheck.2 l hl
      rw [hk] at this
      simp only [Bool.or_eq_true, Bool.and_eq_true, Array.all_eq_true', knownB_iff] at this
      rcases this with ⟨hreg, hgen⟩ | hw
      · exact Or.inl ⟨hstates _ hreg, hgen⟩
      · exact Or.inr hw
  · rw [hidx]; exact hstates j hj

end LeanBatfish.Model
