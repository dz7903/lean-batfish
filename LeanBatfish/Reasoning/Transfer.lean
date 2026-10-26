import LeanBatfish.Model.Router
import LeanBatfish.Reasoning.Accept

/-!
# Which networks routes take as they move

Facts about the functions that carry routes from table to table: they keep the route's
network (OSPF adjacencies, BGP export and import, redistribution), or give it a network
from the configuration (generated routes, aggregates, announcements). When a policy is on
the way, the policy analysis (`LeanBatfish.Policy.accepts_bound`) also bounds the networks
that get through.
-/

namespace LeanBatfish.Reasoning

open Std.Do Policy

set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- What a triple says about an evaluation that succeeds. -/
theorem except_result {α : Type} {x : EvalM α} {Q : α → Prop}
    (h : ⦃⌜True⌝⦄ x ⦃⇓? a => ⌜Q a⌝⦄) {a : α} (hx : x = .ok a) : Q a := by
  subst hx
  have := h True.intro
  have h' : (wp⟦(pure a : Except String α)⟧ (fun a => ⌜Q a⌝, ExceptConds.true)).down := this
  simpa [WP.pure] using h'

/-- A triple about an evaluation from what its successful results satisfy. -/
theorem except_spec {α : Type} {x : EvalM α} {Q : α → Prop} (h : ∀ a, x = .ok a → Q a) :
    ⦃⌜True⌝⦄ x ⦃⇓? a => ⌜Q a⌝⦄ := by
  intro _
  cases hx : x with
  | error e => show (wp⟦(throw e : Except String α)⟧ _).down; simp
  | ok a => show (wp⟦(pure a : Except String α)⟧ _).down; simpa [WP.pure] using h a hx

/-- Running a policy keeps the network (`Policy.process_network`), as a triple. -/
theorem process_spec (ctx : Context) (policy : RoutingPolicy) (output : Route) :
    ⦃⌜True⌝⦄ Policy.process ctx policy output ⦃⇓? o => ⌜o.output.network = output.network⌝⦄ :=
  except_spec fun _ h => Policy.process_network h

/-! ## Collecting -/

theorem mem_collect {α β : Type} {xs : List α} {f : α → EvalM (Array β)} {ys : Array β}
    (h : Model.Router.collect xs f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, ∃ zs, f x = .ok zs ∧ y ∈ zs := by
  induction xs generalizing ys with
  | nil => simp [Model.Router.collect, pure, Except.pure] at h; subst h; simp at hy
  | cons x xs ih =>
    simp only [Model.Router.collect, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i zs hz
      split at h
      · cases h
      · rename_i ws hw
        cases h
        rcases Array.mem_append.mp hy with hy | hy
        · exact ⟨x, by simp, zs, hz, hy⟩
        · obtain ⟨x', hx', zs', hz', hy'⟩ := ih hw hy
          exact ⟨x', by simp [hx'], zs', hz', hy'⟩

/-! ## OSPF -/

/-- A route that keeps its network, or none. -/
abbrev KeepsNet (x : Route) (y : Option Route) : Prop := ∀ z, y = some z → z.network = x.network

theorem sendIntra_network {adj : Ospf.Adjacency} {p : OspfProcess} {x : Route} {y : Option Route}
    (h : Ospf.sendIntra adj p x = .ok y) : KeepsNet x y :=
  except_result (by mvcgen [Ospf.sendIntra, Ospf.adminCost] <;> simp_all +zetaDelta [KeepsNet, Ospf.received, Ospf.inTransit]) h

theorem sendInter_network {adj : Ospf.Adjacency} {a b : Bool} {p : OspfProcess} {x : Route}
    {y : Option Route} (h : Ospf.sendInter adj a b p x = .ok y) : KeepsNet x y :=
  except_result (by mvcgen [Ospf.sendInter, Ospf.adminCost] <;> simp_all +zetaDelta [KeepsNet, Ospf.received, Ospf.inTransit]) h

theorem sendE1_network {adj : Ospf.Adjacency} {p : OspfProcess} {x : Route} {y : Option Route}
    (h : Ospf.sendE1 adj p x = .ok y) : KeepsNet x y :=
  except_result (by mvcgen [Ospf.sendE1, Ospf.adminCost] <;> simp_all +zetaDelta [KeepsNet, Ospf.received, Ospf.inTransit]) h

theorem sendE2_network {adj : Ospf.Adjacency} {p : OspfProcess} {x : Route} {y : Option Route}
    (h : Ospf.sendE2 adj p x = .ok y) : KeepsNet x y :=
  except_result (by mvcgen [Ospf.sendE2, Ospf.adminCost] <;> simp_all +zetaDelta [KeepsNet, Ospf.received, Ospf.inTransit]) h

theorem ospfRedistribute_network {c : Configuration} {p : OspfProcess} {pol : RoutingPolicy}
    {x : Route} {y : Option Route} (h : Ospf.redistribute c p pol x = .ok y) : KeepsNet x y :=
  except_result (by mvcgen [Ospf.redistribute, Ospf.adminCost, process_spec] <;> simp_all +zetaDelta [KeepsNet]) h

/-! ## BGP -/

theorem preExport_network {s : Bgp.Session} {r pre : Route} (h : Bgp.preExport s r = some pre) :
    pre.network = r.network := by
  unfold Bgp.preExport at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpre⟩ := h
  rw [← hpre]

theorem postExport_network (s : Bgp.Session) (nh : Option Ip) (r : Route) :
    (Bgp.postExport s nh r).network = r.network := rfl

/-- The analysis of the policy a run uses bounds the networks it accepts. -/
abbrev PolicyBound (c : Configuration) (name : String) (n : Prefix) : Prop :=
  ∀ P, c.routingPolicies.find? name = some P → (accCall c policyFuel P).safe = true →
    (accCall c policyFuel P).accepted.holds n

/-- What a run of a policy found by name gives: the network is kept, and if the route is
accepted, the policy's analysis bounds the original route's network. -/
theorem process_named {ctx : Context} {name : String} {P : RoutingPolicy} {out : Route}
    {o : Outcome} (hP : ctx.config.routingPolicies.find? name = some P)
    (h : Policy.process ctx P out = .ok o) :
    o.output.network = out.network ∧
      (o.accepted = true → PolicyBound ctx.config name ctx.original.network) := by
  refine ⟨Policy.process_network h, fun hacc Q hQ hs => ?_⟩
  rw [hP] at hQ; cases hQ
  exact Policy.accepts_bound h hacc hs

theorem exportRoute_network {c : Configuration} {s : Bgp.Session} {r y : Route}
    (h : Bgp.exportRoute c s r = .ok (some y)) :
    y.network = r.network ∧ PolicyBound c s.localEnd.af.exportPolicy r.network := by
  unfold Bgp.exportRoute at h
  split at h
  next _ pre hpre =>
    simp only [] at h
    split at h
    next P hP =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i o ho
        have := process_named (ctx := Bgp.policyContext c s .out r) hP ho
        split at h
        · simp [pure, Except.pure] at h
        · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          subst h
          rename_i hacc
          refine ⟨by rw [postExport_network, this.1, preExport_network hpre], ?_⟩
          exact this.2 (by simpa using hacc)
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
  next => simp [pure, Except.pure] at h

/-- Running a policy keeps the network, and if it accepts, the analysis of the policy bounds
the original route's network, under any name the policy has. -/
theorem process_bound_spec (ctx : Context) (P : RoutingPolicy) (out : Route) :
    ⦃⌜True⌝⦄ Policy.process ctx P out
    ⦃⇓? o => ⌜o.output.network = out.network ∧ (o.accepted = true → ∀ name,
      ctx.config.routingPolicies.find? name = some P → PolicyBound ctx.config name ctx.original.network)⌝⦄ :=
  except_spec fun _ h => ⟨Policy.process_network h, fun hacc _ hP => (process_named hP h).2 hacc⟩

theorem importRoute_network {c : Configuration} {s : Bgp.Session} {r y : Route}
    (h : Bgp.importRoute c s r = .ok (some y)) :
    y.network = r.network ∧
      ∀ name, s.localEnd.af.importPolicy = some name → PolicyBound c name r.network := by
  refine except_result (Q := fun y => ∀ z, y = some z → z.network = r.network ∧
      ∀ name, s.localEnd.af.importPolicy = some name → PolicyBound c name r.network) ?_ h y rfl
  mvcgen [Bgp.importRoute, process_bound_spec]
  all_goals simp_all +zetaDelta [Bgp.policyContext]
  · rename_i hnone
    intro name hn P hP _
    rw [hnone name hn] at hP; cases hP
  · rename_i hb hspec
    intro hacc name hn
    obtain ⟨name', hn', hf⟩ := Option.bind_eq_some_iff.mp hb
    rw [hn] at hn'; cases hn'
    first | exact hspec.2 hacc name hf | exact hspec hacc name hf

theorem redistribute_network {c : Configuration} {p : BgpProcess} {pol : RoutingPolicy}
    {mech : OriginMechanism} {r y : Route} (h : Bgp.redistribute c p pol mech r = .ok (some y)) :
    y.network = r.network :=
  except_result (Q := KeepsNet r)
    (by mvcgen [Bgp.redistribute, process_spec] <;> simp_all +zetaDelta [KeepsNet, Bgp.fromMainRib]) h
    y rfl

theorem fromGenerated_network {c : Configuration} {g : Route} {attr : Option RoutingPolicy}
    {rid : Ip} {nh : NextHop} {y : Route} (h : Bgp.fromGenerated c g attr rid nh = .ok y) :
    y.network = g.network :=
  except_result (Q := fun y => y.network = g.network)
    (by mvcgen [Bgp.fromGenerated, process_spec] <;> simp_all +zetaDelta) h

theorem activate_network {c : Configuration} {g : GeneratedRoute} {cs : Array Route} {y : Route}
    (h : g.activate c cs = .ok (some y)) : y.network = g.network := by
  refine except_result (Q := fun y => ∀ z, y = some z → z.network = g.network) ?_ h y rfl
  mvcgen [GeneratedRoute.activate, process_spec]
  invariants
  · Invariant.withEarlyReturnNewDo (onContinue := fun _ _ => ⌜True⌝)
      (onReturn := fun r _ => ⌜∀ z, r = some z → z.network = g.network⌝)
      (onExcept := ExceptConds.true)
  all_goals simp_all +zetaDelta [GeneratedRoute.toRoute]
  all_goals split <;> simp_all

theorem announcementRoute_network {c : Configuration} {p : BgpProcess} {a : Announcement}
    {y : Route} (h : Bgp.announcementRoute c p a = .ok (some y)) : y.network = a.network :=
  except_result (Q := fun y => ∀ z, y = some z → z.network = a.network)
    (by mvcgen [Bgp.announcementRoute, process_spec] <;> simp_all +zetaDelta) h y rfl

theorem fromGenerated_spec (c : Configuration) (g : Route) (attr : Option RoutingPolicy)
    (rid : Ip) (nh : NextHop) :
    ⦃⌜True⌝⦄ Bgp.fromGenerated c g attr rid nh ⦃⇓? y => ⌜y.network = g.network⌝⦄ :=
  except_spec fun _ h => fromGenerated_network h

theorem exportMainRibRoute_network {c : Configuration} {s : Bgp.Session} {r y : Route}
    {attr : Route → Option RoutingPolicy} (h : Bgp.exportMainRibRoute c s r attr = .ok (some y)) :
    y.network = r.network ∧ PolicyBound c s.localEnd.af.exportPolicy r.network := by
  refine except_result (Q := fun y => ∀ z, y = some z →
      z.network = r.network ∧ PolicyBound c s.localEnd.af.exportPolicy r.network) ?_ h y rfl
  mvcgen [Bgp.exportMainRibRoute, process_bound_spec, fromGenerated_spec]
  all_goals simp_all +zetaDelta [Bgp.policyContext, Bgp.fromMainRib, postExport_network]
  all_goals
    rename_i hspec
    exact hspec.2 _ (by assumption)

theorem withPathId_network {ids : Array (Route × Nat)} {r r' y : Route}
    (h : Model.Router.withPathId ids r r' = .ok y) : y.network = r'.network := by
  unfold Model.Router.withPathId at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem mem_of_mergeSort_eq {α : Type} {l : List α} {le : α → α → Bool} {pref suff : List α}
    {x : α} (h : l.mergeSort le = pref ++ x :: suff) : x ∈ l :=
  List.mem_mergeSort.mp (by rw [h]; simp)

theorem aggregateRoutes_network {c : Configuration} {p : BgpProcess} {cur : Array Route}
    {main : Rib} {ys : Array Route} (h : Bgp.aggregateRoutes c p cur main = .ok ys) :
    ∀ y ∈ ys, ∃ a ∈ p.aggregates, y.network = a.network := by
  refine except_result (Q := fun ys => ∀ y ∈ ys, ∃ a ∈ p.aggregates, y.network = a.network) ?_ h
  have hacc : ∀ (c : Configuration) (pol : RoutingPolicy) (r : Route),
      ⦃⌜True⌝⦄ Policy.accepts c pol r ⦃⇓? _ => ⌜True⌝⦄ := fun _ _ _ => except_spec fun _ _ => trivial
  mvcgen [Bgp.aggregateRoutes, process_spec, hacc]
  invariants
  · ⇓? _ => ⌜True⌝
  · ⇓? ⟨_, _, out⟩ => ⌜∀ y ∈ out, ∃ a ∈ p.aggregates, y.network = a.network⌝
  · ⇓? _ => ⌜True⌝
  all_goals simp_all +zetaDelta
  all_goals
    intro y hy
    rcases hy with hy | rfl
    · exact (‹∀ y, y ∈ _ → ∃ a, a ∈ p.aggregates ∧ _› y hy)
    · refine ⟨_, Array.mem_toList_iff.mp (mem_of_mergeSort_eq ‹List.mergeSort _ _ = _›), ?_⟩
      simp_all

end LeanBatfish.Reasoning
