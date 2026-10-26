import LeanBatfish.Reasoning.Policy
import LeanBatfish.Reasoning.Ranges

/-!
# Which networks a policy may accept

An analysis of routing policies: from a policy's statements, a bound on the networks of the
routes it may accept, as a list of network ranges (`Bound`). For a Cisco route map that
permits the prefixes of some prefix lists, the bound is the permit lines of those lists.

The analysis follows the interpreter (`LeanBatfish.Semantics.Policy.Eval`) statement by
statement, with the same fuel. Guards on the route's network give bounds; other guards
(communities, AS paths, ...) give none, so both of their outcomes are allowed. A policy can
also accept through its default action, which statements can set; the analysis assumes the
default actions stay *reject*, and reports whether the statements it analyzed keep them so
(`safe`). The soundness theorem `accepts_bound` says: when the analysis of a policy is safe,
every route the policy accepts has its network in the bound.
-/

namespace LeanBatfish.Policy

open Std.Do

/-- The analysis of statements: bounds on the network of the routes for which they exit with
*true*, and for which they return *true*; and whether they keep the default actions at
*reject*. -/
structure Acc where
  exit : Bound
  ret : Bound
  safe : Bool

namespace Acc

def never : Acc := ⟨Bound.never, Bound.never, true⟩

def or (a b : Acc) : Acc := ⟨a.exit.or b.exit, a.ret.or b.ret, a.safe && b.safe⟩

def anyOf (as : List Acc) : Acc := as.foldr or never

/-- Routes a policy with this analysis accepts: those it exits or returns *true* for. -/
def accepted (a : Acc) : Bound := a.exit.or a.ret

@[simp] theorem anyOf_exit_iff {as : List Acc} {n : Prefix} :
    (anyOf as).exit.holds n ↔ ∃ a ∈ as, a.exit.holds n := by
  induction as with
  | nil => simp [anyOf, never]
  | cons x xs ih => simp only [anyOf, List.foldr_cons, or] at *; simp [ih]

@[simp] theorem anyOf_ret_iff {as : List Acc} {n : Prefix} :
    (anyOf as).ret.holds n ↔ ∃ a ∈ as, a.ret.holds n := by
  induction as with
  | nil => simp [anyOf, never]
  | cons x xs ih => simp only [anyOf, List.foldr_cons, or] at *; simp [ih]

@[simp] theorem anyOf_safe_iff {as : List Acc} : (anyOf as).safe = true ↔ ∀ a ∈ as, a.safe = true := by
  induction as with
  | nil => simp [anyOf, never]
  | cons x xs ih => simp only [anyOf, List.foldr_cons, or] at *; simp [ih]

end Acc

/-- The analysis of a boolean expression: bounds on the network when its value is true, and
when it exits with value true; and whether it keeps the default actions at *reject*. -/
structure EvalAcc where
  value : Bound
  exit : Bound
  safe : Bool

/-- Static statements: returning or exiting with *true* accepts anything; setting a default
action to accept is not analyzed. -/
def staticAcc : StaticStatementType → Acc
  | .returnTrue => ⟨Bound.never, none, true⟩
  | .exitAccept => ⟨none, Bound.never, true⟩
  | .setDefaultActionAccept | .setLocalDefaultActionAccept => ⟨Bound.never, Bound.never, false⟩
  | _ => Acc.never

mutual

def accAll (c : Configuration) : Nat → Array Statement → Acc
  | 0, _ => Acc.never
  | fuel + 1, stmts => Acc.anyOf (stmts.toList.map (accExec c fuel))

def accCall (c : Configuration) : Nat → RoutingPolicy → Acc
  | 0, _ => Acc.never
  | fuel + 1, p => Acc.anyOf (p.statements.toList.map (accExec c fuel))

def accExec (c : Configuration) : Nat → Statement → Acc
  | 0, _ => Acc.never
  | fuel + 1, st =>
    match st with
    | .static t => staticAcc t
    | .ifThen g ts fs =>
      let e := accEval c fuel g
      let a := accAll c fuel ts
      let b := accAll c fuel fs
      ⟨e.exit.or ((e.value.and a.exit).or b.exit), e.exit.or ((e.value.and a.ret).or b.ret),
        e.safe && a.safe && b.safe⟩
    | .call name =>
      -- A called policy that exits makes the caller exit; one that returns does not.
      match c.routingPolicies.find? name with
      | some p => let a := accCall c fuel p; ⟨a.exit, Bound.never, a.safe⟩
      | none => Acc.never
    | .traceable inner => accAll c fuel inner
    | _ => Acc.never

def accEval (c : Configuration) : Nat → BooleanExpr → EvalAcc
  | 0, _ => ⟨Bound.never, Bound.never, true⟩
  | fuel + 1, e =>
    match e with
    | .static .false => ⟨Bound.never, Bound.never, true⟩
    | .static _ => ⟨none, Bound.never, true⟩
    | .call name =>
      match c.routingPolicies.find? name with
      | some p => let a := accCall c fuel p; ⟨a.accepted, a.exit, a.safe⟩
      | none => ⟨Bound.never, Bound.never, true⟩
    | .conjunction es =>
      let xs := es.toList.map (accEval c fuel)
      let exit := Bound.anyOf (xs.map (·.exit))
      ⟨exit.or (Bound.allOf (xs.map (·.value))), exit, xs.all (·.safe)⟩
    | .disjunction es =>
      let xs := es.toList.map (accEval c fuel)
      let exit := Bound.anyOf (xs.map (·.exit))
      ⟨exit.or (Bound.anyOf (xs.map (·.value))), exit, xs.all (·.safe)⟩
    | .not e => let x := accEval c fuel e; ⟨none, x.exit, x.safe⟩
    | .matchPrefixSet ps => ⟨ps.bound c, Bound.never, true⟩
    | .conjunctionChain _ | .firstMatchChain _ | .withEnvironment .. => ⟨none, none, false⟩
    | _ => ⟨none, Bound.never, true⟩

end

/-! ## Soundness -/

set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- The default actions are *reject*. -/
abbrev Rejecting (s : State) : Prop := s.defaultAction = false ∧ s.localDefaultAction = false

/-- The policy runs on a route with network `n`, in configuration `c`. -/
abbrev Runs (n : Prefix) (c : Configuration) (ctx : Context) : Prop :=
  ctx.original.network = n ∧ ctx.config = c

/-- The branch an `If` takes depends on its guard's value. -/
theorem ifThen_branch {c : Configuration} {fuel : Nat} {V : Bound} {ts fs : Array Statement}
    {gv : Bool} {n : Prefix} (hV : gv = true → V.holds n) (sel : Acc → Bound)
    (h : (sel (accAll c fuel (if gv = true then ts else fs))).holds n) :
    (V.and (sel (accAll c fuel ts))).holds n ∨ (sel (accAll c fuel fs)).holds n := by
  cases gv
  · exact Or.inr (by simpa using h)
  · exact Or.inl (Bound.holds_and (hV rfl) (by simpa using h))

set_option maxHeartbeats 4000000 in
/-- The analysis is sound for every part of the interpreter, at every fuel. -/
theorem acc_sound (n : Prefix) (c : Configuration) : ∀ fuel,
    (∀ stmts, ⦃fun ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧ (accAll c fuel stmts).safe = true⌝⦄
      execAll fuel stmts
      ⦃⇓? res ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
        ∀ r, res = some r → (r.exit = true → r.value = true → (accAll c fuel stmts).exit.holds n) ∧
          (r.ret = true → r.value = true → (accAll c fuel stmts).ret.holds n)⌝⦄) ∧
    (∀ p, ⦃fun ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧ (accCall c fuel p).safe = true⌝⦄
      callPolicy fuel p
      ⦃⇓? r ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
        (r.exit = true → r.value = true → (accCall c fuel p).exit.holds n) ∧
        (r.value = true → (accCall c fuel p).accepted.holds n)⌝⦄) ∧
    (∀ st, ⦃fun ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧ (accExec c fuel st).safe = true⌝⦄
      exec fuel st
      ⦃⇓? r ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
        (r.exit = true → r.value = true → (accExec c fuel st).exit.holds n) ∧
        (r.ret = true → r.value = true → (accExec c fuel st).ret.holds n)⌝⦄) ∧
    (∀ e, ⦃fun ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧ (accEval c fuel e).safe = true⌝⦄
      eval fuel e
      ⦃⇓? r ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
        (r.value = true → (accEval c fuel e).value.holds n) ∧
        (r.exit = true → r.value = true → (accEval c fuel e).exit.holds n)⌝⦄) := by
  let F : Frame := fun ctx s => Runs n c ctx ∧ Rejecting s
  have hLong := evalLong_frame F
  have hAdmin := evalAdmin_frame F
  have hNextHop := evalNextHop_frame F
  have hAsList := evalAsList_frame F
  have hLift : ∀ {α : Type} (x : EvalM α),
      ⦃fun ctx s => ⌜F ctx s⌝⦄ liftEval x ⦃⇓? _ ctx s => ⌜F ctx s⌝⦄ :=
    fun x => liftEval_frame F x
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      mvcgen [execAll, callPolicy, exec, eval]
  | succ fuel ih =>
    obtain ⟨hAll, hCall, hExec, hEval⟩ := ih
    refine ⟨fun stmts => ?_, fun p => ?_, fun st => ?_, fun e => ?_⟩
    · mvcgen [execAll, hExec]
      invariants
      · ⇓? ⟨_, b⟩ ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
          ∀ r, b.1 = some (some r) →
            (r.exit = true → r.value = true → (accAll c (fuel + 1) stmts).exit.holds n) ∧
            (r.ret = true → r.value = true → (accAll c (fuel + 1) stmts).ret.holds n)⌝
      all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
      all_goals simp_all +zetaDelta [Runs, Rejecting, accAll]
      rename_i _ h
      exact ⟨fun hx hv => ⟨_, Or.inr (Or.inl rfl), h.2.2.1 hx hv⟩,
        fun hx hv => ⟨_, Or.inr (Or.inl rfl), h.2.2.2 hx hv⟩⟩
    · mvcgen [callPolicy, hExec]
      invariants
      · ⇓? ⟨_, b⟩ ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
          ∀ r, b.1 = some r → (r.exit = true → r.value = true → (accCall c (fuel + 1) p).exit.holds n) ∧
            (r.value = true → (accCall c (fuel + 1) p).accepted.holds n)⌝
      all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
      all_goals simp_all +zetaDelta [Runs, Rejecting, accCall, Acc.accepted]
      · rename_i _ h
        exact ⟨fun hv => ⟨_, Or.inr (Or.inl rfl), h.2.2.1 hv⟩,
          fun hv => Or.inl ⟨_, Or.inr (Or.inl rfl), h.2.2.1 hv⟩⟩
      · rename_i _ h
        exact fun hv => Or.inr ⟨_, Or.inr (Or.inl rfl), h.2.2 hv⟩
    · cases st
      case static t =>
        clear hAll hCall hExec hEval
        cases t <;> mvcgen [exec, staticStatement, startWritingIntermediate] <;>
          simp_all +zetaDelta [Runs, Rejecting, accExec, staticAcc, Acc.never, Bound.holds, Bound.never]
      case ifThen g ts fs =>
        mvcgen [exec, hEval, hAll]
        all_goals simp_all +zetaDelta [Runs, Rejecting, accExec]
        all_goals (try split) <;> (try simp_all)
        rename_i _ _ r2 _ _ _ _ _ _ _ _ hg _ hb
        exact ⟨fun hx hv => Or.inr (ifThen_branch (gv := r2.value) hg.2.2 Acc.exit (hb.2.2.1 hx hv)),
          fun hx hv => Or.inr (ifThen_branch (gv := r2.value) hg.2.2 Acc.ret (hb.2.2.2 hx hv))⟩
      case call name =>
        mvcgen [exec, hCall, lookupPolicy]
        all_goals simp_all +zetaDelta [Runs, Rejecting, accExec]
      case traceable inner =>
        mvcgen [exec, hAll]
        all_goals simp_all +zetaDelta [Runs, Rejecting, accExec]
      all_goals
        mvcgen [exec, write, writeBgp, hLong, hAdmin, hNextHop, hAsList, communityContext, hLift,
          intermediate, readCommunities]
      all_goals simp_all +zetaDelta [Runs, Rejecting, accExec]
    · cases e
      case conjunction es =>
        mvcgen [eval, hEval]
        invariants
        · Invariant.withEarlyReturnNewDo
            (onContinue := fun cur _ ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
              ∀ x ∈ cur.prefix, (accEval c fuel x).value.holds n⌝)
            (onReturn := fun r _ ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
              (r.value = true → (accEval c (fuel + 1) (.conjunction es)).value.holds n) ∧
              (r.exit = true → r.value = true → (accEval c (fuel + 1) (.conjunction es)).exit.holds n)⌝)
            (onExcept := ExceptConds.true)
        all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
        all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]
        · rename_i _ h
          exact ⟨fun hv => Or.inl ⟨_, Or.inr (Or.inl rfl), h.2.2.2 hv⟩,
            fun hv => ⟨_, Or.inr (Or.inl rfl), h.2.2.2 hv⟩⟩
        · rename_i h3 _ _ h
          intro x hx
          rcases hx with hx | rfl
          · exact h3.2.2.2 x hx
          · exact h.2.2
        · rename_i h
          refine Or.inr (Bound.holds_allOf fun b hb => ?_)
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
          exact h.2.2 x (by simpa using hx)
      case disjunction es =>
        mvcgen [eval, hEval]
        invariants
        · Invariant.withEarlyReturnNewDo
            (onContinue := fun _ _ ctx s => ⌜Runs n c ctx ∧ Rejecting s⌝)
            (onReturn := fun r _ ctx s => ⌜Runs n c ctx ∧ Rejecting s ∧
              (r.value = true → (accEval c (fuel + 1) (.disjunction es)).value.holds n) ∧
              (r.exit = true → r.value = true → (accEval c (fuel + 1) (.disjunction es)).exit.holds n)⌝)
            (onExcept := ExceptConds.true)
        all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
        all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]
        · rename_i _ h
          exact ⟨fun hv => Or.inl ⟨_, Or.inr (Or.inl rfl), h.2.2.2 hv⟩,
            fun hv => ⟨_, Or.inr (Or.inl rfl), h.2.2.2 hv⟩⟩
        · rename_i h
          exact Or.inr ⟨_, Or.inr (Or.inl rfl), h.2.2⟩
      case conjunctionChain | firstMatchChain | withEnvironment =>
        intro ctx s h; have := h.2.2; simp only [accEval] at this; cases this
      case static t =>
        cases t <;> mvcgen [eval] <;> simp_all +zetaDelta [Runs, Rejecting, accEval]
      case call name =>
        mvcgen [eval, hCall, lookupPolicy]
        all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
        all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]
      case not e =>
        mvcgen [eval, hEval]
        all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
        all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]
        all_goals split <;> simp_all
      case matchPrefixSet ps =>
        mvcgen [eval]
        all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
        all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]
        · exact PrefixSetExpr.bound_explicit
        · exact PrefixSetExpr.bound_named (by assumption)
      all_goals
        mvcgen [eval, hLong, communityContext, hLift, readTag, readMetric, readLocalPreference,
          readAsPath, readCommunities, intermediate]
      all_goals clear hAll hCall hExec hEval hLong hAdmin hNextHop hAsList hLift
      all_goals simp_all +zetaDelta [Runs, Rejecting, accEval]

/-- What a triple's postcondition says about a run that succeeds. -/
theorem triple_result {α : Type} {x : PolicyM α} {P : Context → State → Prop}
    {Q : α → Context → State → Prop}
    (h : ⦃fun ctx s => ⌜P ctx s⌝⦄ x ⦃⇓? a ctx s => ⌜Q a ctx s⌝⦄) {ctx : Context} {s s' : State}
    {a : α} (hs : P ctx s) (hx : (x.run ctx).run s = .ok (a, s')) : Q a ctx s' := by
  have := h ctx s hs
  simp only [wp, ReaderT.run, StateT.run, PredTrans.apply] at this hx
  unfold PredTrans.pushArg at this
  simp only [StateT.run, Functor.map, PredTrans.apply, PredTrans.bind, PredTrans.pure,
    Function.comp_def, hx] at this
  have h' : (wp⟦(pure (a, s') : Except String (α × State))⟧
      (fun x => ⌜Q x.1 ctx x.2⌝, ExceptConds.true)).down := this
  simpa [WP.pure] using h'

/-- **Soundness of the analysis**: when the analysis of a policy is safe, every route the
policy accepts has its network in the analysis's bound. -/
theorem accepts_bound {ctx : Context} {policy : RoutingPolicy} {output : Route} {o : Outcome}
    (h : process ctx policy output = .ok o) (hacc : o.accepted = true)
    (hsafe : (accCall ctx.config policyFuel policy).safe = true) :
    (accCall ctx.config policyFuel policy).accepted.holds ctx.original.network := by
  simp only [process, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i res hres
    cases h
    simp only [Bool.and_eq_true] at hacc
    have := triple_result ((acc_sound ctx.original.network ctx.config policyFuel).2.1 policy)
      (P := fun ctx' s => Runs ctx.original.network ctx.config ctx' ∧ Rejecting s ∧
        (accCall ctx.config policyFuel policy).safe = true)
      ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hsafe⟩ hres
    exact this.2.2.2 hacc.1

end LeanBatfish.Policy
