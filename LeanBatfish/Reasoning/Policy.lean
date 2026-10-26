import Std.Tactic.Do
import LeanBatfish.Semantics.Policy.Eval

/-!
# Routing policies never change the network

A routing policy can rewrite many attributes of the route it writes (metric, communities,
AS path, next hop, ...), but never its network: Batfish has no statement for that. This
file proves it for the interpreter in `LeanBatfish.Semantics.Policy.Eval`, with Hoare
triples (`Std.Do`), by induction on the evaluation's fuel.
-/

namespace LeanBatfish.Policy

open Std.Do

set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- `Spec.throw_Except` with its universe levels fixed: its instance arguments do not
determine them, and `vcgen` leaves them as metavariables. -/
@[spec high] theorem throw_Except' {ε α : Type} (e : ε) (Q : PostCond α (.except ε .pure)) :
    Triple (ps := .except ε .pure) (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) Q :=
  Spec.throw_Except.{0, 0, 0} (m := Id) (ps := .pure)

/-! ## Reading does not change the state

These parts of the interpreter only read the state, so they keep any property `P` of the
context and state. `P` is explicit: `vcgen` cannot infer it, so uses instantiate it. -/

/-- A property of the context and the state. -/
abbrev Frame := Context → State → Prop

theorem liftEval_frame {α : Type} (P : Frame) (x : EvalM α) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ liftEval x ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  mvcgen [liftEval]
  rename_i h
  cases x with
  | ok a =>
    show (wp⟦(pure a : Except String α)⟧ _).down
    simp [WP.pure]; exact h
  | error e =>
    show (wp⟦(throw e : Except String α)⟧ _).down
    simp; exact True.intro

theorem evalAs_frame (P : Frame) (e : AsExpr) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ evalAs e ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  cases e <;> mvcgen [evalAs, session, readAsPath, intermediate] <;> simp_all +zetaDelta

theorem evalLong_frame (P : Frame) (e : LongExpr) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ evalLong e ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  have hAs := evalAs_frame P
  cases e <;> mvcgen [evalLong, evalLong.oldLocalPreference, hAs, intermediate] <;>
    simp_all +zetaDelta

theorem evalAsList_frame (P : Frame) (e : AsPathListExpr) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ evalAsList e ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  have hAs := evalAs_frame P
  cases e
  · simp only [evalAsList, Array.mapM_eq_foldlM]
    mvcgen [hAs]
    invariants
    · ⇓? _ ctx s => ⌜P ctx s⌝
    all_goals simp_all +zetaDelta
  · mvcgen [evalAsList, hAs] <;> simp_all +zetaDelta

theorem evalAdmin_frame (P : Frame) (e : AdminCostExpr) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ evalAdmin e ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  cases e <;> mvcgen [evalAdmin] <;> simp_all +zetaDelta

theorem evalNextHop_frame (P : Frame) (e : NextHopExpr) :
    ⦃fun ctx s => ⌜P ctx s⌝⦄ evalNextHop e ⦃⇓? _ ctx s => ⌜P ctx s⌝⦄ := by
  cases e <;> mvcgen [evalNextHop, session] <;> simp_all +zetaDelta

/-- The output route has network `n`. -/
abbrev Keeps (n : Prefix) : Assertion (.arg Context (.arg State (.except String .pure))) :=
  fun _ s => ⌜s.output.network = n⌝

/-- The frame of `Keeps n`. -/
abbrev keeps (n : Prefix) : Frame := fun _ s => s.output.network = n

/-! ## Statements -/

theorem staticStatement_spec (n : Prefix) (t : StaticStatementType) :
    ⦃Keeps n⦄ staticStatement t ⦃⇓? _ => Keeps n⦄ := by
  cases t <;> mvcgen [staticStatement, startWritingIntermediate] <;>
    simp_all +zetaDelta [Route.modifyBgp]

theorem discard_keeps {α : Type} (n : Prefix) {x : PolicyM α}
    (h : ⦃Keeps n⦄ x ⦃⇓? _ => Keeps n⦄) : ⦃Keeps n⦄ discard x ⦃⇓? _ => Keeps n⦄ := by
  have : discard x = (do let _ ← x; pure ()) := by
    simp [discard, Functor.mapConst]; rfl
  rw [this]
  mvcgen [h]

/-! ## The interpreter -/

/-- Every part of the interpreter keeps the network of the output route. -/
theorem keeps_network (n : Prefix) : ∀ fuel,
    (∀ stmts, ⦃Keeps n⦄ execAll fuel stmts ⦃⇓? _ => Keeps n⦄) ∧
    (∀ p, ⦃Keeps n⦄ callPolicy fuel p ⦃⇓? _ => Keeps n⦄) ∧
    (∀ st, ⦃Keeps n⦄ exec fuel st ⦃⇓? _ => Keeps n⦄) ∧
    (∀ e, ⦃Keeps n⦄ eval fuel e ⦃⇓? _ => Keeps n⦄) ∧
    ⦃Keeps n⦄ callDefaultPolicy fuel ⦃⇓? _ => Keeps n⦄ := by
  have hLong := evalLong_frame (keeps n)
  have hAdmin := evalAdmin_frame (keeps n)
  have hNextHop := evalNextHop_frame (keeps n)
  have hAsList := evalAsList_frame (keeps n)
  have hLift : ∀ {α : Type} (x : EvalM α),
      ⦃fun ctx s => ⌜keeps n ctx s⌝⦄ liftEval x ⦃⇓? _ ctx s => ⌜keeps n ctx s⌝⦄ :=
    fun x => liftEval_frame (keeps n) x
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, ?_⟩ <;>
      mvcgen [execAll, callPolicy, exec, eval, callDefaultPolicy]
  | succ fuel ih =>
    obtain ⟨hAll, hCall, hExec, hEval, hDef⟩ := ih
    refine ⟨fun stmts => ?_, fun p => ?_, fun st => ?_, fun e => ?_, ?_⟩
    · mvcgen [execAll, hExec]
      all_goals first | exact (⇓? _ => Keeps n) | skip
      all_goals simp_all +zetaDelta
    · mvcgen [callPolicy, hExec]
      all_goals first | exact (⇓? _ => Keeps n) | skip
      all_goals simp_all +zetaDelta
    · cases st <;> mvcgen [exec, hAll, hCall, hEval, staticStatement_spec, write, writeBgp,
        lookupPolicy, hLong, hAdmin, hNextHop, hAsList, communityContext, hLift, readCommunities,
        intermediate]
      all_goals first | exact (⇓? _ => Keeps n) | skip
      all_goals simp_all +zetaDelta [Route.modifyBgp]
    · cases e <;> mvcgen [eval, hEval, hCall, hExec, hDef, lookupPolicy, hLong,
        communityContext, hLift, readTag, readMetric, readLocalPreference, readAsPath,
        readCommunities, intermediate, discard_keeps, hExec]
      all_goals first | exact (⇓? _ => Keeps n) | skip
      all_goals simp_all +zetaDelta
    · mvcgen [callDefaultPolicy, hEval]
      all_goals simp_all +zetaDelta

/-- What a triple's postcondition says about a run that succeeds. -/
theorem triple_run {α : Type} {x : PolicyM α} {P : State → Prop}
    (h : ⦃fun _ s => ⌜P s⌝⦄ x ⦃⇓? _ _ s => ⌜P s⌝⦄) {ctx : Context} {s s' : State} {a : α}
    (hs : P s) (hx : (x.run ctx).run s = .ok (a, s')) : P s' := by
  have := h ctx s hs
  simp only [wp, ReaderT.run, StateT.run, PredTrans.apply] at this hx
  unfold PredTrans.pushArg at this
  simp only [StateT.run, Functor.map, PredTrans.apply, PredTrans.bind, PredTrans.pure,
    Function.comp_def, hx] at this
  have h' : (wp⟦(pure (a, s') : Except String (α × State))⟧
      (fun x => ⌜P x.snd⌝, ExceptConds.true)).down := this
  simpa [WP.pure] using h'

/-- **Policies never change the network**: the route a policy writes keeps the network of
the route it started from. -/
theorem process_network {ctx : Context} {policy : RoutingPolicy} {output : Route} {o : Outcome}
    (h : process ctx policy output = .ok o) : o.output.network = output.network := by
  simp only [process, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i res hres
    cases h
    exact triple_run (P := fun s => s.output.network = output.network)
      ((keeps_network output.network policyFuel).2.1 policy) rfl hres

end LeanBatfish.Policy
