import Libpetri.Spec.Verifier.Bridges
import Libpetri.Spec.Verifier.Split
import Libpetri.Spec.Text.VER_004

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-004: Untimed Over-Approximation (`spec/07-verification.md`)

Three blocks, one per kind of claim the section makes. Two are here; the third waits for the
executor with actions in flight.

* `VER_004_timed` (kind A): what the verifier assumes of the executor's timing. It is a
  predicate over a pair `(R, F)`: `R : TRel K`, the timed step relation the TIME blocks
  constrain, and `F : FireRel K`, the firing relation the CORE and IO blocks constrain and the
  yardstick of [VER-003]. Timing only removes firings: every timed firing is a firing of `F` of a
  transition of the net, and a delay or a reap changes no marking. Timing adds rests: where a
  timed run rests (no enabled transition armed), every enabled transition is reapable, which is
  [VER-002]'s default quiescence; where an on-time run rests (no reap, no delay past a latest
  bound, ruling D3), no transition is enabled, which is the quiescence under `assumeNoReaping`.
  The witness pair is `RefTStep` and `RefFire` (`VER_004_timed_reference`). Wrong executors: a
  firing that loses its deposit, a reap that drains the reaped transition's places, a firing
  that never arms a transition it newly enables, and a delay that quietly disarms the reapable
  transitions.
* `VER_004_split` (kind F): the in-flight split. It is a predicate over a pair `(S, P)`:
  `S : SplitFn K`, the split itself, of the shape of `Split.refSplit` (which transitions split,
  the shape of the split net, the refusals, the opt-out), and `P : SplitPlanFn K`, the
  configuration the verifier hands the split: the `QuiescentCount` demand, the conflict-priority
  demand of [NU-052] and the switch-off of conflict priority when the split under it is refused.
  The witness pair is `Split.refSplit` and `refSplitPlan` (`VER_004_split_reference`). Wrong
  splits: one that ignores the opt-out, one that refuses a ν-join nothing needs to split, one
  without the refusals, one that blames the last refused transition instead of the first, one
  blind to terminal places, one whose completion step keeps a forward;
  wrong plans: one that never switches conflict priority off, one that ignores the
  `QuiescentCount` demand, one that ignores the conflict demand.
* Block B (`VER_004_exec`, in `VER_004_exec.lean`): every run of the executor with actions in
  flight is covered by the split net. It needs RefExec and is not here.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Spec.Verifier (Options)
open Libpetri.Spec.Verifier.Bridges (OnTimeStep RefRests UnarmedReapable AllArmed stamp_after
  rearm_of_enabled)
open Libpetri.Spec.Verifier.Split (SplitCfg splits refusal refusalHead firstRefusal splitTimed
  refSplit)

/-! ## Block A: the timed executor only removes firings and adds rests -/

/-- The states a run of the timed step relation `R` reaches in the timed net `X`, from the
initial state of the marking `m0` at clock reading `now0` (the reference initialiser, which arms
every transition enabled in `m0`). -/
def TimedReach {K : Type} (R : TRel K) (X : TimedNet K) (m0 : K → Nat) (now0 : Nat) :
    TSt K → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ l, R X s l s') (TSt.init X m0 now0)

/-- The states an on-time run of `R` reaches: no reap, and no delay that carries an armed
transition past its latest bound (`OnTimeStep`, ruling D3). -/
def OnTimeReachR {K : Type} (R : TRel K) (X : TimedNet K) (m0 : K → Nat) (now0 : Nat) :
    TSt K → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ l, OnTimeStep R X s l s') (TSt.init X m0 now0)

requirement VER_004_timed
  id "VER-004"
  title "Untimed Over-Approximation (timing only removes firings)"
  kind A
  scope "the executor's timed runs, as every verifier route reads them (SHOULD; the shall sentences bind an implementation that offers verification)"
  source verbatim "spec/07-verification.md"
  covers VER_004.s2, VER_004.s3, VER_004.s4, VER_004.s5
  reading "For every timed step relation R and firing relation F:"
          "every firing step of R, of transition t with deposit d, fires a transition of the net, and is a firing of t under F from the step's marking to its successor's;"
          "a delay or a reap step of R leaves the marking as it is (FramesMarking R);"
          "on a net whose transition names are distinct, at every state an R run reaches from the reference initial state where no enabled transition is armed (RefRests), every enabled transition is reapable (VerQuiescent false);"
          "on a net whose transition names are distinct, at every state an on-time R run (OnTimeStep R: no reap, no delay that carries an armed transition past its latest bound) reaches from the reference initial state where no enabled transition is armed, no transition is enabled (VerQuiescent true)."
  assumes "The model is the pair (R, F). R : TRel K is the timed step relation the TIME blocks constrain (Reference/Timed.lean: a delay of the firing clock, an atomic firing, or a reap, each one step), and F : FireRel K is the firing relation the CORE and IO blocks constrain, through which VER-003 reads reachability (ReachF F). The witness pair is RefTStep and RefFire (VER_004_timed_reference). Runs start at the reference initialiser TSt.init, which arms every transition enabled in the initial marking (TIME-010), the start state of every RefTStep run; that is the 'from the initial marking ([TIME-010])' of the third and the fourth EARS sentences, without which a run could start at a state with an enabled, unarmed transition that is not reapable and rest there. The block constrains R against F and leaves F to the CORE and IO blocks: a lax F that also lets a firing keep the marking would let through an R that loses a deposit, and the consistency theorem rules it out through those blocks, not through this one. Lines 1 and 2 give ProjectsTo R F and are FramesMarking R, the two conjuncts spec_consistent_coreIO_time already joins, so the consistency theorem can take one R and one F for the TIME, CORE and VER blocks."
          "Kind A: the block states what every verifier route assumes of the executor's timing, that timing only removes firings and adds rests; it constrains the executor relation of the TIME blocks, not the verifier. The first two EARS sentences are lines 1 and 2. The body's 'every marking a timed run visits is reachable in the untimed net' follows from them alone (VER_004_timed_reach), and with VER-003's Proven line so does 'A proof of a property of the marking alone on the untimed net therefore holds for the timed net' (marking_properties_transfer and marking_ac3, cited)."
          "Lines 3 and 4 are the third and the fourth EARS sentences. A run rests where no enabled transition is armed (RefRests): the run loop stops on enabled_count() == 0 with nothing in flight (rust/libpetri-runtime/src/executor_core/executor.rs, ReapAware.lean). A timed run is any run of R, late delays, late firings within the tolerance and reaps included; an on-time run is a run of the filter OnTimeStep R (ruling D3: strong urgency filters runs and never restricts R, so the TIME blocks' CoversDelay stays true of the same R). Distinct names are ruling D10 with D23: a stamp is kept per name, so with two transitions of one name a transition can be enabled and unarmed without a reap. Transition names are assumed distinct (ruling D23); no builder and no compose checks them, so the body's 'With that reading, a proof on the untimed net is sound for every timed run, a late one included.' holds on a net whose transition names are distinct, the nets that assumption covers. The body sentence 'The untimed abstraction MUST include this, so every quiescence property reads quiescence reap-aware ([VER-002]): a marking where every enabled transition is reapable counts as quiescent.' is VER-002's VerQuiescent; line 3 is what makes that reading sound for a late executor, and line 4 is why the plain reading of assumeNoReaping is sound for an on-time one. That a rest is a reachable marking at all is line 1 and line 2 (VER_004_timed_reach)."
          "The step relation is atomic: a firing consumes and deposits in one step. An action in flight, whose firing consumes at its start and deposits at its completion with other firings between ([EXEC-001], [CONC-002], [EXEC-003] AC5), is the subject of the in-flight split (VER_004_split) and of block B (VER_004_exec), which covers the executor's runs with actions in flight by the split net through RefExec. The body's paragraph 'Atomic firings and in-flight actions' and the paragraph on restarting a transition in flight (ruling D8: implementation-defined; the split allows a restart, which over-approximates both answers) belong there."
          "AC1, rewritten under ruling D28 (a), says what the routes read of timing: the flat routes read no timing bound, only whether a transition is reapable, and Route B keeps each earliest bound and each latest bound only under assumeNoReaping. It is not a line here: what a flat route reads of timing is VER-002's VerQuiescent (TimingOf only through Reapable) and VER-003's yardstick ReachF F (no timing at all), and the graph Route B reads is VER-012's and VER-010's subject."
          "AC2 (value-blind; the NU-020 name-equality carve-out of NU-050 when implemented) is the shape of the model rather than a line: a marking is a count per place, and F lets every branch of an output spec happen (Reference.Fires: any outcome the spec offers), so a value-dependent choice is free; Soundness.proposition_one and the carve-out's NU-050 block are cited for it. The body's sentence that there is no value predicate left (guards were removed in IO-006) is IO-006's."
          "AC3 is lines 3 and 4 with VER-003's Proven line: a Proven of a quiescence property on the untimed net, read reap-aware, holds at every rest of a late run, and read plainly at every rest of an on-time run. AC3 and the body's second paragraph define the on-time executor as the fourth EARS sentence does, one that reaps no transition and lets no armed transition pass its latest bound (OnTimeStep, ruling D3), which is stronger than firing none late: a delay that carries a transition past its latest bound is not on time even when that transition never fires. Its Route B clause (under assumeNoReaping a firing is one instant step, so a closed graph is exact only for an executor whose actions take no time; the deadline(20) and delayed(60) net with a 150 ms action) needs action duration, which no atomic step relation has (TimedScg.Retrodict.action_duration_escapes); it is VER-012's and VER-023's subject, and the report text that states the assumption is kind N. The test derivation's AC3 clause, the VER-002 AC11 witness, is VER_004_timed_nonvacuous: on p0 to t to p1 with t at window(3, 5), the late run delays past the latest bound, reaps t and rests at the initial marking with t enabled, so DeadlockFree is Violated there in the reap-aware reading and that rest is not quiescent in the plain one."
          "Completeness (a counterexample of the untimed abstraction may be a run the timing forbids; such a Violated stands, and counterexampleTiming and the opt-in check of VER-023 say what it means) is VER-003's and VER-023's subject; this block states only the direction from the timed runs to the untimed net. AC4 to AC8 are VER_004_split's, and AC4's coverage of the executor's runs with actions in flight is block B's (VER_004_exec)."
  signoff "2026-11-13 5da9a4d413c312ac ai"
  statement : ∀ {K : Type} [DecidableEq K], TRel K → FireRel K → Prop :=
    fun R F =>
      (∀ X s t d s', R X s (.fire t d) s' → t ∈ X.net.transitions ∧ F t s.m d s'.m) ∧
      FramesMarking R ∧
      (∀ X m0 now0 s, NamesDistinct X → TimedReach R X m0 now0 s → RefRests X s →
        VerQuiescent false X s.m) ∧
      (∀ X m0 now0 s, NamesDistinct X → OnTimeReachR R X m0 now0 s → RefRests X s →
        VerQuiescent true X s.m)

/- The pinned readable form of the timed block of VER-004: a change to the formula shows up as a
diff here. -/
/--
info: def Libpetri.Spec.VER_004_timed : {K : Type} → [DecidableEq K] → TRel K → FireRel K → Prop :=
fun {K} [DecidableEq K] R F =>
  (∀ (X : TimedNet K) (s : TSt K) (t : Reference.Trans K) (d : List K) (s' : TSt K),
      R X s (TLbl.fire t d) s' → t ∈ X.net.transitions ∧ F t s.m d s'.m) ∧
    FramesMarking R ∧
      (∀ (X : TimedNet K) (m0 : K → ℕ) (now0 : ℕ) (s : TSt K),
          NamesDistinct X → TimedReach R X m0 now0 s → RefRests X s → VerQuiescent false X s.m) ∧
        ∀ (X : TimedNet K) (m0 : K → ℕ) (now0 : ℕ) (s : TSt K),
          NamesDistinct X → OnTimeReachR R X m0 now0 s → RefRests X s → VerQuiescent true X s.m
-/
#guard_msgs in #print VER_004_timed

/-! ### The reference -/

section Inv

variable {K : Type} [DecidableEq K] {X : TimedNet K}

omit [DecidableEq K] in
/-- In the initial state every enabled transition of the net is armed. -/
theorem ver004_allArmed_init (hD : NamesDistinct X) (m0 : K → Nat) (now0 : Nat) :
    AllArmed X (TSt.init X m0 now0) := fun u hu he =>
  ((initArms_init X m0 now0 u ((inNet_iff_mem hD u).mpr hu)).1).mpr he

omit [DecidableEq K] in
/-- In the initial state no enabled transition is unarmed. -/
theorem ver004_unarmed_init (hD : NamesDistinct X) (m0 : K → Nat) (now0 : Nat) :
    UnarmedReapable X (TSt.init X m0 now0) := fun u hu he hna =>
  absurd (ver004_allArmed_init hD m0 now0 u hu he) hna

/-- One step of the timed reference keeps "every enabled, unarmed transition is reapable": an
enabled transition loses its stamp only by a reap, and only an expired, so reapable, transition
is reaped. A firing re-arms every transition it newly enables, since it writes one of that
transition's arc places (`enabled_frame`). -/
theorem ver004_unarmed_step (hD : NamesDistinct X) {s s' : TSt K} (hu : UnarmedReapable X s)
    {l : TLbl K} (hR : RefTStep X s l s') : UnarmedReapable X s' := by
  have hR' : RefTStepW refPolicy X s l s' := hR
  cases hR' with
  | delay δ => exact fun u hu' he hna => hu u hu' he hna
  | reap t ht hx =>
    intro u hu' he hna
    by_cases hne : u.core.name = t.core.name
    · have hut : u = t := by
        have h1 := (inNet_iff_mem hD u).mpr hu'
        have h2 := (inNet_iff_mem hD t).mpr ht
        unfold InNet at h1 h2
        rw [hne] at h1
        rw [h1] at h2
        exact Option.some.inj h2
      subst hut
      exact ((expired_iff X s u).mpr hx).1
    · refine hu u hu' he fun ha => hna ⟨ha.1, ?_⟩
      have := ha.2; simpa [hne] using this
  | fire t d m' ht hf ha hg hx =>
    obtain ⟨-, -, hm⟩ := hf
    subst hm
    intro u hu' he hna
    have hst : ¬ (restampAll refPolicy X s t d (fireNA s.m t.core d) u.core.name).isSome = true :=
      fun h => hna ⟨he, h⟩
    rw [stamp_after hD hu'] at hst
    by_cases hk : refPolicy.keep X s t d (fireNA s.m t.core d) u = true
    · rw [if_pos hk] at hst
      have : s.armed u = true := by
        simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
      exact absurd ((armed_iff s u).mpr this).2 hst
    · rw [if_neg hk] at hst
      by_cases hra : refPolicy.rearm X s t d (fireNA s.m t.core d) u = true
      · rw [if_pos hra] at hst; exact absurd rfl hst
      · have he' : enabledNA (fireNA s.m t.core d) u.core = true := he
        simp only [refPolicy, he', Bool.true_and, Bool.or_eq_true, not_or] at hra
        obtain ⟨hna0, hw⟩ := hra
        have hw' : writesArc t d u = false := by simpa using hw
        have hen0 : enabledNA s.m u.core = true := by
          rw [← Verifier.Bridges.enabled_frame hw']; exact he'
        exact hu u hu' hen0 fun ha0 => hna0 ((armed_iff s u).mp ha0)

/-- Every state a run of the timed reference reaches keeps "every enabled, unarmed transition is
reapable". -/
theorem ver004_unarmed_reach (hD : NamesDistinct X) {m0 : K → Nat} {now0 : Nat} {s : TSt K}
    (h : TimedReach RefTStep X m0 now0 s) : UnarmedReapable X s := by
  induction h with
  | refl => exact ver004_unarmed_init hD m0 now0
  | tail _ hs ih => obtain ⟨l, hl⟩ := hs; exact ver004_unarmed_step hD ih hl

/-- One on-time step of the timed reference keeps every enabled transition armed: it reaps
nothing, a delay changes no stamp, and a firing keeps or re-arms every transition enabled after
it. -/
theorem ver004_allArmed_step (hD : NamesDistinct X) {s s' : TSt K} (hA : AllArmed X s)
    {l : TLbl K} (hR : OnTimeStep RefTStep X s l s') : AllArmed X s' := by
  obtain ⟨hR, hon⟩ := hR
  have hR' : RefTStepW refPolicy X s l s' := hR
  cases hR' with
  | delay δ => exact fun u hu he => hA u hu he
  | reap t ht hx => exact hon.elim
  | fire t d m' ht hf ha hg hx =>
    obtain ⟨-, -, hm⟩ := hf
    subst hm
    intro u hu he
    refine ⟨he, ?_⟩
    show (restampAll refPolicy X s t d (fireNA s.m t.core d) u.core.name).isSome = true
    rw [stamp_after hD hu]
    split_ifs with hk hra
    · have : s.armed u = true := by
        simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
      exact ((armed_iff s u).mpr this).2
    · rfl
    · exact absurd (rearm_of_enabled hA hu t d he) hra

/-- Every state an on-time run of the timed reference reaches has every enabled transition
armed. -/
theorem ver004_allArmed_reach (hD : NamesDistinct X) {m0 : K → Nat} {now0 : Nat} {s : TSt K}
    (h : OnTimeReachR RefTStep X m0 now0 s) : AllArmed X s := by
  induction h with
  | refl => exact ver004_allArmed_init hD m0 now0
  | tail _ hs ih => obtain ⟨l, hl⟩ := hs; exact ver004_allArmed_step hD ih hl

end Inv

/-- The timed reference satisfies the timed block of VER-004: a firing step is a reference
firing of a transition of the net (`refTStep_projects`), a delay or a reap leaves the marking
(`refTStep_framesMarking`), every rest of a run has only reapable transitions enabled
(`ver004_unarmed_reach`: a transition loses its stamp while enabled only by a reap), and every
rest of an on-time run has none enabled (`ver004_allArmed_reach`: an on-time run reaps nothing,
so every enabled transition stays armed). -/
@[evidence holds VER_004_timed]
theorem VER_004_timed_reference {K : Type} [DecidableEq K] :
    VER_004_timed (RefTStep (N := K)) RefFire := by
  refine ⟨fun X s t d s' h => ?_, refTStep_framesMarking, ?_, ?_⟩
  · have h' : RefTStepW refPolicy X s (.fire t d) s' := h
    cases h' with
    | fire t d m' ht hf ha hg hx => exact ⟨ht, hf⟩
  · intro X m0 now0 s hD hr hrest t ht he
    exact ⟨rfl, ver004_unarmed_reach hD hr t ht he (hrest t ht he)⟩
  · intro X m0 now0 s hD hr hrest t ht he
    exact absurd (ver004_allArmed_reach hD hr t ht he) (hrest t ht he)

/-- **Every marking a timed run visits is reachable in the untimed net**, from the statement
alone: on every pair satisfying the timed block, a state an `R` run reaches has a marking the
untimed net reaches under `F` from the initial marking. -/
theorem VER_004_timed_reach {K : Type} [DecidableEq K] {R : TRel K} {F : FireRel K}
    (h : VER_004_timed R F) {X : TimedNet K} {m0 : K → Nat} {now0 : Nat} {s : TSt K}
    (hr : TimedReach R X m0 now0 s) : ReachF F X.net m0 s.m := by
  obtain ⟨h1, h2, -, -⟩ := h
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨l, hl⟩ := hs
    cases l with
    | fire t d =>
      obtain ⟨ht, hf⟩ := h1 _ _ _ _ _ hl
      exact Relation.ReflTransGen.tail ih ⟨_, t, ht, rfl, d, hf⟩
    | delay δ =>
      rw [h2 _ _ _ _ hl (fun _ _ hc => by cases hc)]; exact ih
    | reap t =>
      rw [h2 _ _ _ _ hl (fun _ _ hc => by cases hc)]; exact ih

/-! ### Examples: the [VER-002] AC11 net -/

/-- `t : p0 → p1` (places `0` and `1`). -/
def ver004_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The AC11 net: `t` at `window(3, 5)`, deadline tolerance `0`. -/
def ver004_X : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [ver004_t] },
    timing := fun _ => .window 3 5, tol := 0 }

/-- The marking `{p0}`. -/
def ver004_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at clock reading `0`: `t` armed. -/
def ver004_s0 : TSt Nat := TSt.init ver004_X ver004_m0 0

/-- After a delay of 6 ms: `t` is past its latest bound of 5 ms, so it is expired. -/
def ver004_s1 : TSt Nat := { ver004_s0 with now := ver004_s0.now + 6 }

/-- After the reap of `t`: the marking is still `{p0}`, `t` holds no stamp. -/
def ver004_s2 : TSt Nat :=
  { ver004_s1 with stamp := fun n => if n = ver004_t.core.name then none else ver004_s1.stamp n }

/-- ✓ **AC3, the late run of the [VER-002] AC11 witness**: on `p0 → t → p1` with `t` at
`window(3, 5)`, a late executor waits 6 ms, reaps `t` and comes to rest at `{p0}`. The run is a
run of the timed reference, nothing is armed there, `t` is still enabled, and the rest is
quiescent in [VER-002]'s default reading (every enabled transition is reapable) while it is not in
the plain reading of `assumeNoReaping`. So `DeadlockFree` must read the reap-aware quiescence to
see this rest. -/
@[evidence nonvacuous VER_004_timed]
theorem VER_004_timed_nonvacuous :
    TimedReach RefTStep ver004_X ver004_m0 0 ver004_s2 ∧ RefRests ver004_X ver004_s2 ∧
      Enabled ver004_t ver004_s2.m ∧ VerQuiescent false ver004_X ver004_s2.m ∧
      ¬ VerQuiescent true ver004_X ver004_s2.m := by
  have h1 : RefTStep ver004_X ver004_s0 (.delay 6) ver004_s1 := RefTStepW.delay _ _ _
  have h2 : RefTStep ver004_X ver004_s1 (.reap ver004_t) ver004_s2 :=
    RefTStepW.reap _ _ _ (by simp [ver004_X]) (by decide)
  refine ⟨Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨_, h1⟩) ⟨_, h2⟩,
    by unfold RefRests; decide, by decide, ?_, ?_⟩
  · intro u hu _
    simp only [ver004_X, List.mem_singleton] at hu
    subst hu
    exact ⟨rfl, by decide⟩
  · intro h
    exact absurd (h ver004_t (by simp [ver004_X]) (by decide)).1 (by decide)

/-! ### Violations -/

/-- A timed executor that may also fire a transition and lose the firing: the marking stays
as it was, nothing consumed and nothing deposited. -/
def ver004_fireNoDeposit : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ t d, l = .fire t d ∧ t ∈ X.net.transitions ∧ s' = s

/-- ✗ A firing that loses its deposit violates the timed block (line 1): on the AC11 net, `t`
with deposit `p1` from `{p0}` back to `{p0}` is no firing of `t`, since a firing of `t` leaves
`p1` marked. -/
@[evidence forbids VER_004_timed]
theorem VER_004_timed_forbids_fireNoDeposit : ¬ VER_004_timed ver004_fireNoDeposit RefFire := by
  intro h
  obtain ⟨-, -, hm⟩ := (h.1 ver004_X ver004_s0 ver004_t [1] ver004_s0
    (Or.inr ⟨ver004_t, [1], rfl, by simp [ver004_X], rfl⟩)).2
  have := congrFun hm 1
  revert this
  decide

/-- A timed executor whose reap also drains the reaped transition's net: every place empties. -/
def ver004_reapDrains : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ t, l = .reap t ∧ s' = { s with m := fun _ => 0 }

/-- ✗ A reap that changes the marking violates the timed block (line 2): the reap of `t` from
`{p0}` leaves `p0` empty. -/
@[evidence forbids VER_004_timed]
theorem VER_004_timed_forbids_reapDrains : ¬ VER_004_timed ver004_reapDrains RefFire := by
  intro h
  have := congrFun (h.2.1 ver004_X ver004_s1 (.reap ver004_t) { ver004_s1 with m := fun _ => 0 }
    (Or.inr ⟨ver004_t, rfl, rfl⟩) (fun _ _ hc => by cases hc)) 0
  revert this
  decide

/-- The timing policy that never arms a transition a firing newly enables: only a transition
armed before the firing is armed again. -/
def ver004_noNewArmPolicy : Policy Nat :=
  { refPolicy with rearm := fun _ s _ _ m' u => enabledNA m' u.core && s.armed u }

/-- `u : p1 → p2`, immediate in `ver004_chain`. -/
def ver004_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The chain `t : p0 → p1`, `u : p1 → p2`, both immediate. -/
def ver004_chain : TimedNet Nat :=
  { net := { places := [0, 1, 2], transitions := [ver004_t, ver004_u] },
    timing := fun _ => .immediate, tol := 0 }

/-- The state after `t` fires from `{p0}` under `ver004_noNewArmPolicy`. -/
def ver004_noArm1 : TSt Nat :=
  { m := fireNA ver004_m0 ver004_t.core [1], now := 0,
    stamp := restampAll ver004_noNewArmPolicy ver004_chain (TSt.init ver004_chain ver004_m0 0)
      ver004_t [1] (fireNA ver004_m0 ver004_t.core [1]) }

/-- The firing of `t` from the initial state of the chain, under `ver004_noNewArmPolicy`; it is
on time. -/
theorem ver004_noArm_fire :
    OnTimeStep (RefTStepW ver004_noNewArmPolicy) ver004_chain (TSt.init ver004_chain ver004_m0 0)
      (.fire ver004_t [1]) ver004_noArm1 :=
  ⟨RefTStepW.fire _ _ _ _ _ (by simp [ver004_chain]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) (by decide) (by decide), trivial⟩

/-- ✗ A firing that does not arm the transition it newly enables violates the timed block
(line 3): on the immediate chain `t : p0 → p1`, `u : p1 → p2`, the run fires `t` and rests at
`{p1}` with `u` enabled and unarmed, and `u` is not reapable. -/
@[evidence forbids VER_004_timed]
theorem VER_004_timed_forbids_noNewArm :
    ¬ VER_004_timed (RefTStepW ver004_noNewArmPolicy) RefFire := by
  intro h
  have hq := h.2.2.1 ver004_chain ver004_m0 0 ver004_noArm1 (by unfold NamesDistinct; decide)
    (Relation.ReflTransGen.single ⟨_, ver004_noArm_fire.1⟩) (by unfold RefRests; decide)
  exact absurd (hq ver004_u (by simp [ver004_chain]) (by decide)).2 (by decide)

/-- A timed executor whose delay also clears the stamp of every reapable transition: it reaps
early, inside a delay, without a reap step. -/
def ver004_earlyReap : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ δ, l = .delay δ ∧
    s' = { m := s.m, now := s.now + δ,
           stamp := fun n => if X.net.transitions.any
             (fun u => u.core.name == n && (X.timing u).reapable) then none else s.stamp n }

/-- The state after the early-reaping delay of 1 ms from the initial state of the AC11 net. -/
def ver004_early1 : TSt Nat :=
  { m := ver004_m0, now := 1,
    stamp := fun n => if ver004_X.net.transitions.any
      (fun u => u.core.name == n && (ver004_X.timing u).reapable) then none else ver004_s0.stamp n }

/-- ✗ A delay that disarms the reapable transitions violates the timed block (line 4): on the
AC11 net, a delay of 1 ms is on time (`t` is 4 ms short of its latest bound), and the run then
rests at `{p0}` with `t` enabled. Every rest of this executor is still reap-quiescent (only
reapable transitions lose their stamp), so only line 4 tells it apart. -/
@[evidence forbids VER_004_timed]
theorem VER_004_timed_forbids_earlyReap : ¬ VER_004_timed ver004_earlyReap RefFire := by
  intro h
  have hstep : OnTimeStep ver004_earlyReap ver004_X ver004_s0 (.delay 1) ver004_early1 :=
    ⟨Or.inr ⟨1, rfl, rfl⟩, by decide⟩
  have hq := h.2.2.2 ver004_X ver004_m0 0 ver004_early1 (by unfold NamesDistinct; decide)
    (Relation.ReflTransGen.single ⟨_, hstep⟩) (by unfold RefRests; decide)
  exact absurd (hq ver004_t (by simp [ver004_X]) (by decide)).1 (by decide)

/-! ## Block F: the in-flight split -/

/-- **The in-flight split**, of the shape of `Split.refSplit`: from the split configuration (the
terminal, coloured, ν-join and environment data the split reads, and the demand), the options
and the timed net, the verified net and the split transitions in net order, or the refusal. -/
abbrev SplitFn (K : Type) : Type :=
  SplitCfg K → Options → TimedNet K → Except String (TimedNet K × List String)

/-- **The split plan**: from the options, whether conflict priority applies to the call
([NU-052]), the priorities by transition name, the property, the base configuration and the
net, the configuration the verifier hands the split and whether conflict priority stays on. -/
abbrev SplitPlanFn (K : Type) : Type :=
  Options → Bool → (String → Int) → VerProp K → SplitCfg K → TimedNet K → SplitCfg K × Bool

section Plan

variable {K : Type} [DecidableEq K]

/-- The name of the first transition, in net order, among those named in `sp` that cannot be
split (`first_unsplittable`). -/
def ver004FirstRefused (cfg : SplitCfg K) (net : Reference.Net K) (sp : List String) : Option String :=
  ((net.transitions.filter (fun t => decide (t.core.name ∈ sp))).find?
    (fun t => (refusal cfg net t).isSome)).map (·.core.name)

/-- **The `QuiescentCount` demand** (`quiescent_count_demand`): a `QuiescentCount` with a lower
bound above zero, on a net with a terminal place its waivers do not name, counts its places and
its waiver places as tested. A terminal stop abandons an action in flight, so the counted tokens
it would deposit never arrive. -/
def ver004CountDemand (cfg : SplitCfg K) : VerProp K → List K
  | .quiescentCount ps lo _ w => if lo ≠ 0 ∧ ∃ τ ∈ cfg.terminals, τ ∉ w then ps ++ w else []
  | _ => []

/-- **The pruning transitions** (`conflict_pruners`), in net order: each `H` with strictly higher
priority than another transition that shares an input place with it. -/
def ver004Pruners (prio : String → Int) (net : Reference.Net K) : List (Trans K) :=
  net.transitions.filter fun h => net.transitions.any fun l =>
    l.core.name != h.core.name && decide (prio l.core.name < prio h.core.name) &&
      l.core.inputs.any fun a => h.core.inputs.any fun b => decide (a.place = b.place)

/-- The configuration with the `QuiescentCount` demand added. -/
def ver004WithCount (cfg : SplitCfg K) (φ : VerProp K) : SplitCfg K :=
  { cfg with tested := cfg.tested ++ ver004CountDemand cfg φ }

/-- The configuration with the conflict demand added (`conflict_demand`): every pruning
transition is forced, and its input and read places are tested. -/
def ver004WithConflict (prio : String → Int) (cfg : SplitCfg K) (net : Reference.Net K) : SplitCfg K :=
  { cfg with
    tested := cfg.tested ++ (ver004Pruners prio net).flatMap
      (fun h => h.core.inputs.map (·.place) ++ h.core.reads),
    forced := cfg.forced ++ (ver004Pruners prio net).map (·.core.name) }

/-- **The reference plan** (`with_in_flight`): the `QuiescentCount` demand always; under conflict
priority also the conflict demand, unless the opt-out is off, there is a pruning transition and
the split under that demand is refused, in which case conflict priority is turned off and the
`QuiescentCount` demand alone is handed on. -/
def refSplitPlan : SplitPlanFn K := fun o c prio φ cfg X =>
  if c then
    if o.assumeAtomicFiring = false ∧ ver004Pruners prio X.net ≠ [] ∧
        (ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
          (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net)).isSome then
      (ver004WithCount cfg φ, false)
    else (ver004WithConflict prio (ver004WithCount cfg φ) X.net, true)
  else (ver004WithCount cfg φ, false)

end Plan

/- The reference plan is the second witness of the split block of VER-004. -/
#spec_witness refSplitPlan

requirement VER_004_split
  id "VER-004"
  title "Untimed Over-Approximation (the in-flight split)"
  kind F
  scope "the verified-net function of every verifier entry point, before the terminal rewrite of EXEC-042 (SHOULD; the shall sentences bind an implementation that offers verification)"
  source verbatim "spec/07-verification.md"
  covers VER_004.s6, VER_004.s7, VER_004.s8, VER_004.s9, VER_004.s10, VER_004.s11, VER_004.s12,
        VER_004.s13, VER_004.s14, VER_004.s15
  reading "For every split S and plan P, every split configuration cfg (terminal, coloured, ν-join and environment data, and the demand: the places counted as tested and the transitions forced), options o and timed net X:"
          "if o sets assumeAtomicFiring, S returns X unchanged with no split transition;"
          "if o does not, and no transition splits under cfg (splits: in net order, every transition that is no completion step and no environment step and is forced or has an output place that is terminal, inhibited, reset, drained or tested by the demand), S returns X unchanged with no split transition;"
          "if o does not, and some split transition cannot be split (refusal: a ν-join, a coloured writer, a Timeout forward from an input that is not one, a name the split would add already used), S returns an error whose text opens with transition '<t>' for the first such transition t in net order;"
          "if o does not, some transition splits and none is refused, S returns the split net (splitTimed: each split t replaced in place by its start half, whose only output is inflight:<t>, and its completion step complete:<t>; the in-flight places after the net's places) and the split transitions;"
          "without conflict priority, P hands on cfg with the QuiescentCount demand added and conflict priority off;"
          "with conflict priority, when o sets assumeAtomicFiring, or the net has no pruning transition, or nothing the split would split under the conflict demand is refused, P hands on cfg with the QuiescentCount demand and the conflict demand added and keeps conflict priority on;"
          "with conflict priority, when o does not set assumeAtomicFiring, the net has a pruning transition and some transition the split would split under the conflict demand is refused, P hands on cfg with the QuiescentCount demand alone and turns conflict priority off."
  assumes "The model is the pair (S, P). S : SplitFn K has the shape of Split.refSplit, the reference of in_flight.rs split_in_flight_for (Java InFlightSplit, TypeScript in-flight.ts): the configuration SplitCfg carries what the split reads besides the net (the in-flight place of a name and how a place is rendered, the terminal places, the coloured places with the match keys and relay targets already added, the ν-joins, the environment steps of VER-006 and VER-022, and the demand: tested places and forced transitions). P : SplitPlanFn K is with_in_flight's choice of demand: it adds quiescent_count_demand always and conflict_demand when conflict priority applies, and switches conflict priority off when the split under it is refused. The witness pair is Split.refSplit and refSplitPlan (VER_004_split_reference). The verified net of VER-003's abs is S at P's configuration, and a refusal of S is an error of abs, so VER-003's line 4 makes the verdict Unknown whatever a route would answer: that is the 'answer Unknown on every route' of the eighth EARS sentence."
          "The first EARS sentence defines the tested places (nonMonotone plus the demand's tested places, Split.splitB). The second is P's QuiescentCount demand (ver004CountDemand) in lines 5 to 7, and the third is the tested half of P's conflict demand (ver004Pruners, the tested field of ver004WithConflict) in line 6. The fourth is splits in lines 2 to 4: an output place in any branch, the Timeout branch included, is Split.outs (outPlaces); 'are not a completion step' is Split.isCompletion, whose definition the parenthesis gives; 'pruning transitions while conflict priority applies' is the forced field of ver004WithConflict, which P hands on exactly when conflict priority stays on (line 6) and drops when it turns conflict priority off (line 7); 'While assumeAtomicFiring is not set' is line 1, under which nothing is split. The fifth and the sixth are splitTimed in line 4 (Split.startHalf; Split.endHalf, whose one input is one(inflight:<t>) and which has no inhibitor, read or reset arc; Split.completionOut; Split.splitNet). The seventh is line 2. The eighth is line 3 with VER-003 line 4: 'a transition to split' is one S splits under the configuration P hands on, so under conflict priority it is read after the switch-off of the ninth sentence, which is why the eighth needs no condition on conflict priority (a net with conflict priority, no pruning transition and a ν-join that deposits into an inhibited place keeps conflict priority on by line 6 and is refused by line 3). The ninth is line 7: the split under the conflict demand is refused, so P hands on the QuiescentCount demand alone with conflict priority off, and S then splits as it does without conflict priority (VER_004_split_fallback), refusing only what the split without conflict priority refuses; its 'While assumeAtomicFiring is not set' is line 7's hypothesis, since under the opt-out line 6 keeps conflict priority on. The tenth is line 1 for the net and line 6 for conflict priority."
          "Not in the model, and why. Reference.Trans has no priority and no match spec, so the priorities are P's argument by name, the ν-joins and the coloured places are SplitCfg fields, and the halves' priority and match spec (the start half keeps both; the completion step takes t's priority in all three runtimes, halves in rust/libpetri-verification/src/in_flight.rs, completion in java/src/main/java/org/libpetri/analysis/InFlight.java and halves in typescript/src/verification/in-flight.ts, as the body's second bullet says) are kind N. Whether conflict priority applies to a call (conflict_pruning_applies: CONFLICT selected, a ν-join with a property Route B takes, no reapable transition) is P's argument, decided by NU-052 and VER-012. The terminal rewrite of EXEC-042 that runs after the split, so a terminal also inhibits each completion step and excuses each in-flight place, is EXEC-042's (Novel.TerminalRewrite); Reference.Net carries no terminal list, so the split net's terminals are cfg's. The body sentences 'A marked in-flight place never rests: its completion step is enabled, immediate and not reapable.' and 'The completion step is itself one deposit and is never split again.' are consequences: Split.quiescent_no_inflight, and Split.isCompletion in line 2, cited. The refusal text is Rust's heads (Split.refusalHead). Line 3 asks that it open with transition '<t>', the opening all three runtimes share (refusal_head and demand_refusal_head in in_flight.rs, refusalHead and demandRefusalHead in InFlight.java and in-flight.ts; Python rides Rust); the rest of the wording is kind N. A text that only contains the name would be too weak: a split that blames the last refused transition, with the split list in front, still contains the first one's name, and a one-letter name such as a occurs in the word transition itself (VER_004_split_forbids_lastCulprit). The body's 'An implementation MUST offer the opt-out assumeAtomicFiring (assume_atomic_firing)' is an offer, so it is the coverage condition Ver004OptOutCovers (blocks state safety, offers are coverage: the convention of GlossaryExec.lean), not a line: Options carries the field in every runtime, the reference makes the offer (refSplit_optOut_covers), and every split that meets this block makes it too (VER_004_split_optOut). Ruling D20: the refusal reads the body's 'forwards an exactly(n), all or atLeast input', every cardinality that is not one, and AC6 now says so (clash ver-a#10)."
          "The paragraph 'Atomic firings and in-flight actions' says why the split is needed and is cited: InFlight.inflight_witness (the atomic net proves Unreachable(bad) while the executor marks bad) and InFlight.split_covers_executor. That the split net over-approximates the executor's runs with actions in flight, and so that a Proven holds for them, is block B (VER_004_exec, on RefExec): AC4's first sentence and the sentence 'That is a sound over-approximation for all three.' Ruling D28 (a) scopes it to actions that publish no output before they complete: tokens an action publishes with ctx.flush() (Rust, Python) enter the marking before its completion step, which the split net never reaches, and the report of every split verdict says so (FLUSH_NOTE, kind N). That the split only adds runs (every atomic run is a run of the split net with each split label followed by its completion) is Split.run_splitNet, cited."
          "Ruling D8 (b): whether an executor starts a transition again while an earlier firing of it is in flight is implementation-defined (Rust and Python do, Java and TypeScript do not). The split allows it, which over-approximates both. The report note of a Violated whose trace restarts a transition in flight ('NOTE (CONC-002): ...', restart_note) and AC8 are report text, kind Q, not encoded here: which trace restarts is a function of the trace's markings (restarted_transitions), an open item for a later line."
          "AC4's examples (the inhibitor net from {p, q, go} with t asynchronous, and reset(p), all(p) or atLeast(2, p) instead) are, on the split side, VER_004_split_nonvacuous (t is split, complete:t follows it, inflight:t follows the places) and Split's worked examples through refVerify (Violated with the split, Proven under assumeAtomicFiring); that the executors reach the same markings is block B's. AC5 (byte-identical scripts with or without assumeAtomicFiring when nothing is split) is lines 1 and 2: the verified net is X itself, so every route reads the same net; the scripts are VER-013's. AC6 is lines 3 and 7 and the tenth EARS sentence (line 1, line 6); its report texts are kind N. AC7 is VER_004_split_ac7: t and H are split under conflict priority, and under assumeAtomicFiring nothing is split and conflict priority is kept; the verdicts Violated and Proven are Route B's (VER-012, with a declared ν pair) and the executors marking bad is block B's. The test derivation's AC4 clause is block B's."
  signoff "2026-11-13 ea653f701a1d3b2f ai"
  statement : ∀ {K : Type} [DecidableEq K], SplitFn K → SplitPlanFn K → Prop :=
    fun S P =>
      (∀ cfg o X, o.assumeAtomicFiring = true → S cfg o X = .ok (X, [])) ∧
      (∀ cfg o X, o.assumeAtomicFiring = false → splits cfg X.net = [] →
        S cfg o X = .ok (X, [])) ∧
      (∀ cfg o X t, o.assumeAtomicFiring = false →
        ver004FirstRefused cfg X.net (splits cfg X.net) = some t →
        ∃ e, S cfg o X = .error e ∧ ("transition '" ++ t ++ "'").toList <+: e.toList) ∧
      (∀ cfg o X, o.assumeAtomicFiring = false → splits cfg X.net ≠ [] →
        ver004FirstRefused cfg X.net (splits cfg X.net) = none →
        S cfg o X = .ok (splitTimed cfg (splits cfg X.net) X, splits cfg X.net)) ∧
      (∀ o prio φ cfg X, P o false prio φ cfg X = (ver004WithCount cfg φ, false)) ∧
      (∀ o prio φ cfg X, (o.assumeAtomicFiring = true ∨ ver004Pruners prio X.net = [] ∨
          ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
            (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net) = none) →
        P o true prio φ cfg X = (ver004WithConflict prio (ver004WithCount cfg φ) X.net, true)) ∧
      (∀ o prio φ cfg X t, o.assumeAtomicFiring = false → ver004Pruners prio X.net ≠ [] →
        ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
          (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net) = some t →
        P o true prio φ cfg X = (ver004WithCount cfg φ, false))

/- The pinned readable form of the split block of VER-004: a change to the formula shows up as a
diff here. -/
/--
info: def Libpetri.Spec.VER_004_split : {K : Type} → [DecidableEq K] → SplitFn K → SplitPlanFn K → Prop :=
fun {K} [DecidableEq K] S P =>
  (∀ (cfg : SplitCfg K) (o : Options) (X : TimedNet K), o.assumeAtomicFiring = true → S cfg o X = Except.ok (X, [])) ∧
    (∀ (cfg : SplitCfg K) (o : Options) (X : TimedNet K),
        o.assumeAtomicFiring = false → splits cfg X.net = [] → S cfg o X = Except.ok (X, [])) ∧
      (∀ (cfg : SplitCfg K) (o : Options) (X : TimedNet K) (t : String),
          o.assumeAtomicFiring = false →
            ver004FirstRefused cfg X.net (splits cfg X.net) = some t →
              ∃ e, S cfg o X = Except.error e ∧ ("transition '" ++ t ++ "'").toList <+: e.toList) ∧
        (∀ (cfg : SplitCfg K) (o : Options) (X : TimedNet K),
            o.assumeAtomicFiring = false →
              splits cfg X.net ≠ [] →
                ver004FirstRefused cfg X.net (splits cfg X.net) = none →
                  S cfg o X = Except.ok (splitTimed cfg (splits cfg X.net) X, splits cfg X.net)) ∧
          (∀ (o : Options) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K) (X : TimedNet K),
              P o false prio φ cfg X = (ver004WithCount cfg φ, false)) ∧
            (∀ (o : Options) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K) (X : TimedNet K),
                o.assumeAtomicFiring = true ∨
                    ver004Pruners prio X.net = [] ∨
                      ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
                          (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net) =
                        none →
                  P o true prio φ cfg X = (ver004WithConflict prio (ver004WithCount cfg φ) X.net, true)) ∧
              ∀ (o : Options) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K) (X : TimedNet K) (t : String),
                o.assumeAtomicFiring = false →
                  ver004Pruners prio X.net ≠ [] →
                    ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
                          (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net) =
                        some t →
                      P o true prio φ cfg X = (ver004WithCount cfg φ, false)
-/
#guard_msgs in #print VER_004_split

/-! ### The reference -/

section Ref

variable {K : Type} [DecidableEq K]

/-- The first refused transition exists exactly when the first refusal does. -/
theorem ver004_firstRefused_none_iff (cfg : SplitCfg K) (net : Reference.Net K)
    (sp : List String) :
    ver004FirstRefused cfg net sp = none ↔ firstRefusal cfg net sp = none := by
  unfold ver004FirstRefused firstRefusal
  generalize net.transitions.filter (fun t => decide (t.core.name ∈ sp)) = L
  induction L with
  | nil => simp
  | cons a l ih =>
    cases h : refusal cfg net a with
    | none => simp [h, ih]
    | some c => simp [h]

/-- A refusal text opens with `transition '<t>'`, whichever of the two heads it takes. -/
theorem ver004_refusal_opens (cfg : SplitCfg K) (net : Reference.Net K) (n c : String) :
    ("transition '" ++ n ++ "'").toList <+: (refusalHead cfg net n ++ " " ++ c).toList := by
  have e1 : ("' must be verified as two steps, since its action runs between " : String) =
      "'" ++ " must be verified as two steps, since its action runs between " := by decide
  have e2 : ("' must be verified as two steps, since a terminal place can stop " : String) =
      "'" ++ " must be verified as two steps, since a terminal place can stop " := by decide
  unfold refusalHead
  split <;>
  · simp only [e1, e2, String.toList_append, List.append_assoc]
    simpa only [List.append_assoc] using
      List.prefix_append ("transition '".toList ++ (n.toList ++ "'".toList)) _

/-- The first refusal is the refusal of the first refused transition: its head and a cause. -/
theorem ver004_firstRefused_some (cfg : SplitCfg K) (net : Reference.Net K) (sp : List String)
    {t : String} (h : ver004FirstRefused cfg net sp = some t) :
    ∃ c, firstRefusal cfg net sp = some (refusalHead cfg net t ++ " " ++ c) := by
  unfold ver004FirstRefused at h
  unfold firstRefusal
  generalize net.transitions.filter (fun t => decide (t.core.name ∈ sp)) = L at h ⊢
  induction L with
  | nil => simp at h
  | cons a l ih =>
    cases hr : refusal cfg net a with
    | none =>
      simp only [List.find?_cons, hr, Option.isSome_none] at h
      simp only [List.findSome?_cons, hr, Option.map_none]
      exact ih h
    | some c =>
      simp only [List.find?_cons, hr, Option.isSome_some, Option.map_some,
        Option.some.injEq] at h
      subst h
      exact ⟨c, by simp [hr]⟩

end Ref

/-- The reference pair satisfies the split block of VER-004: `Split.refSplit` returns the net
unchanged under `assumeAtomicFiring` (`refSplit_atomic`) and when nothing splits
(`refSplit_nil`), refuses with a text that opens with `transition '<t>'` for the first refused
transition `t`, and otherwise
returns `splitTimed` of the split transitions; `refSplitPlan` adds the `QuiescentCount` demand,
and under conflict priority the conflict demand, unless the split under it is refused, in which
case it turns conflict priority off. -/
@[evidence holds VER_004_split]
theorem VER_004_split_reference {K : Type} [DecidableEq K] :
    VER_004_split (refSplit (K := K)) refSplitPlan := by
  refine ⟨fun cfg o X h => Verifier.Split.refSplit_atomic cfg X h,
    fun cfg o X _ h => Verifier.Split.refSplit_nil cfg o X h, ?_, ?_, ?_, ?_, ?_⟩
  · intro cfg o X t hat ht
    obtain ⟨c, hc⟩ := ver004_firstRefused_some cfg X.net _ ht
    have hne : splits cfg X.net ≠ [] := by
      intro h0; rw [h0] at ht; simp [ver004FirstRefused] at ht
    refine ⟨_, ?_, ver004_refusal_opens cfg X.net t c⟩
    unfold refSplit
    simp [hat, hne, hc]
  · intro cfg o X hat hne hr
    have hr' := (ver004_firstRefused_none_iff cfg X.net _).mp hr
    unfold refSplit
    simp [hat, hne, hr']
  · intro o prio φ cfg X
    simp [refSplitPlan]
  · intro o prio φ cfg X h
    unfold refSplitPlan
    rcases h with h | h | h <;> simp [h]
  · intro o prio φ cfg X t hat hp ht
    unfold refSplitPlan
    simp [hat, hp, ht]

/-- **Conflict priority off, the split without it**, from the statement alone: when conflict
priority applies, the opt-out is off, the net has a pruning transition and the split under the
conflict demand is refused, the plan hands on exactly what it hands on without conflict
priority, and conflict priority is off. -/
theorem VER_004_split_fallback {K : Type} [DecidableEq K] {S : SplitFn K} {P : SplitPlanFn K}
    (h : VER_004_split S P) {o : Options} {prio : String → Int} {φ : VerProp K}
    {cfg : SplitCfg K} {X : TimedNet K} {t : String} (hat : o.assumeAtomicFiring = false)
    (hp : ver004Pruners prio X.net ≠ [])
    (ht : ver004FirstRefused (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net
      (splits (ver004WithConflict prio (ver004WithCount cfg φ) X.net) X.net) = some t) :
    P o true prio φ cfg X = P o false prio φ cfg X := by
  rw [h.2.2.2.2.2.2 o prio φ cfg X t hat hp ht, h.2.2.2.2.1 o prio φ cfg X]

/-- **The opt-out VER-004 offers** (coverage, not a line of a block): for every net and every
split configuration there are options, with `assumeAtomicFiring` set, under which the split
leaves the net as it is and splits nothing. A split that always splits what needs it, whatever
the options say, does not make the offer. -/
def Ver004OptOutCovers {K : Type} (S : SplitFn K) : Prop :=
  ∀ cfg X, ∃ o : Options, o.assumeAtomicFiring = true ∧ S cfg o X = .ok (X, [])

/-- The reference split makes the offer: set `assumeAtomicFiring` and the net comes back as it
is. -/
theorem refSplit_optOut_covers {K : Type} [DecidableEq K] :
    Ver004OptOutCovers (refSplit (K := K)) :=
  fun cfg X => ⟨{ assumeAtomicFiring := true }, rfl,
    Verifier.Split.refSplit_atomic cfg X rfl⟩

/-- Every split that meets the split block makes the offer, by its first line. -/
theorem VER_004_split_optOut {K : Type} [DecidableEq K] {S : SplitFn K} {P : SplitPlanFn K}
    (h : VER_004_split S P) : Ver004OptOutCovers S :=
  fun cfg X => ⟨{ assumeAtomicFiring := true }, rfl, h.1 cfg _ X rfl⟩

/-! ### Examples -/

/-- The split transitions a split returns, or `none` for a refusal. -/
def ver004Names {K : Type} : Except String (TimedNet K × List String) → Option (List String)
  | .ok p => some p.2
  | .error _ => none

/-- The configuration of the examples: `inflight:<t>` and plain names, nothing else. -/
def ver004_cfg : SplitCfg String := { inflight := fun t => "inflight:" ++ t, render := id }

/-- A transition of the examples, with no read or reset arc. -/
def ver004_tr (n : String) (ins : List (String × Card)) (inh : List String)
    (out : Option (Out String)) : Trans String :=
  { core := ⟨n, ins.map (fun x => ⟨x.1, x.2⟩), inh, [], []⟩, out := out }

/-- An immediate timed net of the examples. -/
def ver004_net (ps : List String) (ts : List (Trans String)) : TimedNet String :=
  { net := { places := ps, transitions := ts }, timing := fun _ => .immediate, tol := 0 }

/-- The AC4 net: `t: one(p) + one(go) → p` and `u: one(q) + inhibitor(p) → r`. -/
def ver004_ac4 : TimedNet String :=
  ver004_net ["p", "q", "go", "r"]
    [ver004_tr "t" [("p", .one), ("go", .one)] [] (some (.place "p")),
     ver004_tr "u" [("q", .one)] ["p"] (some (.place "r"))]

/-- ✓ **AC4, the split**: in the AC4 net `u` inhibits `t`'s output `p`, so `t` is split and
nothing else: the split net lists `t`, then `complete:t`, then `u`; its places are the net's
followed by `inflight:t`; `t`'s start half outputs only `inflight:t` and its completion step
consumes `one(inflight:t)` and deposits `p`. Under `assumeAtomicFiring` the net is verified as
it is. -/
@[evidence nonvacuous VER_004_split]
theorem VER_004_split_nonvacuous :
    splits ver004_cfg ver004_ac4.net = ["t"] ∧
    ver004FirstRefused ver004_cfg ver004_ac4.net ["t"] = none ∧
    ver004Names (refSplit ver004_cfg {} ver004_ac4) = some ["t"] ∧
    (splitTimed ver004_cfg ["t"] ver004_ac4).net.transitions.map (·.core.name) =
      ["t", "complete:t", "u"] ∧
    (splitTimed ver004_cfg ["t"] ver004_ac4).net.places = ["p", "q", "go", "r", "inflight:t"] ∧
    (splitTimed ver004_cfg ["t"] ver004_ac4).net.transitions.map
      (fun u => (u.core.inputs.map (·.place), (u.out.map Verifier.outPlaces).getD [])) =
      [(["p", "go"], ["inflight:t"]), (["inflight:t"], ["p"]), (["q"], ["r"])] ∧
    ver004Names (refSplit ver004_cfg { assumeAtomicFiring := true } ver004_ac4) = some [] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The AC7 net: `t: one(a) → p`, `H: one(p) + one(b) → ok`, `L: one(b) + inhibitor(a) → bad`. -/
def ver004_ac7 : TimedNet String :=
  ver004_net ["a", "b", "p", "ok", "bad"]
    [ver004_tr "t" [("a", .one)] [] (some (.place "p")),
     ver004_tr "H" [("p", .one), ("b", .one)] [] (some (.place "ok")),
     ver004_tr "L" [("b", .one)] ["a"] (some (.place "bad"))]

/-- The AC7 priorities: `H` at 10, every other transition at 0. -/
def ver004_prio7 : String → Int := fun n => if n = "H" then 10 else 0

/-- The AC7 property `Unreachable(bad)`. -/
def ver004_bad : VerProp String := .unreachable ["bad"]

/-- **AC7**: under conflict priority `H` pre-empts `L` (they share `b`), so `H` is split and `p`
counts as tested, which splits `t`: the split names `t` and `H`, and conflict priority stays on.
Under `assumeAtomicFiring` nothing is split and conflict priority stays on. When `H` is a ν-join,
the split under conflict priority is refused, so conflict priority is turned off and the net is
verified as it is without it (nothing else needs the split). -/
theorem VER_004_split_ac7 :
    (ver004Pruners ver004_prio7 ver004_ac7.net).map (·.core.name) = ["H"] ∧
    (refSplitPlan {} true ver004_prio7 ver004_bad ver004_cfg ver004_ac7).2 = true ∧
    ver004Names (refSplit (refSplitPlan {} true ver004_prio7 ver004_bad ver004_cfg ver004_ac7).1
      {} ver004_ac7) = some ["t", "H"] ∧
    (refSplitPlan { assumeAtomicFiring := true } true ver004_prio7 ver004_bad ver004_cfg
      ver004_ac7).2 = true ∧
    ver004Names (refSplit (refSplitPlan { assumeAtomicFiring := true } true ver004_prio7
      ver004_bad ver004_cfg ver004_ac7).1 { assumeAtomicFiring := true } ver004_ac7) = some [] ∧
    (refSplitPlan {} true ver004_prio7 ver004_bad { ver004_cfg with joins := ["H"] }
      ver004_ac7).2 = false ∧
    ver004Names (refSplit (refSplitPlan {} true ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"] } ver004_ac7).1 {} ver004_ac7) = some [] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### Violations -/

/-- A split that ignores `assumeAtomicFiring`. -/
def ver004_ignoresOpt : SplitFn String := fun cfg o X =>
  refSplit cfg { o with assumeAtomicFiring := false } X

/-- ✗ A split that ignores the opt-out violates the split block (line 1): under
`assumeAtomicFiring` it still splits `t` in the AC4 net. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_ignoresOpt : ¬ VER_004_split ver004_ignoresOpt refSplitPlan := by
  intro h
  have := congrArg ver004Names (h.1 ver004_cfg { assumeAtomicFiring := true } ver004_ac4 rfl)
  revert this
  decide +kernel

/-- A split that refuses every net with a ν-join, whether or not the join needs the split. -/
def ver004_refusesJoins : SplitFn String := fun cfg o X =>
  if o.assumeAtomicFiring then .ok (X, [])
  else if X.net.transitions.any (fun t => decide (t.core.name ∈ cfg.joins)) then
    .error "a ν-join"
  else refSplit cfg o X

/-- A net with one ν-join `j: one(k) → out` whose output nothing tests. -/
def ver004_joinNet : TimedNet String :=
  ver004_net ["k", "out"] [ver004_tr "j" [("k", .one)] [] (some (.place "out"))]

/-- ✗ Refusing a ν-join that needs no split violates the split block (line 2): nothing tests
`out`, so nothing splits and the net is verified as it is. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_refusesJoins :
    ¬ VER_004_split ver004_refusesJoins refSplitPlan := by
  intro h
  have := congrArg ver004Names (h.2.1 { ver004_cfg with joins := ["j"] } {} ver004_joinNet rfl
    (by decide +kernel))
  revert this
  decide +kernel

/-- A split without the refusals: it splits whatever needs it. -/
def ver004_noRefusal : SplitFn String := fun cfg o X =>
  if o.assumeAtomicFiring then .ok (X, [])
  else if splits cfg X.net = [] then .ok (X, [])
  else .ok (splitTimed cfg (splits cfg X.net) X, splits cfg X.net)

/-- The AC4 net with a place already named `inflight:t`. -/
def ver004_clash : TimedNet String :=
  { ver004_ac4 with net := { ver004_ac4.net with places := ver004_ac4.net.places ++ ["inflight:t"] } }

/-- ✗ A split without the refusals violates the split block (line 3): the AC4 net that already
uses the name `inflight:t` must be refused, naming `t`. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_noRefusal : ¬ VER_004_split ver004_noRefusal refSplitPlan := by
  intro h
  obtain ⟨e, he, -⟩ := h.2.2.1 ver004_cfg {} ver004_clash "t" rfl (by decide +kernel)
  have h1 : ver004Names (ver004_noRefusal ver004_cfg {} ver004_clash) = some ["t"] := by decide +kernel
  rw [he] at h1
  simp [ver004Names] at h1

/-- The last refused split transition with its cause, in net order. -/
def ver004LastRefused (cfg : SplitCfg String) (net : Reference.Net String) (sp : List String) :
    Option (String × String) :=
  ((net.transitions.filter (fun t => decide (t.core.name ∈ sp))).filterMap
    (fun t => (refusal cfg net t).map (fun c => (t.core.name, c)))).getLast?

/-- The split list as a report would print it, each name followed by `", "`. -/
def ver004ListText (sp : List String) : String := String.join (sp.map (· ++ ", "))

/-- A split whose refusal lists the split transitions and then blames the last refused one
instead of the first. -/
def ver004_lastCulprit : SplitFn String := fun cfg o X =>
  match refSplit cfg o X with
  | .error _ => .error ("In-flight actions (VER-004): " ++ ver004ListText (splits cfg X.net) ++
      (match ver004LastRefused cfg X.net (splits cfg X.net) with
       | some (n, c) => refusalHead cfg X.net n ++ " " ++ c
       | none => ""))
  | .ok r => .ok r

/-- Two ν-joins `a: one(x) → done` and `b: one(y) → done`, with `done` a terminal place. -/
def ver004_twoJoins : TimedNet String :=
  ver004_net ["x", "y", "done"]
    [ver004_tr "a" [("x", .one)] [] (some (.place "done")),
     ver004_tr "b" [("y", .one)] [] (some (.place "done"))]

/-- The configuration of `ver004_twoJoins`: `done` terminal, `a` and `b` ν-joins. -/
def ver004_twoJoinsCfg : SplitCfg String :=
  { ver004_cfg with terminals := ["done"], joins := ["a", "b"] }

/-- The error text of a split, if it refuses. -/
def ver004Err {α : Type} : Except String α → Option String
  | .ok _ => none
  | .error e => some e

/-- ✗ A split that blames the wrong transition violates the split block (line 3): two ν-joins
`a` and `b` both deposit into the terminal place `done`, so both must be split and neither can
be. The first of them in the net is `a`, so the refusal must open with `transition 'a'`; this
split's refusal opens with the list `a, b, ` and then blames `transition 'b'`. It still contains
the letter `a`, which is why the line asks how the text opens and not only what it contains. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_lastCulprit :
    ¬ VER_004_split ver004_lastCulprit refSplitPlan := by
  intro h
  obtain ⟨e, he, hp⟩ := h.2.2.1 ver004_twoJoinsCfg {} ver004_twoJoins "a" rfl (by decide +kernel)
  have h1 : ver004Err (ver004_lastCulprit ver004_twoJoinsCfg {} ver004_twoJoins) = some e := by
    rw [he]; rfl
  have h2 : (ver004Err (ver004_lastCulprit ver004_twoJoinsCfg {} ver004_twoJoins)).map
      (fun e => (("transition '" ++ "a" ++ "'").toList <+: e.toList : Bool)) = some false := by
    decide +kernel
  rw [h1] at h2
  simp only [Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at h2
  exact h2 hp

/-- The wrong culprit in words: on the two-join net the first refused transition is `a`, the
split above names `transition 'b'` and nowhere `transition 'a'`, while the reference refusal
opens with `transition 'a'`. -/
theorem ver004_lastCulprit_text :
    ver004FirstRefused ver004_twoJoinsCfg ver004_twoJoins.net
        (splits ver004_twoJoinsCfg ver004_twoJoins.net) = some "a" ∧
    (ver004Err (ver004_lastCulprit ver004_twoJoinsCfg {} ver004_twoJoins)).map
      (fun e => ("transition 'b'".toList <:+: e.toList : Bool)) = some true ∧
    (ver004Err (ver004_lastCulprit ver004_twoJoinsCfg {} ver004_twoJoins)).map
      (fun e => ("transition 'a'".toList <:+: e.toList : Bool)) = some false ∧
    (ver004Err (refSplit ver004_twoJoinsCfg {} ver004_twoJoins)).map
      (fun e => ("transition 'a'".toList <+: e.toList : Bool)) = some true := by
  decide +kernel

/-- A split blind to terminal places. -/
def ver004_terminalBlind : SplitFn String := fun cfg o X =>
  refSplit { cfg with terminals := [] } o X

/-- A net `t: one(a) → done` with `done` a terminal place. -/
def ver004_termNet : TimedNet String :=
  ver004_net ["a", "done"] [ver004_tr "t" [("a", .one)] [] (some (.place "done"))]

/-- ✗ A split blind to terminal places violates the split block (line 4): `t` deposits into the
terminal `done`, which inhibits every transition, so `t` is split. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_terminalBlind :
    ¬ VER_004_split ver004_terminalBlind refSplitPlan := by
  intro h
  have := congrArg ver004Names (h.2.2.2.1 { ver004_cfg with terminals := ["done"] } {}
    ver004_termNet rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- The split net whose completion steps keep the transition's output spec, forwards included. -/
def ver004_splitKeep {K : Type} (cfg : SplitCfg K) (sp : List String) (X : TimedNet K) :
    TimedNet K :=
  { splitTimed cfg sp X with
    net := { (splitTimed cfg sp X).net with
      transitions := X.net.transitions.flatMap fun t =>
        if t.core.name ∈ sp then
          [Verifier.Split.startHalf cfg t, { Verifier.Split.endHalf cfg t with out := t.out }]
        else [t] } }

/-- A split whose completion step keeps each `forwardInput` leaf. -/
def ver004_keepForward : SplitFn String := fun cfg o X =>
  match refSplit cfg o X with
  | .ok (Y, sp) => if sp = [] then .ok (Y, sp) else .ok (ver004_splitKeep cfg sp X, sp)
  | .error e => .error e

/-- The forward sources of each transition of a split's net. -/
def ver004Fwds {K : Type} : Except String (TimedNet K × List String) → List (List K)
  | .ok p => p.1.net.transitions.map fun u => (u.out.map Verifier.Split.fwdSrcs).getD []
  | .error _ => []

/-- A net `t: one(a) → forwardInput(a, b)` and `u: one(c) + inhibitor(b) → d`. -/
def ver004_fwdNet : TimedNet String :=
  ver004_net ["a", "b", "c", "d"]
    [ver004_tr "t" [("a", .one)] [] (some (.forward "a" "b")),
     ver004_tr "u" [("c", .one)] ["b"] (some (.place "d"))]

/-- ✗ A completion step that keeps a forward violates the split block (line 4): it would draw
from `a`, which the start half has already consumed, where the completion step deposits into `b`
as the place it names. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_keepForward :
    ¬ VER_004_split ver004_keepForward refSplitPlan := by
  intro h
  have := congrArg ver004Fwds (h.2.2.2.1 ver004_cfg {} ver004_fwdNet rfl (by decide +kernel)
    (by decide +kernel))
  revert this
  decide +kernel

/-- A plan that never turns conflict priority off. -/
def ver004_noFallback : SplitPlanFn String := fun _ c prio φ cfg X =>
  if c then (ver004WithConflict prio (ver004WithCount cfg φ) X.net, true)
  else (ver004WithCount cfg φ, false)

/-- ✗ A plan that keeps conflict priority when the split under it is refused violates the split
block (line 7): in the AC7 net with `H` a ν-join, `H` cannot be split, so conflict priority is
turned off. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_noFallback : ¬ VER_004_split refSplit ver004_noFallback := by
  intro h
  have := congrArg Prod.snd (h.2.2.2.2.2.2 {} ver004_prio7 ver004_bad
    { ver004_cfg with joins := ["H"] } ver004_ac7 "H" rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- A plan that ignores the property, so the `QuiescentCount` demand. -/
def ver004_noCountDemand : SplitPlanFn String := fun o c prio _ cfg X =>
  refSplitPlan o c prio (.deadlockFree [] []) cfg X

/-- The terminal-stop net: `t: one(a) → ok`, `f: one(s) → done`, `done` terminal. -/
def ver004_stopNet : TimedNet String :=
  ver004_net ["a", "ok", "s", "done"]
    [ver004_tr "t" [("a", .one)] [] (some (.place "ok")),
     ver004_tr "f" [("s", .one)] [] (some (.place "done"))]

/-- ✗ A plan without the `QuiescentCount` demand violates the split block (line 5): with
`QuiescentCount([a, ok], 1)` on a net whose terminal `done` the property does not waive, `a` and
`ok` count as tested, so `t` is split too. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_noCountDemand :
    ¬ VER_004_split refSplit ver004_noCountDemand := by
  intro h
  have := congrArg (fun p => p.1.tested) (h.2.2.2.2.1 {} ver004_prio7
    (.quiescentCount ["a", "ok"] 1 none []) { ver004_cfg with terminals := ["done"] }
    ver004_stopNet)
  revert this
  decide +kernel

/-- A plan without the conflict demand. -/
def ver004_noConflictDemand : SplitPlanFn String := fun _ c _ φ cfg _ =>
  (ver004WithCount cfg φ, c)

/-- ✗ A plan without the conflict demand violates the split block (line 6): in the AC7 net the
pruning transition `H` must be forced. -/
@[evidence forbids VER_004_split]
theorem VER_004_split_forbids_noConflictDemand :
    ¬ VER_004_split refSplit ver004_noConflictDemand := by
  intro h
  have := congrArg (fun p => p.1.forced) (h.2.2.2.2.2.1 {} ver004_prio7 ver004_bad ver004_cfg
    ver004_ac7 (Or.inr (Or.inr (by decide +kernel))))
  revert this
  decide +kernel

end Libpetri.Spec
