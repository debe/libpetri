import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.EXEC_040

set_option linter.missingDocs true

/-!
# EXEC-040: Standard quiescence (`spec/04-execution-model.md`)

When an executor without environment places stops on its own, over the executor model
(`RefExec`, `Reference/Exec.lean`). The run ends with a `finish c` step; `finish quiescent` is the
end of EXEC-040. The requirement is a predicate over an abstract executor `R : XRel N T`
(glossary `GlossaryExec.lean`), checked against the reference executor and against executors that
test for rest before the enablement update (R-EXEC-10: one that labels that point `update`,
`finishBeforeUpdate`; one that tests right after step 1 and labels that point `test`,
`testAfterStep1`; one that leaves step 2 straight for the test, `skipUpdate`), that end while an
action is still running (AC2), that end while a transition is armed and waiting for its earliest
bound, that wait for "no transition enabled" instead of "no transition armed" (a mutant reading,
ruling D5 and the `exec040_rest_reaped_enabled` citation of `ClashesTime.lean`), and that return
another marking than the one they hold.

Ruling D13 (a) fixes the test point: the termination test (phase `test`) follows the cycle's
enablement update and its deadline step, and rest (`Rest`, glossary) is "nothing armed, nothing in
flight, nothing queued". Line 1 reads the phase the executor sets itself; line 5 reads the step
labels of a run (`after T, until G, never B`, glossary `Ears.lean`), so an executor cannot meet
it by calling an early point its termination test. Ruling D13 (a) also scopes the requirement to
nets without terminal places; lines 3 and 4 read that scope as "no terminal place is marked"
(`Live`), which every state of such a net satisfies (`exec040_live_of_noTerminals`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The steps line 5 reads -/

namespace Exec040

variable {N T : Type}

/-- The step is an executor step of the cycle other than the enablement update, the deadline
step and the answer to a snapshot request: not an outside step ([CONC-001]), not `update`, not
`deadline`, not `snapshot`. After such a step the next termination test needs an update first.
A snapshot answer reads the state and is not a step of the loop ([EXEC-041], `exec041_loopStep`),
so it does not trigger the line. -/
def cycleStep (e : XStep N T) : Bool :=
  !e.2.1.outside &&
    match e.2.1 with
    | .update | .deadline _ | .snapshot _ => false
    | _ => true

/-- The step terminates as quiescent. -/
def finishesQuiescent (e : XStep N T) : Bool :=
  match e.2.1 with
  | .finish .quiescent => true
  | _ => false

end Exec040

open Exec040

/-! ## EXEC-040: Standard Quiescence -/

requirement EXEC_040
  id "EXEC-040"
  title "Standard Quiescence"
  kind B
  scope "executors without environment places"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_040.s1, EXEC_040.s2, EXEC_040.s3, EXEC_040.s4, EXEC_040.s5, EXEC_040.s6, EXEC_040.s7,
        EXEC_040.s8, EXEC_040.s9, EXEC_040.s10, EXEC_040.s11, EXEC_040.s12
  reading "For every executor R and every configuration C without environment places:"
          "a finish quiescent step happens only at the termination test (phase test);"
          "a finish quiescent step happens only at rest: no transition armed, no firing in flight, and the completion, publication and event queues empty;"
          "at a termination test with no terminal place marked and at rest, every executor step is a finish step (outside steps such as the clock advancing are still possible, and an answer to a snapshot request that leaves the state as it is is not a step of the loop and is allowed);"
          "a finish step from such a test leaves the marking as it is;"
          "on every run of R under C, after each executor step other than an enablement update, a deadline step or a snapshot answer, no finish quiescent step happens before the next enablement update."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A run (XRun) is a list of consecutive steps (source, label, target) of R, from any state. A run ends with a step finish c, where c is the termination cause of EXEC-041; 'terminate as quiescent' is finish quiescent, 'terminate' is any finish step. The executor steps are the labels that are not outside (XLbl.outside, CONC-001): an outside step is the host clock advancing or a caller or an action acting, which no executor controls. The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor: the termination checks of run_async in executor_core/executor.rs, after its Phase 3 (update_enablement_and_emit) and Phase 4 (enforce_deadlines)."
          "Scope (ruling D13 (a)): the lead-in scopes the requirement to nets without terminal places. Lines 3 and 4 read that scope as 'no terminal place is marked' (Live), the premise of the first shall sentence, which every state of a net without terminal places satisfies (exec040_live_of_noTerminals). Lines 1, 2 and 5 carry no such premise: they bind every executor without environment places, with terminal places or without, which is stronger than the lead-in and is what the second, third and fourth shall sentences say. A net whose terminal place is marked stops at once on that place, whatever is in flight (EXEC-042); that stop is not quiescence and is not this block's subject. EXEC-042's first line forbids every executor step but finish terminal while a terminal place is marked, so no finish quiescent happens there, and EXEC-041's first line keeps the marking on every finish."
          "The test point (ruling D13 (a), R-EXEC-10) is lines 1 and 5 and the test-point sentence: arming happens only in the enablement update (TIME-010), so straight after a deposit the transition it enabled is off, not armed, and the three conditions read at that instant hold. Line 1 reads the loop phase, which the executor sets itself; line 5 reads the labels of the steps of a run, so an executor that tests early cannot pass by calling the early point its termination test. An executor that tests before the update and calls that point the update breaks line 1 (EXEC_040_forbids_finishBeforeUpdate). One that tests straight after step 1 and calls that point the termination test (in Java or TypeScript the termination check moved above the enablement update, in Rust the enabled and in-flight count check moved above Phase 3) meets lines 1 to 4 and breaks line 5: on the chain it ends at once from the initial state, the token still in place 0 (EXEC_040_forbids_testAfterStep1). One that leaves step 2 straight for the termination test, skipping the update and the deadline step, breaks line 5 as well (EXEC_040_forbids_skipUpdate). Rust, Java and TypeScript all test once per cycle after the update and the deadline step."
          "Rest is the glossary term Rest of GlossaryExec (restB): no transition armed, no firing in flight, the completion, publication and event queues empty, which is ruling D13 (a)'s 'nothing armed, in flight or queued'. Condition 1 is its first conjunct. Condition 2 is its in-flight conjunct together with its completion and publication conjuncts: condition 2's second sentence counts a firing as in flight until its completion and its queued publications are processed, which is why the markdown names three conditions where Rest has five conjuncts. A firing stays in the in-flight list until its settle step, and settling happens only in step 1, the wait and the pass (exec040_canSettle_test), so an action that returned but whose completion is not yet processed still counts. The completion and publication conjuncts have no mutant of their own: a completion or a publication is queued only for a firing in the in-flight list, and that firing cannot settle between step 1b and the test, so in the reference's runs the in-flight conjunct already rejects those states (an argument, not a proved invariant). Condition 3 is the event-queue conjunct. It is vacuous under the requirement's premise (clash exec#14, kept as ruled): without environment places a request is answered error and queues nothing (exec040_no_injection), and the conjunct is there because ENV-010 and ENV-011 reuse the same Rest."
          "The second shall sentence is line 1 and the third is line 5. Line 5 reads 'takes a step' as a step of the loop: the answer to a snapshot request reads the state and is not a step of the loop (EXEC-041's quoted sentence on a finished run, exec041_loopStep), so it does not trigger the line, as it is not a step line 3 bans. Without that exclusion an executor that answers a snapshot at a test at rest, which line 3 allows, could never finish quiescent from that rest: line 5 would then ban the finish until the next update, and line 3 bans the update there (EXEC_040_allows_snapshotAtTest is that run, which line 5 accepts). The fourth is line 2: an executor that ends while an action runs breaks line 2 (EXEC_040_forbids_finishInFlight), and one that ends while a Window(3, 5) transition is armed and waiting for its earliest bound, nothing being ready yet, breaks it too (EXEC_040_forbids_finishWhileArmed)."
          "The first shall sentence is lines 3 and 4. 'Shall terminate' is read as line 3: at such a test the executor takes no step but a finish (in particular no firing pass, begin), of any cause. A finish closed is also a finish, so a closed executor at rest may report either cause (ruling D53 (c), EXEC-041); a finish stopped is allowed by line 3 as well and is tied to a stopped executor by EXEC-041; a finish terminal is excluded by EXEC-041, which requires a marked terminal place for it. That a finish step is in fact offered at every such test is coverage, which belongs to the consistency theorem, as for every requirement over an abstract executor: its conjunct is Exec040Covers, a clause of ExecCoversW5 (ConsistencyExec.lean). Line 3 alone is safety, so an executor that never finishes at rest (the reference without its finish quiescent rule, or a stale enabled count that never reaches zero) passes this block and fails that conjunct. The reference offers finish quiescent at every such test (exec040_finish_offered), the lemma the coverage conjunct is proved from. 'Return the marking as it is' is line 4 (EXEC_040_forbids_emptyMarking); 'The final marking is returned.' is the same line."
          "Condition 1 reads 'armed', not 'enabled' (ruling D5): a reaped transition that is still enabled holds no clock (TIME-013), so the executor stops with its tokens in place. EXEC_040_allows_reapedRest is the run: a Window(3, 5) transition reaped at reading 10 stays enabled, the test finds rest, and the reference finishes quiescent with the token still in the input place. The mutant reading that waits for 'no transition enabled' starts a firing pass there instead (EXEC_040_mutant_enabled_killed); the Phase 1 citation exec040_rest_reaped_enabled (ClashesTime.lean) shows that from this rest nothing ever fires and u stays enabled, so an executor that waits for 'no transition enabled' never stops."
          "AC1 (a chain A to B to C runs to completion and returns the marking with the token in C) is liveness: that the executor gets to the end is an ideal run (IdealRun, an assumption of kind A: every action returns) together with the coverage above, not a line. EXEC_040_nonvacuous decides the chain's run from the initial state: two firings, then finish quiescent with the token in C and A and B empty; the same run exercises line 5's trigger, its release and its banned step. The test derivation (a chain of 5 transitions) is the same run, longer."
          "AC2 (parallel branches: the executor waits for every action in flight before it terminates) is line 2: no finish quiescent while a firing is in flight (EXEC_040_forbids_finishInFlight, with the chain's first action still running)."
  signoff "2026-11-13 d7c9760fb7ca0f84 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C, C.envs = [] →
      (on (fun s s' => R C s (.finish .quiescent) s'), shall (fun s _ => s.phase = .test)) ∧
      (on (fun s s' => R C s (.finish .quiescent) s'), shall (fun s _ => Rest C s)) ∧
      (while (fun s => Live C s ∧ s.phase = .test ∧ Rest C s), never (fun s s' =>
        ∃ l, R C s l s' ∧ l.outside = false ∧ (∀ a, l = .snapshot a → s' ≠ s) ∧ ∀ c, l ≠ .finish c)) ∧
      (on (fun s s' => (Live C s ∧ s.phase = .test ∧ Rest C s) ∧ ∃ c, R C s (.finish c) s'),
        shall (fun s s' => s'.M = s.M)) ∧
      (∀ s0 tr, XRun R C s0 tr → (after cycleStep, until isUpdate, never finishesQuiescent) tr)

/- The pinned readable form of EXEC-040: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_040 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    C.envs = [] →
      (on fun s s' => R C s (XLbl.finish Cause.quiescent) s', shall fun s x => s.phase = Phase.test) ∧
        (on fun s s' => R C s (XLbl.finish Cause.quiescent) s', shall fun s x => Rest C s) ∧
          (while fun s => Live C s ∧ s.phase = Phase.test ∧ Rest C s, never fun s s' =>
              ∃ l,
                R C s l s' ∧
                  l.outside = false ∧
                    (∀ (a : Option Bool), l = XLbl.snapshot a → s' ≠ s) ∧ ∀ (c : Cause), l ≠ XLbl.finish c) ∧
            (on fun s s' => (Live C s ∧ s.phase = Phase.test ∧ Rest C s) ∧ ∃ c, R C s (XLbl.finish c) s', shall
                fun s s' => s'.M = s.M) ∧
              ∀ (s0 : XSt N T) (tr : List (XStep N T)),
                XRun R C s0 tr → (after cycleStep, until isUpdate, never finishesQuiescent) tr
-/
#guard_msgs in #print EXEC_040

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The lines of EXEC-040 with the rest predicate as a parameter `rest` (the requirement reads
`Rest`). -/
def exec040Lines (rest : Cfg N T → XSt N T → Prop) (R : XRel N T) : Prop :=
  ∀ C, C.envs = [] →
    (on (fun s s' => R C s (.finish .quiescent) s'), shall (fun s _ => s.phase = .test)) ∧
    (on (fun s s' => R C s (.finish .quiescent) s'), shall (fun s _ => rest C s)) ∧
    (while (fun s => Live C s ∧ s.phase = .test ∧ rest C s), never (fun s s' =>
      ∃ l, R C s l s' ∧ l.outside = false ∧ (∀ a, l = .snapshot a → s' ≠ s) ∧
        ∀ c, l ≠ .finish c)) ∧
    (on (fun s s' => (Live C s ∧ s.phase = .test ∧ rest C s) ∧ ∃ c, R C s (.finish c) s'),
      shall (fun s s' => s'.M = s.M)) ∧
    (∀ s0 tr, XRun R C s0 tr → (after cycleStep, until isUpdate, never finishesQuiescent) tr)

omit [DecidableEq N] in
/-- A net without terminal places has no terminal place marked in any state: the requirement's
scope (ruling D13 (a)) is inside the premise `Live` of lines 3 and 4. -/
theorem exec040_live_of_noTerminals {C : Cfg N T} (h : C.terminals = []) (s : XSt N T) :
    Live C s := by
  simp [Live, liveB, h]

omit [DecidableEq N] in
/-- No settle step at the termination test: settling is allowed in step 1, the wait and the
pass only. -/
theorem exec040_canSettle_test {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hp : s.phase = .test) : canSettle C s i f = false := by
  simp [canSettle, settleOk, hp]

/-- **At the termination test** the executor with judgement points `P` takes no executor step
but `begin` or a `finish`: every other rule names another phase. -/
theorem exec040_test_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (hp : s.phase = .test) (h : xstepW P C s l = some s') :
    l.outside = true ∨ l = .begin ∨ ∃ c, l = .finish c := by
  have hc := fun i f => exec040_canSettle_test (C := C) (i := i) (f := f) hp
  cases l with
  | commit i =>
    obtain ⟨f, e, -, -, h1, -⟩ := commitStep_some (P := P) h
    simp [hc] at h1
  | fail i =>
    obtain ⟨f, -, h1, -⟩ := failStep_some (P := P) h
    simp [hc] at h1
  | tdeposit i =>
    obtain ⟨f, e, -, -, h1, -⟩ := tdepositStep_some h
    simp [hc] at h1
  | endCompletions => obtain ⟨h1, -⟩ := xstepW_endCompletions h; simp [hp] at h1
  | publish i =>
    obtain ⟨b, rest, -, -, h1, -⟩ := publishStep_some h
    rcases h1 with h1 | ⟨h1, -⟩ <;> simp [hp] at h1
  | endPublications => obtain ⟨h1, -⟩ := xstepW_endPublications h; simp [hp] at h1
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, h1, -⟩ := injectStep_some h
    rcases h1 with h1 | h1 <;> simp [hp] at h1
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, h1, -⟩ := discardStep_some h
    rcases h1 with h1 | h1 <;> simp [hp] at h1
  | snapshot a =>
    obtain ⟨-, h1, -⟩ := snapshotStep_some h
    rcases h1 with h1 | h1 | h1 <;> simp [hp] at h1
  | endEvents => obtain ⟨h1, -⟩ := xstepW_endEvents h; simp [hp] at h1
  | update => obtain ⟨h1, -⟩ := xstepW_update h; simp [hp] at h1
  | deadline ns => obtain ⟨h1, -⟩ := xstepW_deadline h; simp [hp] at h1
  | begin => exact .inr (.inl rfl)
  | finish c => exact .inr (.inr ⟨c, rfl⟩)
  | start n sy =>
    obtain ⟨t, rest, -, h1, -⟩ := startStep_some h
    simp [hp] at h1
  | lose n =>
    obtain ⟨t, rest, -, h1, -⟩ := loseStep_some h
    simp [hp] at h1
  | endPass => obtain ⟨h1, -⟩ := xstepW_endPass h; simp [hp] at h1
  | park tmr => obtain ⟨h1, -⟩ := parkStep_some h; simp [hp] at h1
  | wake => obtain ⟨h1, -⟩ := wakeStep_some h; simp [hp] at h1
  | delay _ | write _ _ _ | flush _ | ret _ _ | expire _ _ | request _ _ _ | drain | close
  | terminateNow => exact .inl rfl

/-- Every finish step of the executor with judgement points `P` leaves the marking. -/
theorem exec040_finish_M {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {c : Cause}
    (h : xstepW P C s (.finish c) = some s') : s'.M = s.M := by
  cases c with
  | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
  | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
  | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
  | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl

omit [DecidableEq N] in
/-- What `cycleStep` reads: an executor step that is neither the update, a deadline step nor a
snapshot answer. -/
theorem exec040_cycleStep_iff {e : XStep N T} :
    cycleStep e = true ↔
      e.2.1.outside = false ∧ e.2.1 ≠ .update ∧ (∀ ns, e.2.1 ≠ .deadline ns) ∧
        ∀ a, e.2.1 ≠ .snapshot a := by
  obtain ⟨s, l, s'⟩ := e
  cases l <;> simp [cycleStep, XLbl.outside]

/-- **No early test point**: every executor step of the executor with judgement points `P` other
than the update and a deadline step leaves the loop outside the two phases that follow the update
(`isBoundary`: `deadline` and `test`). -/
theorem exec040_step_nonBoundary {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (ho : l.outside = false) (hu : l ≠ .update)
    (hd : ∀ ns, l ≠ .deadline ns) : isBoundary s'.phase = false := by
  cases l with
  | delay | write | flush | ret | expire | request | drain | close | terminateNow =>
    simp [XLbl.outside] at ho
  | commit i =>
    obtain ⟨f, e, -, -, hc, -, -, rfl⟩ := commitStep_some h
    exact canSettle_phase hc
  | fail i =>
    obtain ⟨f, -, hc, -, rfl⟩ := failStep_some h
    exact canSettle_phase hc
  | tdeposit i =>
    obtain ⟨f, e, -, -, hc, -, rfl⟩ := tdepositStep_some h
    exact canSettle_phase hc
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    simp [isBoundary]
  | publish i =>
    obtain ⟨b, rest, -, -, hph, rfl⟩ := publishStep_some h
    rcases hph with hp | ⟨hp, -⟩ <;> simp [hp, isBoundary]
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    simp [isBoundary]
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := injectStep_some h
    rcases hph with hp | hp <;> simp [hp, isBoundary]
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := discardStep_some h
    rcases hph with hp | hp <;> simp [hp, isBoundary]
  | snapshot a =>
    obtain ⟨-, hph, -, rfl⟩ := snapshotStep_some h
    rcases hph with hp | hp | hp <;> simp [hp, isBoundary]
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    simp [isBoundary]
  | update => exact absurd rfl hu
  | deadline ns => exact absurd rfl (hd ns)
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; simp [isBoundary]
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; simp [isBoundary]
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; simp [isBoundary]
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; simp [isBoundary]
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    simp [isBoundary]
  | start n sy =>
    obtain ⟨t, rest, -, hph, -, -, -, -, -, rfl⟩ := startStep_some h
    simp [hph, isBoundary]
  | lose n =>
    obtain ⟨t, rest, -, hph, -, -, -, -, rfl⟩ := loseStep_some h
    simp [hph, isBoundary]
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    split <;> simp [isBoundary]
  | park tmr =>
    obtain ⟨hph, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    simp [hph, isBoundary]
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    simp [isBoundary]

omit [DecidableEq N] in
/-- A line `after T, until G, never B` holds of every run of `R` when some invariant `I` of the
states holds after every `T` step, is kept by every step that is not a `G` step, and allows no
`B` step (the proof pattern of EXEC-001). -/
theorem exec040_aun_of_inv {R : XRel N T} {C : Cfg N T} (I : XSt N T → Prop)
    {trig go bad : XStep N T → Bool}
    (hbad : ∀ s l s', R C s l s' → I s → bad (s, l, s') = false)
    (hkeep : ∀ s l s', R C s l s' → I s → go (s, l, s') = false → I s')
    (htrig : ∀ s l s', R C s l s' → trig (s, l, s') = true → I s') :
    ∀ s0 tr, XRun R C s0 tr → AfterUntilNever trig go bad tr := by
  suffices H : ∀ (tr : List (XStep N T)) (s0 : XSt N T) (b : Bool), XRun R C s0 tr →
      (b = true → I s0) → (afterUntilNever trig go bad).scan b tr = true from
    fun s0 tr h => H tr s0 false h (by simp)
  intro tr
  induction tr with
  | nil => intro _ _ _ _; rfl
  | cons e rest ih =>
    intro s0 b hr hb
    obtain ⟨s, l, s'⟩ := e
    obtain ⟨he, hE, hr'⟩ := hr
    simp only at he hE hr'
    subst he
    simp only [Watch.scan, afterUntilNever, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih s' _ hr' ?_⟩
    · cases b
      · simp
      · simp [hbad _ _ _ hE (hb rfl)]
    · intro hn
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hn
      rcases hn with ⟨h1, h2⟩ | h1
      · exact hkeep _ _ _ hE (hb h1) h2
      · exact htrig _ _ _ hE h1

omit [DecidableEq N] in
/-- Line 5 from four facts about the phases of `R`: outside steps keep the phase, every other
executor step but the update and a deadline step leaves the loop outside `deadline` and `test`,
a deadline step starts in `deadline` and `finish quiescent` in `test`. The invariant is "the
phase is neither `deadline` nor `test`": only the update leaves it. -/
theorem exec040_run_of {R : XRel N T} {C : Cfg N T}
    (hout : ∀ s l s', R C s l s' → l.outside = true → s'.phase = s.phase)
    (hstep : ∀ s l s', R C s l s' → l.outside = false → l ≠ .update →
      (∀ ns, l ≠ .deadline ns) → isBoundary s'.phase = false)
    (hdl : ∀ s ns s', R C s (.deadline ns) s' → s.phase = .deadline)
    (hfq : ∀ s s', R C s (.finish .quiescent) s' → s.phase = .test) :
    ∀ s0 tr, XRun R C s0 tr → (after cycleStep, until isUpdate, never finishesQuiescent) tr := by
  refine exec040_aun_of_inv (fun s => isBoundary s.phase = false) ?_ ?_ ?_
  · intro s l s' h hI
    cases l with
    | finish c =>
      cases c with
      | quiescent => simp [hfq s s' h, isBoundary] at hI
      | _ => rfl
    | _ => rfl
  · intro s l s' h hI hg
    cases ho : l.outside with
    | true => rw [hout s l s' h ho]; exact hI
    | false =>
      by_cases hd : ∃ ns, l = .deadline ns
      · obtain ⟨ns, rfl⟩ := hd
        simp [hdl s ns s' h, isBoundary] at hI
      · refine hstep s l s' h ho ?_ fun ns e => hd ⟨ns, e⟩
        rintro rfl
        simp [isUpdate] at hg
  · intro s l s' h ht
    obtain ⟨ho, hu, hd, -⟩ := exec040_cycleStep_iff.mp ht
    exact hstep s l s' h ho hu hd

/-- The executor with judgement points `P` meets line 5. -/
theorem exec040_run_xstepW (P : XPol N T) (C : Cfg N T) :
    ∀ s0 tr, XRun (fun C s l s' => xstepW P C s l = some s') C s0 tr →
      (after cycleStep, until isUpdate, never finishesQuiescent) tr :=
  exec040_run_of (fun _ _ _ h ho => (xstepW_outside_frame h ho).2.2.1)
    (fun _ _ _ h ho hu hd => exec040_step_nonBoundary h ho hu hd)
    (fun _ _ _ h => (xstepW_deadline h).1) (fun _ _ h => (xstepW_finishQuiescent h).1)

/-- The executor of any judgement points `P` meets the lines of EXEC-040: `finish quiescent`
requires phase `test` and `finishQ`, which contains `restB` (`xstepW_finishQuiescent`); at a
test only `begin` and the finishes are steps (`exec040_test_step`), and `begin` requires
`finishQ` to fail, which it does not at rest without environment places (`xstepW_begin`); every
finish keeps the marking (`exec040_finish_M`); only the update enters the phases after it
(`exec040_run_xstepW`). -/
theorem exec040Lines_xstepW (P : XPol N T) :
    exec040Lines (fun C s => Rest C s) (fun C s l s' => xstepW P C s l = some s') := by
  intro C hE
  refine ⟨fun s s' h => (xstepW_finishQuiescent h).1, fun s s' h => ?_, ?_, ?_,
    exec040_run_xstepW P C⟩
  · have hq := (xstepW_finishQuiescent h).2.2.1
    simp only [finishQ, Bool.and_eq_true] at hq
    exact hq.1
  · rintro s s' ⟨l, hl, ho, -, hf⟩ ⟨-, hp, hr⟩
    rcases exec040_test_step hp hl with h1 | rfl | ⟨c, rfl⟩
    · simp [ho] at h1
    · have hq := (xstepW_begin hl).2.2.1
      have hr' : restB C s = true := hr
      simp [finishQ, hr', hE] at hq
    · exact hf c rfl
  · rintro s s' ⟨-, c, h⟩
    exact exec040_finish_M h

/-- Without environment places a request queues nothing: it is answered `error` and the state
stays as it is. Condition 3 ("No external events are pending.") is vacuous in the requirement's
scope (clash exec#14). -/
theorem exec040_no_injection {C : Cfg N T} (hE : C.envs = []) {s s' : XSt N T} {p : N} {x : T}
    {r : Reply} (h : RefExec C s (.request p x r) s') : r = .error ∧ s' = s := by
  obtain ⟨hr, h1⟩ := requestStep_some (C := C) h
  have he : replyFor C s p = .error := by simp [replyFor, hE]
  rw [he] at hr
  subst hr
  rcases h1 with ⟨h2, -⟩ | ⟨-, h2⟩
  · cases h2
  · exact ⟨rfl, h2⟩

/-- Coverage (the first shall sentence's 'shall terminate', for the consistency theorem's
`ExecCovers`): without environment places the reference offers `finish quiescent` at every
termination test with no terminal place marked and at rest. -/
theorem exec040_finish_offered (C : Cfg N T) (s : XSt N T) (hE : C.envs = []) (hL : Live C s)
    (hp : s.phase = .test) (hr : Rest C s) :
    ∃ s', RefExec C s (.finish .quiescent) s' := by
  have hl : liveB C s = true := hL
  have hr' : restB C s = true := hr
  exact ⟨{ s with phase := .done .quiescent, eq := [] }, by
    simp [RefExec, xstep, xstepW, hp, hl, finishQ, hr', hE]⟩

end Reference

/-- ✓ The reference executor satisfies EXEC-040 (`exec040Lines_xstepW` at `refXPol`). -/
@[evidence holds EXEC_040]
theorem EXEC_040_reference {N T : Type} [DecidableEq N] :
    EXEC_040 (RefExec (N := N) (T := T)) :=
  exec040Lines_xstepW refXPol

/-! ### Examples

Transitions take one token from one place and put one into another; validation and the relay
check accept everything (they are EXEC-021's subject); no terminal and no environment places. The
chain `t1 : 0 → 1`, `t2 : 1 → 2` is Immediate (AC1); the transition `u : 0 → 1` is `Window(3, 5)`
with tolerance `0` (the example of `exec040_rest_reaped_enabled`). The token is `7`, in place `0`.
-/

/-- A transition named `n`: one token from `i`, output spec `Out.place o`. -/
def exec040_t (n : String) (i o : Nat) : Trans Nat :=
  { core := { name := n, inputs := [⟨i, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place o) }

/-- The configuration of the examples: transitions `ts`, all with timing `tm`. -/
def exec040_cfg (ts : List (Trans Nat)) (tm : Libpetri.Novel.TimedScg.Timing) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := ts }, timing := fun _ => tm, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The chain `0 → 1 → 2`, Immediate. -/
def exec040_chain : Cfg Nat Nat := exec040_cfg [exec040_t "t1" 0 1, exec040_t "t2" 1 2] .immediate

/-- One transition `u : 0 → 1`, `Window(3, 5)`. -/
def exec040_win : Cfg Nat Nat := exec040_cfg [exec040_t "u" 0 1] (.window 3 5)

/-- The initial marking: the token `7` in place `0`. -/
def exec040_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- Steps 1, 1b and 2 of a cycle with nothing queued. -/
def exec040_top : List (XLbl Nat Nat) := [.endCompletions, .endPublications, .endEvents]

/-- The chain's first cycle: `t1` starts, its action runs. -/
def exec040_c1 : List (XLbl Nat Nat) :=
  exec040_top ++ [.update, .deadline [], .begin, .start "t1" false, .endPass]

/-- Up to the deposit of `t1`'s token in `1` and steps 1b and 2 of that cycle: the next step is
the enablement update, which arms `t2`. -/
def exec040_afterDeposit : List (XLbl Nat Nat) :=
  exec040_c1 ++ [.write 0 1 7, .ret 0 true, .commit 0] ++ exec040_top

/-- The chain's run up to its last termination test: `t2` fires and deposits in `2`. -/
def exec040_chainRest : List (XLbl Nat Nat) :=
  exec040_afterDeposit ++ [.update, .deadline [], .begin, .start "t2" false, .endPass,
    .write 1 2 7, .ret 1 true, .commit 1] ++ exec040_top ++ [.update, .deadline []]

/-- `u` armed at reading `0`, waiting for its earliest bound `3`: the first termination test. -/
def exec040_armed : List (XLbl Nat Nat) := exec040_top ++ [.update, .deadline []]

/-- `u` reaped at reading `10`, still enabled: the second termination test. -/
def exec040_reaped : List (XLbl Nat Nat) :=
  exec040_armed ++ [.begin, .endPass, .delay 10, .wake] ++ exec040_top ++
    [.update, .deadline ["u"]]

/-- The run of the step function `g` from `s` along the labels `ls`, as the list of its steps
(`none` when some label is not a step). -/
def exec040_trace {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (C : Cfg N T) : XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (exec040_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace of `g` is a run of the executor of `g`. -/
theorem exec040_trace_run {N T : Type} {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} : ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
    exec040_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | _, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [exec040_trace] at h
    cases hg : g C s l with
    | none => simp [hg] at h
    | some s' =>
      cases ht : exec040_trace g C s' ls with
      | none => simp [hg, ht] at h
      | some tr' =>
        simp only [hg, ht, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hg, exec040_trace_run ht⟩

/-- A decided trace of `g` that breaks line 5 refutes line 5 for the executor of `g`. -/
theorem exec040_not_run {N T : Type} {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s0 : XSt N T} {ls : List (XLbl N T)}
    (hc : (exec040_trace g C s0 ls).map
      (fun tr => decide ((after cycleStep, until isUpdate, never finishesQuiescent) tr)) =
      some false) :
    ¬ ∀ s0 tr, XRun (fun C s l s' => g C s l = some s') C s0 tr →
      (after cycleStep, until isUpdate, never finishesQuiescent) tr := by
  intro h
  cases ht : exec040_trace g C s0 ls with
  | none => simp [ht] at hc
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at hc
    exact hc (h s0 tr (exec040_trace_run ht))

/-! ### Violation: the test before the enablement update, labelled `update` (R-EXEC-10) -/

/-- An executor that also tests for rest at the top of step 3, before the update has armed what
the cycle's deposits enabled; otherwise the reference. -/
def exec040_earlyStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if (s.phase = .test || s.phase = .update) && liveB C s && finishQ C s then
      some { s with phase := .done .quiescent, eq := [] } else none
  | l => xstep C s l

/-- The executor of `exec040_earlyStep`. -/
def exec040_early {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_earlyStep C s l = some s'

/-- ✗ Testing before the update violates EXEC-040 (line 1): on the chain, straight after `t1`'s
token lands in `1`, `t2` is enabled and not yet armed, nothing is in flight, and the executor
finishes quiescent with the token half-way (AC1). -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_finishBeforeUpdate :
    ¬ EXEC_040 (exec040_early (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec040_earlyStep (C := exec040_chain)
    (o := xrun exec040_chain (xinit exec040_m0 0) exec040_afterDeposit) (l := .finish .quiescent)
    (p := fun s _ => s.phase != .test) (by decide)
  have := (h exec040_chain rfl).1 s s' hs
  simp [this] at hp

/-! ### Violation: the test straight after step 1, labelled `test` (R-EXEC-10) -/

/-- An executor that runs its termination test straight after step 1, before the enablement
update, and calls that point its termination test: `endCompletions` goes to phase `test` when
`restB` holds (nothing armed yet) and on to step 1b otherwise; every other rule is the
reference's. In Java or TypeScript this is the termination check moved above the enablement
update, in Rust the enabled and in-flight count check moved above Phase 3. -/
def exec040_step1TestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endCompletions =>
    if s.phase = .completions && liveB C s && s.cq.isEmpty && s.mode != .stopped then
      some { s with phase := if restB C s then .test else .publications } else none
  | l => xstep C s l

/-- The executor of `exec040_step1TestStep`. -/
def exec040_step1Test {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_step1TestStep C s l = some s'

/-- ✗ Testing straight after step 1 violates EXEC-040 (line 5), though lines 1 to 4 accept it:
on the chain, from the initial state (the token in `0`, `t1` enabled and not yet armed) the
executor leaves step 1 for its test and finishes quiescent before any update; nothing ever fires
and the token stays in `0` (AC1). -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_testAfterStep1 :
    ¬ EXEC_040 (exec040_step1Test (N := Nat) (T := Nat)) := by
  intro h
  exact exec040_not_run (g := exec040_step1TestStep) (C := exec040_chain)
    (s0 := xinit exec040_m0 0) (ls := [.endCompletions, .finish .quiescent]) (by decide)
    (h exec040_chain rfl).2.2.2.2

/-- The executor that tests straight after step 1 ends on the chain with the token in `0`. -/
theorem exec040_step1Test_endsAtOnce :
    (exec040_trace exec040_step1TestStep exec040_chain (xinit exec040_m0 0)
      [.endCompletions, .finish .quiescent]).map
      (fun tr => tr.getLast?.map fun e => decide (e.2.2.phase = .done .quiescent) &&
        e.2.2.M 0 == [7] && e.2.2.M 2 == []) = some (some true) := by
  decide

/-! ### Violation: step 2 goes straight to the test (R-EXEC-10) -/

/-- An executor whose end of step 2 goes straight to the termination test, skipping the update and
the deadline step; every other rule is the reference's. -/
def exec040_skipUpdateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents => (xstep C s .endEvents).map fun s' => { s' with phase := .test }
  | l => xstep C s l

/-- ✗ Skipping the update violates EXEC-040 (line 5): on the chain the executor reaches its test
without an update, `t1` enabled and never armed, and finishes quiescent with the token in `0`. -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_skipUpdate :
    ¬ EXEC_040 (fun C s l s' => exec040_skipUpdateStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  exact exec040_not_run (g := exec040_skipUpdateStep) (C := exec040_chain)
    (s0 := xinit exec040_m0 0) (ls := exec040_top ++ [.finish .quiescent]) (by decide)
    (h exec040_chain rfl).2.2.2.2

/-! ### Violation: ending while an action runs (AC2) -/

/-- An executor whose rest ignores the firings in flight: it ends once nothing is armed and no
completion is queued, without waiting for the actions still running. -/
def exec040_noFlStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.phase = .test && liveB C s && C.X.net.transitions.all (fun u => !armedB s u) &&
        s.cq.isEmpty && s.pq.isEmpty && s.eq.isEmpty then
      some { s with phase := .done .quiescent, eq := [] } else none
  | l => xstep C s l

/-- The executor of `exec040_noFlStep`. -/
def exec040_noFl {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_noFlStep C s l = some s'

/-- ✗ Ending while an action runs violates EXEC-040 (line 2, AC2): on the chain, `t1`'s action is
still running at the first cycle's test, nothing is armed, and the executor finishes. -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_finishInFlight : ¬ EXEC_040 (exec040_noFl (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec040_noFlStep (C := exec040_chain)
    (o := xrun exec040_chain (xinit exec040_m0 0) (exec040_c1 ++ exec040_armed))
    (l := .finish .quiescent) (p := fun s _ => !s.fl.isEmpty) (by decide)
  have hr : restB exec040_chain s = true := (h exec040_chain rfl).2.1 s s' hs
  simp only [restB, Bool.and_eq_true] at hr
  simp [hr.1.1.1.2] at hp

/-! ### Violation: ending while a transition is armed -/

/-- An executor whose rest reads "nothing Ready or Expired at the cycle reading" (`nothingDue`)
for "nothing armed": it ends while a transition waits for its earliest bound. -/
def exec040_dueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.phase = .test && liveB C s && nothingDue C s && s.fl.isEmpty &&
        s.cq.isEmpty && s.pq.isEmpty && s.eq.isEmpty then
      some { s with phase := .done .quiescent, eq := [] } else none
  | l => xstep C s l

/-- The executor of `exec040_dueStep`. -/
def exec040_due {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_dueStep C s l = some s'

/-- ✗ Ending while a transition is armed violates EXEC-040 (line 2, condition 1): `u`,
`Window(3, 5)`, is armed at reading `0`; at the test nothing is Ready yet, and the executor
finishes instead of waiting for reading `3`. -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_finishWhileArmed : ¬ EXEC_040 (exec040_due (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec040_dueStep (C := exec040_win)
    (o := xrun exec040_win (xinit exec040_m0 0) exec040_armed)
    (l := .finish .quiescent) (p := fun s _ => !restB exec040_win s) (by decide +kernel)
  have hr : restB exec040_win s = true := (h exec040_win rfl).2.1 s s' hs
  simp [hr] at hp

/-! ### Violation: another marking returned -/

/-- An executor whose `finish quiescent` hands back an empty marking; otherwise the reference. -/
def exec040_emptyStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent => (xstep C s (.finish .quiescent)).map fun s₁ => { s₁ with M := fun _ => [] }
  | l => xstep C s l

/-- The executor of `exec040_emptyStep`. -/
def exec040_empty {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_emptyStep C s l = some s'

/-- ✗ Returning another marking violates EXEC-040 (line 4): at the rest after `u` is reaped,
the token `7` is in `0`, and the finish returns an empty place `0`. -/
@[evidence forbids EXEC_040]
theorem EXEC_040_forbids_emptyMarking : ¬ EXEC_040 (exec040_empty (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec040_emptyStep (C := exec040_win)
    (o := xrun exec040_win (xinit exec040_m0 0) exec040_reaped) (l := .finish .quiescent)
    (p := fun s s' => liveB exec040_win s && decide (s.phase = .test) && restB exec040_win s &&
      s'.M 0 != s.M 0) (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  have hM := (h exec040_win rfl).2.2.2.1 s s' ⟨⟨hp.1.1.1, hp.1.1.2, hp.1.2⟩, _, hs⟩
  exact hp.2 (by rw [hM])

/-! ### Mutant: wait for "no transition enabled" (ruling D5) -/

/-- Rest read with "enabled" for "armed": no transition enabled, nothing in flight or queued. -/
def exec040_restEnB {N T : Type} (C : Cfg N T) (s : XSt N T) : Bool :=
  C.X.net.transitions.all (fun u => !enabledNA (qCount s.M) u.core) && s.fl.isEmpty &&
    s.cq.isEmpty && s.pq.isEmpty && s.eq.isEmpty

/-- The finish premise of that reading. -/
def exec040_finishQEn {N T : Type} (C : Cfg N T) (s : XSt N T) : Bool :=
  exec040_restEnB C s && (C.envs.isEmpty || s.mode != .open)

/-- An executor that ends only when no transition is enabled, and otherwise starts a firing
pass; every other rule is the reference's. -/
def exec040_enStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.phase = .test && liveB C s && exec040_finishQEn C s then
      some { s with phase := .done .quiescent, eq := [] } else none
  | .begin =>
    if s.phase = .test && liveB C s && !exec040_finishQEn C s &&
        !(s.mode.closing && s.fl.isEmpty) then
      some { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                    started := false }
    else none
  | l => xstep C s l

/-- The executor of `exec040_enStep`. -/
def exec040_en {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec040_enStep C s l = some s'

/-- Mutant reading of EXEC-040 (ruling D5, the literal 'no transition enabled'): the lines over
the rest that reads "enabled" for "armed". -/
def EXEC_040_mutant_enabled {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  exec040Lines (fun C s => exec040_restEnB C s = true) R

/-- The mutant executor agrees with the reference on every label but `finish quiescent` and
`begin`. -/
theorem exec040_enStep_eq {N T : Type} [DecidableEq N] {C : Cfg N T} {s : XSt N T}
    {l : XLbl N T} (hq : l ≠ .finish .quiescent) (hb : l ≠ .begin) :
    exec040_enStep C s l = xstep C s l := by
  cases l with
  | begin => exact absurd rfl hb
  | finish c => cases c with
    | quiescent => exact absurd rfl hq
    | _ => rfl
  | _ => rfl

/-- The executor that waits for "no transition enabled" meets the mutant reading. -/
theorem exec040_en_mutant {N T : Type} [DecidableEq N] :
    EXEC_040_mutant_enabled (exec040_en (N := N) (T := T)) := by
  intro C hE
  have hfin : ∀ {s s' : XSt N T}, exec040_enStep C s (.finish .quiescent) = some s' →
      s.phase = .test ∧ exec040_finishQEn C s = true ∧ s'.M = s.M ∧
        isBoundary s'.phase = false := by
    intro s s' h
    simp only [exec040_enStep] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      cases h
      exact ⟨hc.1.1, hc.2, rfl, rfl⟩
    · cases h
  have hbeg : ∀ {s s' : XSt N T}, exec040_enStep C s .begin = some s' →
      s'.phase = .pass := by
    intro s s' h
    simp only [exec040_enStep] at h
    split at h
    · cases h; rfl
    · cases h
  have href : ∀ {s s' : XSt N T} {l : XLbl N T}, exec040_en C s l s' →
      l ≠ .finish .quiescent → l ≠ .begin → xstep C s l = some s' := by
    intro s s' l h hq hb
    rw [← exec040_enStep_eq hq hb]; exact h
  refine ⟨fun s s' h => (hfin h).1, fun s s' h => ?_, ?_, ?_, ?_⟩
  · have hq := (hfin h).2.1
    simp only [exec040_finishQEn, Bool.and_eq_true] at hq
    exact hq.1
  · rintro s s' ⟨l, hl, ho, -, hf⟩ ⟨-, hp, hr⟩
    by_cases hb : l = .begin
    · subst hb
      simp only [exec040_en, exec040_enStep] at hl
      split at hl
      · rename_i hc
        simp [exec040_finishQEn, hr, hE] at hc
      · cases hl
    · rcases exec040_test_step hp (href hl (fun h => hf _ h) hb) with h1 | h1 | ⟨c, rfl⟩
      · simp [ho] at h1
      · exact hb h1
      · exact hf c rfl
  · rintro s s' ⟨-, c, h⟩
    cases c with
    | quiescent => exact (hfin h).2.2.1
    | closed => exact exec040_finish_M (P := refXPol) (show xstep C s (.finish .closed) = some s' from h)
    | terminal => exact exec040_finish_M (P := refXPol) (show xstep C s (.finish .terminal) = some s' from h)
    | stopped => exact exec040_finish_M (P := refXPol) (show xstep C s (.finish .stopped) = some s' from h)
  · refine exec040_run_of (fun s l s' h ho => ?_) (fun s l s' h ho hu hd => ?_)
      (fun s ns s' h => (xstepW_deadline (href h (by simp) (by simp))).1)
      (fun s s' h => (hfin h).1)
    · exact (xstepW_outside_frame (href h (by rintro rfl; simp [XLbl.outside] at ho)
        (by rintro rfl; simp [XLbl.outside] at ho)) ho).2.2.1
    · by_cases hq : l = .finish .quiescent
      · subst hq; exact (hfin h).2.2.2
      · by_cases hb : l = .begin
        · subst hb; simp [hbeg h, isBoundary]
        · exact exec040_step_nonBoundary (href h hq hb) ho hu hd

/-- The executor that waits for "no transition enabled" kills the mutant: it meets the mutant
reading, but not EXEC-040. At the rest after `u` is reaped (reading `10`, `Window(3, 5)`), `u` is
enabled and not armed; the executor starts a firing pass instead of ending (line 3). From this
rest nothing ever fires and `u` stays enabled (`exec040_rest_reaped_enabled`, Phase 1), so the
executor never ends. -/
@[evidence mutant EXEC_040]
theorem EXEC_040_mutant_enabled_killed :
    EXEC_040_mutant_enabled (exec040_en (N := Nat) (T := Nat)) ∧
      ¬ EXEC_040 (exec040_en (N := Nat) (T := Nat)) := by
  refine ⟨exec040_en_mutant, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec040_enStep (C := exec040_win)
    (o := xrun exec040_win (xinit exec040_m0 0) exec040_reaped) (l := .begin)
    (p := fun s _ => liveB exec040_win s && decide (s.phase = .test) && restB exec040_win s)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact (h exec040_win rfl).2.2.1 s s' ⟨.begin, hs, rfl, (fun _ h => nomatch h), fun c => by simp⟩
    ⟨hp.1.1, hp.1.2, hp.2⟩

/-! ### Allowed: a reaped transition that stays enabled does not block the end -/

/-- ✓ EXEC-040 allows the end with a reaped, still enabled transition: the reference satisfies
it, and at the rest after `u` is reaped (`u` enabled, its token in `0`) it finishes quiescent,
the token still in `0` (condition 1's second sentence, [TIME-013]). -/
@[evidence allows EXEC_040]
theorem EXEC_040_allows_reapedRest :
    EXEC_040 (RefExec (N := Nat) (T := Nat)) ∧
      ∃ s s', RefExec exec040_win s (.finish .quiescent) s' ∧
        ReapedE s (exec040_t "u" 0 1) ∧ enabledNA (qCount s.M) (exec040_t "u" 0 1).core = true ∧
        s'.M 0 = [7] := by
  refine ⟨EXEC_040_reference, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec040_win)
    (o := xrun exec040_win (xinit exec040_m0 0) exec040_reaped) (l := .finish .quiescent)
    (p := fun s s' => decide (s.st "u" = .reaped) &&
      enabledNA (qCount s.M) (exec040_t "u" 0 1).core && s'.M 0 == [7])
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩

/-! ### Allowed: a snapshot answer at the termination test -/

/-- The step answers a snapshot request. -/
def exec040_isSnapshot {N T : Type} (e : XStep N T) : Bool :=
  match e.2.1 with
  | .snapshot _ => true
  | _ => false

/-- The reference, plus an answer to a snapshot request at the termination test that leaves the
state as it is (line 3 allows it: it is not a step of the loop). -/
def exec040_snapTestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .snapshot a => if s.phase = .test then some s else xstep C s (.snapshot a)
  | l => xstep C s l

/-- ✓ EXEC-040 allows a snapshot answer at the termination test: on the chain, at its last test
at rest, the executor answers a snapshot request, changing nothing, and then finishes quiescent.
Line 5 accepts the run, because a snapshot answer is not a step of the loop and does not trigger
it. -/
@[evidence allows EXEC_040]
theorem EXEC_040_allows_snapshotAtTest :
    ∃ tr, XRun (fun C s l s' => exec040_snapTestStep C s l = some s') exec040_chain
        (xinit exec040_m0 0) tr ∧
      tr.any exec040_isSnapshot = true ∧ tr.any finishesQuiescent = true ∧
      (after cycleStep, until isUpdate, never finishesQuiescent) tr := by
  have h1 : (exec040_trace exec040_snapTestStep exec040_chain (xinit exec040_m0 0)
      (exec040_chainRest ++ [.snapshot none, .finish .quiescent])).map
      (fun tr => tr.any exec040_isSnapshot && tr.any finishesQuiescent &&
        decide ((after cycleStep, until isUpdate, never finishesQuiescent) tr)) =
      some true := by decide
  cases ht : exec040_trace exec040_snapTestStep exec040_chain (xinit exec040_m0 0)
      (exec040_chainRest ++ [.snapshot none, .finish .quiescent]) with
  | none => simp [ht] at h1
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h1
    exact ⟨tr, exec040_trace_run ht, h1.1.1, h1.1.2, h1.2⟩

/-! ### Every line exercised -/

/-- Every line of EXEC-040 is exercised by the reference. The chain (AC1, the test derivation)
runs from its initial state through two firings to `finish quiescent`, the token in `2` and
places `0` and `1` empty (lines 1, 2 and 4 on a real end). At its last termination test, with no
terminal place marked and at rest, the executor offers `finish quiescent` and no `begin` (line 3
has a state to speak of). At the chain's first test, with `t1`'s action running, there is no
finish (line 2's premise is not met by accident). The chain's run, as a run of the reference,
holds line 5's trigger (an executor step other than the update, a deadline step and a snapshot
answer), its release (an update) and its banned step (`finish quiescent`). -/
@[evidence nonvacuous EXEC_040]
theorem EXEC_040_nonvacuous :
    (∃ s, xrun exec040_chain (xinit exec040_m0 0) (exec040_chainRest ++ [.finish .quiescent]) =
        some s ∧ s.phase = .done .quiescent ∧ s.M 2 = [7] ∧ s.M 0 = [] ∧ s.M 1 = []) ∧
    (∃ s s', RefExec exec040_chain s (.finish .quiescent) s' ∧ Live exec040_chain s ∧
      s.phase = .test ∧ Rest exec040_chain s ∧ ¬ ∃ s'', RefExec exec040_chain s .begin s'') ∧
    (∃ s, xrun exec040_chain (xinit exec040_m0 0) (exec040_c1 ++ exec040_armed) = some s ∧
      s.phase = .test ∧ ¬ ∃ s', RefExec exec040_chain s (.finish .quiescent) s') ∧
    (∃ tr, XRun RefExec exec040_chain (xinit exec040_m0 0) tr ∧
      tr.any cycleStep = true ∧ tr.any isUpdate = true ∧ tr.any finishesQuiescent = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨s, -, hs, -, hp⟩ := step_of_check (fun _ s _ => some s) (C := exec040_chain)
      (o := xrun exec040_chain (xinit exec040_m0 0) (exec040_chainRest ++ [.finish .quiescent]))
      (l := .update)
      (p := fun s _ => decide (s.phase = .done .quiescent) && s.M 2 == [7] && s.M 0 == [] &&
        s.M 1 == []) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := exec040_chain)
      (o := xrun exec040_chain (xinit exec040_m0 0) exec040_chainRest) (l := .finish .quiescent)
      (p := fun s _ => liveB exec040_chain s && decide (s.phase = .test) &&
        restB exec040_chain s) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    have hb : (xrun exec040_chain (xinit exec040_m0 0) exec040_chainRest).bind
        (fun s => (xstep exec040_chain s .begin).isNone) = some true := by decide
    rw [ho] at hb
    refine ⟨s, s', hs, hp.1.1, hp.1.2, hp.2, fun ⟨s'', h''⟩ => ?_⟩
    simp only [Option.bind_some, Option.some.injEq, Option.isNone_iff_eq_none] at hb
    simp [RefExec, hb] at h''
  · have h1 : (xrun exec040_chain (xinit exec040_m0 0) (exec040_c1 ++ exec040_armed)).map
        (fun s => decide (s.phase = .test) && (xstep exec040_chain s (.finish .quiescent)).isNone) =
        some true := by decide
    cases ho : xrun exec040_chain (xinit exec040_m0 0) (exec040_c1 ++ exec040_armed) with
    | none => simp [ho] at h1
    | some s =>
      simp only [ho, Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq,
        Option.isNone_iff_eq_none] at h1
      exact ⟨s, rfl, h1.1, fun ⟨s', h'⟩ => by simp [RefExec, h1.2] at h'⟩
  · have h1 : (exec040_trace xstep exec040_chain (xinit exec040_m0 0)
        (exec040_chainRest ++ [.finish .quiescent])).map
        (fun tr => tr.any cycleStep && tr.any isUpdate && tr.any finishesQuiescent) =
        some true := by decide
    cases ht : exec040_trace xstep exec040_chain (xinit exec040_m0 0)
        (exec040_chainRest ++ [.finish .quiescent]) with
    | none => simp [ht] at h1
    | some tr =>
      simp only [ht, Option.map_some, Option.some.injEq, Bool.and_eq_true] at h1
      exact ⟨tr, exec040_trace_run ht, h1.1.1, h1.1.2, h1.2⟩

end Libpetri.Spec
