import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.EXEC_041

set_option linter.missingDocs true

/-!
# EXEC-041: Execution Result (`spec/04-execution-model.md`)

A run of the executor model (`RefExec`, `Reference/Exec.lean`) ends with a `finish c` step: the
loop enters the phase `done c`, and the state's marking is the marking the run returns. The
requirement is a predicate over an abstract executor `R : XRel N T` (glossary
`GlossaryExec.lean`): a finish returns the marking as it is and records its cause, a run ends
only by a finish, nothing the loop does follows it, nothing that happens afterwards changes the
result, and each cause names a stop that really happened, so a truncated run is never reported
with a completed cause.

Ruling D53 (c): at a rest reached after a close, `quiescent` (Java, Rust) and `closed`
(TypeScript) both conform; the reference offers both (`EXEC_041_nonvacuous`), and the
TypeScript reading is allowed (`EXEC_041_allows_closedAtClosedRest`). Ruling D13 (a): the
termination test reads rest as nothing armed, in flight or queued (`Rest`).

The block is checked against the reference, against executors that report one signal for every
cause, take the terminal token out of the returned marking, end the run by a close or by step 1
instead of a finish, keep the loop running after the finish, settle an abandoned firing after the
finish, deposit a late result after the finish, report a close as quiescent while a transition
is armed, report `terminal` at a rest with no terminal place marked, report `closed` with no
close, and report `stopped` for a close.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-041: Execution Result -/

/-- A step of the executor's loop ([EXEC-001]): an executor step, not an outside step
([CONC-001]), other than the answer to a snapshot request, which reads the state and changes
nothing ([ENV-014]; [EXEC-042] lets a snapshot taken after a terminal stop still report the
abandoned work). -/
def exec041_loopStep {N T : Type} : XLbl N T → Bool
  | .snapshot _ => false
  | l => !l.outside

/-- A step of the loop is not an outside step. -/
theorem exec041_loopStep_outside {N T : Type} {l : XLbl N T} (h : exec041_loopStep l = true) :
    l.outside = false := by
  cases l <;> simp_all [exec041_loopStep, XLbl.outside]

/-- The label is a finish. -/
def exec041_isFinish {N T : Type} : XLbl N T → Bool
  | .finish _ => true
  | _ => false

requirement EXEC_041
  id "EXEC-041"
  title "Execution Result"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_041.s1, EXEC_041.s2, EXEC_041.s3, EXEC_041.s4, EXEC_041.s5, EXEC_041.s6, EXEC_041.s7,
        EXEC_041.s8, EXEC_041.s9, EXEC_041.s10, EXEC_041.s11, EXEC_041.s12, EXEC_041.s13,
        EXEC_041.s14
  reading "For every executor R and every configuration C:"
          "for every cause c, a finish step with cause c leaves the marking as it is and enters the finished phase with cause c, from which the caller reads the returned marking and the termination reason;"
          "while the run is finished (its phase is a finished phase), no step of the loop happens: no executor step other than the answer to a snapshot request (the outside steps stay possible: time passing, an action writing, flushing, returning or timing out, a caller requesting, draining, closing or terminating);"
          "every step from a finished state leaves the marking and the phase, and so the cause, as they are;"
          "a finish with cause quiescent happens only at rest: nothing armed, nothing in flight, no completion, publication or injection queued;"
          "a finish with cause terminal happens only when a terminal place is marked;"
          "a finish with cause closed happens only when the mode is closed or stopped (a close or an immediate termination was requested);"
          "a finish with cause stopped happens only when the mode is stopped (an immediate termination was requested);"
          "every step from an executing phase into a finished phase is a finish step: a run ends only by a finish."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A run ends with a step finish c, which enters the phase done c; the run's returned marking is the marking M of that state and its termination reason is c. The caller reads both from that state, by whichever of the quoted MUST's three channels the runtime uses (the return value, a distinct event, a raised error): 'available to the caller' in line 1 fixes what the caller can read, not the channel. The witness is the reference executor RefExec (Reference/Exec.lean)."
          "Naming: the markdown's 'the executor finishes a run' is a finish step; 'the termination reason' is its cause c, of type Cause (glossary GlossaryExec.lean), which the target state records as its phase done c. 'End a run' is entering a finished phase, a phase that is not an executing phase (isExecPhase). 'A step of its loop' is exec041_loopStep: an executor step (a label l with l.outside = false, CONC-001) other than the answer to a snapshot request, which the quoted sentence names. The outside steps are time passing and the actions, callers and hosts acting on the executor. A snapshot answer reads the state and changes nothing; EXEC-042's 'A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight' may answer one after a terminal stop (Rust answers a snapshot queued behind the stop after its loop), so line 2 leaves it to ENV-014, and line 3 still says it changes neither the marking nor the reason."
          "The shall sentences on the finish are lines 1, 8, 2 and 3. Line 1 is 'make the marking the run ended with, unchanged by the finish, and the termination reason of the finish available to the caller' (EXEC_041_forbids_sameSignal: every finish reports quiescent, so a chain closed before its first pass, t armed and 7 still in place 0, reports the completed reason; EXEC_041_forbids_consumeTerminal: the finish empties the terminal place). Line 8 is 'end a run only by finishing it': without it an executor could enter a finished phase by another step and skip every check on the cause and on the returned marking (EXEC_041_forbids_closeEndsRun: the close itself ends an executing run reporting quiescent while t is armed; EXEC_041_forbids_terminalShortcut: step 1 ends the run at a marked terminal place and empties it). Lines 2 and 3 are the sentence on a finished run: no executor step (EXEC_041_forbids_stepAfterFinish: a loop that keeps running after its finish; EXEC_041_forbids_settleAfterFinish: an abandoned firing settled after the finish), and no step, outside steps included, changes the returned marking or the reason (EXEC_041_forbids_lateDeposit: a late return deposited after the finish). Together they give 'at most one finish per run' (EXEC_041_atMostOnce) and 'after a finish, no step of the loop' over every run (EXEC_041_run)."
          "The reason sentences are lines 4 to 7. Lines 4 and 5 say a completed reason names a run that completed, so a run that stops before rest with no terminal place marked reports closed or stopped and its end state records that reason (EXEC_041_ac3). That is the markdown's distinguishability rule in the direction ruling D53 (c) fixes: a truncated run is never reported with a completed reason. The converse is allowed: the quoted sentence 'At a rest the run reached after a close or an immediate termination, ...' is the reference offering both quiescent and closed at a closed rest (EXEC_041_nonvacuous), the TypeScript reading, closed only, satisfying the block (EXEC_041_allows_closedAtClosedRest), and lines 4, 6 and 7 together allowing quiescent, closed and stopped at a rest reached after an immediate termination."
          "Lines 6 and 7 say a truncating reason names a stop a caller requested. The model has two: close (ENV-013) and the immediate termination of ENV-015 (terminateNow, Java, ruling D47 (c)). The lines read 'after a close / an immediate termination was requested' as the mode of the source state: closing (closed or stopped) for closed, stopped for stopped. Java reports closed or quiescent after terminateNow when nothing is in flight, so closed is allowed in the stopped mode too. That the mode becomes closed only by a close step, stopped only by a terminateNow step and draining only by a drain step holds in the reference (closeStep, terminateStep and drainStep in Reference/Exec.lean) but is not this block's line: it is pinned for closed by ENV-013's lines 3 and 4 (the mode becomes closed only by a close and leaves closed only for an immediate termination) and for stopped by ENV-015's lines 1 and 2 (the mode becomes stopped only by an immediate termination and stays stopped). An executor whose wake set the mode closed with no close request passes lines 6 and 7 here and breaks ENV-013's line 3. Lines 6 and 7 do not read the draining mode."
          "Host fault (the spec follows the Java runtime): a fault of the host runtime is not an action failure (EXEC-030) and is outside the model, which has no label for it, so no finish step of the model is a host fault and lines 6 and 7 do not read it. In Java a VirtualMachineError or LinkageError thrown inside a firing is rethrown by ExecutorSupport.rethrowIfFatal (ExecutorSupport.java, called from fireTransitionGuarded in BitmapNetExecutor.java and PrecompiledNetExecutor.java); it escapes the loop, whose finally block records the reason STOPPED, since no quiescence, terminal place, wait interruption or close was seen (executeLoop in BitmapNetExecutor.java and PrecompiledNetExecutor.java; TerminationReason.STOPPED is 'stopped before quiescence for another reason'), and run() raises the error. The run is told apart from quiescence by the raised error and by the truncating reason, as the quoted MUST asks, and the quoted reason sentence names this end: stopped after a fault of the host runtime that ends the run with a raised error. Rust, TypeScript and Python have no host fault that ends the run with a reported reason."
          "Run budget: a caller's run budget is not a step of the model, and its expiry is not a finish of the loop; this is the quoted sentence 'A run budget that expires ends the caller's wait, not the loop: ...'. Java run(Duration) and TypeScript run(timeoutMs) fail the caller's stage or promise (the raised-error channel of the quoted MUST: a truncating reason, no marking), and TypeScript also records stopped. Under the abandon policy, the default in both, the loop goes on stepping and changing the marking; under the close policy the expiry is followed by a close step (ENV-013). Either way the loop has not finished, so its later steps and its later finish are steps of a running loop and lines 2 and 3 do not read them as steps after a finish. The expiry does not set the mode stopped: Mode.stopped refuses injections, discards the queued ones and ends the loop at the end of its cycle, none of which the abandon policy does. TypeScript keeps reporting stopped when that loop later finishes (it sets the reason only while it reads running): the reason of the caller's run, which ended at the expiry, does not change, and lines 4 to 7 allow a truncating reason for a loop that later reached rest."
          "Same signal (the quoted 'Emitting the same completion signal ...' sentence): an executor whose every finish reports quiescent breaks line 1 on a truncated run (EXEC_041_forbids_sameSignal). Whether the ExecutionCompleted event, which every runtime emits for every cause, is 'the same completion signal' when the reason is queryable is an event question (EVT-003, ruling D74, wave W7), not this block's."
          "Cause values and interrupted (kind Q, Java): the Cause type lists quiescent, terminal, closed and stopped. Where the runtime has a cancellation the executor observes in its own wait, the executor may finish the run on it, and shall then report `interrupted`, and shall report `interrupted` only after such a cancellation. The model has no host cancellation, so no step reports interrupted; the sentence is checked by the Java tests the test derivation names (a real interrupt raised from a foreign thread while the orchestrator is parked, in the built-in and the hosted wait, ends the run INTERRUPTED; an interrupt flag set before run() or by an action mid-run does not). Rust, TypeScript and Python have no such cancellation, so the Where clause does not apply to them. interrupted is a truncating reason: a model with it would add a cause with no completed-reason line. The completed reasons are quiescent and terminal (lines 4 and 5); the others are truncations."
          "Ambient host state (kind Q, Java): The executor shall not treat host cancellation state that it did not set itself, such as a thread's interrupt flag set before the run or by the run's own action code, as a request to stop the run. The model has no host cancellation state, so no step can read it; the sentence, AC4 and AC5 are checked by the Java tests the test derivation names (an interrupt flag set before run(), set by an action mid-run, and a real interrupt raised from a foreign thread in the built-in and the hosted wait). They are vacuous in Rust, TypeScript and Python, which expose no ambient cancellation state, as the markdown's sentence after the quoted one says ('Where the runtime exposes no ambient cancellation state an executor could consult, the previous sentence and AC4/AC5 hold vacuously.')."
          "AC1 (return value contains the token state after quiescence) is line 1 at a quiescent finish: the returned marking is the marking of the test state, which line 4 says is at rest; that the finish happens at the test after the update is EXEC-040's. EXEC_041_nonvacuous returns the token 70 in place 1 of a chain 0 to 1."
          "AC2 (all places with tokens are represented) holds by the type of the result: the returned marking is a queue marking, a queue for every place (QMarking N T = N → List T), so no place with tokens can be missing; which tokens it holds is line 1. Materializing it from ring buffers is CONC-025's."
          "AC3 (a run that stops before quiescence is distinguishable) is lines 1, 4, 5 and 8 (EXEC_041_ac3, with line 8 making every end of a run a finish that lines 4 and 5 check); EXEC_041_nonvacuous finishes a run closed with an armed transition left unfired, and EXEC_041_forbids_closeAsQuiescent and EXEC_041_forbids_closeEndsRun kill executors that report that run quiescent."
          "AC4 and AC5 (ambient host cancellation) are kind Q: Java tests, see the ambient host state assumption."
          "The test derivation describes the runtimes' tests and is documentation, not quoted."
  signoff "2026-11-13 ddec5895d41c87cf ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ c, on (fun s s' => R C s (.finish c) s'),
        shall (fun s s' => s'.M = s.M ∧ s'.phase = .done c)) ∧
      (while (fun s => isExecPhase s.phase = false),
        never (fun s s' => ∃ l : XLbl _ _, exec041_loopStep l = true ∧ R C s l s')) ∧
      (on (fun s s' => isExecPhase s.phase = false ∧ ∃ l, R C s l s'),
        shall (fun s s' => s'.M = s.M ∧ s'.phase = s.phase)) ∧
      (on (fun s s' => R C s (.finish .quiescent) s'), shall (fun s _ => Rest C s)) ∧
      (on (fun s s' => R C s (.finish .terminal) s'), shall (fun s _ => ¬ Live C s)) ∧
      (on (fun s s' => R C s (.finish .closed) s'), shall (fun s _ => s.mode.closing = true)) ∧
      (on (fun s s' => R C s (.finish .stopped) s'), shall (fun s _ => s.mode = .stopped)) ∧
      (∀ l, on (fun s s' => isExecPhase s.phase = true ∧ isExecPhase s'.phase = false ∧ R C s l s'),
        shall (fun _ _ => exec041_isFinish l = true))

/- The pinned readable form of EXEC-041: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_041 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (c : Cause), on fun s s' => R C s (XLbl.finish c) s', shall fun s s' => s'.M = s.M ∧ s'.phase = Phase.done c) ∧
      (while fun s => isExecPhase s.phase = false, never fun s s' => ∃ l, exec041_loopStep l = true ∧ R C s l s') ∧
        (on fun s s' => isExecPhase s.phase = false ∧ ∃ l, R C s l s', shall fun s s' =>
            s'.M = s.M ∧ s'.phase = s.phase) ∧
          (on fun s s' => R C s (XLbl.finish Cause.quiescent) s', shall fun s x => Rest C s) ∧
            (on fun s s' => R C s (XLbl.finish Cause.terminal) s', shall fun s x => ¬Live C s) ∧
              (on fun s s' => R C s (XLbl.finish Cause.closed) s', shall fun s x => s.mode.closing = true) ∧
                (on fun s s' => R C s (XLbl.finish Cause.stopped) s', shall fun s x => s.mode = Mode.stopped) ∧
                  ∀ (l : XLbl N T),
                    on fun s s' => isExecPhase s.phase = true ∧ isExecPhase s'.phase = false ∧ R C s l s', shall
                      fun x x_1 => exec041_isFinish l = true
-/
#guard_msgs in #print EXEC_041

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- From a finished state the reference takes outside steps only: the rule of every executor step
reads an executing phase (each inversion lemma names the phase its rule needs). -/
theorem exec041_ref_outside {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (hd : isExecPhase s.phase = false) : l.outside = true := by
  have hc : ∀ {i : Nat} {f : Firing N T}, canSettle C s i f = true → False := by
    intro i f hc
    unfold canSettle at hc
    simp [hd] at hc
  have hph : ∀ {p : Phase}, s.phase = p → isExecPhase p = true → False := by
    intro p hp he
    rw [hp] at hd
    rw [hd] at he
    exact Bool.false_ne_true he
  cases l with
  | commit i => obtain ⟨f, e, -, -, h1, -⟩ := commitStep_some h; exact (hc h1).elim
  | fail i => obtain ⟨f, -, h1, -⟩ := failStep_some h; exact (hc h1).elim
  | tdeposit i => obtain ⟨f, e, -, -, h1, -⟩ := tdepositStep_some h; exact (hc h1).elim
  | endCompletions => exact (hph (xstepW_endCompletions h).1 rfl).elim
  | publish i =>
    obtain ⟨b, rest, -, -, hp, -⟩ := publishStep_some h
    rcases hp with hp | ⟨hp, -⟩ <;> exact (hph hp rfl).elim
  | endPublications => exact (hph (xstepW_endPublications h).1 rfl).elim
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hp, -⟩ := injectStep_some h
    rcases hp with hp | hp <;> exact (hph hp rfl).elim
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hp, -⟩ := discardStep_some h
    rcases hp with hp | hp <;> exact (hph hp rfl).elim
  | snapshot a =>
    obtain ⟨-, hp, -⟩ := snapshotStep_some h
    rcases hp with hp | hp | hp <;> exact (hph hp rfl).elim
  | endEvents => exact (hph (xstepW_endEvents h).1 rfl).elim
  | update => exact (hph (xstepW_update h).1 rfl).elim
  | deadline ns => exact (hph (xstepW_deadline h).1 rfl).elim
  | begin => exact (hph (xstepW_begin h).1 rfl).elim
  | start n sy =>
    obtain ⟨t, rest, -, hp, -⟩ := startStep_some h
    exact (hph hp rfl).elim
  | lose n =>
    obtain ⟨t, rest, -, hp, -⟩ := loseStep_some h
    exact (hph hp rfl).elim
  | endPass => exact (hph (xstepW_endPass h).1 rfl).elim
  | finish c =>
    cases c with
    | quiescent => exact (hph (xstepW_finishQuiescent h).1 rfl).elim
    | closed => exact (hph (xstepW_finishClosed h).1 rfl).elim
    | terminal => exact absurd ((xstepW_finishTerminal h).1.symm.trans hd) (by decide)
    | stopped => exact (hph (xstepW_finishStopped h).1 rfl).elim
  | park tmr => exact (hph (parkStep_some h).1 rfl).elim
  | wake => exact (hph (wakeStep_some h).1 rfl).elim
  | delay _ | write _ _ _ | flush _ | ret _ _ | expire _ _ | request _ _ _ | drain | close
  | terminateNow => rfl

/-- In the reference only a finish leaves an executing phase for a finished one: every other rule
names an executing target phase or keeps the source's, and an outside step keeps the phase
(`xstepW_outside_frame`). -/
theorem exec041_ref_enter {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (he : isExecPhase s.phase = true)
    (hd : isExecPhase s'.phase = false) : exec041_isFinish l = true := by
  have hif : isExecPhase (if s.phase = .await then .completions else s.phase) = true := by
    split
    · rfl
    · exact he
  have suff : isExecPhase s'.phase = true → False := by
    rw [hd]
    exact Bool.false_ne_true
  have hout : l.outside = true → False := fun ho => by
    obtain ⟨-, -, hp, -⟩ := xstepW_outside_frame h ho
    rw [hp] at hd
    rw [hd] at he
    exact Bool.false_ne_true he
  cases l with
  | finish c => rfl
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact (suff hif).elim
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact (suff hif).elim
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact (suff hif).elim
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact (suff rfl).elim
  | publish i =>
    obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
    exact (suff hif).elim
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact (suff rfl).elim
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h
    exact (suff hif).elim
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h
    exact (suff hif).elim
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact (suff he).elim
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact (suff rfl).elim
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact (suff rfl).elim
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact (suff rfl).elim
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact (suff rfl).elim
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact (suff he).elim
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact (suff he).elim
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    refine (suff ?_).elim
    show isExecPhase (if s.started then .completions else .await) = true
    split <;> rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact (suff he).elim
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact (suff rfl).elim
  | delay _ | write _ _ _ | flush _ | ret _ _ | expire _ _ | request _ _ _ | drain | close
  | terminateNow => exact (hout rfl).elim

end Reference

/-- ✓ The reference executor satisfies EXEC-041: each `finish` rule enters `done c` with the
marking as it is and reads its cause's premise (`xstepW_finishQuiescent` and its siblings), only
a finish enters a finished phase (`exec041_ref_enter`), and from a finished phase only outside
steps are offered (`exec041_ref_outside`), which keep the marking and the phase
(`xstepW_outside_frame`). -/
@[evidence holds EXEC_041]
theorem EXEC_041_reference {N T : Type} [DecidableEq N] :
    EXEC_041 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun c s s' h => ?_, fun s s' ⟨l, hl, h⟩ hd => ?_, fun s s' ⟨hd, l, h⟩ => ?_,
    fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_,
    fun l s s' ⟨he, hd, h⟩ => exec041_ref_enter h he hd⟩
  · cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact ⟨rfl, rfl⟩
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact ⟨rfl, rfl⟩
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact ⟨rfl, rfl⟩
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact ⟨rfl, rfl⟩
  · have := exec041_ref_outside h hd
    rw [exec041_loopStep_outside hl] at this
    exact absurd this (by decide)
  · obtain ⟨hM, -, hp, -⟩ := xstepW_outside_frame h (exec041_ref_outside h hd)
    exact ⟨hM, hp⟩
  · obtain ⟨-, -, hq, -⟩ := xstepW_finishQuiescent h
    unfold finishQ at hq
    simp only [Bool.and_eq_true] at hq
    exact hq.1
  · obtain ⟨-, hl, -⟩ := xstepW_finishTerminal h
    intro hL
    unfold Live at hL
    rw [hl] at hL
    exact absurd hL (by decide)
  · exact (xstepW_finishClosed h).2.2.1
  · exact (xstepW_finishStopped h).2.2.1

/-! ### Consequences -/

section Consequences

variable {N T : Type} [DecidableEq N]

/-- EXEC-041 is made of step lines, so an executor that takes a subset of the steps of one that
satisfies it satisfies it too. -/
theorem EXEC_041_anti {R R' : XRel N T} (h : EXEC_041 R)
    (hR : ∀ C s l s', R' C s l s' → R C s l s') : EXEC_041 R' := by
  intro C
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h C
  exact ⟨fun c s s' hs => h1 c s s' (hR _ _ _ _ hs),
    fun s s' ⟨l, hl, hs⟩ => h2 s s' ⟨l, hl, hR _ _ _ _ hs⟩,
    fun s s' ⟨hd, l, hs⟩ => h3 s s' ⟨hd, l, hR _ _ _ _ hs⟩,
    fun s s' hs => h4 s s' (hR _ _ _ _ hs), fun s s' hs => h5 s s' (hR _ _ _ _ hs),
    fun s s' hs => h6 s s' (hR _ _ _ _ hs), fun s s' hs => h7 s s' (hR _ _ _ _ hs),
    fun l s s' ⟨he, hd, hs⟩ => h8 l s s' ⟨he, hd, hR _ _ _ _ hs⟩⟩

/-- AC3: a finish from a state that is not at rest and has no terminal place marked (a run that
stops before quiescence) reports a truncating cause, closed or stopped, and its end state records
it, so the caller tells it apart from a quiesced run. -/
theorem EXEC_041_ac3 {R : XRel N T} (h : EXEC_041 R) {C : Cfg N T} {s s' : XSt N T} {c : Cause}
    (hs : R C s (.finish c) s') (hr : ¬ Rest C s) (hl : Live C s) :
    (c = .closed ∨ c = .stopped) ∧ s'.phase = .done c := by
  obtain ⟨h1, -, -, h4, h5, -, -⟩ := h C
  refine ⟨?_, (h1 c s s' hs).2⟩
  cases c with
  | quiescent => exact absurd (h4 s s' hs) hr
  | terminal => exact absurd hl (h5 s s' hs)
  | closed => exact Or.inl rfl
  | stopped => exact Or.inr rfl

/-- The scan behind `EXEC_041_run`: from a memory that has seen a finish only in a finished
state, an `after finish, never bad` watch accepts every run of an executor satisfying EXEC-041,
for any `bad` made of loop steps. -/
theorem exec041_scan {R : XRel N T} (h : EXEC_041 R) {C : Cfg N T}
    {bad : XStep N T → Bool} (hbad : ∀ st, bad st = true → exec041_loopStep st.2.1 = true) :
    ∀ (tr : List (XStep N T)) (s : XSt N T) (a : Bool), XRun R C s tr →
      (a = true → isExecPhase s.phase = false) →
      (afterNever (fun st : XStep N T => exec041_isFinish st.2.1) bad).scan a tr = true
  | [], _, _, _, _ => rfl
  | (src, l, tgt) :: rest, s, a, hr, ha => by
    obtain ⟨h1, hstep, hrest⟩ := hr
    simp only at h1 hstep hrest
    subst h1
    obtain ⟨h1', h2', h3', -⟩ := h C
    have hok : (!(a && bad (src, l, tgt))) = true := by
      cases a with
      | false => rfl
      | true =>
        cases hb : bad (src, l, tgt) with
        | false => rfl
        | true => exact absurd (ha rfl) (h2' src tgt ⟨l, hbad _ hb, hstep⟩)
    have hnext : (a || exec041_isFinish l) = true → isExecPhase tgt.phase = false := by
      intro hn
      cases a with
      | true => rw [(h3' src tgt ⟨ha rfl, l, hstep⟩).2]; exact ha rfl
      | false =>
        cases l with
        | finish c => rw [(h1' c src tgt hstep).2]; rfl
        | _ => simp [exec041_isFinish] at hn
    simp only [Watch.scan, afterNever] at hok ⊢
    rw [hok, Bool.true_and]
    exact exec041_scan h hbad rest tgt _ hrest hnext

/-- In every run of an executor satisfying EXEC-041, no step of the loop follows a finish. -/
theorem EXEC_041_run {R : XRel N T} (h : EXEC_041 R) {C : Cfg N T} {s0 : XSt N T}
    {tr : List (XStep N T)} (hr : XRun R C s0 tr) :
    AfterNever (fun st : XStep N T => exec041_isFinish st.2.1)
      (fun st => exec041_loopStep st.2.1) tr :=
  exec041_scan h (fun _ hb => hb) tr s0 false hr (fun h => absurd h (by decide))

/-- In every run of an executor satisfying EXEC-041, at most one step is a finish. -/
theorem EXEC_041_atMostOnce {R : XRel N T} (h : EXEC_041 R) {C : Cfg N T} {s0 : XSt N T}
    {tr : List (XStep N T)} (hr : XRun R C s0 tr) :
    AtMostOnce (fun st : XStep N T => exec041_isFinish st.2.1) tr :=
  exec041_scan h (fun st hb => by
      obtain ⟨_, l, _⟩ := st
      cases l <;> simp_all [exec041_isFinish, exec041_loopStep, XLbl.outside]) tr s0 false hr
    (fun h => absurd h (by decide))

end Consequences

/-! ### Examples

Places `0` and `1`; transition `t` takes one token from `0` and puts one in `1`; every transition
is immediate; no environment places; validation and the relay check accept everything. -/

/-- `t`: one token from `0`, output place `1`. -/
def exec041_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration with terminal places `terms` and transitions `ts`. -/
def exec041_cfg (terms : List Nat) (ts : List (Trans Nat)) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := ts }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := terms, envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The chain `0 → t → 1`. -/
def exec041_c1 : Cfg Nat Nat := exec041_cfg [] [exec041_t]
/-- The chain with `1` terminal. -/
def exec041_cT : Cfg Nat Nat := exec041_cfg [1] [exec041_t]
/-- No transition. -/
def exec041_c0 : Cfg Nat Nat := exec041_cfg [] []
/-- No transition, `1` terminal. -/
def exec041_c0T : Cfg Nat Nat := exec041_cfg [1] []

/-- One token `7` in place `0`. -/
def exec041_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []
/-- One token `9` in place `1`. -/
def exec041_m1 : QMarking Nat Nat := fun p => if p = 1 then [9] else []
/-- No token. -/
def exec041_mE : QMarking Nat Nat := fun _ => []

/-- Steps 1 to 4 of a cycle, up to the termination test. -/
def exec041_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- A pass that starts `t` asynchronously; its action writes `70` to `1` and returns; step 1
commits it. -/
def exec041_fire : List (XLbl Nat Nat) :=
  [.begin, .start "t" false, .endPass, .write 0 1 70, .ret 0 true, .commit 0]

/-- An immediate termination while `t` is in flight, and the finish after it. -/
def exec041_stop : List (XLbl Nat Nat) :=
  exec041_toTest ++ [.begin, .start "t" false, .endPass, .terminateNow, .finish .stopped]

/-- The reference state after `ls` from `M0`. -/
def exec041_at (C : Cfg Nat Nat) (M0 : QMarking Nat Nat) (ls : List (XLbl Nat Nat)) :
    Option (XSt Nat Nat) :=
  xrun C (xinit M0 0) ls

/-! ### Every line exercised -/

/-- Every line of EXEC-041 is exercised by the reference: the chain finishes quiescent and
returns `70` in `1` (line 1, line 4, AC1; the finish is a step from the executing phase `test`
into a finished phase, the trigger of line 8); with `1` terminal it finishes terminal with `70` in `1`
(line 5); closed before the pass, it finishes closed with `t` armed and unfired, not at rest, `7`
still in `0` (lines 4 and 6, AC3); at a closed rest both finishes are offered (ruling D53 (c));
after an immediate termination the run finishes stopped with `t` in flight, and the late return of
its action deposits nothing (lines 2, 3 and 7). -/
@[evidence nonvacuous EXEC_041]
theorem EXEC_041_nonvacuous :
    (∃ s s', RefExec exec041_c1 s (.finish .quiescent) s' ∧ s'.M 1 = [70]) ∧
    (∃ s s', RefExec exec041_cT s (.finish .terminal) s' ∧ s'.M 1 = [70]) ∧
    (∃ s s', RefExec exec041_c1 s (.finish .closed) s' ∧ ¬ Rest exec041_c1 s ∧ s'.M 0 = [7]) ∧
    (∃ s, (∃ s', RefExec exec041_c0 s (.finish .quiescent) s') ∧
      ∃ s', RefExec exec041_c0 s (.finish .closed) s') ∧
    (∃ s s', RefExec exec041_c1 s (.ret 0 true) s' ∧ s.phase = .done .stopped ∧
      s.fl.length = 1 ∧ s'.phase = .done .stopped ∧ s'.M 1 = []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec041_c1)
      (o := exec041_at exec041_c1 exec041_m0 (exec041_toTest ++ exec041_fire ++ exec041_toTest))
      (l := .finish .quiescent) (p := fun _ s' => s'.M 1 == [70]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec041_cT)
      (o := exec041_at exec041_cT exec041_m0 (exec041_toTest ++ exec041_fire))
      (l := .finish .terminal) (p := fun _ s' => s'.M 1 == [70]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec041_c1)
      (o := exec041_at exec041_c1 exec041_m0 (.close :: exec041_toTest))
      (l := .finish .closed) (p := fun s s' => !restB exec041_c1 s && s'.M 0 == [7]) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    exact ⟨s, s', hs, fun h => by unfold Rest at h; rw [hp.1] at h; exact absurd h (by decide),
      hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec041_c0)
      (o := exec041_at exec041_c0 exec041_mE (.close :: exec041_toTest))
      (l := .finish .quiescent)
      (p := fun s _ => (xstep exec041_c0 s (.finish .closed)).isSome) (by decide)
    obtain ⟨s'', h''⟩ := Option.isSome_iff_exists.mp hp
    exact ⟨s, ⟨s', hs⟩, s'', h''⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec041_c1)
      (o := exec041_at exec041_c1 exec041_m0 (exec041_stop ++ [.write 0 1 70]))
      (l := .ret 0 true)
      (p := fun s s' => s.phase == .done .stopped && s.fl.length == 1 &&
        s'.phase == .done .stopped && s'.M 1 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-! ### Allowed: closed only at a closed rest (ruling D53 (c), TypeScript) -/

/-- The TypeScript reading: once a close (or an immediate termination) was requested, the run
never finishes quiescent; otherwise the reference. -/
def exec041_closedFirst {N T : Type} [DecidableEq N] : XRel N T := fun C s l s' =>
  RefExec C s l s' ∧ ¬ (l = .finish .quiescent ∧ s.mode ≠ .open)

/-- ✓ Reporting `closed` at every closed rest (TypeScript) meets EXEC-041, as reporting
`quiescent` there (Java, Rust) does: the block fixes neither (ruling D53 (c)). -/
@[evidence allows EXEC_041]
theorem EXEC_041_allows_closedAtClosedRest :
    EXEC_041 (exec041_closedFirst (N := Nat) (T := Nat)) :=
  EXEC_041_anti EXEC_041_reference fun _ _ _ _ h => h.1

/-! ### Violation: one signal for every cause (line 1) -/

/-- Every finish reports `quiescent`, whatever ended the run; otherwise the reference. -/
def exec041_sameSignalStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish c => (xstep C s (.finish c)).map fun s₁ => { s₁ with phase := .done .quiescent }
  | l => xstep C s l

/-- ✗ The same completion signal for a quiesced and a truncated run violates EXEC-041 (line 1):
the chain is closed before its first pass, so `t` is armed, never fires and `7` stays in `0`; the
run is not at rest when it finishes, and it reports `quiescent`. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_sameSignal :
    ¬ EXEC_041 (fun C s l s' => exec041_sameSignalStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_sameSignalStep (C := exec041_c1)
    (o := exec041_at exec041_c1 exec041_m0 (.close :: exec041_toTest))
    (l := .finish .closed)
    (p := fun s s' => s'.phase == .done .quiescent && !restB exec041_c1 s && s'.M 0 == [7])
    (by decide)
  simp only [Bool.and_eq_true] at hp
  have := ((h exec041_c1).1 .closed s s' hs).2
  rw [this] at hp
  exact absurd hp.1.1 (by decide)

/-! ### Violation: the run ended by a step other than a finish (line 8) -/

/-- A close ends an executing run itself, with the reason read before the close took effect
(`quiescent`) and the marking as it is; otherwise the reference. -/
def exec041_closeEndsRunStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => if isExecPhase s.phase then
        (xstep C s .close).map fun s₁ => { s₁ with phase := .done .quiescent }
      else xstep C s .close
  | l => xstep C s l

/-- ✗ Ending the run by a close violates EXEC-041 (line 8): the chain is closed at the
termination test with `t` armed and `7` still in `0`, and the close itself ends the run with the
completed reason `quiescent`, a step no finish line reads. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_closeEndsRun :
    ¬ EXEC_041 (fun C s l s' => exec041_closeEndsRunStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_closeEndsRunStep (C := exec041_c1)
    (o := exec041_at exec041_c1 exec041_m0 exec041_toTest) (l := .close)
    (p := fun s s' => isExecPhase s.phase && !isExecPhase s'.phase &&
      s'.phase == .done .quiescent && !restB exec041_c1 s' && s'.M 0 == [7]) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have h8 : exec041_isFinish (XLbl.close : XLbl Nat Nat) = true :=
    (h exec041_c1).2.2.2.2.2.2.2 .close s s' ⟨hp.1.1.1.1, hp.1.1.1.2, hs⟩
  exact absurd h8 (by decide)

/-- Step 1 notices a marked terminal place and ends the run itself, emptying the terminal places;
otherwise the reference. -/
def exec041_terminalShortcutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endCompletions => if isExecPhase s.phase && !liveB C s then
        some { s with phase := .done .terminal, M := fun p => if p ∈ C.terminals then [] else s.M p }
      else xstep C s .endCompletions
  | l => xstep C s l

/-- ✗ Ending the run in step 1 violates EXEC-041 (line 8): the run starts with `9` in the
terminal place `1`, step 1 ends it reporting `terminal`, and it returns `1` empty, which line 1
would have caught on a finish. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_terminalShortcut :
    ¬ EXEC_041 (fun C s l s' =>
      exec041_terminalShortcutStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_terminalShortcutStep (C := exec041_c0T)
    (o := exec041_at exec041_c0T exec041_m1 []) (l := .endCompletions)
    (p := fun s s' => isExecPhase s.phase && !isExecPhase s'.phase && s'.M 1 != s.M 1)
    (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have h8 : exec041_isFinish (XLbl.endCompletions : XLbl Nat Nat) = true :=
    (h exec041_c0T).2.2.2.2.2.2.2 .endCompletions s s' ⟨hp.1.1, hp.1.2, hs⟩
  exact absurd h8 (by decide)

/-! ### Violation: the returned marking altered at the finish (line 1) -/

/-- A terminal finish takes the token out of the terminal place, as if the stop consumed it;
otherwise the reference. -/
def exec041_consumeTerminalStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal => (xstep C s (.finish .terminal)).map fun s₁ =>
      { s₁ with M := fun p => if p ∈ C.terminals then [] else s₁.M p }
  | l => xstep C s l

/-- ✗ Altering the marking at the finish violates EXEC-041 (line 1): the run starts with `9` in
the terminal place `1` and returns `1` empty. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_consumeTerminal :
    ¬ EXEC_041 (fun C s l s' => exec041_consumeTerminalStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_consumeTerminalStep (C := exec041_c0T)
    (o := exec041_at exec041_c0T exec041_m1 []) (l := .finish .terminal)
    (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := ((h exec041_c0T).1 .terminal s s' hs).1
  simp [this] at hp

/-! ### Violation: the loop runs on after its finish (line 2) -/

/-- The wait wakes a finished loop back into step 1; otherwise the reference. -/
def exec041_stepAfterFinishStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .wake => if isExecPhase s.phase then xstep C s .wake else some { s with phase := .completions }
  | l => xstep C s l

/-- ✗ An executor step after the finish violates EXEC-041 (line 2): the empty net finishes
quiescent and its loop wakes again. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_stepAfterFinish :
    ¬ EXEC_041 (fun C s l s' => exec041_stepAfterFinishStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_stepAfterFinishStep (C := exec041_c0)
    (o := exec041_at exec041_c0 exec041_mE (exec041_toTest ++ [.finish .quiescent]))
    (l := .wake) (p := fun s _ => !isExecPhase s.phase) (by decide)
  exact (h exec041_c0).2.1 s s' ⟨.wake, rfl, hs⟩ (by simpa using hp)

/-! ### Violation: an abandoned firing settled after the finish (line 2) -/

/-- After the finish, a queued outcome of an abandoned firing is still settled as a failure
(TransitionFailed after the run ended); otherwise the reference. -/
def exec041_settleAfterFinishStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => if isExecPhase s.phase then xstep C s (.fail i)
      else if s.cq.contains i then some (settle s i) else none
  | l => xstep C s l

/-- ✗ Settling after the finish violates EXEC-041 (line 2), though it changes neither the marking
nor the cause: `t` is in flight when the run finishes stopped, its action then fails, and the
executor settles it. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_settleAfterFinish :
    ¬ EXEC_041 (fun C s l s' => exec041_settleAfterFinishStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_settleAfterFinishStep (C := exec041_c1)
    (o := exec041_at exec041_c1 exec041_m0 (exec041_stop ++ [.ret 0 false]))
    (l := .fail 0) (p := fun s _ => !isExecPhase s.phase) (by decide)
  exact (h exec041_c1).2.1 s s' ⟨.fail 0, rfl, hs⟩ (by simpa using hp)

/-! ### Violation: a late result deposited after the finish (line 3) -/

/-- After the finish, the return of an abandoned action deposits what it wrote; otherwise the
reference. -/
def exec041_lateDepositStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      if isExecPhase s.phase then s₁ else
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with M := qAppend s₁.M f.buf }
      | none => s₁
  | l => xstep C s l

/-- ✗ Changing the returned marking after the finish violates EXEC-041 (line 3): the run
finishes stopped with `t` in flight, its action writes `70` to `1` and returns, and `70` lands in
the returned marking. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_lateDeposit :
    ¬ EXEC_041 (fun C s l s' => exec041_lateDepositStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_lateDepositStep (C := exec041_c1)
    (o := exec041_at exec041_c1 exec041_m0 (exec041_stop ++ [.write 0 1 70]))
    (l := .ret 0 true) (p := fun s s' => !isExecPhase s.phase && s'.M 1 != s.M 1) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have := ((h exec041_c1).2.2.1 s s' ⟨hp.1, _, hs⟩).1
  simp [this] at hp

/-! ### Violation: a close reported as quiescent while a transition is armed (line 4) -/

/-- A closed executor with nothing in flight finishes quiescent, whether or not a transition is
armed; otherwise the reference. -/
def exec041_closeAsQuiescentStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
      if s.phase = .test && liveB C s && (finishQ C s || (s.mode.closing && s.fl.isEmpty)) then
        some { s with phase := .done .quiescent, eq := [] } else none
  | l => xstep C s l

/-- ✗ Reporting a truncated run as quiescent violates EXEC-041 (line 4, AC3): the chain is closed
before its first pass, `t` is armed and never fires, and the run reports `quiescent`. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_closeAsQuiescent :
    ¬ EXEC_041 (fun C s l s' => exec041_closeAsQuiescentStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_closeAsQuiescentStep (C := exec041_c1)
    (o := exec041_at exec041_c1 exec041_m0 (.close :: exec041_toTest))
    (l := .finish .quiescent) (p := fun s _ => !restB exec041_c1 s) (by decide)
  have := (h exec041_c1).2.2.2.1 s s' hs
  unfold Rest at this
  simp [this] at hp

/-! ### Violation: terminal reported with no terminal place marked (line 5) -/

/-- A net that declares terminal places reports every rest as `terminal`; otherwise the
reference. -/
def exec041_terminalAtRestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal =>
      if isExecPhase s.phase &&
          (!liveB C s || (s.phase = .test && !C.terminals.isEmpty && restB C s)) then
        some { s with phase := .done .terminal, eq := [], pq := [] } else none
  | l => xstep C s l

/-- ✗ Reporting `terminal` with no terminal place marked violates EXEC-041 (line 5): the empty
net with `1` terminal reaches rest with `1` empty and reports `terminal`. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_terminalAtRest :
    ¬ EXEC_041 (fun C s l s' => exec041_terminalAtRestStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_terminalAtRestStep (C := exec041_c0T)
    (o := exec041_at exec041_c0T exec041_mE exec041_toTest)
    (l := .finish .terminal) (p := fun s _ => liveB exec041_c0T s) (by decide)
  exact (h exec041_c0T).2.2.2.2.1 s s' hs hp

/-! ### Violation: closed reported with no close (line 6) -/

/-- An idle executor reports `closed` at rest, though nobody closed it; otherwise the reference. -/
def exec041_closedAtOpenRestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .closed =>
      if s.phase = .test && liveB C s && ((s.mode.closing && s.fl.isEmpty) || restB C s) then
        some { s with phase := .done .closed, eq := [] } else none
  | l => xstep C s l

/-- ✗ Reporting `closed` with no close violates EXEC-041 (line 6): the empty net, open, reaches
rest and reports `closed`. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_closedAtOpenRest :
    ¬ EXEC_041 (fun C s l s' => exec041_closedAtOpenRestStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_closedAtOpenRestStep (C := exec041_c0)
    (o := exec041_at exec041_c0 exec041_mE exec041_toTest)
    (l := .finish .closed) (p := fun s _ => !s.mode.closing) (by decide)
  have := (h exec041_c0).2.2.2.2.2.1 s s' hs
  simp [this] at hp

/-! ### Violation: a close reported as stopped (line 7) -/

/-- A close ends the loop at the top of its cycle as an immediate termination would, and reports
`stopped`; otherwise the reference. -/
def exec041_closeAsStopStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .stopped =>
      if s.phase = .completions && liveB C s && s.mode.closing then
        some { s with phase := .done .stopped, eq := [], pq := [] } else none
  | l => xstep C s l

/-- ✗ Reporting `stopped` for a close violates EXEC-041 (line 7): the empty net is closed and the
run reports `stopped`. -/
@[evidence forbids EXEC_041]
theorem EXEC_041_forbids_closeAsStop :
    ¬ EXEC_041 (fun C s l s' => exec041_closeAsStopStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec041_closeAsStopStep (C := exec041_c0)
    (o := exec041_at exec041_c0 exec041_mE [.close])
    (l := .finish .stopped) (p := fun s _ => s.mode != .stopped) (by decide)
  have := (h exec041_c0).2.2.2.2.2.2.1 s s' hs
  simp [this] at hp
end Libpetri.Spec
