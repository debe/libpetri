import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EXEC_041
import Libpetri.Spec.Req.ENV_016
import Libpetri.Spec.Text.ENV_016

set_option linter.missingDocs true

/-!
# ENV-016, second block: awaitTermination (`spec/06-environment-places.md`)

ENV-016 has two halves. The run-with-timeout policy is the first block, `ENV_016`
(`ENV_016.lean`, wave W5). This file states the other half, `awaitTermination(timeout)`, over the
event model of wave W7 (ruling D47 (c)): its answer waits for the termination bookkeeping, and
that bookkeeping is the step that ends the run, answers the queued events and emits
`ExecutionCompleted`.

The model is a pair: an executor with events `E : EvExec N T` (`Reference/Events.lean`) and the
answer relation `A : AwaitRel N T` of its `awaitTermination`. `A C none b` says that on an
executor whose loop was never started the call answers `b`; `A C (some (H, s)) b` says that when
the wait ends at a point of a run where the run has emitted the events `H` and is in state `s`,
the call answers `b`. The witnesses are the reference executor with events `refEvExec` and
`refAwait`, which answers true when the loop was never started and otherwise whether the loop
has finished.

The five lines: a call on a loop that never started answers true; an answer while the loop runs
is false; an answer true comes only after the run took its finish step and answered in it every
accepted event still queued; an answer true comes only when no later step of the run emits
`ExecutionCompleted`; and an answer once the loop has finished is true, whatever the run
emitted, so a failing event store cannot defeat it. That the call returns at all is an offer, so
it is no line: `Env016AwaitCovers` is the coverage clause for the consistency theorem.

The evidence checks the block against the reference and six wrong implementations: one that
waits out its timeout on a loop that never started, one that always answers true (the default
method of Java's `PetriNetExecutor` interface), one whose loop ends before it answers the events
still queued, one whose close ends the run without the finish step, one that releases the call
before it emits `ExecutionCompleted`, and one that answers true only once `ExecutionCompleted` is
in the store. It also shows that an `inject()` that queues its event after the loop has finished
is no fault of `awaitTermination`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Points of a run and the answer of awaitTermination -/

section Carrier

variable {N T : Type}

/-- The state a labelled run from `s` ends in: `s` for the empty run, the target of its last
step otherwise. -/
def env016_endSt (s : XSt N T) : List (EvStep N T) → XSt N T
  | [] => s
  | st :: rest => env016_endSt st.dst rest

/-- **A point of a run** of `E` under `C`: `run` is a labelled run of `E` from the initial state
of `M0` at reading `r0`, `H` is everything the run has emitted (its boot events, then the
events of each step), and `s` is the state it has reached. -/
def RunAt (E : EvExec N T) (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat)
    (run : List (EvStep N T)) (H : List (NetEvent N T)) (s : XSt N T) : Prop :=
  LRun E C (E.boot C M0) (xinit M0 r0) run ∧ H = E.boot C M0 ++ EvStep.events run ∧
    s = env016_endSt (xinit M0 r0) run

/-- The answer relation of `awaitTermination` ([ENV-016]): `A C none b` says that on an
executor whose loop was never started the call answers `b`; `A C (some (H, s)) b` says that when
the wait ends at a point of a run that has emitted `H` and is in state `s`, the call answers
`b`. -/
abbrev AwaitRel (N T : Type) := Cfg N T → Option (List (NetEvent N T) × XSt N T) → Bool → Prop

/-- The reference answer: true when the loop was never started, and otherwise whether the loop
has finished. -/
def refAwaitAns : Option (List (NetEvent N T) × XSt N T) → Bool
  | none => true
  | some (_, s) => !isExecPhase s.phase

/-- **The reference awaitTermination**: the graph of `refAwaitAns`. Java's
`awaitTermination(Duration)` (in `BitmapNetExecutor` and `PrecompiledNetExecutor`) answers true
at once when the executor never started, and otherwise waits on the future the loop completes as
the last act of its termination bookkeeping (`terminatedFuture`, completed in the `finally` of
`executeLoop`). -/
def refAwait : AwaitRel N T := fun _ o b => b = refAwaitAns o

end Carrier

/- The reference awaitTermination is the second witness model of the block's `holds` theorem. -/
#spec_witness refAwait

/-! ## ENV-016, second block: awaitTermination -/

requirement ENV_016_await
  id "ENV-016"
  title "Observable Termination (awaitTermination)"
  kind B
  scope "executors that provide awaitTermination (Java: BitmapNetExecutor and PrecompiledNetExecutor), for the first run of an executor"
  source verbatim "spec/06-environment-places.md"
  covers ENV_016.s1, ENV_016.s2, ENV_016.s3, ENV_016.s4, ENV_016.s5, ENV_016.s6, ENV_016.s7,
        ENV_016.s8, ENV_016.s9, ENV_016.s10
  reading "For every executor with events E, every answer relation A of its awaitTermination and every configuration C:"
          "a call on an executor whose loop was never started answers true;"
          "at every point of a run of E, with the events H emitted so far and the state s, an answer given while the loop is running is false;"
          "at every point of a run of E, an answer true is given only when the run has taken a finish step that left no accepted event queued;"
          "at every point of a run of E, an answer true is given only when no later step of the run emits ExecutionCompleted;"
          "at every point of a run of E at which the loop has finished, the answer is true, whatever the events H are."
  assumes "The model is a pair: an executor with events E : EvExec N T (Reference/Events.lean), whose steps E.step C H s l evs s' append the events evs, and the answer relation A : AwaitRel N T of its awaitTermination. A C none b says that on an executor whose loop was never started the call answers b; A C (some (H, s)) b says that when the wait ends at a point of a run (RunAt: a labelled run of E from the initial state, H everything it emitted, s the state it reached) the call answers b. The call reads and changes nothing: A is not a step of E. The witnesses are refEvExec (under both emission variants) and refAwait, which answers true when the loop was never started and otherwise whether the loop has finished."
          "The wait itself is kind Q and not modelled: the sentence that the call waits until the loop has finished its termination bookkeeping or the timeout has expired, whichever comes first, 'blocks until' and 'within the timeout' of the first quoted sentence, and 'promptly' and 'at once, without waiting for the timeout' of the sentences on a loop that never started. The model places the answer at the moment the wait ends, a point of the run, so a run that finishes during the wait is answered at its finished state. An implementation that polls without waiting meets every line; one that waits out its timeout on a loop that never started and then answers true meets line 1."
          "The termination bookkeeping is the finish step of the model: the step finish c enters the finished phase, answers every accepted event still queued (eq becomes empty: Java completes those inject() futures with false in drainPendingExternalEvents) and emits ExecutionCompleted (EVT-003) when the store accepts it. Java does the same work in the finally block of its loop (executeLoop in BitmapNetExecutor and PrecompiledNetExecutor) and completes the future awaitTermination waits on, terminatedFuture, last."
          "Line 1 is AC2 and the sentence on a loop that never started: an implementation that waits out its timeout on a loop that never started and answers false breaks it (ENV_016_await_mutant_blocksUnstarted, which keeps lines 2 to 5). A rejected start is a loop that never started: when the submit of Java's run(Duration) is rejected, as on an executor whose own pool an earlier close() shut down or on a caller-supplied executor that rejects the task, run puts started back to its previous value before it rethrows, so the call answers true at once. A started flag left set over a loop that never runs makes the call wait out its timeout and answer false, the behaviour ENV_016_await_mutant_blocksUnstarted models, which RD-34 (a) in spec/runtime-defects.md recorded."
          "Lines 2 and 5 are AC1: false while the loop is still running, true once it has stopped. The default method of Java's PetriNetExecutor interface answers true always, so an executor that kept it would break line 2 (ENV_016_await_forbids_alwaysTrue), and line 3 with it: on an executor that never leaves a finished phase (EXEC-041) an answer true while the loop runs has no finish step behind it, so line 2 has no mutant that keeps every other line; BitmapNetExecutor and PrecompiledNetExecutor override it."
          "Lines 3 and 4 are the first quoted sentence, 'blocks until the orchestrator loop has finished its termination bookkeeping (pending inject() futures completed, ExecutionCompleted emitted)'. Line 3: an answer true needs a finish step in the run that left no accepted event queued. An executor whose loop ends before it answers the events still queued breaks it (ENV_016_await_mutant_lateDrain, which keeps lines 1, 2, 4 and 5), and so does one whose close ends the run without the finish step, so that its caller is told the loop terminated although no ExecutionCompleted was ever emitted (ENV_016_await_forbids_closeEnds). Line 3 reads the queue in the finish step, not at the point of the answer: an inject() that queues its event after the loop has finished breaks the inject() requirements (ENV-003, ENV-013), not this block (ENV_016_await_allows_lateInject)."
          "Line 4: an answer true needs the emission of ExecutionCompleted to be over, so no later step of the run emits it. An executor that completes the future the call waits on before it emits ExecutionCompleted, which a later step then appends, breaks it although its store never fails (ENV_016_await_mutant_lateCompleted, which keeps lines 1, 2, 3 and 5). Line 4 does not ask that ExecutionCompleted is in H: a store that throws on it never receives it, and line 4 then holds since nothing of it is still to come."
          "Line 5 is 'MUST NOT itself be defeated by a failure in that bookkeeping' for the answer: once the loop has finished the answer is true. A store that throws when the termination events are appended is modelled as an executor whose finish step appends nothing, since the events never reach the store (in Java a throwing snapshot append skips ExecutionCompleted too: in the finally of executeLoop the final marking snapshot and ExecutionCompleted are emitted in one try whose catch swallows the store failure). The reference answer reads the state only, so it meets the block over that executor as well (ENV_016_await_allows_throwingStore), while an answer that waits for ExecutionCompleted to reach the store answers false for ever and breaks line 5 (ENV_016_await_mutant_waitsForStore, which keeps lines 1 to 4). A failure before the first cycle has no step of its own in the model, which has no step for a loop that dies before its run. Java emits ExecutionStarted and the first marking snapshot inside the try/finally of its loop (executeLoop in BitmapNetExecutor and PrecompiledNetExecutor), so a store that throws on them ends the loop through the same finally, which sets the termination reason (stopped, unless a marked terminal place or an earlier close decides it), answers the queued events and completes the future the call waits on: the run ends with a finish step whose events never reach the store, as in ENV_016_await_allows_throwingStore, and the call answers true once the loop has stopped (AC1). A loop that dies there without the finish step and without completing that future, the behaviour RD-34 (b) in spec/runtime-defects.md recorded, reads in the model as a loop that stays running: it meets every line but breaks AC1 and the quoted 'MUST NOT itself be defeated by a failure in that bookkeeping (for example a throwing event store)', so AC1 is tested for it (AbstractNetExecutorEnvironmentTest awaitTermination_trueAfterABootThatThrew_ENV016_AC1), not proven."
          "That the call returns at all is an offer and so no line: the sentence that a failure in the termination bookkeeping shall not keep the call from returning its answer, and 'returning whether termination was observed', are the coverage clause Env016AwaitCovers (every call has an answer), which the consistency theorem takes with the block. An implementation whose call never returns or raises meets every line and fails it (env016_await_covers_hang). The clause asks an answer at every argument, unreachable states included, which is more than the sentence needs and which the reference meets."
          "Lines 3 to 5 also bound the executor, not only its answer: at a finished point line 5 asks true, so the run must have taken a finish step that answered the queue and must emit no ExecutionCompleted later. This restates for awaitTermination what EXEC-041 ('end a run only by finishing it'), ENV-013 (a closed executor ends its run with no external event queued) and EVT-003 already ask of the loop."
          "Scope (Status Proposed, priority MAY, ruling D47 (c)): only Java provides awaitTermination, in BitmapNetExecutor and PrecompiledNetExecutor. TypeScript provides the run-timeout policy of the first block but not awaitTermination; Rust and Python provide neither (spec/runtime-defects.md, UB-02 and UB-03). The run-timeout policy and the third paragraph's EARS sentences are the first block of ENV-016, ENV_016 (ENV_016.lean); AC3 is that block's."
          "One run per executor, as the quoted scope sentence says: a point of a run starts from the initial state. Whether an executor may run again is not specified. Java does not refuse a second run(), and its termination future is completed once, so on a second run of the same executor its awaitTermination answers true while the second loop runs; that is outside this block and is no runtime defect while the spec leaves a second run open."
          "The test derivation (awaitTermination reports the transition of a run whose action is still in flight when a short timeout expires) is ENV_016_await_nonvacuous on the first block's run: while the action is in flight the loop is running and the answer is false; after the close of the timeout policy, the action's return and the closed finish, the answer is true, the finish step left no accepted event queued and the run has emitted ExecutionCompleted. A call before the run answers true."
  signoff "2026-11-13 cce583aca99ae0ed ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → AwaitRel N T → Prop :=
    fun E A => ∀ C,
      (∀ b, A C none b → b = true) ∧
      (∀ M0 r0 run H s b, RunAt E C M0 r0 run H s → A C (some (H, s)) b →
        isExecPhase s.phase = true → b = false) ∧
      (∀ M0 r0 run H s, RunAt E C M0 r0 run H s → A C (some (H, s)) true →
        ∃ st ∈ run, exec041_isFinish st.lbl = true ∧ st.dst.eq = []) ∧
      (∀ M0 r0 run H s, RunAt E C M0 r0 run H s → A C (some (H, s)) true →
        ∀ run', LRun E C H s run' → ∀ e ∈ EvStep.events run', e.kind ≠ .executionCompleted) ∧
      (∀ M0 r0 run H s b, RunAt E C M0 r0 run H s → A C (some (H, s)) b →
        isExecPhase s.phase = false → b = true)

/- The pinned readable form of the block: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_016_await : {N T : Type} → [DecidableEq N] → EvExec N T → AwaitRel N T → Prop :=
fun {N T} [DecidableEq N] E A =>
  ∀ (C : Cfg N T),
    (∀ (b : Bool), A C none b → b = true) ∧
      (∀ (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)) (H : List (NetEvent N T)) (s : XSt N T) (b : Bool),
          RunAt E C M0 r0 run H s → A C (some (H, s)) b → isExecPhase s.phase = true → b = false) ∧
        (∀ (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)) (H : List (NetEvent N T)) (s : XSt N T),
            RunAt E C M0 r0 run H s →
              A C (some (H, s)) true → ∃ st ∈ run, exec041_isFinish st.lbl = true ∧ st.dst.eq = []) ∧
          (∀ (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)) (H : List (NetEvent N T)) (s : XSt N T),
              RunAt E C M0 r0 run H s →
                A C (some (H, s)) true →
                  ∀ (run' : List (EvStep N T)),
                    LRun E C H s run' → ∀ e ∈ EvStep.events run', e.kind ≠ NetEventKind.executionCompleted) ∧
            ∀ (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)) (H : List (NetEvent N T)) (s : XSt N T) (b : Bool),
              RunAt E C M0 r0 run H s → A C (some (H, s)) b → isExecPhase s.phase = false → b = true
-/
#guard_msgs in #print ENV_016_await

/-! ## Executors with events from a step function

The reference and the wrong executors below all have this form: steps given by a function,
events by an emission. The reference is `env016_exec (refBoot P) xstep (refEmitW P)`, which is
`refEvExec P` itself. -/

section Exec

variable {N T : Type}

/-- The executor with events that steps as `stepF` says and appends `emit`'s events. -/
def env016_exec (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    EvExec N T where
  boot := boot
  step := fun C H s l evs s' => stepF C s l = some s' ∧ evs = emit C H s l s'

/-- The labelled run of `env016_exec` from history `H` and state `s` along the labels `ls`, if
every label is a step. -/
def env016_run (stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T))
    (C : Cfg N T) : List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (stepF C s l).bind fun s' =>
      (env016_run stepF emit C (H ++ emit C H s l s') s' ls).map (⟨s, l, emit C H s l s', s'⟩ :: ·)

/-- A run `env016_run` builds is a labelled run of `env016_exec`. -/
theorem env016_run_lrun {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      env016_run stepF emit C H s ls = some run → LRun (env016_exec boot stepF emit) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [env016_run] at h
    cases hs : stepF C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : env016_run stepF emit C (H ++ emit C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, env016_run_lrun hr⟩

/-- A run `env016_run` builds from the initial state gives a point of a run. -/
theorem env016_runAt {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    {C : Cfg N T} {M0 : QMarking N T} {r0 : Nat} {ls : List (XLbl N T)} {run : List (EvStep N T)}
    (h : env016_run stepF emit C (boot C M0) (xinit M0 r0) ls = some run) :
    RunAt (env016_exec boot stepF emit) C M0 r0 run (boot C M0 ++ EvStep.events run)
      (env016_endSt (xinit M0 r0) run) :=
  ⟨env016_run_lrun h, rfl, rfl⟩

/-- Read a value off a decided check of an optional value. -/
theorem env016l1_of_map {α : Type} {o : Option α} {p : α → Bool} (h : o.map p = some true) :
    ∃ a, o = some a ∧ p a = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some a => exact ⟨a, rfl, by simpa [ho] using h⟩

/-- **Steps like the reference's around the end of a run**: while the loop runs, every step is a
reference step; once it has finished, every step is an outside step and the loop stays
finished. -/
def env016_RefLike [DecidableEq N] [Ord N] (stepF :Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) : Prop :=
  (∀ C s l s', isExecPhase s.phase = true → stepF C s l = some s' → xstep C s l = some s') ∧
  (∀ C s l s', isExecPhase s.phase = false → stepF C s l = some s' →
    l.outside = true ∧ isExecPhase s'.phase = false)

/-- **An emission quiet outside**: no outside step emits `ExecutionCompleted`. -/
def env016_OutsideQuiet
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    Prop :=
  ∀ C H s l s', l.outside = true → ∀ e ∈ emit C H s l s', e.kind ≠ .executionCompleted

end Exec

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The reference executor with events is an executor of the form `env016_exec`. -/
theorem refEvExec_eq_env016 (P : EvPol) :
    refEvExec (N := N) (T := T) P = env016_exec (refBoot P) xstep (refEmitW P) := rfl

/-- The reference steps are like the reference's around the end of a run: once the loop has
finished, only outside steps remain and none of them changes the phase. -/
theorem env016_xstep_refLike : env016_RefLike (xstep (N := N) (T := T)) := by
  refine ⟨fun _ _ _ _ _ h => h, fun C s l s' hd h => ?_⟩
  have hR : RefExec C s l s' := h
  have ho := exec041_ref_outside hR hd
  obtain ⟨-, -, hp, -⟩ := xstepW_outside_frame hR ho
  exact ⟨ho, hp ▸ hd⟩

omit [Ord N] in
/-- A reference step that finishes the run is a finish, and it leaves no accepted event
queued. -/
theorem env016_enter_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (he : isExecPhase s.phase = true)
    (hd : isExecPhase s'.phase = false) : exec041_isFinish l = true ∧ s'.eq = [] := by
  refine ⟨exec041_ref_enter h he hd, ?_⟩
  have hf := exec041_ref_enter h he hd
  cases l with
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | _ => simp [exec041_isFinish] at hf

/-- **A run that starts running and ends finished took a finish step that left no accepted event
queued**: the step that left the running phase is a reference step, so it is a finish and it
empties the queue. -/
theorem env016_run_finish
    {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hR : env016_RefLike stepF) {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (env016_exec boot stepF emit) C H s run → isExecPhase s.phase = true →
      isExecPhase (env016_endSt s run).phase = false →
      ∃ st ∈ run, exec041_isFinish st.lbl = true ∧ st.dst.eq = []
  | _, s, [], _, hr, hd => absurd (hr.symm.trans hd) (by decide)
  | H, s, st :: rest, hl, hr, hd => by
    obtain ⟨hsrc, ⟨hstep, -⟩, hrest⟩ := hl
    subst hsrc
    have hx : RefExec C st.src st.lbl st.dst := hR.1 _ _ _ _ hr hstep
    cases hy : isExecPhase st.dst.phase with
    | false => exact ⟨st, List.mem_cons_self .., env016_enter_step hx hr hy⟩
    | true =>
      obtain ⟨st', hm, hc⟩ := env016_run_finish hR hrest hy hd
      exact ⟨st', List.mem_cons_of_mem _ hm, hc⟩

omit [DecidableEq N] [Ord N] in
/-- **After the loop has finished, no step emits `ExecutionCompleted`**: only outside steps
remain, the loop stays finished, and an emission quiet outside emits nothing of the kind. -/
theorem env016_cont
    {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hR : ∀ C s l s', isExecPhase s.phase = false → stepF C s l = some s' →
      l.outside = true ∧ isExecPhase s'.phase = false)
    (hem : env016_OutsideQuiet emit) {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (env016_exec boot stepF emit) C H s run → isExecPhase s.phase = false →
      ∀ e ∈ EvStep.events run, e.kind ≠ .executionCompleted
  | _, _, [], _, _ => by simp [EvStep.events]
  | H, s, st :: rest, hl, hd => by
    obtain ⟨hsrc, ⟨hstep, hev⟩, hrest⟩ := hl
    subst hsrc
    obtain ⟨ho, hd'⟩ := hR _ _ _ _ hd hstep
    intro e he
    simp only [EvStep.events, List.flatMap_cons, List.mem_append] at he
    rcases he with he | he
    · rw [hev] at he; exact hem _ _ _ _ _ ho e he
    · exact env016_cont hR hem hrest hd' e he

/-- The reference answer meets the block over every executor whose steps are like the
reference's around the end of a run and whose emission is quiet outside. -/
theorem env016_await_of_refLike (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (stepF : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T))
    (hR : env016_RefLike stepF) (hem : env016_OutsideQuiet emit) :
    ENV_016_await (env016_exec boot stepF emit) refAwait := by
  have hdone : ∀ {C : Cfg N T} {H : List (NetEvent N T)} {s : XSt N T},
      refAwait C (some (H, s)) true → isExecPhase s.phase = false := fun {_ _ s} h => by
    change true = !isExecPhase s.phase at h
    cases hp : isExecPhase s.phase
    · rfl
    · rw [hp] at h; exact absurd h (by decide)
  intro C
  refine ⟨fun b h => h, fun M0 r0 run H s b _ h hx => ?_, fun M0 r0 run H s hr h => ?_,
    fun M0 r0 run H s _ h run' hl => ?_, fun M0 r0 run H s b _ h hx => ?_⟩
  · change b = !isExecPhase s.phase at h
    rw [h, hx]; rfl
  · obtain ⟨hl, -, rfl⟩ := hr
    exact env016_run_finish hR hl rfl (hdone h)
  · exact env016_cont hR.2 hem hl (hdone h)
  · change b = !isExecPhase s.phase at h
    rw [h, hx]; rfl

/-- The reference emission is quiet outside: `ExecutionCompleted` comes only from a finish,
which is no outside step. -/
theorem env016_refEmitW_quiet (P : EvPol) : env016_OutsideQuiet (refEmitW (N := N) (T := T) P) := by
  intro C H s l s' ho e he
  cases l <;> simp [XLbl.outside] at ho
  all_goals (try simp [refEmitW] at he)
  obtain ⟨-, he⟩ := he
  split at he
  · simp at he; subst he; simp [NetEvent.kind]
  · simp at he

/-- ✓ The reference with the Java and TypeScript emission meets the awaitTermination block of
ENV-016. A call before the run answers true. During the run the answer is whether the loop has
finished, so it is false while the loop runs. The loop finishes only by a finish step, and that
step answers every event still queued and emits `ExecutionCompleted`; after it only callers
act, and none of their steps emits `ExecutionCompleted` again. -/
@[evidence holds ENV_016_await]
theorem ENV_016_await_reference : ENV_016_await (refEvExec (N := N) (T := T) polJT) refAwait := by
  rw [refEvExec_eq_env016]
  exact env016_await_of_refLike _ _ _ env016_xstep_refLike (env016_refEmitW_quiet _)

/-- ✓ The reference with the Rust and Python emission meets the block too: the answer reads the
state of the loop, not which events the run emits. -/
@[evidence holds ENV_016_await]
theorem ENV_016_await_rust : ENV_016_await (refEvExec (N := N) (T := T) polRust) refAwait := by
  rw [refEvExec_eq_env016]
  exact env016_await_of_refLike _ _ _ env016_xstep_refLike (env016_refEmitW_quiet _)

/-- **The coverage conjunct the block asks of the consistency theorem**: every call of
awaitTermination has an answer, on an executor that never started and at every point of a run
("returning whether termination was observed within the timeout"; "MUST NOT itself be
defeated"). It is a clause over the answer relation. Offers are never a line of a block
(glossary `GlossaryExec.lean`). -/
def Env016AwaitCovers {N T : Type} (A : AwaitRel N T) : Prop :=
  ∀ C o, ∃ b, A C o b

omit [DecidableEq N] [Ord N] in
/-- The reference answer meets the coverage conjunct: it is the graph of a total function. -/
theorem env016_await_ref_covers : Env016AwaitCovers (refAwait (N := N) (T := T)) :=
  fun _ o => ⟨refAwaitAns o, rfl⟩

end Reference

/-! ## The five lines, one at a time -/

section Lines

variable {N T : Type}

/-- Line 1 of `ENV_016_await` alone: a call on a loop that never started answers true. -/
def env016_l1 (_E : EvExec N T) (A : AwaitRel N T) : Prop := ∀ C b, A C none b → b = true

/-- Line 2 of `ENV_016_await` alone: while the loop runs, the call answers false. -/
def env016_l2 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  ∀ C M0 r0 run H s b, RunAt E C M0 r0 run H s → A C (some (H, s)) b →
    isExecPhase s.phase = true → b = false

/-- Line 3 of `ENV_016_await` alone: an answer true needs a finish step that left no accepted
event queued. -/
def env016_l3 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  ∀ C M0 r0 run H s, RunAt E C M0 r0 run H s → A C (some (H, s)) true →
    ∃ st ∈ run, exec041_isFinish st.lbl = true ∧ st.dst.eq = []

/-- Line 4 of `ENV_016_await` alone: after an answer true, no later step emits
`ExecutionCompleted`. -/
def env016_l4 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  ∀ C M0 r0 run H s, RunAt E C M0 r0 run H s → A C (some (H, s)) true →
    ∀ run', LRun E C H s run' → ∀ e ∈ EvStep.events run', e.kind ≠ .executionCompleted

/-- Line 5 of `ENV_016_await` alone: once the loop has finished, the call answers true. -/
def env016_l5 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  ∀ C M0 r0 run H s b, RunAt E C M0 r0 run H s → A C (some (H, s)) b →
    isExecPhase s.phase = false → b = true

/-- `ENV_016_await` is its five lines. -/
theorem env016_await_iff [DecidableEq N] (E : EvExec N T) (A : AwaitRel N T) :
    ENV_016_await E A ↔
      env016_l1 E A ∧ env016_l2 E A ∧ env016_l3 E A ∧ env016_l4 E A ∧ env016_l5 E A :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2.1, fun C => (h C).2.2.2.1,
      fun C => (h C).2.2.2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2.1 C, h.2.2.2.1 C, h.2.2.2.2 C⟩⟩

/-- Every line but line 1. -/
def env016_but1 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  env016_l2 E A ∧ env016_l3 E A ∧ env016_l4 E A ∧ env016_l5 E A

/-- Every line but line 3. -/
def env016_but3 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  env016_l1 E A ∧ env016_l2 E A ∧ env016_l4 E A ∧ env016_l5 E A

/-- Every line but line 4. -/
def env016_but4 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  env016_l1 E A ∧ env016_l2 E A ∧ env016_l3 E A ∧ env016_l5 E A

/-- Every line but line 5. -/
def env016_but5 (E : EvExec N T) (A : AwaitRel N T) : Prop :=
  env016_l1 E A ∧ env016_l2 E A ∧ env016_l3 E A ∧ env016_l4 E A

/-- The reference answer meets lines 1, 2 and 5 over every executor: it reads only whether the
loop has finished. -/
theorem env016_ref_l125 (E : EvExec N T) :
    env016_l1 E refAwait ∧ env016_l2 E refAwait ∧ env016_l5 E refAwait := by
  refine ⟨fun _ _ h => h, fun C M0 r0 run H s b _ h hx => ?_, fun C M0 r0 run H s b _ h hx => ?_⟩
  · change b = !isExecPhase s.phase at h
    rw [h, hx]; rfl
  · change b = !isExecPhase s.phase at h
    rw [h, hx]; rfl

end Lines

/-! ## Examples

`env016_tc`: place `0` is a terminal place and holds one token from the start, so the loop may
finish at once; place `1` is an environment place. There are no transitions. -/

/-- The configuration of the terminal examples. -/
def env016_tc : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [0], envs := [1], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking of the terminal examples: one token in the terminal place `0`. -/
def env016_tm0 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- The initial marking of the first block's run: one token in place `0`. -/
def env016_m0 : QMarking Nat Nat := fun p => if p = 0 then [5] else []

/-! ### Every line exercised -/

/-- The labels of the test derivation: the loop parks with the action of `t` in flight, the
caller's timeout expires under the close policy, the action writes `7` to place `1` and returns,
and the loop finishes closed. -/
def env016_closedRun : List (XLbl Nat Nat) :=
  env016_toPark ++ [.close] ++ env016_toTest ++ [.finish .closed]

/-- The reference with the Java and TypeScript emission, along `ls` from the first block's
initial state. -/
def env016_refRun (ls : List (XLbl Nat Nat)) : Option (List (EvStep Nat Nat)) :=
  env016_run xstep (refEmitW polJT) env016_c (refBoot polJT env016_c env016_m0)
    (xinit env016_m0 0) ls

/-- Every line of the block is exercised by the reference, on the first block's run (transition
`t` moves the token of place `0` to place `1` through an asynchronous action). (1) A call before
the run answers true. (2) The loop parks with the firing of `t` in flight: the loop is running
and the call answers false. (3) The caller's timeout expires under the close policy, the action
writes `7` and returns, and the loop finishes closed: the finish step left no event queued, the
run has emitted `ExecutionCompleted`, place `1` holds `7`, and the call answers true. -/
@[evidence nonvacuous ENV_016_await]
theorem ENV_016_await_nonvacuous :
    refAwait (N := Nat) (T := Nat) env016_c none true ∧
    (∃ run H s, RunAt (refEvExec polJT) env016_c env016_m0 0 run H s ∧
      isExecPhase s.phase = true ∧ s.fl ≠ [] ∧ refAwait env016_c (some (H, s)) false) ∧
    (∃ run H s, RunAt (refEvExec polJT) env016_c env016_m0 0 run H s ∧
      s.phase = .done .closed ∧ (∃ st ∈ run, exec041_isFinish st.lbl = true ∧ st.dst.eq = []) ∧
      NetEvent.executionCompleted ∈ H ∧ s.M 1 = [7] ∧ refAwait env016_c (some (H, s)) true) := by
  refine ⟨rfl, ?_, ?_⟩
  · obtain ⟨run, ho, hp⟩ := env016l1_of_map (o := env016_refRun env016_toPark)
      (p := fun run => isExecPhase (env016_endSt (xinit env016_m0 0) run).phase &&
        !(env016_endSt (xinit env016_m0 0) run).fl.isEmpty) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    refine ⟨run, _, _, (by rw [refEvExec_eq_env016]; exact env016_runAt ho), hp.1, hp.2, ?_⟩
    change false = !isExecPhase _
    rw [hp.1]; rfl
  · obtain ⟨run, ho, hp⟩ := env016l1_of_map (o := env016_refRun env016_closedRun)
      (p := fun run => (env016_endSt (xinit env016_m0 0) run).phase == .done .closed &&
        run.any (fun st => exec041_isFinish st.lbl && st.dst.eq.isEmpty) &&
        (refBoot polJT env016_c env016_m0 ++ EvStep.events run).contains .executionCompleted &&
        (env016_endSt (xinit env016_m0 0) run).M 1 == [7]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.isEmpty_iff,
      List.contains_iff_mem] at hp
    obtain ⟨⟨⟨hph, hfin⟩, hec⟩, hM⟩ := hp
    refine ⟨run, _, _, (by rw [refEvExec_eq_env016]; exact env016_runAt ho), hph, hfin, hec, hM, ?_⟩
    change true = !isExecPhase _
    rw [hph]; rfl

/-! ### Violation: a call on a loop that never started waits (line 1) -/

/-- An implementation that waits out its timeout on a loop that never started and answers false:
Java's `awaitTermination` without its `if (!started) return true` guard waits on a future that
only a run completes. Otherwise it answers as the reference. -/
def env016_blocksUnstarted {N T : Type} : AwaitRel N T :=
  fun _ o b => b = match o with
    | none => false
    | some (_, s) => !isExecPhase s.phase

/-- ✗ Waiting on a loop that never started violates the block (line 1, AC2 "returns promptly
(true) if the loop was never started"): the call answers false although there is nothing to wait
for. Once the loop has started it answers as the reference, so it keeps lines 2 to 5. -/
@[evidence mutant ENV_016_await]
theorem ENV_016_await_mutant_blocksUnstarted :
    env016_but1 (refEvExec (N := Nat) (T := Nat) polJT) env016_blocksUnstarted ∧
      ¬ ENV_016_await (refEvExec (N := Nat) (T := Nat) polJT) env016_blocksUnstarted := by
  obtain ⟨-, h2, h3, h4, h5⟩ := (env016_await_iff _ _).1
    (ENV_016_await_reference (N := Nat) (T := Nat))
  refine ⟨⟨fun C M0 r0 run H s b hr hA => h2 C M0 r0 run H s b hr hA,
    fun C M0 r0 run H s hr hA => h3 C M0 r0 run H s hr hA,
    fun C M0 r0 run H s hr hA => h4 C M0 r0 run H s hr hA,
    fun C M0 r0 run H s b hr hA => h5 C M0 r0 run H s b hr hA⟩, fun h => ?_⟩
  exact absurd ((h env016_c).1 false rfl) (by decide)

/-! ### Violation: always true (line 2) -/

/-- An implementation that answers true always: the default method `awaitTermination` of Java's
`PetriNetExecutor` interface, which an executor that does not
override it inherits. -/
def env016_alwaysTrue {N T : Type} : AwaitRel N T := fun _ _ b => b = true

/-- ✗ Answering true always violates the block (line 2, AC1 "returns false while the loop is
still running"): at the start of a run the loop is running, and the call answers true. It breaks
line 3 as well, since no finish step has happened yet: on an executor that never leaves a
finished phase, an answer true while the loop runs always lacks the finish step line 3 asks
for. -/
@[evidence forbids ENV_016_await]
theorem ENV_016_await_forbids_alwaysTrue :
    ¬ ENV_016_await (refEvExec (N := Nat) (T := Nat) polJT) env016_alwaysTrue := by
  intro h
  have hr : RunAt (refEvExec (N := Nat) (T := Nat) polJT) env016_c env016_m0 0 []
      (refBoot polJT env016_c env016_m0 ++ EvStep.events []) (env016_endSt (xinit env016_m0 0) []) :=
    by rw [refEvExec_eq_env016]; exact env016_runAt (ls := []) rfl
  exact absurd ((h env016_c).2.1 _ _ _ _ _ true hr rfl rfl) (by decide)

/-! ### Violation: the loop ends before it answers the queued events (line 3) -/

/-- An executor whose finish step ends the run but leaves the accepted events queued, to be
answered later: the future the call waits on is completed before the pending `inject()` futures
are. Every other step is the reference's. -/
def env016_lateDrainStep (C : Cfg Nat Nat) (s : XSt Nat Nat) :
    XLbl Nat Nat → Option (XSt Nat Nat)
  | .finish c => (xstep C s (.finish c)).map fun s' => { s' with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env016_lateDrainStep`, with the reference emission. -/
def env016_lateDrain : EvExec Nat Nat :=
  env016_exec (refBoot polJT) env016_lateDrainStep (refEmitW polJT)

/-- Once the loop has finished, the late-drain executor steps as the reference: only outside
steps remain, and the loop stays finished. -/
theorem env016_lateDrain_after : ∀ (C : Cfg Nat Nat) (s : XSt Nat Nat) (l : XLbl Nat Nat) s',
    isExecPhase s.phase = false → env016_lateDrainStep C s l = some s' →
    l.outside = true ∧ isExecPhase s'.phase = false := by
  intro C s l s' hd h
  cases l with
  | finish c =>
    simp only [env016_lateDrainStep, Option.map_eq_some_iff] at h
    obtain ⟨s'', hx, -⟩ := h
    exact absurd (env016_xstep_refLike.2 _ _ _ _ hd hx).1 (by simp [XLbl.outside])
  | _ => exact env016_xstep_refLike.2 _ _ _ _ hd h

/-- The late-drain executor with the reference answer breaks the block: a caller injects `5`
into the environment place `1`, and the run then finishes on its marked terminal place; the
finish step leaves the event queued, unanswered, and the call answers true. -/
theorem env016_lateDrain_breaks :
    ¬ ENV_016_await env016_lateDrain (refAwait (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨run, ho, hp⟩ := env016l1_of_map
    (o := env016_run env016_lateDrainStep (refEmitW polJT) env016_tc
      (refBoot polJT env016_tc env016_tm0) (xinit env016_tm0 0)
      [.request 1 5 .accepted, .finish .terminal])
    (p := fun run => !isExecPhase (env016_endSt (xinit env016_tm0 0) run).phase &&
      !run.any (fun st => exec041_isFinish st.lbl && st.dst.eq.isEmpty)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hA : refAwait env016_tc
      (some (refBoot polJT env016_tc env016_tm0 ++ EvStep.events run,
        env016_endSt (xinit env016_tm0 0) run)) true := by
    change true = !isExecPhase _
    rw [hp.1]; rfl
  obtain ⟨st, hm, hf, he⟩ := (h env016_tc).2.2.1 _ _ _ _ _ (env016_runAt ho) hA
  have : run.any (fun st => exec041_isFinish st.lbl && st.dst.eq.isEmpty) = true :=
    List.any_eq_true.2 ⟨st, hm, by simp [hf, he]⟩
  rw [hp.2] at this
  exact absurd this (by decide)

/-- ✗ Answering before the queued events are answered violates the block (line 3, "blocks until
the orchestrator loop has finished its termination bookkeeping (pending `inject()` futures
completed, ..."): a caller injects `5` into the environment place `1`, and the run then finishes
on its marked terminal place; the finish step leaves the event queued, unanswered, and the call
answers true. It answers as the reference and emits as the reference, so it keeps lines 1, 2, 4
and 5. -/
@[evidence mutant ENV_016_await]
theorem ENV_016_await_mutant_lateDrain :
    env016_but3 env016_lateDrain (refAwait (N := Nat) (T := Nat)) ∧
      ¬ ENV_016_await env016_lateDrain (refAwait (N := Nat) (T := Nat)) := by
  obtain ⟨h1, h2, h5⟩ := env016_ref_l125 (N := Nat) (T := Nat) env016_lateDrain
  refine ⟨⟨h1, h2, fun C M0 r0 run H s _ hA run' hl => ?_, h5⟩, env016_lateDrain_breaks⟩
  have hd : isExecPhase s.phase = false := by
    change true = !isExecPhase s.phase at hA
    cases hp : isExecPhase s.phase
    · rfl
    · rw [hp] at hA; exact absurd hA (by decide)
  exact env016_cont env016_lateDrain_after (env016_refEmitW_quiet polJT) hl hd

/-! ### Violation: a close ends the run without the finish step (line 3) -/

/-- An executor whose close ends the run on the spot, without the finish step, so the run ends
without its termination bookkeeping and without `ExecutionCompleted`. Every other step is the
reference's. -/
def env016_closeEndsStep (C : Cfg Nat Nat) (s : XSt Nat Nat) :
    XLbl Nat Nat → Option (XSt Nat Nat)
  | .close => (closeStep s).map fun s' => { s' with phase := .done .closed }
  | l => xstep C s l

/-- The executor of `env016_closeEndsStep`, with the reference emission. -/
def env016_closeEnds : EvExec Nat Nat :=
  env016_exec (refBoot polJT) env016_closeEndsStep (refEmitW polJT)

/-- ✗ Answering true for a run that ended without its finish step violates the block (line 3,
"`ExecutionCompleted` emitted"): the caller closes the executor at the start of the first block's
run, the close ends the run at once, and the call answers true, although the run never took the
step that emits `ExecutionCompleted`. -/
@[evidence forbids ENV_016_await]
theorem ENV_016_await_forbids_closeEnds :
    ¬ ENV_016_await env016_closeEnds (refAwait (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨run, ho, hp⟩ := env016l1_of_map
    (o := env016_run env016_closeEndsStep (refEmitW polJT) env016_c
      (refBoot polJT env016_c env016_m0) (xinit env016_m0 0) [.close])
    (p := fun run => !isExecPhase (env016_endSt (xinit env016_m0 0) run).phase &&
      !run.any (fun st => exec041_isFinish st.lbl)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hA : refAwait env016_c
      (some (refBoot polJT env016_c env016_m0 ++ EvStep.events run,
        env016_endSt (xinit env016_m0 0) run)) true := by
    change true = !isExecPhase _
    rw [hp.1]; rfl
  obtain ⟨st, hm, hf, -⟩ := (h env016_c).2.2.1 _ _ _ _ _ (env016_runAt ho) hA
  have : run.any (fun st => exec041_isFinish st.lbl) = true := List.any_eq_true.2 ⟨st, hm, hf⟩
  rw [hp.2] at this
  exact absurd this (by decide)

/-! ### Allowed: an inject() that queues after the loop has finished (line 3) -/

/-- An executor whose `inject()` misses the loop's end: once the loop has finished, an accepted
request still queues its event, and nothing will answer it. Java's `inject` without the re-check
after `externalEventQueue.offer` (`inject` in `BitmapNetExecutor`) would do this. Every other
step is the reference's. -/
def env016_lateInjectStep (C : Cfg Nat Nat) (s : XSt Nat Nat) :
    XLbl Nat Nat → Option (XSt Nat Nat)
  | .request p x .accepted =>
      if !isExecPhase s.phase && C.envs.contains p then
        some { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1 }
      else xstep C s (.request p x .accepted)
  | l => xstep C s l

/-- The executor of `env016_lateInjectStep`, with the reference emission. -/
def env016_lateInject : EvExec Nat Nat :=
  env016_exec (refBoot polJT) env016_lateInjectStep (refEmitW polJT)

/-- The late `inject()` steps as the reference while the loop runs, and its extra step is an
outside step that keeps the loop finished. -/
theorem env016_lateInject_refLike : env016_RefLike env016_lateInjectStep := by
  refine ⟨fun C s l s' hr h => ?_, fun C s l s' hd h => ?_⟩
  · unfold env016_lateInjectStep at h
    split at h
    · rw [hr] at h; simpa using h
    · exact h
  · unfold env016_lateInjectStep at h
    split at h
    · split at h
      · cases h; exact ⟨rfl, hd⟩
      · exact env016_xstep_refLike.2 _ _ _ _ hd h
    · exact env016_xstep_refLike.2 _ _ _ _ hd h

/-- ✓ An `inject()` that queues its event after the loop has finished is no fault of
`awaitTermination` (line 3 reads the queue in the finish step): the run finishes on its marked
terminal place with nothing queued, a late caller's event is then queued and never answered,
and the call still answers true. That late event breaks the `inject()` requirements
([ENV-003], [ENV-013]), not this block. -/
@[evidence allows ENV_016_await]
theorem ENV_016_await_allows_lateInject :
    ENV_016_await env016_lateInject (refAwait (N := Nat) (T := Nat)) :=
  env016_await_of_refLike _ _ _ env016_lateInject_refLike (env016_refEmitW_quiet _)

/-! ### Violation: the call is released before ExecutionCompleted is emitted (line 4) -/

/-- The emission of an executor that completes the future the call waits on before it emits
`ExecutionCompleted`: its finish step appends its events without `ExecutionCompleted`, and the
first later step appends the missing `ExecutionCompleted`. Java would do this if
`terminatedFuture.complete` moved above the emission in the `finally` block of its loop
(`executeLoop` in `BitmapNetExecutor`). The store never fails. -/
def env016_lateCompletedEmit (C : Cfg Nat Nat) (H : List (NetEvent Nat Nat)) (s : XSt Nat Nat)
    (l : XLbl Nat Nat) (s' : XSt Nat Nat) : List (NetEvent Nat Nat) :=
  match l with
  | .finish _ => (refEmitW polJT C H s l s').filter (fun e => e.kind != .executionCompleted)
  | _ => refEmitW polJT C H s l s' ++
      (if !isExecPhase s.phase && !H.any (fun e => e.kind == .executionCompleted)
       then [.executionCompleted] else [])

/-- The reference executor with the late `ExecutionCompleted`. -/
def env016_lateCompleted : EvExec Nat Nat :=
  env016_exec (refBoot polJT) xstep env016_lateCompletedEmit

/-- The late-`ExecutionCompleted` executor with the reference answer breaks the block: the run
finishes on its marked terminal place, the call answers true, and only the next step emits
`ExecutionCompleted`. -/
theorem env016_lateCompleted_breaks :
    ¬ ENV_016_await env016_lateCompleted (refAwait (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨run, ho, hp⟩ := env016l1_of_map
    (o := env016_run xstep env016_lateCompletedEmit env016_tc
      (refBoot polJT env016_tc env016_tm0) (xinit env016_tm0 0) [.finish .terminal])
    (p := fun run => !isExecPhase (env016_endSt (xinit env016_tm0 0) run).phase &&
      !(refBoot polJT env016_tc env016_tm0 ++ EvStep.events run).any
        (fun e => e.kind == .executionCompleted)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hA : refAwait env016_tc
      (some (refBoot polJT env016_tc env016_tm0 ++ EvStep.events run,
        env016_endSt (xinit env016_tm0 0) run)) true := by
    change true = !isExecPhase _
    rw [hp.1]; rfl
  let s := env016_endSt (xinit env016_tm0 0) run
  let H := refBoot polJT env016_tc env016_tm0 ++ EvStep.events run
  have hl : LRun env016_lateCompleted env016_tc H s
      [⟨s, .delay 1, env016_lateCompletedEmit env016_tc H s (.delay 1) { s with now := s.now + 1 },
        { s with now := s.now + 1 }⟩] := ⟨rfl, ⟨rfl, rfl⟩, trivial⟩
  apply (h env016_tc).2.2.2.1 _ _ _ _ _ (env016_runAt ho) hA _ hl .executionCompleted _ rfl
  simp only [EvStep.events, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    env016_lateCompletedEmit]
  rw [show isExecPhase s.phase = false from hp.1,
    show H.any (fun e => e.kind == .executionCompleted) = false from hp.2]
  simp

/-- ✗ Answering before `ExecutionCompleted` is emitted violates the block (line 4,
"`ExecutionCompleted` emitted"): the run finishes on its marked terminal place, the call answers
true, and only the next step, one tick of the clock, emits `ExecutionCompleted`. The store did
not fail, the answer simply came first. It steps as the reference and answers as the reference,
so it keeps lines 1, 2, 3 and 5. -/
@[evidence mutant ENV_016_await]
theorem ENV_016_await_mutant_lateCompleted :
    env016_but4 env016_lateCompleted (refAwait (N := Nat) (T := Nat)) ∧
      ¬ ENV_016_await env016_lateCompleted (refAwait (N := Nat) (T := Nat)) := by
  obtain ⟨h1, h2, h5⟩ := env016_ref_l125 (N := Nat) (T := Nat) env016_lateCompleted
  refine ⟨⟨h1, h2, fun C M0 r0 run H s hr hA => ?_, h5⟩, env016_lateCompleted_breaks⟩
  have hd : isExecPhase s.phase = false := by
    change true = !isExecPhase s.phase at hA
    cases hp : isExecPhase s.phase
    · rfl
    · rw [hp] at hA; exact absurd hA (by decide)
  obtain ⟨hl, -, rfl⟩ := hr
  exact env016_run_finish env016_xstep_refLike hl rfl hd

/-! ### A throwing event store, and an answer that waits for it (line 5) -/

/-- The emission of an executor whose event store throws on the termination events: the finish
step appends nothing, since the events never reach the store. Every other step emits as the
Java and TypeScript reference. -/
def env016_throwingEmit {N T : Type} [DecidableEq N] [Ord N] (C : Cfg N T) (H : List (NetEvent N T))
    (s : XSt N T) : XLbl N T → XSt N T → List (NetEvent N T)
  | .finish _, _ => []
  | l, s' => refEmitW polJT C H s l s'

/-- The reference executor over a store that throws on the termination events. -/
def env016_throwingStore {N T : Type} [DecidableEq N] [Ord N] : EvExec N T :=
  env016_exec (refBoot polJT) xstep env016_throwingEmit

/-- ✓ A failing store does not defeat the reference answer: over the store that throws on the
termination events the reference still meets the block, since it answers from the state of the
loop and never from what reached the store. `ExecutionCompleted` never comes, so nothing of it
is still to come when the call answers true. -/
@[evidence allows ENV_016_await]
theorem ENV_016_await_allows_throwingStore {N T : Type} [DecidableEq N] [Ord N] :
    ENV_016_await (env016_throwingStore (N := N) (T := T)) refAwait := by
  refine env016_await_of_refLike _ _ _ env016_xstep_refLike ?_
  intro C H s l s' ho e he
  cases l <;> simp [XLbl.outside] at ho
  all_goals (simp only [env016_throwingEmit] at he
             exact env016_refEmitW_quiet polJT C H s _ s' rfl e he)

/-- An implementation that answers true only once `ExecutionCompleted` has reached the store:
it waits for the store's acknowledgement rather than for the loop. -/
def env016_waitsForStore {N T : Type} : AwaitRel N T :=
  fun _ o b => b = match o with
    | none => true
    | some (H, s) => !isExecPhase s.phase && H.any (fun e => e.kind == .executionCompleted)

/-- The answer that waits for the store breaks the block over the throwing store: the run
finishes on its marked terminal place, `ExecutionCompleted` never reaches the store, and the call
answers false although the loop has finished. -/
theorem env016_waitsForStore_breaks :
    ¬ ENV_016_await (env016_throwingStore (N := Nat) (T := Nat)) env016_waitsForStore := by
  intro h
  obtain ⟨run, ho, hp⟩ := env016l1_of_map
    (o := env016_run xstep env016_throwingEmit env016_tc
      (refBoot polJT env016_tc env016_tm0) (xinit env016_tm0 0) [.finish .terminal])
    (p := fun run => !isExecPhase (env016_endSt (xinit env016_tm0 0) run).phase &&
      !(refBoot polJT env016_tc env016_tm0 ++ EvStep.events run).any
        (fun e => e.kind == .executionCompleted)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hA : env016_waitsForStore env016_tc
      (some (refBoot polJT env016_tc env016_tm0 ++ EvStep.events run,
        env016_endSt (xinit env016_tm0 0) run)) false := by
    change false = (!isExecPhase _ && _)
    rw [hp.1, hp.2]; rfl
  exact absurd ((h env016_tc).2.2.2.2 _ _ _ _ _ false (env016_runAt ho) hA hp.1) (by decide)

/-- An answer true of the store-waiting call is an answer true of the reference. -/
theorem env016_waits_imp {N T : Type} {C : Cfg N T} {H : List (NetEvent N T)} {s : XSt N T}
    (h : env016_waitsForStore C (some (H, s)) true) : refAwait C (some (H, s)) true := by
  change true = (!isExecPhase s.phase && _) at h
  change true = !isExecPhase s.phase
  cases hp : isExecPhase s.phase <;> simp_all

/-- ✗ Waiting for the store violates the block (line 5, "MUST NOT itself be defeated by a failure
in that bookkeeping (for example a throwing event store)"): the run finishes on its marked
terminal place, the store throws on the termination events so `ExecutionCompleted` never reaches
it, and the call answers false although the loop has finished. When it answers true the
reference answers true too, so it keeps lines 1 to 4. -/
@[evidence mutant ENV_016_await]
theorem ENV_016_await_mutant_waitsForStore :
    env016_but5 (env016_throwingStore (N := Nat) (T := Nat)) env016_waitsForStore ∧
      ¬ ENV_016_await (env016_throwingStore (N := Nat) (T := Nat)) env016_waitsForStore := by
  obtain ⟨-, -, h3, h4, -⟩ := (env016_await_iff _ _).1
    (ENV_016_await_allows_throwingStore (N := Nat) (T := Nat))
  refine ⟨⟨fun _ _ h => h, fun C M0 r0 run H s b _ h hx => ?_,
    fun C M0 r0 run H s hr hA => h3 C M0 r0 run H s hr (env016_waits_imp hA),
    fun C M0 r0 run H s hr hA => h4 C M0 r0 run H s hr (env016_waits_imp hA)⟩,
    env016_waitsForStore_breaks⟩
  change b = (!isExecPhase s.phase && _) at h
  rw [h, hx]; rfl

/-! ### Coverage: the call never returns -/

/-- An implementation whose call never returns: no answer at all. -/
def env016_hangs {N T : Type} : AwaitRel N T := fun _ _ _ => False

/-- The call returning is coverage, not a line: an implementation whose call never returns meets
every line of the block (they say nothing of a call that has no answer) and fails the coverage
conjunct `Env016AwaitCovers`: a call before the run has no answer. -/
@[evidence cites "ENV-016" "awaitTermination returns whether termination was observed within the timeout and is not defeated by a failure in the termination bookkeeping: a call that never returns meets every line of the block and fails its coverage clause Env016AwaitCovers"]
theorem env016_await_covers_hang :
    ENV_016_await (refEvExec (N := Nat) (T := Nat) polJT) env016_hangs ∧
      ¬ Env016AwaitCovers (env016_hangs (N := Nat) (T := Nat)) := by
  refine ⟨fun _ => ⟨fun _ h => h.elim, fun _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim,
    fun _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ h => h.elim⟩, fun h => ?_⟩
  obtain ⟨_, hx⟩ := h env016_c none
  exact hx

end Libpetri.Spec
