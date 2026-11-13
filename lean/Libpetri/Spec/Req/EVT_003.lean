import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Reference.EventsLink
import Libpetri.Spec.Req.EXEC_041

set_option linter.missingDocs true

/-!
# EVT-003: ExecutionCompleted Event (`spec/08-events-observability.md`)

Every run that finishes announces its end with exactly one `ExecutionCompleted` event, and after
it the run emits nothing but log messages and `ActionTimedOut` events. The event marks the end of
the loop, whatever the termination reason ([EXEC-041]); it is not a proof that every transition
completed: a terminal stop ([EXEC-042]) and an immediate termination ([ENV-015]) end the run with
firings in flight. Only a quiescent finish guarantees that nothing is in flight. Rulings D74 (a),
D38 (a) and D13 (a) split the requirement into two blocks with the same spec ID:

* `EVT_003`, for every executor, over an executor with events (`EvExec`,
  `Reference/Events.lean`). Line 1: the boot emits no `ExecutionCompleted`, a step that leaves
  the loop (from a phase of the loop to a finished phase) emits exactly one, and no other step
  emits one. Line 2: in the event trace of a run, no orchestrator
  event (anything but a log message or an `ActionTimedOut`) comes after an `ExecutionCompleted`.
  Line 3: a step that leaves the loop into the finished phase `done quiescent`, whatever it is
  labelled, happens only when no firing is in flight.
* `EVT_003_duration`, the Java and TypeScript companion (kind F) over the total duration the event
  carries: it is at least the time the run took on the executor's firing clock.

The witness of the first block is the reference executor with events `refEvExec`, under both
emission variants; the witness of the second is `refDurOf`, the firing clock's reading at the
event minus its reading when the executor was built, as Java and TypeScript measure it. The
wrong executors step as the reference (or finish quiescent too early) and emit otherwise: one
that announces the end only of a quiescent run, one that announces it each time the loop parks,
one that reports a late completion after the end, one that finishes quiescent with firings in
flight, and one that enters the quiescent end with firings in flight under a label that is not a
finish. The wrong duration is left at zero.

The worked example (`evt003_cfg`): transition `a` takes the token of place 0 and puts one into
place 9, a terminal place; transition `b` takes the token of place 1 and has an action budget
(an `Out.Timeout` node) whose outcome puts a token into place 3. With a token in place 1 only, `b`
runs, completes, and the next cycle finishes quiescent. With tokens in places 0 and 1, `a` and `b`
both start, `a` marks the terminal place, the run stops with `b` still in flight, and `b`'s budget
expires after the end.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-003, every executor: one ExecutionCompleted per finish, nothing after it -/

requirement EVT_003
  id "EVT-003"
  title "ExecutionCompleted Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "*When* the executor finishes a run ([EXEC-041]), it *shall* emit exactly one ExecutionCompleted event, whatever the termination reason."
        "The executor *shall* emit ExecutionCompleted events only when it finishes a run."
        "*If* the executor has emitted the ExecutionCompleted event of a run, *then* it *shall not* emit another event of that run other than a log message ([EVT-013]) or an ActionTimedOut event ([EVT-010])."
        "*When* the executor finishes a run with the termination reason `quiescent` ([EXEC-040]), it *shall* have no firing in flight, so every firing of the run has ended before its ExecutionCompleted event."
  reading "For every executor with events E and every configuration C:"
          "the events a run emits before its first step contain no ExecutionCompleted event, whatever the initial marking, and for every history H a step labelled l from state s to state s' that appends the events evs appends exactly one ExecutionCompleted event if it leaves the loop (s is in a phase of the loop and s' in a finished phase), whatever its label and termination reason, and none otherwise;"
          "for every initial marking M0, every initial reading r0 and every event trace tr of a run of E from M0 at r0 (the events the run emits before its first step, then the events of each step), no event of tr after an ExecutionCompleted event is an orchestrator event, that is an event other than a log message or an ActionTimedOut event;"
          "for every history H, a step labelled l from state s to state s' that appends the events evs and leaves the loop with the termination reason quiescent (s is in a phase of the loop and s' in the finished phase done quiescent), whatever its label, happens only from a state with no firing in flight."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. Trace E C M0 r0 tr says that tr is what E emits on some run from the initial state of M0. A trace is a finite prefix of a run, so line 2 holds after every step. A run finishes with a step finish c, whose cause c is the termination reason of EXEC-041 (quiescent, terminal, closed or stopped). Line 1 reads 'finishes' off the states, not off the label: a step finishes the run when it leaves the loop, from a phase of the loop (isExecPhase) to a finished phase, whatever it is labelled, so an executor that leaves its loop without a finish step still owes the event. Line 3 reads the quiescent finish the same way: a step from a phase of the loop into the finished phase done quiescent, whose cause is the termination reason the caller reads (EXEC-041, its first line), whatever it is labelled. The witness is the reference executor with events refEvExec under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python): every finish emits ExecutionCompleted last, after the snapshot of the marking, and no other step emits one. refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so lines 1 and 2 constrain what is emitted; line 3 constrains when a quiescent finish may happen."
          "Line 1 is the first two quoted sentences. An executor that announces the end only of a quiescent run, and emits nothing when a terminal place stops the run, breaks it (EVT_003_mutant_quiescentOnly); so does one that announces the end each time the loop parks to wait for an event, because a reactive net that waits has not finished (EVT_003_mutant_atPark); so does one that can leave its loop at the end of a firing pass without a finish step and so emits nothing (EVT_003_mutant_leavesWithoutFinish), the shape of TypeScript's executeLoop, which emits ExecutionCompleted after its while loop with no try/finally (typescript/src/runtime/bitmap-net-executor.ts), if a cycle threw. The reference leaves its loop only by a finish (EXEC-041, its last line), so on it the two readings agree (evt003_ref_leaves). The boot half of line 1 (no ExecutionCompleted before the first step) has no mutant of its own: an executor that announces the end at the boot breaks line 2 as well as soon as a later step emits an orchestrator event (EVT_003_mutant_bootCompleted keeps line 3 and the step half of line 1)."
          "Line 2 is the third quoted sentence. 'Another event of that run' reads the trace of one run: a second run of the same executor is a run of its own, with its own ExecutionStarted (EVT-002). An executor that reports a late completion of an abandoned firing after the end breaks it (EVT_003_mutant_lateCompletion). Log messages and ActionTimedOut events are left out on purpose (rulings D74 (a) and R7 (a) of the events design): Java and TypeScript emit ActionTimedOut from the action's own timer, off the orchestrator loop (the timeout callback that fireTransition hands ExecutorSupport.withActionTimeout in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java; the TimeoutSentinel handler in fireTransition of typescript/src/runtime/bitmap-net-executor.ts), with no check that the run is still going, so a firing a terminal stop abandoned can time out after ExecutionCompleted (EVT_003_allows_inFlightAtTerminal); an abandoned action can still log. The reference emits ActionTimedOut after the end under polJT for the same reason. Whether ActionTimedOut after the end is itself allowed is EVT-010's (ruling D65)."
          "Line 3 is the fourth quoted sentence: only a quiescent finish has nothing in flight (ruling D74 (a)). An executor that finishes quiescent while firings are still in flight breaks it (EVT_003_mutant_earlyQuiescent); so does one that enters done quiescent with firings in flight under a step that is not labelled a finish (EVT_003_mutant_relabelQuiescent), the shape of an executor that computes the termination reason from the state after its loop exits rather than from the step that ended it, as TypeScript does (executeLoop in typescript/src/runtime/bitmap-net-executor.ts sets quiescent whenever the run is neither terminal nor closed). Line 3 does not lean on EXEC-041's last line (a step that leaves the loop is a finish): reading it off the phases, it holds on its own. On the reference the two readings agree: it leaves the loop only by a finish (evt003_ref_leaves), a finish c enters done c (EXEC-041, its first line), and a quiescent finish needs Rest (evt003_line3_emitExec). The other termination reasons do not wait: a terminal stop abandons the firings in flight (EXEC-042) and an immediate termination does too (ENV-015), and the reference emits ExecutionCompleted at such a stop with a firing in flight (EVT_003_allows_inFlightAtTerminal), so a reading that waits for every transition to complete before the event would forbid the run EXEC-042 asks for. Line 3 follows from EXEC-041's line on the quiescent reason (Rest, ruling D13 (a)); here it is the event's reading: the ExecutionCompleted of a quiescent run comes after the end of every firing. AC2 (at a quiescent finish no firing is in flight; a terminal stop or an immediate termination may leave firings in flight) is line 3, EVT_003_allows_inFlightAtTerminal and EVT_003_allows_inFlightAtStop (an immediate termination finishes the run stopped with a firing still in flight, and its finish emits one ExecutionCompleted)."
          "AC1 (emitted exactly once per run that finishes, whatever the termination reason, and followed by no event of the run other than a log message or an ActionTimedOut) is lines 1 and 2 together: in every trace there is at most one ExecutionCompleted (evt003_atMostOnce, since it is itself an orchestrator event), and a run that finishes has exactly one (evt003_exactlyOnce). A run that has not finished has none: a loop that the timeout policy of a caller's run budget leaves running has not finished (EXEC-041's run budget sentence), so TypeScript, whose run() rejects under the default abandon policy while the loop goes on (run in typescript/src/runtime/bitmap-net-executor.ts), emits the event when the loop finishes, not when the caller's run ends."
          "The event carries no termination reason, and a consumer reads the reason as EXEC-041 says (the return value, the queryable reason, or a raised error). The ExecutionCompleted event is the end-of-run marker every runtime emits for every reason, not the completion signal EXEC-041 forbids to share between a quiesced and a truncated run: no line here reads the event as proof that the net quiesced. Interrupted (Java's cancellation observed in the wait) is not a cause of the model; Java emits ExecutionCompleted on that path too, after a WARN log message (the finally block of executeLoop in BitmapNetExecutor.java), which meets line 2. All runtimes emit the event once, at the end of the loop: Java in the finally block of executeLoop (BitmapNetExecutor.java, PrecompiledNetExecutor.java), TypeScript after the while loop of executeLoop (bitmap-net-executor.ts, precompiled-net-executor.ts), Rust at the end of run_sync and run_async, right after the final MarkingSnapshot (rust/libpetri-runtime/src/executor_core/executor.rs), which Python runs on."
          "The payload is not modelled in this block (ruling D38 (a)): the timestamp (the epoch clock is the CORE-011 slice) and the net name are listed in the markdown without a shall sentence; the execution ID on the event is EVT-002's third block, EVT_002_lifecycleId; the total duration is this requirement's second block, EVT_003_duration. Rust and Python events carry neither ID nor duration (rust/libpetri-event/src/net_event.rs ExecutionCompleted)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020; Java swallows a failing append of ExecutionCompleted through ExecutorSupport.swallowEventStoreFailure in executeLoop); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (run a net to quiescence, verify the last event is ExecutionCompleted, emitted once) is EVT_003_nonvacuous: a run that fires one transition and quiesces ends with ExecutionCompleted, emitted once. 'Last' holds of a quiescent run; after a terminal stop an ActionTimedOut of an abandoned firing may follow (EVT_003_allows_inFlightAtTerminal). The duration check of the test derivation is the second block's."
  signoff "2026-11-13 0a42de0e37536960 ai"
  statement : ∀ {N T : Type}, EvExec N T → Prop :=
    fun {N T} E => ∀ C,
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .executionCompleted) ∧
        ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
          kindCount .executionCompleted evs =
            if isExecPhase s.phase && !isExecPhase s'.phase then 1 else 0)) ∧
      (∀ M0 r0 tr, Trace E C M0 r0 tr →
        (after (fun e : NetEvent N T => e.kind == .executionCompleted), never
          (fun e : NetEvent N T => e.isOrch)) tr) ∧
      (∀ H l evs, on (fun s s' => E.step C H s l evs s' ∧ isExecPhase s.phase = true ∧
          s'.phase = .done .quiescent), shall (fun s _ => s.fl = []))

/- The pinned readable form of EVT-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_003 : {N T : Type} → EvExec N T → Prop :=
fun {N T} E =>
  ∀ (C : Cfg N T),
    ((∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.executionCompleted) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s l evs s', shall fun s s' =>
            kindCount NetEventKind.executionCompleted evs =
              if (isExecPhase s.phase && !isExecPhase s'.phase) = true then 1 else 0) ∧
      (∀ (M0 : QMarking N T) (r0 : ℕ) (tr : List (NetEvent N T)),
          Trace E C M0 r0 tr → (after fun e => e.kind == NetEventKind.executionCompleted, never fun e => e.isOrch) tr) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s l evs s' ∧ isExecPhase s.phase = true ∧ s'.phase = Phase.done Cause.quiescent,
            shall fun s x => s.fl = []
-/
#guard_msgs in #print EVT_003

/-! ## The three lines, one at a time -/

section Lines

variable {N T : Type}

/-- The event is an `ExecutionCompleted`. -/
def evt003_isDone (e : NetEvent N T) : Bool := e.kind == .executionCompleted

/-- The step from `s` to `s'` leaves the loop: from a phase of the loop to a finished phase. -/
def evt003_leaves (s s' : XSt N T) : Bool := isExecPhase s.phase && !isExecPhase s'.phase

/-- Line 1 of `EVT_003` alone: the boot emits no `ExecutionCompleted`; a step that leaves the
loop emits exactly one, and every other step none. -/
def evt003_line1 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .executionCompleted) ∧
    ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
      kindCount .executionCompleted evs = if evt003_leaves s s' then 1 else 0)

/-- Line 2 of `EVT_003` alone: in every event trace, no orchestrator event follows an
`ExecutionCompleted`. -/
def evt003_line2 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 tr, Trace E C M0 r0 tr →
    (after (evt003_isDone (N := N) (T := T)), never (NetEvent.isOrch (N := N) (T := T))) tr

/-- Line 3 of `EVT_003` alone: a quiescent finish happens only with no firing in flight. -/
def evt003_line3 (E : EvExec N T) : Prop :=
  ∀ C H l evs, on (fun s s' => E.step C H s l evs s' ∧ isExecPhase s.phase = true ∧
    s'.phase = .done .quiescent), shall (fun s _ => s.fl = [])

/-- `EVT_003` is its three lines. -/
theorem evt003_iff (E : EvExec N T) :
    EVT_003 E ↔ evt003_line1 E ∧ evt003_line2 E ∧ evt003_line3 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2 C⟩⟩

/-- The step half of line 1 of `EVT_003`: a step that leaves the loop emits exactly one
`ExecutionCompleted`, every other step none. -/
def evt003_line1Steps (E : EvExec N T) : Prop :=
  ∀ C H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
    kindCount .executionCompleted evs = if evt003_leaves s s' then 1 else 0)

/-- Lines 2 and 3 of `EVT_003`: what an executor that announces the end of some runs only still
meets. -/
def evt003_lines23 (E : EvExec N T) : Prop := evt003_line2 E ∧ evt003_line3 E

/-- Lines 1 and 3 of `EVT_003`: what an executor that reports late events still meets. -/
def evt003_lines13 (E : EvExec N T) : Prop := evt003_line1 E ∧ evt003_line3 E

/-- Lines 1 and 2 of `EVT_003`: what an executor that finishes quiescent too early still meets. -/
def evt003_lines12 (E : EvExec N T) : Prop := evt003_line1 E ∧ evt003_line2 E

end Lines

/-! ## The pattern of line 2 on event lists -/

section Watches

variable {σ : Type}

/-- For `after T, never B`, the memory after a piece is the memory before, or a trigger in the
piece. -/
theorem evt003_after_eq (trig bad : σ → Bool) :
    ∀ (a : Bool) (l : List σ), (afterNever trig bad).after a l = (a || l.any trig)
  | a, [] => by simp [Watch.after]
  | a, e :: l => by
    have h : (afterNever trig bad).after a (e :: l) = (afterNever trig bad).after (a || trig e) l :=
      rfl
    rw [h, evt003_after_eq trig bad _ l, List.any_cons, Bool.or_assoc]

/-- `after T, never B` has no end check: scanning a piece is checking every event of it. -/
theorem evt003_scan_eq_okAll (trig bad : σ → Bool) :
    ∀ (a : Bool) (l : List σ), (afterNever trig bad).scan a l = (afterNever trig bad).okAll a l
  | a, [] => rfl
  | a, e :: l => by simp only [Watch.scan, Watch.okAll, evt003_scan_eq_okAll trig bad _ l]

/-- With no trigger in a piece, `after T, never B` accepts it from the fresh memory. -/
theorem evt003_scan_false_of_noTrig {trig bad : σ → Bool} :
    ∀ {l : List σ}, (∀ e ∈ l, trig e = false) → (afterNever trig bad).scan false l = true
  | [], _ => rfl
  | e :: l, h => by
    simp only [Watch.scan, afterNever, Bool.false_and, Bool.not_false, Bool.true_and,
      h e (List.mem_cons_self ..), Bool.or_false]
    exact evt003_scan_false_of_noTrig fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- `after T, never B` is monotone in `B`. -/
theorem evt003_afterNever_mono {trig bad bad' : σ → Bool}
    (hb : ∀ e, bad' e = true → bad e = true) :
    ∀ (a : Bool) (l : List σ), (afterNever trig bad).scan a l = true →
      (afterNever trig bad').scan a l = true
  | _, [], _ => rfl
  | a, e :: l, h => by
    simp only [Watch.scan, afterNever, Bool.and_eq_true] at h ⊢
    refine ⟨?_, evt003_afterNever_mono hb _ l h.2⟩
    cases a <;> cases hbe : bad' e <;> simp_all

/-- `at-most-once p` counts: from the fresh memory at most one event, from the fired memory none. -/
theorem evt003_countP_of_scan {p : σ → Bool} :
    ∀ l : List σ, ((afterNever p p).scan true l = true → l.countP p = 0) ∧
      ((afterNever p p).scan false l = true → l.countP p ≤ 1)
  | [] => ⟨fun _ => rfl, fun _ => by simp⟩
  | e :: l => by
    obtain ⟨ih1, ih2⟩ := evt003_countP_of_scan (p := p) l
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [Watch.scan, afterNever, Bool.true_and, Bool.true_or, Bool.and_eq_true,
        Bool.not_eq_true'] at h
      simp [h.1, ih1 h.2]
    · simp only [Watch.scan, afterNever, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.false_or] at h
      cases hp : p e
      · rw [hp] at h; simp [hp, ih2 h]
      · rw [hp] at h; simp [hp, ih1 h]

end Watches

/-! ## Line 2 from where the loop ends -/

section LineTwo

variable {N T : Type}

/-- A finish enters a finished phase, and a step from a finished phase stays in one: the part of
[EXEC-041] (its lines 1 and 3) that line 2 rests on. -/
def evt003_FinishAbsorbs (R : XRel N T) : Prop :=
  ∀ C s l s', R C s l s' → (exec041_isFinish l = true → isExecPhase s'.phase = false) ∧
    (isExecPhase s.phase = false → isExecPhase s'.phase = false)

/-- An executor that meets EXEC-041 enters a finished phase only by a finish and never leaves it. -/
theorem evt003_absorbs_of_exec041 [DecidableEq N] {R : XRel N T} (h : EXEC_041 R) :
    evt003_FinishAbsorbs R := by
  intro C s l s' hs
  obtain ⟨h1, -, h3, -⟩ := h C
  refine ⟨fun hf => ?_, fun hd => ?_⟩
  · cases l with
    | finish c => rw [(h1 c s s' hs).2]; rfl
    | _ => simp [exec041_isFinish] at hf
  · rw [(h3 s s' ⟨hd, l, hs⟩).2]; exact hd

/-- The scan behind line 2: along a labelled run from a state that is finished whenever the memory
says an `ExecutionCompleted` was seen, line 2's pattern accepts the run's events. -/
theorem evt003_scan_run {E : EvExec N T} {C : Cfg N T} (hab : evt003_FinishAbsorbs E.erase)
    (hfin : ∀ H s l evs s', E.step C H s l evs s' → evs.any evt003_isDone = true →
      exec041_isFinish l = true)
    (hin : ∀ H s l evs s', E.step C H s l evs s' →
      (afterNever evt003_isDone NetEvent.isOrch).scan false evs = true)
    (hdone : ∀ H s l evs s', E.step C H s l evs s' → isExecPhase s.phase = false →
      ∀ e ∈ evs, e.isOrch = false) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)} (a : Bool),
      LRun E C H s run → (a = true → isExecPhase s.phase = false) →
      (afterNever evt003_isDone NetEvent.isOrch).scan a (EvStep.events run) = true
  | _, _, [], a, _, _ => by simp [EvStep.events, Watch.scan, afterNever]
  | H, s, st :: rest, a, ⟨hsrc, hst, hr⟩, ha => by
    have hev : EvStep.events (st :: rest) = st.evs ++ EvStep.events rest := by
      simp [EvStep.events]
    have herase : E.erase C st.src st.lbl st.dst := ⟨H, st.evs, hst⟩
    rw [hev, Watch.scan_append]
    have hok : (afterNever evt003_isDone NetEvent.isOrch).okAll a st.evs = true := by
      rw [← evt003_scan_eq_okAll]
      cases a with
      | false => exact hin H st.src st.lbl st.evs st.dst hst
      | true =>
        have hd : isExecPhase st.src.phase = false := by rw [hsrc]; exact ha rfl
        exact afterNever_scan_of_absent _ (hdone H st.src st.lbl st.evs st.dst hst hd)
    rw [hok, Bool.true_and]
    refine evt003_scan_run hab hfin hin hdone _ hr fun hn => ?_
    rw [evt003_after_eq] at hn
    cases a with
    | true =>
      have hd : isExecPhase st.src.phase = false := by rw [hsrc]; exact ha rfl
      exact (hab C st.src st.lbl st.dst herase).2 hd
    | false =>
      simp only [Bool.false_or] at hn
      exact (hab C st.src st.lbl st.dst herase).1 (hfin H st.src st.lbl st.evs st.dst hst hn)

/-- **Line 2 from four step facts**: an executor that enters a finished phase only by a finish and
never leaves it (EXEC-041), whose boot emits no `ExecutionCompleted`, whose steps emit one only at
a finish and no orchestrator event after it within the step, and whose steps from a finished
phase emit no orchestrator event, meets line 2. -/
theorem evt003_line2_of {E : EvExec N T} (hab : evt003_FinishAbsorbs E.erase)
    (hboot : ∀ C M0, ∀ e ∈ E.boot C M0, e.kind ≠ .executionCompleted)
    (hfin : ∀ C H s l evs s', E.step C H s l evs s' → evs.any evt003_isDone = true →
      exec041_isFinish l = true)
    (hin : ∀ C H s l evs s', E.step C H s l evs s' →
      (afterNever evt003_isDone NetEvent.isOrch).scan false evs = true)
    (hdone : ∀ C H s l evs s', E.step C H s l evs s' → isExecPhase s.phase = false →
      ∀ e ∈ evs, e.isOrch = false) :
    evt003_line2 E := by
  rintro C M0 r0 tr ⟨run, hr, rfl⟩
  have hb : ∀ e ∈ E.boot C M0, evt003_isDone e = false := fun e he => by
    simp [evt003_isDone, hboot C M0 e he]
  show (afterNever evt003_isDone NetEvent.isOrch).scan false (E.boot C M0 ++ EvStep.events run) =
    true
  rw [Watch.scan_append, ← evt003_scan_eq_okAll, evt003_scan_false_of_noTrig hb, Bool.true_and,
    evt003_after_eq, Bool.false_or, List.any_eq_false.2 (fun e he => by simp [hb e he])]
  exact evt003_scan_run hab (hfin C) (hin C) (hdone C) false hr (fun h => absurd h (by decide))

end LineTwo

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- No label but a finish makes the reference emit an `ExecutionCompleted`. -/
theorem evt003_ref_noDone (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : exec041_isFinish l = false) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .executionCompleted := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l <;> simp_all [lblKinds, exec041_isFinish]

/-- The reference emits one `ExecutionCompleted` at a finish and none elsewhere. -/
theorem evt003_ref_count (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) :
    kindCount .executionCompleted (refEmitW P C H s l s') = if exec041_isFinish l then 1 else 0 := by
  cases hf : exec041_isFinish l with
  | false =>
    simp only [Bool.false_eq_true, if_false, kindCount]
    exact List.countP_eq_zero.2 fun e he => by simp [evt003_ref_noDone P C H s hf s' e he]
  | true =>
    cases l with
    | finish c =>
      simp only [refEmitW, kindCount, if_true]
      cases P.snapshots <;> simp [NetEvent.kind]
    | _ => simp [exec041_isFinish] at hf

/-- The reference emits no orchestrator event after an `ExecutionCompleted` within one step. -/
theorem evt003_ref_inStep (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) :
    (afterNever evt003_isDone NetEvent.isOrch).scan false (refEmitW P C H s l s') = true := by
  cases hf : exec041_isFinish l with
  | false =>
    exact evt003_scan_false_of_noTrig fun e he => by
      simp [evt003_isDone, evt003_ref_noDone P C H s hf s' e he]
  | true =>
    cases l with
    | finish c =>
      simp only [refEmitW]
      cases P.snapshots <;>
        simp [Watch.scan, afterNever, evt003_isDone, NetEvent.isOrch, NetEvent.kind]
    | _ => simp [exec041_isFinish] at hf

/-- An outside step of the reference emits no orchestrator event: at most an `ActionTimedOut`. -/
theorem evt003_ref_outsideQuiet (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (ho : l.outside = true) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.isOrch = false := by
  intro e he
  have hk := refEmitW_kind P C H s l s' e he
  cases l <;> simp [XLbl.outside] at ho <;> simp_all [lblKinds, NetEvent.isOrch]

omit [Ord N] in
/-- **The reference leaves its loop exactly at a finish**: a step of `RefExec` goes from a phase
of the loop to a finished phase exactly when its label is a finish (EXEC-041, its first and last
lines, and the phases a finish starts from). -/
theorem evt003_ref_leaves {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s') :
    evt003_leaves s s' = exec041_isFinish l := by
  obtain ⟨h1, -, -, -, -, -, -, h8⟩ := EXEC_041_reference (N := N) (T := T) C
  cases hf : exec041_isFinish l with
  | true =>
    cases l with
    | finish c =>
      have hs' := (h1 c s s' h).2
      have hs : isExecPhase s.phase = true := by
        cases c with
        | quiescent => rw [(xstepW_finishQuiescent h).1]; rfl
        | terminal => exact (xstepW_finishTerminal h).1
        | closed => rw [(xstepW_finishClosed h).1]; rfl
        | stopped => rw [(xstepW_finishStopped h).1]; rfl
      unfold evt003_leaves
      rw [hs, hs']; rfl
    | _ => simp [exec041_isFinish] at hf
  | false =>
    unfold evt003_leaves
    cases he : isExecPhase s.phase with
    | false => rfl
    | true =>
      cases hd : isExecPhase s'.phase with
      | true => rfl
      | false =>
        have := h8 l s s' ⟨he, hd, h⟩
        rw [hf] at this
        cases this

omit [Ord N] in
/-- Line 1 for an executor that steps as the reference: its boot emits no `ExecutionCompleted`
and each step emits one exactly at a finish, which is where the reference leaves its loop. -/
theorem evt003_line1_emitExec {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hboot : ∀ C M0, ∀ e ∈ boot C M0, e.kind ≠ .executionCompleted)
    (hc : ∀ C H s l s', RefExec C s l s' →
      kindCount .executionCompleted (emit C H s l s') = if exec041_isFinish l then 1 else 0) :
    evt003_line1 (emitExec boot emit) :=
  fun C => ⟨hboot C, fun H l _ s s' ⟨hs, he⟩ => by
    dsimp only; rw [he, evt003_ref_leaves hs]; exact hc C H s l s' hs⟩

omit [Ord N] in
/-- Line 2 for an executor that steps as the reference: its boot emits no `ExecutionCompleted`,
each step emits one only at a finish and no orchestrator event after it, and an outside step emits
no orchestrator event. -/
theorem evt003_line2_emitExec {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hboot : ∀ C M0, ∀ e ∈ boot C M0, e.kind ≠ .executionCompleted)
    (hfin : ∀ C H s l s', RefExec C s l s' → (emit C H s l s').any evt003_isDone = true →
      exec041_isFinish l = true)
    (hin : ∀ C H s l s', RefExec C s l s' →
      (afterNever evt003_isDone NetEvent.isOrch).scan false (emit C H s l s') = true)
    (hout : ∀ C H s l s', RefExec C s l s' → l.outside = true →
      ∀ e ∈ emit C H s l s', e.isOrch = false) :
    evt003_line2 (emitExec boot emit) := by
  refine evt003_line2_of ?_ hboot ?_ ?_ ?_
  · rw [emitExec_erase]; exact evt003_absorbs_of_exec041 EXEC_041_reference
  · rintro C H s l evs s' ⟨hs, rfl⟩; exact hfin C H s l s' hs
  · rintro C H s l evs s' ⟨hs, rfl⟩; exact hin C H s l s' hs
  · rintro C H s l evs s' ⟨hs, rfl⟩ hd
    exact hout C H s l s' hs (exec041_ref_outside hs hd)

omit [Ord N] in
/-- Line 3 for every executor that steps as the reference: a step of the reference that leaves
the loop into `done quiescent` is a finish (`evt003_ref_leaves`) whose cause is quiescent
(EXEC-041, its first line), and that finish needs rest, which has nothing in flight. -/
theorem evt003_line3_emitExec (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    evt003_line3 (emitExec boot emit) := by
  rintro C H l evs s s' ⟨⟨hs, -⟩, hx, hd⟩
  have hl : exec041_isFinish l = true := by
    rw [← evt003_ref_leaves hs]; unfold evt003_leaves; rw [hx, hd]; rfl
  cases l with
  | finish c =>
    have hc := ((EXEC_041_reference (N := N) (T := T) C).1 c s s' hs).2
    rw [hd] at hc
    cases hc
    obtain ⟨-, -, hq, -⟩ := xstepW_finishQuiescent hs
    simp only [finishQ, restB, Bool.and_eq_true, List.isEmpty_iff] at hq
    exact hq.1.1.1.1.2
  | _ => simp [exec041_isFinish] at hl

/-- The reference boot emits no `ExecutionCompleted`. -/
theorem evt003_refBoot_noDone (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .executionCompleted := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- A finish is the only step of the reference whose events hold an `ExecutionCompleted`. -/
theorem evt003_ref_fin (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) (h : (refEmitW P C H s l s').any evt003_isDone = true) :
    exec041_isFinish l = true := by
  cases hf : exec041_isFinish l with
  | true => rfl
  | false =>
    obtain ⟨e, he, hd⟩ := List.any_eq_true.1 h
    exact absurd (by simpa [evt003_isDone] using hd) (evt003_ref_noDone P C H s hf s' e he)

/-- The reference meets EVT-003 under every emission variant. -/
theorem evt003_ref (P : EvPol) : EVT_003 (refEvExec (N := N) (T := T) P) :=
  (evt003_iff _).2
    ⟨evt003_line1_emitExec (evt003_refBoot_noDone P) fun C H s l s' _ => evt003_ref_count P C H s l s',
     evt003_line2_emitExec (evt003_refBoot_noDone P)
       (fun C H s l s' _ => evt003_ref_fin P C H s l s')
       (fun C H s l s' _ => evt003_ref_inStep P C H s l s')
       (fun C H s _ s' _ ho => evt003_ref_outsideQuiet P C H s ho s'),
     evt003_line3_emitExec _ _⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-003: every finish,
whatever its cause, emits the snapshot of the marking and then one `ExecutionCompleted`; no other
step emits one; after the end only an action's timer may still report an `ActionTimedOut`; and a
quiescent finish needs rest, so nothing is in flight. -/
@[evidence holds EVT_003]
theorem EVT_003_reference : EVT_003 (refEvExec (N := N) (T := T) polJT) := evt003_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-003 too: every finish
emits one `ExecutionCompleted`, and nothing at all follows it. -/
@[evidence holds EVT_003]
theorem EVT_003_rust : EVT_003 (refEvExec (N := N) (T := T) polRust) := evt003_ref polRust

end Reference

/-! ## Consequences: once per run -/

section Consequences

variable {N T : Type}

/-- In every event trace of an executor that meets EVT-003 there is at most one
`ExecutionCompleted`: it is itself an orchestrator event, so line 2 forbids a second one. -/
theorem evt003_atMostOnce {E : EvExec N T} (h : EVT_003 E) {C : Cfg N T} {M0 : QMarking N T}
    {r0 : Nat} {tr : List (NetEvent N T)} (ht : Trace E C M0 r0 tr) :
    (at-most-once (evt003_isDone (N := N) (T := T))) tr :=
  evt003_afterNever_mono (trig := evt003_isDone) (bad := NetEvent.isOrch)
    (bad' := evt003_isDone) (fun e he => by
      have hk : e.kind = .executionCompleted := by simpa [evt003_isDone] using he
      simp [NetEvent.isOrch, hk])
    false tr (((evt003_iff E).1 h).2.1 C M0 r0 tr ht)

/-- Every step of a labelled run is a step of the executor. -/
theorem evt003_lrun_mem {E : EvExec N T} {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)}, LRun E C H s run →
      ∀ st ∈ run, ∃ H', E.step C H' st.src st.lbl st.evs st.dst
  | _, _, [], _ => by simp
  | H, _, x :: rest, ⟨_, hx, hr⟩ => by
    intro st hst
    rcases List.mem_cons.1 hst with rfl | hst
    · exact ⟨H, hx⟩
    · exact evt003_lrun_mem hr st hst

/-- The events of one step of a run are counted among the run's events. -/
theorem evt003_count_le (k : NetEventKind) :
    ∀ {run : List (EvStep N T)} {st : EvStep N T}, st ∈ run →
      kindCount k st.evs ≤ kindCount k (EvStep.events run)
  | [], _, h => absurd h (List.not_mem_nil)
  | x :: rest, st, h => by
    have hev : EvStep.events (x :: rest) = x.evs ++ EvStep.events rest := by
      simp [EvStep.events]
    simp only [hev, kindCount, List.countP_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left_of_le (evt003_count_le k h)

/-- **Exactly once per finished run** (AC1): the event trace of a run of an executor that meets
EVT-003 holds exactly one `ExecutionCompleted` when the run has a step that leaves the loop. -/
theorem evt003_exactlyOnce {E : EvExec N T} (h : EVT_003 E) {C : Cfg N T} {M0 : QMarking N T}
    {r0 : Nat} {run : List (EvStep N T)} (hr : LRun E C (E.boot C M0) (xinit M0 r0) run)
    (hf : ∃ st ∈ run, evt003_leaves st.src st.dst = true) :
    kindCount .executionCompleted (E.boot C M0 ++ EvStep.events run) = 1 := by
  have hle : kindCount .executionCompleted (E.boot C M0 ++ EvStep.events run) ≤ 1 :=
    (evt003_countP_of_scan _).2 (evt003_atMostOnce h ⟨run, hr, rfl⟩)
  obtain ⟨st, hst, hfin⟩ := hf
  obtain ⟨H', hstep⟩ := evt003_lrun_mem hr st hst
  have h1 := ((evt003_iff E).1 h).1 C |>.2 H' st.lbl st.evs st.src st.dst hstep
  dsimp only at h1
  rw [hfin, if_pos rfl] at h1
  have hge := evt003_count_le .executionCompleted hst
  rw [h1] at hge
  have : kindCount .executionCompleted (E.boot C M0 ++ EvStep.events run) ≥ 1 := by
    simp only [kindCount, List.countP_append] at hge ⊢
    exact Nat.le_add_left_of_le hge
  omega

end Consequences

/-! ## The worked example -/

/-- Transition `a`: takes one token from place 0 and puts one into place 9. -/
def evt003_ta : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 9) }

/-- Transition `b`: takes one token from place 1; its action has a budget (an `Out.Timeout`
node) whose outcome puts a token into place 3. -/
def evt003_tb : Trans Nat :=
  { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.timeout (.place 3)) }

/-- The configuration of the example: places 0, 1, 3 and 9, place 9 terminal, `a` declared before
`b`, both Immediate, no environment place, every outcome accepted. -/
def evt003_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 3, 9], transitions := [evt003_ta, evt003_tb] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [9], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => true,
    res := 0 }

/-- The same net with place 0 an environment place: a reactive net that waits for events. -/
def evt003_envCfg : Cfg Nat Nat := { evt003_cfg with envs := [0] }

/-- The token 7 in place 0 and the token 8 in place 1. -/
def evt003_m01 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- The token 8 in place 1 only. -/
def evt003_m1 : QMarking Nat Nat := fun p => if p = 1 then [8] else []

/-- The terminal place 9 already marked. -/
def evt003_mT : QMarking Nat Nat := fun p => if p = 9 then [1] else []

/-- The empty marking. -/
def evt003_mE : QMarking Nat Nat := fun _ => []

/-- One cycle up to the firing pass. -/
def evt003_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- `b` starts, its action writes 4 into place 3 and returns, the completion is settled, and the
next cycle finds nothing armed, in flight or queued and finishes quiescent. -/
def evt003_quiLbls : List (XLbl Nat Nat) :=
  evt003_pre ++ [.start "b" false, .endPass, .write 0 3 4, .ret 0 true, .commit 0,
    .endCompletions, .endPublications, .endEvents, .update, .deadline [], .finish .quiescent]

/-- `a` and `b` start; `a`'s action writes 5 into the terminal place 9 and returns; its completion
is settled while `b` is still in flight. -/
def evt003_termPre : List (XLbl Nat Nat) :=
  evt003_pre ++ [.start "a" false, .start "b" false, .endPass, .write 0 9 5, .ret 0 true,
    .commit 0]

/-- The terminal place stops the run with `b` in flight; then `b`'s budget expires. -/
def evt003_termLbls : List (XLbl Nat Nat) :=
  evt003_termPre ++ [.finish .terminal, .expire 1 [(3, 4)]]

/-- The terminal place stops the run with `b` in flight; then `b`'s action returns. -/
def evt003_lateLbls : List (XLbl Nat Nat) := evt003_termPre ++ [.finish .terminal, .ret 1 true]

/-- `a` and `b` start, and the next cycle reaches the termination test with both in flight. -/
def evt003_toTest : List (XLbl Nat Nat) :=
  evt003_pre ++ [.start "a" false, .start "b" false, .endPass, .endCompletions, .endPublications,
    .endEvents, .update, .deadline []]

/-- ✓ The block is exercised by the reference: with the token 8 in place 1, `b` takes it, its
action writes 4 into place 3 and returns, and the next cycle finds nothing left to do. The run
emits `ExecutionStarted`, the snapshot, `TransitionEnabled b`, `TokenRemoved 1 8`,
`TransitionStarted b`, `TokenAdded 3 4`, `TransitionCompleted b`, the final snapshot and, last,
`ExecutionCompleted`, exactly once. -/
@[evidence nonvacuous EVT_003]
theorem EVT_003_nonvacuous :
    ∃ tr, Trace (refEvExec polJT) evt003_cfg evt003_m1 0 tr ∧
      tr = [.executionStarted, .markingSnapshot [(1, [8])], .transitionEnabled "b",
        .tokenRemoved 1 8, .transitionStarted "b" [(1, 8)], .tokenAdded 3 4,
        .transitionCompleted "b" [(3, 4)] 0, .markingSnapshot [(3, [4])], .executionCompleted] ∧
      kindCount .executionCompleted tr = 1 := by
  have h : refTrace polJT evt003_cfg evt003_m1 0 evt003_quiLbls =
      some [.executionStarted, .markingSnapshot [(1, [8])], .transitionEnabled "b",
        .tokenRemoved 1 8, .transitionStarted "b" [(1, 8)], .tokenAdded 3 4,
        .transitionCompleted "b" [(3, 4)] 0, .markingSnapshot [(3, [4])],
        .executionCompleted] := by
    decide +kernel
  exact ⟨_, refTrace_trace polJT h, rfl, by decide⟩

/-- ✓ The end of the run does not wait for every transition: with tokens in places 0 and 1, `a`
and `b` both start, `a` puts 5 into the terminal place 9, and the run stops with `b` still in
flight. The Java and TypeScript reference emits the snapshot and `ExecutionCompleted` at that
stop, and when `b`'s budget expires afterwards, an `ActionTimedOut b` from the action's timer
follows the end. Both are allowed: the reference meets EVT-003. -/
@[evidence allows EVT_003]
theorem EVT_003_allows_inFlightAtTerminal :
    EVT_003 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      ∃ tr, Trace (refEvExec polJT) evt003_cfg evt003_m01 0 tr ∧
        tr = [.executionStarted, .markingSnapshot [(0, [7]), (1, [8])], .transitionEnabled "a",
          .transitionEnabled "b", .tokenRemoved 0 7, .transitionStarted "a" [(0, 7)],
          .tokenRemoved 1 8, .transitionStarted "b" [(1, 8)], .tokenAdded 9 5,
          .transitionCompleted "a" [(9, 5)] 0, .markingSnapshot [(9, [5])], .executionCompleted,
          .actionTimedOut "b"] := by
  refine ⟨EVT_003_reference, ?_⟩
  have h : refTrace polJT evt003_cfg evt003_m01 0 evt003_termLbls =
      some [.executionStarted, .markingSnapshot [(0, [7]), (1, [8])], .transitionEnabled "a",
        .transitionEnabled "b", .tokenRemoved 0 7, .transitionStarted "a" [(0, 7)],
        .tokenRemoved 1 8, .transitionStarted "b" [(1, 8)], .tokenAdded 9 5,
        .transitionCompleted "a" [(9, 5)] 0, .markingSnapshot [(9, [5])], .executionCompleted,
        .actionTimedOut "b"] := by
    decide +kernel
  exact ⟨_, refTrace_trace polJT h, rfl⟩

/-! ## Wrong executors -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The labelled run of `emitExec boot emit` from history `H` and state `s` along the labels
`ls`, if every label is a step (`refRun` for any emission). -/
def evt003Run (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T →
    List (NetEvent N T)) (C : Cfg N T) :
    List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (xstep C s l).bind fun s' =>
      (evt003Run emit C (H ++ emit C H s l s') s' ls).map (⟨s, l, emit C H s l s', s'⟩ :: ·)

omit [Ord N] in
/-- A run `evt003Run` builds is a labelled run of `emitExec boot emit`. -/
theorem evt003Run_lrun {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      evt003Run emit C H s ls = some run → LRun (emitExec boot emit) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [evt003Run] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : evt003Run emit C (H ++ emit C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, evt003Run_lrun C hr⟩

/-! ### Announcing the end of a quiescent run only (line 1) -/

/-- Keep the reference's events at this label: every label but a finish whose cause is not
`quiescent`. -/
def evt003_keepQ : XLbl N T → Bool
  | .finish .quiescent => true
  | .finish _ => false
  | _ => true

/-- The Java and TypeScript emission, silent at a finish that is not quiescent. -/
def evt003_qOnlyEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  if evt003_keepQ l then refEmitW polJT C H s l s' else []

/-- The executor that announces the end only of a quiescent run. -/
def evt003_quiescentOnly : EvExec N T := emitExec (refBoot polJT) evt003_qOnlyEmit

/-- The executor that announces the end only of a quiescent run keeps lines 2 and 3: it emits
less than the reference, and never anything after the end but an `ActionTimedOut`. -/
theorem evt003_quiescentOnly_lines23 : evt003_lines23 (evt003_quiescentOnly (N := N) (T := T)) := by
  refine ⟨evt003_line2_emitExec (evt003_refBoot_noDone polJT) ?_ ?_ ?_, evt003_line3_emitExec _ _⟩
  · intro C H s l s' _ h
    unfold evt003_qOnlyEmit at h
    split at h
    · exact evt003_ref_fin polJT C H s l s' h
    · simp at h
  · intro C H s l s' _
    unfold evt003_qOnlyEmit
    split
    · exact evt003_ref_inStep polJT C H s l s'
    · rfl
  · intro C H s l s' _ ho e he
    unfold evt003_qOnlyEmit at he
    split at he
    · exact evt003_ref_outsideQuiet polJT C H s ho s' e he
    · simp at he

/-! ### Announcing the end each time the loop parks (line 1) -/

/-- The Java and TypeScript emission, with an `ExecutionCompleted` each time the loop parks to
wait. -/
def evt003_parkEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  refEmitW polJT C H s l s' ++
    match l with
    | .park _ => [.executionCompleted]
    | _ => []

/-- The executor that announces the end of the run each time its loop parks to wait. -/
def evt003_atPark : EvExec N T := emitExec (refBoot polJT) evt003_parkEmit

/-! ### Reporting a late completion after the end (line 2) -/

/-- A late completion: when the action of a firing returns after the run has finished, a
`TransitionCompleted` naming its transition, with no produced token. -/
def evt003_late (s : XSt N T) (l : XLbl N T) : List (NetEvent N T) :=
  match l with
  | .ret i _ =>
    if isExecPhase s.phase then []
    else
      match s.fl.find? (·.id == i) with
      | some f => [.transitionCompleted f.t.core.name [] (s.now - f.start)]
      | none => []
  | _ => []

omit [DecidableEq N] [Ord N] in
/-- A late completion is a `TransitionCompleted`. -/
theorem evt003_late_kind (s : XSt N T) (l : XLbl N T) :
    ∀ e ∈ evt003_late s l, e.kind = .transitionCompleted := by
  intro e he
  unfold evt003_late at he
  split at he
  · split at he
    · cases he
    · split at he
      · simp only [List.mem_singleton] at he; subst he; rfl
      · cases he
  · cases he

/-- The Java and TypeScript emission, with a late completion when an abandoned action returns
after the end. -/
def evt003_lateEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  refEmitW polJT C H s l s' ++ evt003_late s l

/-- The executor that reports the late completion of a firing it abandoned at the end. -/
def evt003_lateCompletion : EvExec N T := emitExec (refBoot polJT) evt003_lateEmit

/-- The executor that reports late completions keeps lines 1 and 3: a late completion is not an
`ExecutionCompleted`, and it steps as the reference. -/
theorem evt003_lateCompletion_lines13 :
    evt003_lines13 (evt003_lateCompletion (N := N) (T := T)) := by
  refine ⟨evt003_line1_emitExec (evt003_refBoot_noDone polJT) fun C H s l s' _ => ?_,
    evt003_line3_emitExec _ _⟩
  have h0 : kindCount .executionCompleted (evt003_late s l) = 0 :=
    List.countP_eq_zero.2 fun e he => by simp [evt003_late_kind s l e he]
  simp only [kindCount] at h0 ⊢
  rw [evt003_lateEmit, List.countP_append, h0, Nat.add_zero]
  exact evt003_ref_count polJT C H s l s'

/-! ### Finishing quiescent with firings in flight (line 3) -/

/-- A step of the reference, or a quiescent finish at the termination test as soon as nothing is
queued, without waiting for the firings in flight. -/
def evt003_earlyQStep (C : Cfg N T) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : Prop :=
  xstep C s l = some s' ∨
    (l = .finish .quiescent ∧ s.phase = .test ∧ s.cq = [] ∧ s.pq = [] ∧ s.eq = [] ∧
      s' = { s with phase := .done .quiescent, eq := [] })

/-- The executor that finishes quiescent while firings are still in flight, and emits as the
Java and TypeScript reference. -/
def evt003_earlyQuiescent : EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' => evt003_earlyQStep C s l s' ∧ evs = refEmitW polJT C H s l s'

/-- The executor that finishes quiescent too early keeps lines 1 and 2: its extra finish emits the
end once, and enters a finished phase it never leaves. -/
theorem evt003_earlyQuiescent_lines12 :
    evt003_lines12 (evt003_earlyQuiescent (N := N) (T := T)) := by
  refine ⟨fun C => ⟨evt003_refBoot_noDone polJT C, fun H l _ s s' ⟨hs, he⟩ => ?_⟩,
    evt003_line2_of ?_ (evt003_refBoot_noDone polJT) ?_ ?_ ?_⟩
  · dsimp only; rw [he, evt003_ref_count polJT C H s l s']
    rcases hs with h | ⟨rfl, hph, -, -, -, rfl⟩
    · rw [evt003_ref_leaves h]
    · simp [evt003_leaves, hph, isExecPhase, exec041_isFinish]
  · rintro C s l s' ⟨H, evs, h | ⟨rfl, -, -, -, -, rfl⟩, -⟩
    · exact evt003_absorbs_of_exec041 EXEC_041_reference C s l s' h
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rintro C H s l evs s' ⟨-, rfl⟩ h
    exact evt003_ref_fin polJT C H s l s' h
  · rintro C H s l evs s' ⟨-, rfl⟩
    exact evt003_ref_inStep polJT C H s l s'
  · rintro C H s l evs s' ⟨h | ⟨rfl, hph, -⟩, rfl⟩ hd
    · exact evt003_ref_outsideQuiet polJT C H s (exec041_ref_outside h hd) s'
    · rw [hph] at hd; exact absurd hd (by decide)

/-! ### Leaving the loop without a finish step (line 1) -/

/-- A step of the reference, or leaving the loop at the end of the firing pass: entering the
finished phase `done stopped` under the label `endPass`, which is not a finish. -/
def evt003_silentEndStep (C : Cfg N T) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : Prop :=
  xstep C s l = some s' ∨ (l = .endPass ∧ s.phase = .pass ∧ s' = { s with phase := .done .stopped })

/-- The executor whose loop can end at the end of a firing pass without a finish step, and so
without an `ExecutionCompleted`; it emits as the Java and TypeScript reference. -/
def evt003_leavesWithoutFinish : EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' => evt003_silentEndStep C s l s' ∧ evs = refEmitW polJT C H s l s'

/-- The executor that leaves its loop without a finish step keeps lines 2 and 3: it emits what the
reference emits, and its silent end is entered from a phase of the loop and never left. -/
theorem evt003_leavesWithoutFinish_lines23 :
    evt003_lines23 (evt003_leavesWithoutFinish (N := N) (T := T)) := by
  refine ⟨evt003_line2_of ?_ (evt003_refBoot_noDone polJT) ?_ ?_ ?_, ?_⟩
  · rintro C s l s' ⟨H, evs, h | ⟨rfl, hph, rfl⟩, -⟩
    · exact evt003_absorbs_of_exec041 EXEC_041_reference C s l s' h
    · refine ⟨fun _ => rfl, fun hd => ?_⟩
      rw [hph] at hd; exact absurd hd (by decide)
  · rintro C H s l evs s' ⟨-, rfl⟩ h
    exact evt003_ref_fin polJT C H s l s' h
  · rintro C H s l evs s' ⟨-, rfl⟩
    exact evt003_ref_inStep polJT C H s l s'
  · rintro C H s l evs s' ⟨h | ⟨rfl, hph, -⟩, rfl⟩ hd
    · exact evt003_ref_outsideQuiet polJT C H s (exec041_ref_outside h hd) s'
    · rw [hph] at hd; exact absurd hd (by decide)
  · rintro C H l evs s s' ⟨⟨h | ⟨-, -, rfl⟩, he⟩, hx, hd⟩
    · exact evt003_line3_emitExec (refBoot polJT) (refEmitW polJT) C H l evs s s' ⟨⟨h, he⟩, hx, hd⟩
    · simp at hd

/-! ### Announcing the end at the boot (line 1, boot half) -/

/-- The executor that also emits `ExecutionCompleted` at the boot, after the Java and TypeScript
boot events, and otherwise steps and emits as the reference. -/
def evt003_bootCompleted : EvExec N T :=
  emitExec (fun C M0 => refBoot polJT C M0 ++ [.executionCompleted]) (refEmitW polJT)

/-- The step half of line 1 of `EVT_003` and its line 3: what an executor that announces the end
at the boot still meets. -/
def evt003_steps1and3 (E : EvExec N T) : Prop := evt003_line1Steps E ∧ evt003_line3 E

/-- The executor that announces the end at the boot keeps line 3 and the step half of line 1: its
steps are the reference's. -/
theorem evt003_bootCompleted_keeps :
    evt003_steps1and3 (evt003_bootCompleted (N := N) (T := T)) :=
  ⟨fun C H l _ s s' ⟨hs, he⟩ => by
    dsimp only; rw [he, evt003_ref_leaves hs]; exact evt003_ref_count polJT C H s l s',
   evt003_line3_emitExec _ _⟩

/-! ### Entering `done quiescent` under another label (line 3) -/

/-- The executor that ends the run in the finished phase `done quiescent` at the termination test
as soon as nothing is queued, without waiting for the firings in flight, under the label
`endPass`, which is not a finish, and emits there what the reference emits at a quiescent finish;
every other step is the reference's. It is the shape of an executor that computes the
termination reason from the state after its loop exits rather than from the step that ended
it. -/
def evt003_relabelQuiescent : EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' =>
    (xstep C s l = some s' ∧ evs = refEmitW polJT C H s l s') ∨
    (l = .endPass ∧ s.phase = .test ∧ s.cq = [] ∧ s.pq = [] ∧ s.eq = [] ∧
      s' = { s with phase := .done .quiescent, eq := [] } ∧
      evs = refEmitW polJT C H s (.finish .quiescent) s')

/-- Every labelled run of the relabelling executor emits what a labelled run of the executor that
finishes quiescent too early emits: its relabelled step is that executor's early finish. -/
theorem evt003_relabel_into {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun evt003_relabelQuiescent C H s run →
        ∃ run', LRun evt003_earlyQuiescent C H s run' ∧ EvStep.events run' = EvStep.events run
  | _, _, [], _ => ⟨[], trivial, rfl⟩
  | H, s, st :: rest, ⟨hsrc, hst, hr⟩ => by
    obtain ⟨run', hr', he⟩ := evt003_relabel_into hr
    rcases hst with ⟨h, hev⟩ | ⟨-, hph, hcq, hpq, heq, hs', hev⟩
    · refine ⟨st :: run', ⟨hsrc, ⟨Or.inl h, hev⟩, hr'⟩, ?_⟩
      simp [EvStep.events] at he ⊢; exact he
    · refine ⟨⟨st.src, .finish .quiescent, st.evs, st.dst⟩ :: run',
        ⟨hsrc, ⟨Or.inr ⟨rfl, hph, hcq, hpq, heq, hs'⟩, hev⟩, hr'⟩, ?_⟩
      simp [EvStep.events] at he ⊢; exact he

/-- The relabelling executor keeps lines 1 and 2: its relabelled step leaves the loop and emits
the end once, and its runs emit what runs of the executor that finishes quiescent too early
emit. -/
theorem evt003_relabelQuiescent_lines12 :
    evt003_lines12 (evt003_relabelQuiescent (N := N) (T := T)) := by
  refine ⟨fun C => ⟨evt003_refBoot_noDone polJT C, fun H l evs s s' hs => ?_⟩, ?_⟩
  · rcases hs with ⟨h, he⟩ | ⟨-, hph, -, -, -, rfl, he⟩
    · rw [he, evt003_ref_count polJT C H s l s', evt003_ref_leaves h]
    · rw [he, evt003_ref_count polJT C H s _ _]
      simp [evt003_leaves, hph, isExecPhase, exec041_isFinish]
  · rintro C M0 r0 tr ⟨run, hr, rfl⟩
    obtain ⟨run', hr', he⟩ := evt003_relabel_into hr
    have := evt003_earlyQuiescent_lines12.2 C M0 r0 _ ⟨run', hr', rfl⟩
    rw [he] at this
    exact this

end Mutants

/-- ✗ Announcing the end only of a quiescent run violates EVT-003 (line 1): a net started with its
terminal place 9 already marked stops at once, terminal, and the executor emits no
`ExecutionCompleted` for that run. It emits less than the reference, so it keeps lines 2 and 3. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_quiescentOnly :
    evt003_lines23 (evt003_quiescentOnly (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_quiescentOnly (N := Nat) (T := Nat)) := by
  refine ⟨evt003_quiescentOnly_lines23, fun h => ?_⟩
  obtain ⟨s', hs⟩ : ∃ s', xstep evt003_cfg (xinit evt003_mT 0) (.finish .terminal) = some s' :=
    Option.isSome_iff_exists.1 (by decide +kernel)
  have h1 := (h evt003_cfg).1.2 [] (.finish .terminal) _ _ _ ⟨hs, rfl⟩
  obtain ⟨hph, -, rfl⟩ := xstepW_finishTerminal hs
  simp only [evt003_qOnlyEmit, evt003_keepQ, kindCount, hph] at h1
  simp [isExecPhase] at h1

/-- ✗ Announcing the end each time the loop parks violates EVT-003 (line 1): with place 0 an
environment place and no token anywhere, the first cycle finds nothing to start and the loop
parks to wait for an event; the run has not finished, yet the executor emits
`ExecutionCompleted`. It steps as the reference, so it keeps line 3. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_atPark :
    evt003_line3 (evt003_atPark (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_atPark (N := Nat) (T := Nat)) := by
  refine ⟨evt003_line3_emitExec _ _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := evt003_envCfg)
    (o := xrun evt003_envCfg (xinit evt003_mE 0) (evt003_pre ++ [.endPass])) (l := .park none)
    (p := fun _ _ => true) (by decide +kernel)
  have h1 := (h evt003_envCfg).1.2 [] (.park none) _ s s' ⟨hs, rfl⟩
  have h0 := evt003_ref_count polJT evt003_envCfg [] s (.park none) s'
  simp only [evt003_parkEmit, kindCount, List.countP_append] at h1 h0
  rw [h0] at h1
  have hl := evt003_ref_leaves (C := evt003_envCfg) hs
  simp [exec041_isFinish, NetEvent.kind] at h1
  simp [evt003_leaves, exec041_isFinish, h1.1, h1.2] at hl

/-- ✗ Reporting a late completion after the end violates EVT-003 (line 2): with tokens in places
0 and 1, `a` puts 5 into the terminal place 9 and the run stops with `b` in flight; when `b`'s
action returns afterwards, the executor emits `TransitionCompleted b` after `ExecutionCompleted`.
A late completion is not an `ExecutionCompleted` and the executor steps as the reference, so it
keeps lines 1 and 3. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_lateCompletion :
    evt003_lines13 (evt003_lateCompletion (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_lateCompletion (N := Nat) (T := Nat)) := by
  refine ⟨evt003_lateCompletion_lines13, fun h => ?_⟩
  have hc : (evt003Run evt003_lateEmit evt003_cfg (refBoot polJT evt003_cfg evt003_m01)
      (xinit evt003_m01 0) evt003_lateLbls).map (fun run =>
        decide ((after (fun e : NetEvent Nat Nat => e.kind == .executionCompleted), never
          (fun e : NetEvent Nat Nat => e.isOrch))
          (refBoot polJT evt003_cfg evt003_m01 ++ EvStep.events run))) = some false := by
    decide +kernel
  cases hr : evt003Run evt003_lateEmit evt003_cfg (refBoot polJT evt003_cfg evt003_m01)
      (xinit evt003_m01 0) evt003_lateLbls with
  | none => simp [hr] at hc
  | some run =>
    simp only [hr, Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at hc
    exact hc ((h evt003_cfg).2.1 evt003_m01 0 _ ⟨run, evt003Run_lrun evt003_cfg hr, rfl⟩)

/-- ✗ Finishing quiescent while firings are in flight violates EVT-003 (line 3): with tokens in
places 0 and 1, `a` and `b` both start, and at the next termination test nothing is queued, so the
executor finishes quiescent with both firings still in flight. Its extra finish emits the end
once and is never left, so it keeps lines 1 and 2. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_earlyQuiescent :
    evt003_lines12 (evt003_earlyQuiescent (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_earlyQuiescent (N := Nat) (T := Nat)) := by
  refine ⟨evt003_earlyQuiescent_lines12, fun h => ?_⟩
  have hc : (xrun evt003_cfg (xinit evt003_m01 0) evt003_toTest).map (fun s =>
      decide (s.phase = .test) && s.cq.isEmpty && s.pq.isEmpty && s.eq.isEmpty &&
        !s.fl.isEmpty) = some true := by
    decide +kernel
  cases hr : xrun evt003_cfg (xinit evt003_m01 0) evt003_toTest with
  | none => simp [hr] at hc
  | some s =>
    simp only [hr, Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq,
      List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨⟨hph, hcq⟩, hpq⟩, heq⟩, hfl⟩ := hc
    have := (h evt003_cfg).2.2 [] (.finish .quiescent) _ s
      { s with phase := .done .quiescent, eq := [] }
      ⟨⟨Or.inr ⟨rfl, hph, hcq, hpq, heq, rfl⟩, rfl⟩, by rw [hph]; rfl, rfl⟩
    exact hfl this

/-- ✗ Entering `done quiescent` with firings in flight under a label that is not a finish
violates EVT-003 (line 3): with tokens in places 0 and 1, `a` and `b` both start, and at the next
termination test nothing is queued, so the executor's `endPass` step enters `done quiescent`,
the termination reason the caller reads (EXEC-041), with both firings still in flight. Line 3
reads the quiescent finish off the phases, as line 1 reads every finish, so the label does not
hide it. The step leaves the loop and emits the end once, and the runs emit what those of the
executor that finishes quiescent too early emit, so it keeps lines 1 and 2. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_relabelQuiescent :
    evt003_lines12 (evt003_relabelQuiescent (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_relabelQuiescent (N := Nat) (T := Nat)) := by
  refine ⟨evt003_relabelQuiescent_lines12, fun h => ?_⟩
  have hc : (xrun evt003_cfg (xinit evt003_m01 0) evt003_toTest).map (fun s =>
      decide (s.phase = .test) && s.cq.isEmpty && s.pq.isEmpty && s.eq.isEmpty &&
        !s.fl.isEmpty) = some true := by
    decide +kernel
  cases hr : xrun evt003_cfg (xinit evt003_m01 0) evt003_toTest with
  | none => simp [hr] at hc
  | some s =>
    simp only [hr, Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq,
      List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨⟨hph, hcq⟩, hpq⟩, heq⟩, hfl⟩ := hc
    have := (h evt003_cfg).2.2 [] .endPass _ s { s with phase := .done .quiescent, eq := [] }
      ⟨Or.inr ⟨rfl, hph, hcq, hpq, heq, rfl, rfl⟩, by rw [hph]; rfl, rfl⟩
    exact hfl this

/-- ✗ Leaving the loop without a finish step violates EVT-003 (line 1): with the token 8 in
place 1, `b` starts, and at the end of that firing pass the executor enters a finished phase
under the label `endPass`, which emits nothing, so the run ends without an `ExecutionCompleted`.
This is the shape of a loop that throws out of a cycle before its end-of-run code. It emits what
the reference emits and its silent end is never left, so it keeps lines 2 and 3. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_leavesWithoutFinish :
    evt003_lines23 (evt003_leavesWithoutFinish (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_leavesWithoutFinish (N := Nat) (T := Nat)) := by
  refine ⟨evt003_leavesWithoutFinish_lines23, fun h => ?_⟩
  obtain ⟨s, hs, hph⟩ : ∃ s, xrun evt003_cfg (xinit evt003_m1 0)
      (evt003_pre ++ [.start "b" false]) = some s ∧ s.phase = .pass := by
    cases ho : xrun evt003_cfg (xinit evt003_m1 0) (evt003_pre ++ [.start "b" false]) with
    | none => exact absurd ho (by decide +kernel)
    | some s =>
      refine ⟨s, rfl, ?_⟩
      have : (xrun evt003_cfg (xinit evt003_m1 0) (evt003_pre ++ [.start "b" false])).map
          (fun s => decide (s.phase = .pass)) = some true := by decide +kernel
      rw [ho] at this
      simpa using this
  have h1 := (h evt003_cfg).1.2 [] .endPass _ s { s with phase := .done .stopped }
    ⟨Or.inr ⟨rfl, hph, rfl⟩, rfl⟩
  have h0 : kindCount .executionCompleted
      (refEmitW polJT evt003_cfg [] s .endPass { s with phase := .done .stopped }) = 0 :=
    evt003_ref_count polJT evt003_cfg [] s .endPass _
  rw [h0] at h1
  simp [hph, isExecPhase] at h1

/-- ✗ Announcing the end at the boot violates EVT-003 (line 1): with the token 8 in place 1, the
run emits `ExecutionCompleted` before its first step. Its steps are the reference's, so it keeps
line 3 and the step half of line 1; it breaks line 2 too, since the run's later events follow
that `ExecutionCompleted`, so the boot half of line 1 has no mutant that keeps every other
line. -/
@[evidence mutant EVT_003]
theorem EVT_003_mutant_bootCompleted :
    evt003_steps1and3 (evt003_bootCompleted (N := Nat) (T := Nat)) ∧
      ¬ EVT_003 (evt003_bootCompleted (N := Nat) (T := Nat)) := by
  refine ⟨evt003_bootCompleted_keeps, fun h => ?_⟩
  exact (h evt003_cfg).1.1 evt003_m1 .executionCompleted (by simp [evt003_bootCompleted, emitExec])
    rfl

/-- ✓ An immediate termination ends the run with a firing still in flight: with the token 8 in
place 1, `b` starts, the caller terminates the executor at once, and the run finishes stopped
while `b`'s action is still running. That finish emits one `ExecutionCompleted`, which the block
allows. -/
@[evidence allows EVT_003]
theorem EVT_003_allows_inFlightAtStop :
    EVT_003 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      ∃ s s' evs, (refEvExec (N := Nat) (T := Nat) polJT).step evt003_cfg [] s
        (.finish .stopped) evs s' ∧ s.fl ≠ [] ∧ kindCount .executionCompleted evs = 1 := by
  refine ⟨EVT_003_reference, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt003_cfg)
    (o := xrun evt003_cfg (xinit evt003_m1 0)
      (evt003_pre ++ [.start "b" false, .endPass, .terminateNow]))
    (l := .finish .stopped) (p := fun s _ => !s.fl.isEmpty) (by decide +kernel)
  refine ⟨s, s', _, ⟨hs, rfl⟩, ?_, ?_⟩
  · simpa using hp
  · rw [evt003_ref_count polJT evt003_cfg [] s _ s']; rfl

/-! ## EVT-003, the total duration (Java and TypeScript) -/

/-- **The reference total duration**: the firing clock's reading `e` when the run emits
`ExecutionCompleted`, minus its reading `b` when the executor was built, whatever it read (`_r`)
when the run started, as Java (`clockNanos() - startNanos`, `startNanos` taken in the
constructor) and TypeScript (`nowMs() - startMs`, `startMs` taken in the constructor) measure it. -/
def refDurOf (b _r e : Nat) : Nat := e - b

/- The reference total duration is the witness model of the duration block. -/
#spec_witness refDurOf

requirement EVT_003_duration
  id "EVT-003"
  title "ExecutionCompleted Event (total duration)"
  kind F
  scope "Java and TypeScript executors (the ExecutionCompleted event of Rust and Python carries no duration)"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the ExecutionCompleted event carries a total duration (Java and TypeScript), the total duration *shall* be at least the time the run took on the executor's firing clock ([TIME-015]), from the reading at its ExecutionStarted event to the reading at its ExecutionCompleted event."
  reading "For every duration assignment dur, where dur b r e is the total duration the ExecutionCompleted event of a run carries when the executor's firing clock read b when the executor was built, r when the run emitted its ExecutionStarted event and e when it emits its ExecutionCompleted event: for all readings with b ≤ r ≤ e, the duration is at least e - r."
  assumes "This is the second block of EVT-003 and the Java and TypeScript companion of ruling D38 (a), which states durations as bounds: the event model of the first block (NetEvent in Spec/GlossaryEvents.lean) carries no duration and the executor state no start reading, so this block states the duration over what a host observes, three readings of the executor's firing clock and the duration on the event, and needs no new field. The firing clock is the executor's injected clock of TIME-015 (the system's monotonic clock by default), so its readings never decrease: b ≤ r ≤ e. The epoch clock that stamps events (CORE-011) is not read."
          "Java and TypeScript measure the duration from the construction of the executor, not from the start of the run: Java as clockNanos() - startNanos with startNanos taken in the constructor (the constructor and elapsedDuration in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java), TypeScript as nowMs() - startMs with startMs taken in the constructor (the constructor and executeLoop in typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts). The witness refDurOf is that difference, e - b. It meets the line because b ≤ r. For the first run of a fresh executor it is the run's own time plus the time between construction and run(); for a later run of the same executor it also counts the earlier runs and the time between them. The line is a bound, so both are allowed (EVT_003_duration_nonvacuous)."
          "The line is the quoted sentence and AC3 (where the event carries a total duration, it is at least the time the run took on the executor's firing clock). An executor that leaves the duration at zero breaks it on every run during which the clock advances (EVT_003_duration_forbids_zero). The test derivation checks the bound with a firing clock that advances during the run; under an injected clock that does not move, the duration may be 0 and still meet the line."
          "The model is a restriction: the duration is a function of the three readings only, so a duration that depends on anything else (the number of firings, a second clock) cannot be written as an assignment. Rust and Python are out of scope: their ExecutionCompleted event has no duration field (rust/libpetri-event/src/net_event.rs ExecutionCompleted carries the net name and timestamp only). When the event is emitted is the first block's; the shared assumptions of the executor event blocks (store enabled, events are values) apply."
  signoff "2026-11-13 7dad8ab40c4313d6 ai"
  statement : (Nat → Nat → Nat → Nat) → Prop :=
    fun dur => ∀ b r e, b ≤ r → r ≤ e → e - r ≤ dur b r e

/- The pinned readable form of the duration block. -/
/--
info: def Libpetri.Spec.EVT_003_duration : (ℕ → ℕ → ℕ → ℕ) → Prop :=
fun dur => ∀ (b r e : ℕ), b ≤ r → r ≤ e → e - r ≤ dur b r e
-/
#guard_msgs in #print EVT_003_duration

/-- ✓ The reference total duration meets the block: measured from the construction of the
executor, it is never less than the time since the run started. -/
@[evidence holds EVT_003_duration]
theorem EVT_003_duration_reference : EVT_003_duration refDurOf := by
  intro b r e hbr _
  simp only [refDurOf]
  omega

/-- ✓ The block is exercised by the reference: an executor built at reading 0 whose first run goes
from 0 to 5 reports 5; its second run, from 10 to 15, reports 15, more than its own 5, which the
bound allows. -/
@[evidence nonvacuous EVT_003_duration]
theorem EVT_003_duration_nonvacuous :
    refDurOf 0 0 5 = 5 ∧ refDurOf 0 10 15 = 15 ∧ 15 - 10 ≤ refDurOf 0 10 15 := by
  decide

/-- The duration left at zero. -/
def evt003_durZero (_b _r _e : Nat) : Nat := 0

/-- ✗ Leaving the duration at zero violates the block: a run from reading 0 to reading 5 reports
0, less than the 5 it took. -/
@[evidence forbids EVT_003_duration]
theorem EVT_003_duration_forbids_zero : ¬ EVT_003_duration evt003_durZero := by
  intro h
  exact absurd (h 0 0 5 (le_refl _) (by decide)) (by decide)

end Libpetri.Spec

