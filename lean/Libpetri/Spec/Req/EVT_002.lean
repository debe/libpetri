import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events

set_option linter.missingDocs true

/-!
# EVT-002: ExecutionStarted Event (`spec/08-events-observability.md`)

Every run announces itself with exactly one `ExecutionStarted` event, and nothing but log
messages comes before it. Ruling D98 (a) splits the requirement into three blocks with the same
spec ID:

* `EVT_002`, for every executor, over the event trace of a run (`Trace`,
  `Reference/Events.lean`: the boot events, then the events of each step). Line 1: the trace
  holds an `ExecutionStarted`. Line 2: it holds at most one. Line 3: every event before it is a
  log message.
* `EVT_002_executionId`, a pure-function line (kind F) over the execution ID an executor draws
  when it is constructed: two executors constructed in one process carry different IDs, whatever
  the clock reads. This is the MUST half of [TIME-015] AC14, which no other block states.
* `EVT_002_lifecycleId`, the Java and TypeScript companion (kind F) over the IDs the lifecycle
  events carry: the `ExecutionStarted` and the `ExecutionCompleted` of every run of an executor
  carry that executor's ID.

The witness of the first block is the reference executor with events `refEvExec`, under both
emission variants; the witness of the second is `refExecutionId`, the hex-formatted construction
counter that Java, TypeScript and Rust draw from; the witness of the third is
`refLifecycleIds`, both events built from the executor's own ID. The wrong executors step as the
reference and emit otherwise: one whose boot announces nothing, one that announces the run again
after every wait, and one that publishes the initial marking before announcing the run. The
wrong ID assignment takes the ID from the clock reading. The wrong lifecycle IDs draw a fresh ID
for `ExecutionStarted`, or put the ν execution scope on `ExecutionCompleted`.

The worked example (`evt002_cfg`): transition `t` takes a token from place 0, an environment
place. With the token 7 in place 0, a run emits `ExecutionStarted`, the snapshot, then
`TransitionEnabled t`, `TokenRemoved 0 7` and `TransitionStarted t`. With place 0 empty, the
first cycle finds nothing to start and the loop waits for an event.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-002, every executor: one ExecutionStarted per run, only logs before it -/

requirement EVT_002
  id "EVT-002"
  title "ExecutionStarted Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "*When* a run starts, the executor *shall* emit an ExecutionStarted event before its first cycle ([EXEC-001]) and before any event of the run other than a log message ([EVT-013])."
        "The executor *shall* emit at most one ExecutionStarted event per run."
  reading "For every executor with events E, every configuration C, every initial marking M0, every initial reading r0 and every event trace tr of a run of E from M0 at r0 (the events the run emits before its first step, then the events of each step):"
          "tr contains an ExecutionStarted event;"
          "tr contains at most one ExecutionStarted event;"
          "every event of tr before its first ExecutionStarted event is a log message."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step (its boot) and a step relation that says which events each step appends. Trace E C M0 r0 tr says that tr is what E emits on some run from the initial state of M0: the boot events, then the events of each step, in order. A trace is a finite prefix of a run and the empty run is a run, so every line holds after every step, and the boot events alone are a trace. The first cycle of the run (EXEC-001) begins with its first step, so 'before its first cycle' in the first quoted sentence reads as 'among the boot events': an executor that emits ExecutionStarted only inside its first step breaks line 1 on the boot-only trace, even when that step emits nothing else. The witness is the reference executor with events refEvExec, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python): its boot is ExecutionStarted, then the snapshot of the initial marking, and no step emits an ExecutionStarted. refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else."
          "Line 1 and line 3 are the first quoted sentence: the run announces itself, and no event other than a log message comes first. An executor that announces nothing at all breaks line 1 and keeps lines 2 and 3 (EVT_002_mutant_silent); one that publishes the snapshot of the initial marking before ExecutionStarted breaks line 3 (EVT_002_mutant_snapshotFirst). Line 2 is the second quoted sentence: an executor that announces the run again each time it wakes from a wait breaks it (EVT_002_mutant_wakeAgain). AC1 (emitted exactly once per execution run, before any transitions fire) is lines 1 and 2 (exactly once) and line 3 (TransitionStarted is not a log message, so it comes after)."
          "A run is one call that runs the executor: a second run of the same executor is a run of its own, with its own boot and its own ExecutionStarted, and the lines read each run's trace from its boot. Java and TypeScript emit ExecutionStarted first in their run loop (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java, at the top of the try block of executeLoop; typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts, executeLoop), Rust at the top of run_sync and of the asynchronous run (rust/libpetri-runtime/src/executor_core/executor.rs, run_sync and run_async), which Python runs on. No runtime emits it anywhere else."
          "Log messages before ExecutionStarted are allowed, and where they fall is not fixed (ruling D20; design note SC-3): Java and TypeScript report unknown initial places and dead arcs at construction, before the run (warnUnknownInitialPlaces and warnDeadArcs in BitmapNetExecutor.Builder.build; warnUnknownPlace and findDeadArcs in the bitmap-net-executor.ts constructor); Rust reports dead arcs at construction (warn_dead_arcs) and the unknown initial places right after ExecutionStarted and the snapshot of the initial marking (warn_unknown_places after emit_marking_snapshot in run_sync and run_async, executor_core/executor.rs). An executor whose boot puts a construction diagnostic first meets the block (EVT_002_allows_diagnosticsFirst). The reference emits no diagnostic yet (Reference/Events.lean)."
          "The payload is not modelled (ruling D38 (a)): the timestamp (the epoch clock is the CORE-011 slice) and the net name, which every runtime's event carries (the net of the model has no name), are listed in the markdown without a shall sentence, so no block states them. The execution ID: Java and TypeScript events carry it and Rust and Python events do not (the execution_id field of Executor, executor_core/executor.rs: the ID exists, kept off the events so as not to change the session archive format, EVT-025). Distinctness of the ID (AC2) is the second block of EVT-002, EVT_002_executionId; the ID on the ExecutionStarted and ExecutionCompleted events (the sentence on the lifecycle events) is the third, EVT_002_lifecycleId. The event model of this block (NetEvent in Spec/GlossaryEvents.lean) carries no ID, so an executor that puts a wrong ID on its events meets this block and breaks the third."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020, cited by the markdown sentence that a run's events reach the event store only while the store is enabled; Java's PrecompiledNetExecutor and Rust emit only when the store is enabled, so a run with a noop store that emits nothing is no breach); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (run the net, verify the first event other than a log message is ExecutionStarted with the correct net name) is EVT_002_nonvacuous without the net name: a run that enables and starts a transition emits ExecutionStarted first, exactly once, and the TransitionStarted after it. The net-name check is a runtime test only, for the payload reason above."
  signoff "2026-11-13 402b10defa18579f ai"
  statement : ∀ {N T : Type}, EvExec N T → Prop :=
    fun {N T} E => ∀ C M0 r0 tr, Trace E C M0 r0 tr →
      (occurs (fun e : NetEvent N T => e.kind == .executionStarted)) tr ∧
      (at-most-once (fun e : NetEvent N T => e.kind == .executionStarted)) tr ∧
      (until (fun e : NetEvent N T => e.kind == .executionStarted), never
        (fun e : NetEvent N T => !e.isLog && e.kind != .executionStarted)) tr

/- The pinned readable form of EVT-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_002 : {N T : Type} → EvExec N T → Prop :=
fun {N T} E =>
  ∀ (C : Cfg N T) (M0 : QMarking N T) (r0 : ℕ) (tr : List (NetEvent N T)),
    Trace E C M0 r0 tr →
      (occurs fun e => e.kind == NetEventKind.executionStarted) tr ∧
        (at-most-once fun e => e.kind == NetEventKind.executionStarted) tr ∧
          (until fun e => e.kind == NetEventKind.executionStarted, never fun e =>
              !e.isLog && e.kind != NetEventKind.executionStarted)
            tr
-/
#guard_msgs in #print EVT_002

/-! ## The three lines, one at a time -/

section Lines

variable {N T : Type}

/-- The event is an `ExecutionStarted`. -/
def evt002_isStart (e : NetEvent N T) : Bool := e.kind == .executionStarted

/-- The event may not come before `ExecutionStarted`: neither a log message nor the
`ExecutionStarted` itself. -/
def evt002_early (e : NetEvent N T) : Bool := !e.isLog && e.kind != .executionStarted

/-- Line 1 of `EVT_002` alone: every trace holds an `ExecutionStarted`. -/
def evt002_line1 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 tr, Trace E C M0 r0 tr → (occurs (evt002_isStart (N := N) (T := T))) tr

/-- Line 2 of `EVT_002` alone: every trace holds at most one `ExecutionStarted`. -/
def evt002_line2 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 tr, Trace E C M0 r0 tr → (at-most-once (evt002_isStart (N := N) (T := T))) tr

/-- Line 3 of `EVT_002` alone: only log messages come before the first `ExecutionStarted`. -/
def evt002_line3 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 tr, Trace E C M0 r0 tr →
    (until (evt002_isStart (N := N) (T := T)), never (evt002_early (N := N) (T := T))) tr

/-- `EVT_002` is its three lines. -/
theorem evt002_iff (E : EvExec N T) :
    EVT_002 E ↔ evt002_line1 E ∧ evt002_line2 E ∧ evt002_line3 E :=
  ⟨fun h => ⟨fun C M0 r0 tr ht => (h C M0 r0 tr ht).1, fun C M0 r0 tr ht => (h C M0 r0 tr ht).2.1,
      fun C M0 r0 tr ht => (h C M0 r0 tr ht).2.2⟩,
   fun h C M0 r0 tr ht => ⟨h.1 C M0 r0 tr ht, h.2.1 C M0 r0 tr ht, h.2.2 C M0 r0 tr ht⟩⟩

/-- Lines 1 and 2 of `EVT_002`: what an executor that announces the run late still meets. -/
def evt002_lines12 (E : EvExec N T) : Prop := evt002_line1 E ∧ evt002_line2 E

/-- Lines 1 and 3 of `EVT_002`: what an executor that announces the run twice still meets. -/
def evt002_lines13 (E : EvExec N T) : Prop := evt002_line1 E ∧ evt002_line3 E

/-- Lines 2 and 3 of `EVT_002`: what an executor that emits nothing still meets. -/
def evt002_lines23 (E : EvExec N T) : Prop := evt002_line2 E ∧ evt002_line3 E

/-! ### The three patterns on a trace of the shape logs, ExecutionStarted, the rest -/

/-- A trace whose events are log messages, then an `ExecutionStarted`, then anything, holds an
`ExecutionStarted`. -/
theorem evt002_occurs_shape (pre post : List (NetEvent N T)) :
    (occurs (evt002_isStart (N := N) (T := T))) (pre ++ .executionStarted :: post) := by
  show List.any _ _ = true
  simp only [List.any_append, List.any_cons]
  simp [evt002_isStart, NetEvent.kind]

/-- From the memory "seen", `until ExecutionStarted, never early` holds on any trace. -/
theorem evt002_until_seen :
    ∀ post : List (NetEvent N T),
      (untilNever (evt002_isStart (N := N) (T := T)) (evt002_early (N := N) (T := T))).scan true
        post = true
  | [] => rfl
  | _ :: rest => by
    simp only [Watch.scan, untilNever, Bool.true_or, Bool.true_and]
    exact evt002_until_seen rest

/-- On such a trace, no event comes too early. -/
theorem evt002_until_shape {pre : List (NetEvent N T)} (hpre : ∀ e ∈ pre, e.isLog = true)
    (post : List (NetEvent N T)) :
    (until (evt002_isStart (N := N) (T := T)), never (evt002_early (N := N) (T := T)))
      (pre ++ .executionStarted :: post) := by
  show (untilNever _ _).scan false _ = true
  induction pre with
  | nil =>
    have h1 : evt002_early (.executionStarted : NetEvent N T) = false := by
      simp [evt002_early, NetEvent.kind]
    have h2 : evt002_isStart (.executionStarted : NetEvent N T) = true := by
      simp [evt002_isStart, NetEvent.kind]
    simp only [List.nil_append, Watch.scan, untilNever, h1, h2, Bool.not_false, Bool.or_true,
      Bool.true_and]
    exact evt002_until_seen post
  | cons e pre ih =>
    have he := hpre e (List.mem_cons_self ..)
    have h1 : evt002_early e = false := by simp [evt002_early, he]
    have h2 : evt002_isStart e = false := by
      have hk : e.kind = .logMessage := by simpa [NetEvent.isLog] using he
      simp [evt002_isStart, hk]
    simp only [List.cons_append, Watch.scan, untilNever, h1, h2, Bool.not_false, Bool.or_true,
      Bool.true_and, Bool.false_or]
    exact ih fun x hx => hpre x (List.mem_cons_of_mem _ hx)

/-- On such a trace with no `ExecutionStarted` among the rest, there is at most one. -/
theorem evt002_once_shape {pre post : List (NetEvent N T)}
    (hpre : ∀ e ∈ pre, evt002_isStart e = false) (hpost : ∀ e ∈ post, evt002_isStart e = false) :
    (at-most-once (evt002_isStart (N := N) (T := T))) (pre ++ .executionStarted :: post) := by
  show (afterNever _ _).scan false _ = true
  induction pre with
  | nil =>
    simp only [List.nil_append, Watch.scan, afterNever, Bool.false_and, Bool.not_false,
      Bool.true_and]
    exact afterNever_scan_of_absent _ hpost
  | cons e pre ih =>
    have he := hpre e (List.mem_cons_self ..)
    simp only [List.cons_append, Watch.scan, afterNever, he, Bool.false_and, Bool.not_false,
      Bool.true_and, Bool.or_false]
    exact ih fun x hx => hpre x (List.mem_cons_of_mem _ hx)

/-- A log message is not an `ExecutionStarted`. -/
theorem evt002_isStart_of_log {e : NetEvent N T} (h : e.isLog = true) : evt002_isStart e = false := by
  have hk : e.kind = .logMessage := by simpa [NetEvent.isLog] using h
  simp [evt002_isStart, hk]

/-- No event of a labelled run is an `ExecutionStarted` when no step emits one. -/
theorem evt002_lrun_noStart {E : EvExec N T}
    (hs : ∀ C H s l evs s', E.step C H s l evs s' → ∀ e ∈ evs, evt002_isStart e = false)
    {C : Cfg N T} : ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun E C H s run → ∀ e ∈ EvStep.events run, evt002_isStart e = false
  | _, _, [], _ => by simp [EvStep.events]
  | H, s, st :: rest, ⟨_, hst, hr⟩ => by
    intro e he
    simp only [EvStep.events, List.flatMap_cons, List.mem_append] at he
    rcases he with he | he
    · exact hs C H st.src st.lbl st.evs st.dst hst e he
    · exact evt002_lrun_noStart hs hr e he

/-- **The sufficient shape**: an executor whose boot is log messages, then one
`ExecutionStarted`, then events that are not `ExecutionStarted`, and none of whose steps emits an
`ExecutionStarted`, meets EVT-002. -/
theorem evt002_of_shape {E : EvExec N T}
    (hb : ∀ C M0, ∃ pre post, E.boot C M0 = pre ++ .executionStarted :: post ∧
      (∀ e ∈ pre, e.isLog = true) ∧ ∀ e ∈ post, evt002_isStart e = false)
    (hs : ∀ C H s l evs s', E.step C H s l evs s' → ∀ e ∈ evs, evt002_isStart e = false) :
    EVT_002 E := by
  refine (evt002_iff E).2 ⟨?_, ?_, ?_⟩ <;> rintro C M0 r0 tr ⟨run, hr, rfl⟩ <;>
    obtain ⟨pre, post, hbt, hpre, hpost⟩ := hb C M0 <;> rw [hbt, List.append_assoc, List.cons_append]
  · exact evt002_occurs_shape _ _
  · refine evt002_once_shape (fun e he => evt002_isStart_of_log (hpre e he)) fun e he => ?_
    rcases List.mem_append.1 he with he | he
    · exact hpost e he
    · rw [hbt] at hr
      exact evt002_lrun_noStart hs hr e he
  · exact evt002_until_shape hpre _

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- No label of the reference emits an `ExecutionStarted`. -/
theorem refEmitW_noStart (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) : ∀ e ∈ refEmitW P C H s l s', evt002_isStart e = false := by
  intro e he
  have hk := refEmitW_kind P C H s l s' e he
  unfold evt002_isStart
  cases l <;> simp only [lblKinds, List.mem_cons, List.not_mem_nil, or_false] at hk <;>
    first
    | (rcases hk with hk | hk | hk <;> simp [hk])
    | (rcases hk with hk | hk <;> simp [hk])
    | simp [hk]

/-- Every executor that steps and emits as the reference meets EVT-002 when its boot is log
messages, then `ExecutionStarted`, then events that are not `ExecutionStarted`. -/
theorem evt002_refSteps {boot : Cfg N T → QMarking N T → List (NetEvent N T)} (P : EvPol)
    (hb : ∀ C M0, ∃ pre post, boot C M0 = pre ++ .executionStarted :: post ∧
      (∀ e ∈ pre, e.isLog = true) ∧ ∀ e ∈ post, evt002_isStart e = false) :
    EVT_002 (emitExec boot (refEmitW P)) :=
  evt002_of_shape hb fun C H s l evs s' hs => by
    obtain ⟨-, rfl⟩ := hs
    exact refEmitW_noStart P C H s l s'

/-- The reference boot is `ExecutionStarted`, then events that are not `ExecutionStarted`. -/
theorem refBoot_shape (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∃ pre post, refBoot P C M0 = pre ++ .executionStarted :: post ∧
      (∀ e ∈ pre, e.isLog = true) ∧ ∀ e ∈ post, evt002_isStart e = false := by
  refine ⟨[], if P.snapshots then [.markingSnapshot (snapOf C M0)] else [], rfl, by simp, ?_⟩
  intro e he
  split at he
  · simp only [List.mem_singleton] at he; subst he; rfl
  · cases he

/-- The reference meets EVT-002 under every emission variant. -/
theorem evt002_ref (P : EvPol) : EVT_002 (refEvExec (N := N) (T := T) P) :=
  evt002_refSteps P (refBoot_shape P)

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-002: a run first
announces itself with `ExecutionStarted`, then publishes the snapshot of the initial marking,
and no step announces the run again. -/
@[evidence holds EVT_002]
theorem EVT_002_reference : EVT_002 (refEvExec (N := N) (T := T) polJT) := evt002_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-002 too: its boot is also
`ExecutionStarted`, then the snapshot of the initial marking. -/
@[evidence holds EVT_002]
theorem EVT_002_rust : EVT_002 (refEvExec (N := N) (T := T) polRust) := evt002_ref polRust

end Reference

/-! ## The worked example -/

/-- Transition `t`: takes one token from place 0. -/
def evt002_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The configuration of the example: place 0, an environment place, and transition `t`,
Immediate. -/
def evt002_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [evt002_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The marking with the token 7 in place 0. -/
def evt002_m7 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- The empty marking. -/
def evt002_m0 : QMarking Nat Nat := fun _ => []

/-- One cycle up to the start of `t`. -/
def evt002_startLbls : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- One cycle that finds nothing to start, the loop waiting, then waking up. -/
def evt002_wakeLbls : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass, .wake]

/-- ✓ The block is exercised by the reference: with the token 7 in place 0, the run emits
`ExecutionStarted`, then the snapshot of the initial marking, then `TransitionEnabled t`,
`TokenRemoved 0 7` and `TransitionStarted t`. So the trace holds exactly one
`ExecutionStarted`, it is the first event, and the transition starts after it. -/
@[evidence nonvacuous EVT_002]
theorem EVT_002_nonvacuous :
    ∃ tr, Trace (refEvExec polJT) evt002_cfg evt002_m7 0 tr ∧
      tr = [.executionStarted, .markingSnapshot [(0, [7])], .transitionEnabled "t",
        .tokenRemoved 0 7, .transitionStarted "t" [(0, 7)]] ∧
      kindCount .executionStarted tr = 1 ∧ kindCount .transitionStarted tr = 1 := by
  have h : refTrace polJT evt002_cfg evt002_m7 0 evt002_startLbls =
      some [.executionStarted, .markingSnapshot [(0, [7])], .transitionEnabled "t",
        .tokenRemoved 0 7, .transitionStarted "t" [(0, 7)]] := by decide +kernel
  exact ⟨_, refTrace_trace polJT h, rfl, by decide, by decide⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The labelled run of `emitExec boot emit` from history `H` and state `s` along the labels
`ls`, if every label is a step (`refRun` for any emission). -/
def evt002Run (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T →
    List (NetEvent N T)) (C : Cfg N T) :
    List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (xstep C s l).bind fun s' =>
      (evt002Run emit C (H ++ emit C H s l s') s' ls).map (⟨s, l, emit C H s l s', s'⟩ :: ·)

omit [Ord N] in
/-- A run `evt002Run` builds is a labelled run of `emitExec boot emit`. -/
theorem evt002Run_lrun {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      evt002Run emit C H s ls = some run → LRun (emitExec boot emit) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [evt002Run] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : evt002Run emit C (H ++ emit C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, evt002Run_lrun C hr⟩

/-- The Java and TypeScript emission, with an `ExecutionStarted` each time the loop wakes up
from a wait. -/
def evt002_wakeEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .wake => [.executionStarted]
  | _ => refEmitW polJT C H s l s'

/-- The executor that announces the run again each time it wakes from a wait. -/
def evt002_wakeAgain : EvExec N T := emitExec (refBoot polJT) evt002_wakeEmit

/-- The boot that publishes the snapshot of the initial marking, then announces the run. -/
def evt002_snapFirstBoot (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  [.markingSnapshot (snapOf C M0), .executionStarted]

/-- The executor that publishes the initial marking before it announces the run. -/
def evt002_snapshotFirst : EvExec N T := emitExec evt002_snapFirstBoot (refEmitW polJT)

/-- The boot that reports an unknown initial place first, then boots as Java and TypeScript. -/
def evt002_diagBoot (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  .logMessage none .warn "unknown initial place" :: refBoot polJT C M0

/-- The executor that reports a construction diagnostic before it announces the run. -/
def evt002_diagFirst : EvExec N T := emitExec evt002_diagBoot (refEmitW polJT)

/-- The executor that emits nothing at all, at the boot or at any step, and steps as the
reference. -/
def evt002_mute : EvExec N T := emitExec (fun _ _ => []) (fun _ _ _ _ _ => [])

omit [Ord N] in
/-- The mute executor appends nothing on any run. -/
theorem evt002_mute_events {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (evt002_mute (N := N) (T := T)) C H s run → EvStep.events run = []
  | _, _, [], _ => rfl
  | _, _, st :: rest, ⟨_, ⟨_, hev⟩, hrest⟩ => by
    simp only [EvStep.events, List.flatMap_cons] at hrest ⊢
    rw [hev]
    exact evt002_mute_events hrest

omit [Ord N] in
/-- The mute executor's traces are empty, so it keeps lines 2 and 3: nothing is announced twice
and nothing comes before an announcement. -/
theorem evt002_mute_lines23 : evt002_lines23 (evt002_mute (N := N) (T := T)) := by
  constructor <;> rintro C M0 r0 tr ⟨run, hr, rfl⟩ <;>
    rw [show (evt002_mute (N := N) (T := T)).boot C M0 = [] from rfl, evt002_mute_events hr] <;> rfl

/-- An executor whose boot is the reference boot announces the run first, whatever its steps
emit: it keeps lines 1 and 3. -/
theorem evt002_refBoot_lines13
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    evt002_line1 (emitExec (refBoot polJT) emit) ∧ evt002_line3 (emitExec (refBoot polJT) emit) := by
  constructor <;> rintro C M0 r0 tr ⟨run, -, rfl⟩ <;>
    obtain ⟨pre, post, hbt, hpre, -⟩ := refBoot_shape (N := N) polJT C M0 <;>
    simp only [emitExec] <;> rw [hbt, List.append_assoc, List.cons_append]
  · exact evt002_occurs_shape _ _
  · exact evt002_until_shape hpre _

/-- An executor that publishes the snapshot first still announces the run, once: it keeps lines 1
and 2. -/
theorem evt002_snapshotFirst_lines12 : evt002_lines12 (evt002_snapshotFirst (N := N) (T := T)) := by
  have hs : ∀ C H s l evs s', (evt002_snapshotFirst (N := N) (T := T)).step C H s l evs s' →
      ∀ e ∈ evs, evt002_isStart e = false := fun C H s l evs s' hs => by
    obtain ⟨-, rfl⟩ := hs; exact refEmitW_noStart polJT C H s l s'
  constructor <;> rintro C M0 r0 tr ⟨run, hr, rfl⟩
  · exact evt002_occurs_shape [.markingSnapshot (snapOf C M0)] _
  · exact evt002_once_shape (pre := [.markingSnapshot (snapOf C M0)])
      (by simp [evt002_isStart, NetEvent.kind]) (post := EvStep.events run)
      (fun e he => evt002_lrun_noStart hs hr e he)

end Mutants

/-- ✗ A run that announces nothing violates EVT-002 (line 1): an executor that emits no event at
all, at the boot or at any step, has emitted nothing when it is booted, so its trace holds no
`ExecutionStarted`. With no event at all, nothing is announced twice and nothing comes before an
announcement, so it keeps lines 2 and 3. -/
@[evidence mutant EVT_002]
theorem EVT_002_mutant_silent :
    evt002_lines23 (evt002_mute (N := Nat) (T := Nat)) ∧
      ¬ EVT_002 (evt002_mute (N := Nat) (T := Nat)) := by
  refine ⟨evt002_mute_lines23, fun h => ?_⟩
  have := (h evt002_cfg evt002_m0 0 [] ⟨[], trivial, rfl⟩).1
  exact absurd this (by decide)

/-- ✗ Announcing the run again after a wait violates EVT-002 (line 2): with place 0 empty, the
first cycle finds nothing to start, the loop waits for an event, wakes up and emits a second
`ExecutionStarted`. The boot announces the run first, so the executor keeps lines 1 and 3. -/
@[evidence mutant EVT_002]
theorem EVT_002_mutant_wakeAgain :
    evt002_lines13 (evt002_wakeAgain (N := Nat) (T := Nat)) ∧
      ¬ EVT_002 (evt002_wakeAgain (N := Nat) (T := Nat)) := by
  refine ⟨evt002_refBoot_lines13 _, fun h => ?_⟩
  have hc : (evt002Run evt002_wakeEmit evt002_cfg (refBoot polJT evt002_cfg evt002_m0)
      (xinit evt002_m0 0) evt002_wakeLbls).map (fun run =>
        decide ((at-most-once (fun e : NetEvent Nat Nat => e.kind == .executionStarted))
          (refBoot polJT evt002_cfg evt002_m0 ++ EvStep.events run))) = some false := by
    decide +kernel
  cases hr : evt002Run evt002_wakeEmit evt002_cfg (refBoot polJT evt002_cfg evt002_m0)
      (xinit evt002_m0 0) evt002_wakeLbls with
  | none => simp [hr] at hc
  | some run =>
    simp only [hr, Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at hc
    exact hc (h evt002_cfg evt002_m0 0 _ ⟨run, evt002Run_lrun evt002_cfg hr, rfl⟩).2.1

/-- ✗ Publishing the initial marking before announcing the run violates EVT-002 (line 3): with
the token 7 in place 0, the boot emits the snapshot of place 0 first and `ExecutionStarted`
second, and a snapshot is not a log message. The run is still announced, once, so the executor
keeps lines 1 and 2. -/
@[evidence mutant EVT_002]
theorem EVT_002_mutant_snapshotFirst :
    evt002_lines12 (evt002_snapshotFirst (N := Nat) (T := Nat)) ∧
      ¬ EVT_002 (evt002_snapshotFirst (N := Nat) (T := Nat)) := by
  refine ⟨evt002_snapshotFirst_lines12, fun h => ?_⟩
  have := (h evt002_cfg evt002_m7 0 _ ⟨[], trivial, rfl⟩).2.2
  exact absurd this (by decide +kernel)

/-- ✓ A log message before `ExecutionStarted` is allowed: an executor that reports an unknown
initial place when it is constructed, as Java and TypeScript do, and only then announces the run,
meets EVT-002. -/
@[evidence allows EVT_002]
theorem EVT_002_allows_diagnosticsFirst : EVT_002 (evt002_diagFirst (N := Nat) (T := Nat)) :=
  evt002_refSteps polJT fun C M0 => by
    obtain ⟨pre, post, hbt, hpre, hpost⟩ := refBoot_shape (N := Nat) (T := Nat) polJT C M0
    refine ⟨.logMessage none .warn "unknown initial place" :: pre, post, ?_, ?_, hpost⟩
    · simp only [evt002_diagBoot, hbt, List.cons_append]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · exact hpre e he

/-! ## EVT-002, the execution ID: two executors, two IDs -/

/-- The digit value of a lower-case hex digit (`'0'`..`'9'`, `'a'`..`'f'`). -/
def evt002HexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

/-- A list of hex digits read back as a number. -/
def evt002ReadHex (l : List Char) : Nat := l.foldl (fun acc c => 16 * acc + evt002HexVal c) 0

/-- **The reference execution ID**: the executor constructed `k`-th in its process gets `k` in
lower-case hex, whatever the clock reads (`r`), as Java (`Long.toHexString` of a shared
counter), TypeScript (`toString(16)` of a shared counter) and Rust (`{:x}` of a shared atomic
counter) draw it. -/
def refExecutionId (k _r : Nat) : String := String.ofList (Nat.toDigits 16 k)

/- The reference execution ID is the witness model of the execution ID block. -/
#spec_witness refExecutionId

/-- A hex digit reads back as its value. -/
theorem evt002HexVal_digitChar : ∀ n, n < 16 → evt002HexVal n.digitChar = n := by decide

/-- The hex digits of `n` read back as `n`. -/
theorem evt002ReadHex_toDigits (n : Nat) : evt002ReadHex (Nat.toDigits 16 n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · simp [evt002ReadHex, evt002HexVal_digitChar n ‹_›]
    · have hlt : n / 16 < n := Nat.div_lt_self (by omega) (by decide)
      have hih := ih (n / 16) hlt
      simp only [evt002ReadHex, List.foldl_append, List.foldl_cons, List.foldl_nil] at hih ⊢
      rw [hih, evt002HexVal_digitChar _ (Nat.mod_lt _ (by decide))]
      omega

/-- Distinct counter values give distinct reference IDs. -/
theorem refExecutionId_inj {k k' r r' : Nat} (h : refExecutionId k r = refExecutionId k' r') :
    k = k' := by
  have := congrArg evt002ReadHex (String.ofList_injective h)
  rwa [evt002ReadHex_toDigits, evt002ReadHex_toDigits] at this

requirement EVT_002_executionId
  id "EVT-002"
  title "ExecutionStarted Event (execution ID)"
  kind F
  scope "Java, TypeScript and Rust executors"
  source verbatim "spec/08-events-observability.md"
  quote "Two executors constructed in one process from the same copy of the library *shall* carry different execution IDs, whatever the clock reads when each is constructed ([TIME-015] AC14)."
  reading "For every execution ID assignment ids, where ids k r is the execution ID of the executor constructed k-th in its process from one copy of the library while the clock reads r: two executors constructed at different places k and k' in the construction order carry different IDs, for all clock readings r and r'."
  assumes "This is the second block of EVT-002 (ruling D98 (a)): the ID identifies the executor, and its distinctness is the MUST half of TIME-015 AC14, which no other block states (TIME-015 points AC14 at this block). The model is the assignment ids : Nat → Nat → String: the ID depends on the executor's place k in the process's construction order and, in a wrong implementation, on the clock reading r at construction. All runtimes draw the ID at construction from one counter per copy of the library shared by both executors (EXECUTION_ID_SEQ and nextExecutionId in java/src/main/java/org/libpetri/runtime/ExecutorSupport.java, used by the executionId field of BitmapNetExecutor.java and PrecompiledNetExecutor.java; executionIdCounter and nextExecutionId in typescript/src/runtime/executor-support.ts, used by the runId field of bitmap-net-executor.ts and precompiled-net-executor.ts; EXECUTION_ID_SEQ in rust/libpetri-runtime/src/executor_core/executor.rs, drawn in Executor::from_parts), so k counts the executors of both kinds. The witness refExecutionId is that counter in lower-case hex. An implementation that takes the ID from the clock reading, as TypeScript did before AC14 (the doc comment of nextExecutionId, executor-support.ts), separates executors constructed at different readings and breaks the line under an injected clock that reads the same twice (EVT_002_executionId_mutant_clock)."
          "Out of scope: a counter that wraps (2 to the 64 constructions in Java and Rust; TypeScript numbers stay exact up to 2 to the 53), executors in different processes (a per-process counter restarts at 0, which AC14 does not ask to avoid), executors constructed from different copies of the library in one process, each with its own counter that starts at 0 (a TypeScript module instance per worker thread or realm, each with its own executionIdCounter in executor-support.ts; a Java class loaded by two class loaders, each with its own ExecutorSupport.EXECUTION_ID_SEQ; two instances of the Rust crate), and reproducibility, the SHOULD half of AC14 (refExecutionId does not read the clock, so a replay with the same construction order gets the same IDs, EVT_002_executionId_nonvacuous). Whether the ID is on the events is the third block, EVT_002_lifecycleId: Java and TypeScript put it on ExecutionStarted and ExecutionCompleted, Rust and Python do not."
          "The model is a restriction: the ID is a function of the construction place k and the clock reading r and of nothing else, so an ID drawn from randomness, a thread or the net cannot be written as an assignment, and the block separates the counter from a clock-derived ID only. No runtime draws the ID from anything but the counter. Python is out of scope: the binding constructs Rust executors, which draw from the Rust counter, but it exposes no execution ID (no execution_id in rust/libpetri-py/src), so from Python the line cannot be observed; Rust exposes it through the pub fn execution_id (Executor::execution_id, executor_core/executor.rs) and not on events."
          "AC2 (two executors constructed in one process carry different execution IDs, even at the same clock reading) is the line. The text before ruling D98 asked for an ID unique across runs: one executor can run more than once and keeps its ID, so no runtime has a per-run ID."
  signoff "2026-11-13 616505a7f94df939 ai"
  statement : (Nat → Nat → String) → Prop :=
    fun ids => ∀ k k' r r', k ≠ k' → ids k r ≠ ids k' r'

/- The pinned readable form of the execution ID block. -/
/--
info: def Libpetri.Spec.EVT_002_executionId : (ℕ → ℕ → String) → Prop :=
fun ids => ∀ (k k' r r' : ℕ), k ≠ k' → ids k r ≠ ids k' r'
-/
#guard_msgs in #print EVT_002_executionId

/-- ✓ The reference execution ID meets the block: the counter is read in hex, and two counter
values never print the same. -/
@[evidence holds EVT_002_executionId, evidence cites "TIME-015" "AC14: two executors constructed in one process carry different execution IDs, whatever the clock reads"]
theorem EVT_002_executionId_reference : EVT_002_executionId refExecutionId :=
  fun _ _ _ _ hk h => hk (refExecutionId_inj h)

/-- ✓ The block is exercised by the reference: the first two executors constructed while the
clock reads 5 get the IDs "0" and "1"; the 27th gets "1a" whatever the clock reads, so a replay in
the same construction order gets the same IDs. -/
@[evidence nonvacuous EVT_002_executionId]
theorem EVT_002_executionId_nonvacuous :
    refExecutionId 0 5 = "0" ∧ refExecutionId 1 5 = "1" ∧
      refExecutionId 26 0 = "1a" ∧ refExecutionId 26 9 = "1a" := by
  decide +kernel

/-- The ID taken from the clock reading at construction. -/
def evt002ClockId (_k r : Nat) : String := refExecutionId r 0

/-- Executors constructed at different clock readings carry different IDs: what an ID taken from
the clock still meets. -/
def evt002_apartAcrossReadings (ids : Nat → Nat → String) : Prop :=
  ∀ k k' r r', r ≠ r' → ids k r ≠ ids k' r'

/-- ✗ Taking the ID from the clock reading violates the block: under an injected clock that reads
3 at both constructions, the first two executors both get "3". Such an ID still separates
executors constructed at different readings. -/
@[evidence mutant EVT_002_executionId]
theorem EVT_002_executionId_mutant_clock :
    evt002_apartAcrossReadings evt002ClockId ∧ ¬ EVT_002_executionId evt002ClockId := by
  refine ⟨fun _ _ _ _ hr h => hr (refExecutionId_inj h), fun h => h 0 1 3 3 (by decide) rfl⟩

/-! ## EVT-002, the ID on the lifecycle events (Java and TypeScript) -/

/-- What a Java or TypeScript host observes of the execution IDs: `exec k r` is the ID the
executor constructed `k`-th in its process while the clock reads `r` reports
(`executionId()`); `onStarted k r j` and `onCompleted k r j` are the IDs on the
`ExecutionStarted` and the `ExecutionCompleted` event of that executor's `j`-th run. -/
structure Evt002LifeIds where
  /-- The executor's own ID, `executionId()`. -/
  exec : Nat → Nat → String
  /-- The ID on the `ExecutionStarted` event of run `j`. -/
  onStarted : Nat → Nat → Nat → String
  /-- The ID on the `ExecutionCompleted` event of run `j`. -/
  onCompleted : Nat → Nat → Nat → String

/-- **The reference lifecycle IDs**: the executor's ID is the construction counter
`refExecutionId`, and both lifecycle events of every run are built from it, as Java
(`executeLoop` in `BitmapNetExecutor.java` and `PrecompiledNetExecutor.java`) and TypeScript
(`executeLoop` in `bitmap-net-executor.ts` and `precompiled-net-executor.ts`) build them from
`executionId()`. -/
def refLifecycleIds : Evt002LifeIds :=
  { exec := refExecutionId,
    onStarted := fun k r _ => refExecutionId k r,
    onCompleted := fun k r _ => refExecutionId k r }

/- The reference lifecycle IDs are the witness model of the lifecycle ID block. -/
#spec_witness refLifecycleIds

requirement EVT_002_lifecycleId
  id "EVT-002"
  title "ExecutionStarted Event (execution ID on the lifecycle events)"
  kind F
  scope "Java and TypeScript executors (the lifecycle events of Rust and Python carry no execution ID)"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the lifecycle events carry the execution ID (Java and TypeScript), the ExecutionStarted and ExecutionCompleted events of every run *shall* carry the ID of the executor that runs it."
  reading "For every observation L of the execution IDs, where L.exec k r is the ID of the executor constructed k-th in its process while the clock reads r, and L.onStarted k r j and L.onCompleted k r j are the IDs on the ExecutionStarted and ExecutionCompleted events of its j-th run: for all k, r and j,"
          "the ExecutionStarted event of the run carries the executor's ID, L.onStarted k r j = L.exec k r;"
          "the ExecutionCompleted event of the run carries the executor's ID, L.onCompleted k r j = L.exec k r."
  assumes "This is the third block of EVT-002 and the Java and TypeScript companion of ruling D98 (a): the event model of the first block (NetEvent in Spec/GlossaryEvents.lean) carries no execution ID, so this block states the ID on the events over what a host observes, the executor's executionId() and the ID field of each lifecycle event, and needs no new field on NetEvent. The model is Evt002LifeIds, indexed by the executor (its place k in the construction order and the reading r at construction, as in EVT_002_executionId) and the run j, so every run of one executor carries the same ID and both events of one run carry the same ID. The witness refLifecycleIds builds both events from executionId(), as both Java executors and both TypeScript executors do."
          "Each line has its own wrong observation. An executor that draws a fresh ID from the shared counter for its ExecutionStarted event (TypeScript nextExecutionId() from executor-support.ts in place of this.executionId()) gives the first executor the ID 0 and its event the ID 1; its executor IDs stay distinct, so it meets the first two blocks and breaks line 1 (EVT_002_lifecycleId_mutant_freshDraw). An executor that puts its ν execution scope (NU-011, a random token drawn per executor and not the execution ID, the doc of Builder.executionScope in BitmapNetExecutor.java) on its ExecutionCompleted event breaks line 2 (EVT_002_lifecycleId_mutant_scopeOnCompleted)."
          "When an ExecutionCompleted event is emitted, and whether every run emits one, is EVT-003; this block says only which ID it carries. Rust and Python are out of scope: their lifecycle events have no ID field (the execution_id field and Executor::execution_id in executor_core/executor.rs, kept off so as not to change the session archive format, EVT-025). That the IDs of two executors differ is EVT_002_executionId; evt002_started_ids_apart shows that the two blocks together keep the ExecutionStarted events of two executors apart."
  signoff "2026-11-13 59784c3fe92eac83 ai"
  statement : Evt002LifeIds → Prop :=
    fun L => ∀ k r j, L.onStarted k r j = L.exec k r ∧ L.onCompleted k r j = L.exec k r

/- The pinned readable form of the lifecycle ID block. -/
/--
info: def Libpetri.Spec.EVT_002_lifecycleId : Evt002LifeIds → Prop :=
fun L => ∀ (k r j : ℕ), L.onStarted k r j = L.exec k r ∧ L.onCompleted k r j = L.exec k r
-/
#guard_msgs in #print EVT_002_lifecycleId

/-- ✓ The reference lifecycle IDs meet the block: both events of every run are built from the
executor's own ID. -/
@[evidence holds EVT_002_lifecycleId]
theorem EVT_002_lifecycleId_reference : EVT_002_lifecycleId refLifecycleIds :=
  fun _ _ _ => ⟨rfl, rfl⟩

/-- ✓ The block is exercised by the reference: the second executor constructed while the clock
reads 5 has the ID "1", and its first and second runs both announce and complete with "1". -/
@[evidence nonvacuous EVT_002_lifecycleId]
theorem EVT_002_lifecycleId_nonvacuous :
    refLifecycleIds.exec 1 5 = "1" ∧
      refLifecycleIds.onStarted 1 5 0 = "1" ∧ refLifecycleIds.onCompleted 1 5 0 = "1" ∧
      refLifecycleIds.onStarted 1 5 1 = "1" ∧ refLifecycleIds.onCompleted 1 5 1 = "1" := by
  decide +kernel

/-- With the two ID blocks, the `ExecutionStarted` events of two executors constructed in one
process carry different IDs, whatever the clock reads and whichever runs they announce. -/
theorem evt002_started_ids_apart {L : Evt002LifeIds} (hid : EVT_002_executionId L.exec)
    (hl : EVT_002_lifecycleId L) {k k' : Nat} (r r' j j' : Nat) (hk : k ≠ k') :
    L.onStarted k r j ≠ L.onStarted k' r' j' := by
  rw [(hl k r j).1, (hl k' r' j').1]
  exact hid k k' r r' hk

/-- Line 1 of `EVT_002_lifecycleId` alone: every `ExecutionStarted` carries the executor's ID. -/
def evt002_lifeLine1 (L : Evt002LifeIds) : Prop := ∀ k r j, L.onStarted k r j = L.exec k r

/-- Line 2 of `EVT_002_lifecycleId` alone: every `ExecutionCompleted` carries the executor's
ID. -/
def evt002_lifeLine2 (L : Evt002LifeIds) : Prop := ∀ k r j, L.onCompleted k r j = L.exec k r

/-- What an executor that draws a fresh ID for its `ExecutionStarted` still meets: its executor
IDs are apart, and its `ExecutionCompleted` events carry its ID. -/
def evt002_idsApartLine2 (L : Evt002LifeIds) : Prop :=
  EVT_002_executionId L.exec ∧ evt002_lifeLine2 L

/-- The executor that draws a fresh ID from the shared counter for its `ExecutionStarted` event:
the `k`-th executor takes `2k` at construction and `2k + 1` for the event. -/
def evt002_freshDraw : Evt002LifeIds :=
  { exec := fun k _ => refExecutionId (2 * k) 0,
    onStarted := fun k _ _ => refExecutionId (2 * k + 1) 0,
    onCompleted := fun k _ _ => refExecutionId (2 * k) 0 }

/-- The executor that puts its ν execution scope, a token other than its ID, on its
`ExecutionCompleted` event. -/
def evt002_scopeOnCompleted : Evt002LifeIds :=
  { exec := refExecutionId,
    onStarted := fun k r _ => refExecutionId k r,
    onCompleted := fun k _ _ => "scope-" ++ refExecutionId k 0 }

/-- ✗ Drawing a fresh ID for the `ExecutionStarted` event violates the block (line 1): the first
executor has the ID "0" and its `ExecutionStarted` carries "1". Its executor IDs "0", "2", "4"
… are still apart, so it meets `EVT_002_executionId`, and its `ExecutionCompleted` events carry
the right ID. -/
@[evidence mutant EVT_002_lifecycleId]
theorem EVT_002_lifecycleId_mutant_freshDraw :
    evt002_idsApartLine2 evt002_freshDraw ∧ ¬ EVT_002_lifecycleId evt002_freshDraw := by
  refine ⟨⟨fun k k' r r' hk h => hk ?_, fun _ _ _ => rfl⟩, fun h => ?_⟩
  · have := refExecutionId_inj (r := 0) (r' := 0) h
    omega
  · exact absurd (h 0 0 0).1 (by decide +kernel)

/-- ✗ Putting the ν execution scope on the `ExecutionCompleted` event violates the block
(line 2): the first executor has the ID "0" and its `ExecutionCompleted` carries "scope-0". Its
`ExecutionStarted` events carry the right ID. -/
@[evidence mutant EVT_002_lifecycleId]
theorem EVT_002_lifecycleId_mutant_scopeOnCompleted :
    evt002_lifeLine1 evt002_scopeOnCompleted ∧ ¬ EVT_002_lifecycleId evt002_scopeOnCompleted := by
  refine ⟨fun _ _ _ => rfl, fun h => ?_⟩
  exact absurd (h 0 0 0).2 (by decide +kernel)

end Libpetri.Spec
