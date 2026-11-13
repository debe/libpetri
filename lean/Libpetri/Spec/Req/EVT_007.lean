import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Text.EVT_007

set_option linter.missingDocs true

/-!
# EVT-007: TransitionCompleted Event (`spec/08-events-observability.md`)

When the executor deposits the outcome of a firing whose action completed successfully, it
reports the deposited tokens (one `TokenAdded` event per token, [EVT-011]) and then one
`TransitionCompleted` event naming the transition. It reports a completion at no other time,
except that Java and TypeScript also report one when they deposit a timeout outcome (ruling D65
(a): allowed, not required). The requirement has two blocks with the same spec ID (rulings D33 (a)
and D38 (a)):

* `EVT_007`, for every executor: it reads an event only through its kind and the transition it
  names, which every runtime's event carries. Line 1: the deposit of an admitted completion emits,
  log messages aside, `TokenAdded` events and then exactly one `TransitionCompleted` naming the
  firing's transition. Line 2: nothing but such a deposit or the deposit of a timeout outcome emits
  a `TransitionCompleted`, neither another step nor the boot of a run. Line 3: a timeout deposit
  emits no `TransitionCompleted`, or one only, naming the firing's transition, as its last event
  other than log messages.
* `EVT_007_payload`, for the executors whose `TransitionCompleted` carries the produced tokens and
  the duration (Java and TypeScript; the Rust and Python event has neither). Line 1: the
  `TokenAdded` events of an admitted completion carry the produced tokens in emission order, and
  the event lists the same tokens. Line 2: after a timeout outcome the event lists that outcome's
  tokens. Line 3: the duration is at most the firing-clock time from the start of the firing to
  the deposit (ruling D38 (a): a bound, zero allowed).

Both are predicates over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`); the witness is the reference executor with events `refEvExec`. The
wrong executors step as the reference and emit otherwise: one that reports the completion before
the deposited tokens, one that reports no completion, one that reports a rejected completion as
completed, one that reports a mid-action publication as a completion, one that reports a timeout
outcome's completion before its tokens or twice, one that lists no produced tokens, one that
lists none after a timeout, and one that measures the duration from clock zero.

The worked example (`evt007_cfg`): transition `t` takes the two tokens 7 and 8 from place 0. Its
output spec is "a token in place 1, or, if the action's budget runs out, the two inputs forwarded
to place 2". The run starts at clock reading 2. When the action writes 50 to place 1 and returns
3 time units later, the deposit reports `TokenAdded` 1 50 and then `TransitionCompleted t`
listing (1, 50) with duration 3.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-007, every executor: the deposited tokens first, then one TransitionCompleted -/

requirement EVT_007
  id "EVT-007"
  title "TransitionCompleted Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_007.s1, EVT_007.s2, EVT_007.s3
  reading "For every executor with events E and every configuration C:"
          "for every history H of the events emitted before the step, a commit step of a firing identity i, from state s to state s', that appends the events evs: if f is the firing with identity i in flight in s, the events of evs that are not log messages are a list of TokenAdded events followed by one TransitionCompleted event naming f's transition;"
          "the events a run emits before its first step contain no TransitionCompleted event, whatever the initial marking, and for every history H a step that is neither a commit step nor a timeout deposit step appends no TransitionCompleted event;"
          "for every history H, a timeout deposit step of a firing identity i, from state s to state s', that appends the events evs: if f is the firing with identity i in flight in s, either no event of evs is a TransitionCompleted, or the events of evs that are not log messages end with a TransitionCompleted event naming f's transition and contain no other TransitionCompleted event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else. All three lines hold for every history H."
          "Naming: an admitted completion is a normal return of the action that the executor processes (glossary: Admitted completion); it is deposited only when output validation and the join-relay check accept its emission (EXEC-021), and that deposit is the commit step (label commit i); the deposit of a timeout outcome is the timeout deposit step (label tdeposit i, EXEC-022). The lead-in of the section says the same in words: the event is emitted when the executor deposits the outcome of a firing whose action completed successfully. A failed firing (EVT-008), an admitted completion that validation rejects included, and a completion abandoned by a terminal stop (EXEC-042) have no commit step."
          "Main block and companion (rulings D33 (a) and D38 (a)): this block reads an event only through its kind and the transition it names. The produced tokens and the duration are read only by the second block of EVT-007, EVT_007_payload, scoped to Java and TypeScript: the Rust TransitionCompleted event carries the transition name and a timestamp only (rust/libpetri-event/src/net_event.rs TransitionCompleted), and Python rides on it."
          "Line 1 is the first quoted sentence. Every runtime deposits the tokens one by one, emits a TokenAdded event for each, and then the TransitionCompleted event: Rust in handle_completion and in the synchronous paths of fire_transition_sync and fire_transition_async (rust/libpetri-runtime/src/executor_core/executor.rs); Java in processCompletedTransitions and processSyncOutput (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java); TypeScript after every output has landed (processCompletedTransitions in typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts). Which TokenAdded events the deposit emits, one per deposited token naming its place, is EVT-011's, as the cross-reference says; with it, the TransitionCompleted comes after the TokenAdded event of every token the action produced at completion (AC1). An executor that reports the completion before the deposited tokens breaks line 1 (EVT_007_mutant_completedFirst), and so does one that deposits silently (EVT_007_mutant_silentCommit)."
          "Line 1 is stated on the events that are not log messages because the runtimes interleave diagnostics with the deposit: Rust emits the IO-016 multiplicity warning before the TokenAdded events and the CORE-072 unknown-place warning between them and the TransitionCompleted (warn_multiplicity and warn_unknown_places in handle_completion, executor_core/executor.rs), Java warns about an unknown place inside the deposit, TypeScript inside the loop (warnUnknownPlace in processCompletedTransitions of bitmap-net-executor.ts). Which log messages a deposit emits is EVT-013's."
          "AC1 also says the event comes after output deposition. Tokens the action published before it completed (IO-015, mid-action publication, Rust and Python only) are not part of the deposit of the completion: a publish step deposits them with their own TokenAdded events and no completion event (ruling D17, EXEC-020), and Rust processes completions before publications in a cycle (run_async drains completion_rx through handle_completion before flush_rx through handle_flush, executor_core/executor.rs), so such a TokenAdded event can follow the TransitionCompleted (EVT_007_allows_publishedAfter). The event marks the deposit of the tokens the action produced at completion, as the requirement text says."
          "Line 2 is the second quoted sentence. No runtime emits TransitionCompleted outside these sites. An executor that reports a completion that output validation rejects as completed breaks it (EVT_007_mutant_completedOnRejection; EVT-008 rejects it too), and so do one that reports a mid-action publication as a completion (EVT_007_mutant_completedAtPublish), one that reports a completion at the boot (EVT_007_mutant_bootCompleted) and one that reports a completion for a failed firing at the end of step 1, after the fail step settled it (EVT_007_mutant_completedAfterFail)."
          "Line 3 is the third quoted sentence, the weak form of ruling D65 (a). Java and TypeScript emit ActionTimedOut from the action's timer and then, when the executor deposits the timeout outcome, TokenAdded events and a TransitionCompleted listing them (in Java, ExecutorSupport.withActionTimeout in java/src/main/java/org/libpetri/runtime/ExecutorSupport.java completes the future normally with the timeout output and BitmapNetExecutor.processCompletedTransitions deposits it; in TypeScript, the timeout branch of fireTransition in bitmap-net-executor.ts emits the event and processCompletedTransitions deposits the outcome). Rust emits ActionTimedOut and the TokenAdded events and no TransitionCompleted (handle_completion in executor_core/executor.rs: the event is guarded by completion.timed_out.is_none()), and a Rust test pins it (async_timeout_emits_action_timed_out in rust/libpetri-runtime/src/executor.rs). Both are allowed: the reference meets EVT_007 under both emission variants, and at the same timeout deposit polJT emits the event and polRust does not (EVT_007_allows_timeoutEither). What line 3 still fixes: if the event is emitted, it names the firing's transition, it is the only one of the deposit, and it comes after the deposited tokens. An executor that reports it before them breaks line 3 (EVT_007_mutant_timeoutCompletedFirst), and so does one that reports it twice (EVT_007_mutant_timeoutCompletedTwice). Ruling D65 (b) would make the event forbidden after a timeout outcome, and (c) required; either is a later change of line 3."
          "AC2 (the duration reflects action execution time) is the companion's line 3, scoped to Java and TypeScript; the Rust event has no duration."
          "Not fixed here: the timestamp the event carries (the epoch clock is the CORE-011 slice), and the defensive copy of the list (EVT-001; an event is a value here). That a commit step is offered at all when an admitted completion is waiting is the executor model's (EXEC-020's coverage clause Exec020Covers in Req/EXEC_cycle.lean, a conjunct of ExecCoversW5 in ConsistencyExec.lean), not a line here."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); no host callback throws inside a deposit (Java reports a throw of the event store in the middle of a deposit as a TransitionFailed of a partly deposited firing; TypeScript drops the event and goes on, since emitEvent in bitmap-net-executor.ts and precompiled-net-executor.ts catches the failure through swallowEventStoreFailure; the model's deposit is atomic); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (fire a transition whose action produces a token after the clock advanced; verify the TokenAdded event, then TransitionCompleted naming the transition, which in Java and TypeScript lists the produced token with a duration no larger than the clock advance) is split. The shape is EVT_007_nonvacuous: t's action writes 50 to place 1 and returns, and the deposit emits TokenAdded 1 50 and then TransitionCompleted t; its timeout deposit emits TransitionCompleted t after the two TokenAdded events under the Java and TypeScript emission and none under the Rust emission. The produced tokens and the duration are EVT_007_payload_nonvacuous. A duration above zero is not required (ruling D38 (a)): the firing clock may return the same reading twice (TIME-015), and Java reports zero for every synchronously completed action (EVT_007_payload_allows_zeroDuration)."
  signoff "2026-11-13 36b0cc1699bf112c ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (∀ H i evs, on (fun s s' => E.step C H s (.commit i) evs s'), shall (fun s _ =>
          ∀ f, s.fl.find? (·.id == i) = some f →
            ∃ (as : List (NetEvent _ _)) (pl : List (_ × _)) (d : Nat),
              evs.filter (fun e => !e.isLog) =
                as ++ [.transitionCompleted f.t.core.name pl d] ∧
              ∀ e ∈ as, e.kind = .tokenAdded)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionCompleted) ∧
        ∀ H l evs, (∀ i, l ≠ .commit i) → (∀ i, l ≠ .tdeposit i) →
          on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
            ∀ e ∈ evs, e.kind ≠ .transitionCompleted)) ∧
      (∀ H i evs, on (fun s s' => E.step C H s (.tdeposit i) evs s'), shall (fun s _ =>
          ∀ f, s.fl.find? (·.id == i) = some f →
            (∀ e ∈ evs, e.kind ≠ .transitionCompleted) ∨
            ∃ (pre : List (NetEvent _ _)) (pl : List (_ × _)) (d : Nat),
              evs.filter (fun e => !e.isLog) =
                pre ++ [.transitionCompleted f.t.core.name pl d] ∧
              ∀ e ∈ pre, e.kind ≠ .transitionCompleted))

/- The pinned readable form of EVT-007: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_007 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (∀ (H : List (NetEvent N T)) (i : ℕ) (evs : List (NetEvent N T)),
        on fun s s' => E.step C H s (XLbl.commit i) evs s', shall fun s x =>
          ∀ (f : Firing N T),
            List.find? (fun x => x.id == i) s.fl = some f →
              ∃ as pl d,
                List.filter (fun e => !e.isLog) evs = as ++ [NetEvent.transitionCompleted f.t.core.name pl d] ∧
                  ∀ e ∈ as, e.kind = NetEventKind.tokenAdded) ∧
      ((∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionCompleted) ∧
          ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
            (∀ (i : ℕ), l ≠ XLbl.commit i) →
              (∀ (i : ℕ), l ≠ XLbl.tdeposit i) →
                on fun s s' => E.step C H s l evs s', shall fun x x_1 =>
                  ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionCompleted) ∧
        ∀ (H : List (NetEvent N T)) (i : ℕ) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s (XLbl.tdeposit i) evs s', shall fun s x =>
            ∀ (f : Firing N T),
              List.find? (fun x => x.id == i) s.fl = some f →
                (∀ e ∈ evs, e.kind ≠ NetEventKind.transitionCompleted) ∨
                  ∃ pre pl d,
                    List.filter (fun e => !e.isLog) evs = pre ++ [NetEvent.transitionCompleted f.t.core.name pl d] ∧
                      ∀ e ∈ pre, e.kind ≠ NetEventKind.transitionCompleted
-/
#guard_msgs in #print EVT_007

/-! ## EVT-007, Java and TypeScript companion: the produced tokens and the duration -/

requirement EVT_007_payload
  id "EVT-007"
  title "TransitionCompleted Event (produced tokens and duration)"
  kind B
  scope "Java and TypeScript executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_007.s4, EVT_007.s5, EVT_007.s6
  reading "For every executor with events E, every configuration C, every history H, every firing identity i and every list of events evs:"
          "a commit step of i from state s to state s' that appends evs, where f is the firing with identity i in flight in s and f's outcome is the returned emission e: the events of evs that are not log messages are the TokenAdded events of e, one per token in emission order, followed by one TransitionCompleted event naming f's transition that lists e, with some duration;"
          "a timeout deposit step of i from s to s' that appends evs, where f is the firing with identity i in flight in s and f's outcome is the timeout outcome e: every TransitionCompleted event in evs lists e;"
          "a commit step or a timeout deposit step of i from s to s' that appends evs, where f is the firing with identity i in flight in s: every TransitionCompleted event in evs has a duration of at most the reading of s minus the reading at f's start."
  assumes "This is the second block of EVT-007 (rulings D33 (a) and D38 (a)): the produced tokens and the duration, for the executors whose TransitionCompleted event carries them. The first block, EVT_007, states the shape and the emission points for every executor. Java's TransitionCompleted carries List<Token<?>> producedTokens and Duration duration (java/src/main/java/org/libpetri/event/NetEvent.java TransitionCompleted), TypeScript's producedTokens and durationMs (typescript/src/event/net-event.ts); Rust's carries neither, so this block does not apply to Rust and Python. The model lists each produced token with its place (the outcome e : List (N × T)), while the Java and TypeScript lists hold the tokens alone, in the order of the outcome entries the executor walks; a runtime event is read as the model's by pairing its i-th token with the place of the i-th entry of the deposited outcome, which is the place of the deposit's i-th TokenAdded event. The witness is refEvExec polJT, and EVT_007_payload_rust shows the reference with the Rust emission meets it too, vacuously after a timeout outcome, where it emits no TransitionCompleted."
          "Line 1 is the first quoted sentence. Java and TypeScript walk the emission in order, deposit each token, emit its TokenAdded event and append the token to the produced list, then emit TransitionCompleted with that list (Java BitmapNetExecutor and PrecompiledNetExecutor: processSyncOutput for an action that completes synchronously and processCompletedTransitions for one that completes later; TypeScript bitmap-net-executor.ts and precompiled-net-executor.ts: processCompletedTransitions). The produced tokens are the emission of the completion, the tokens the action produced at completion (EXEC-020); tokens it published before (IO-015) are deposited by a publish step and are not listed, and only Rust offers a publication, whose event has no list. Line 1 also fixes the order of the TokenAdded events across places, emission order, which EVT-011 leaves to this block. An executor that lists no produced tokens breaks line 1 and meets the first block (EVT_007_payload_mutant_producedEmpty)."
          "Line 2 is the second quoted sentence. Java and TypeScript deposit a timeout outcome through the same completion code, so the event lists the timeout outcome's tokens. An executor that lists none breaks line 2 (EVT_007_payload_mutant_timeoutEmpty). Like the reference, both executors of Java and TypeScript run only the join-relay check on a timeout outcome and do not validate it against the output spec (ruling D24 (a); TransitionContext.isDetachedForTimeout in processCompletedTransitions), so every timeout outcome the check accepts is deposited and listed. An executor that also validated it and failed the firing (the behaviour RD-01 recorded) would emit no TransitionCompleted for that firing; line 2 does not catch it, EXEC-021, EXEC-022 and IO-013 do."
          "Line 3 is the third quoted sentence and AC2, as a bound (ruling D38 (a)): the duration is never more than the firing-clock time between the start of the firing and the deposit, and zero is allowed. Java measures clockNanos() at processing minus the reading recorded in the in-flight record, which is taken after the action was invoked (BitmapNetExecutor.fireTransition stores it in the InFlightTransition record, PrecompiledNetExecutor.fireTransition in inFlightStartNanos, and processCompletedTransitions subtracts it), and reports Duration.ZERO for every synchronously completed action (processSyncOutput in both Java executors); TypeScript reports nowMs() at processing minus the reading taken when it fired the transition (the startMs of the in-flight record in bitmap-net-executor.ts and inFlightStartMs in precompiled-net-executor.ts, both set in fireTransition, and durationMs in processCompletedTransitions). The reference reports the difference of the two readings exactly. An executor that reports the reading since clock zero breaks line 3 (EVT_007_payload_mutant_durationFromZero). A duration above zero is not required (ruling D38 (a)): the firing clock may return the same reading twice (TIME-015), and the reference reports zero for an action that returns at the reading it started at (EVT_007_payload_allows_zeroDuration)."
          "As in the first block: the timestamp is not modelled, the defensive copy is EVT-001's, and the shared assumptions (store enabled, no host callback throws inside a deposit, events are values, distinct names) apply."
          "The Java and TypeScript half of the test derivation (TransitionCompleted lists the produced token with a duration no larger than the clock advance) is EVT_007_payload_nonvacuous: the run starts at reading 2, t starts at 2, its action writes 50 to place 1 and returns at reading 5, and TransitionCompleted t lists (1, 50) with duration 3; when instead its budget runs out at reading 6, TransitionCompleted t lists (2, 7) and (2, 8), the timeout outcome, with duration 4."
  signoff "2026-11-13 85d1a27d515969e0 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C H i evs,
      (on (fun s s' => E.step C H s (.commit i) evs s'), shall (fun s _ =>
        ∀ f e, s.fl.find? (·.id == i) = some f → f.out = some (.ok e) →
          ∃ d, evs.filter (fun x => !x.isLog) =
            addedEvs e ++ [.transitionCompleted f.t.core.name e d])) ∧
      (on (fun s s' => E.step C H s (.tdeposit i) evs s'), shall (fun s _ =>
        ∀ f e, s.fl.find? (·.id == i) = some f → f.out = some (.timedOut e) →
          ∀ m pl d, NetEvent.transitionCompleted m pl d ∈ evs → pl = e)) ∧
      (∀ l, l = .commit i ∨ l = .tdeposit i →
        on (fun s s' => E.step C H s l evs s'), shall (fun s _ =>
          ∀ f, s.fl.find? (·.id == i) = some f →
            ∀ m pl d, NetEvent.transitionCompleted m pl d ∈ evs → d ≤ s.now - f.start))

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_007_payload : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (H : List (NetEvent N T)) (i : ℕ) (evs : List (NetEvent N T)),
    (on fun s s' => E.step C H s (XLbl.commit i) evs s', shall fun s x =>
        ∀ (f : Firing N T) (e : List (N × T)),
          List.find? (fun x => x.id == i) s.fl = some f →
            f.out = some (Outcome.ok e) →
              ∃ d,
                List.filter (fun x => !x.isLog) evs = addedEvs e ++ [NetEvent.transitionCompleted f.t.core.name e d]) ∧
      (on fun s s' => E.step C H s (XLbl.tdeposit i) evs s', shall fun s x =>
          ∀ (f : Firing N T) (e : List (N × T)),
            List.find? (fun x => x.id == i) s.fl = some f →
              f.out = some (Outcome.timedOut e) →
                ∀ (m : String) (pl : List (N × T)) (d : ℕ), NetEvent.transitionCompleted m pl d ∈ evs → pl = e) ∧
        ∀ (l : XLbl N T),
          l = XLbl.commit i ∨ l = XLbl.tdeposit i →
            on fun s s' => E.step C H s l evs s', shall fun s x =>
              ∀ (f : Firing N T),
                List.find? (fun x => x.id == i) s.fl = some f →
                  ∀ (m : String) (pl : List (N × T)) (d : ℕ),
                    NetEvent.transitionCompleted m pl d ∈ evs → d ≤ s.now - f.start
-/
#guard_msgs in #print EVT_007_payload

/-! ## The lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_007` alone: the deposit of an admitted completion emits, log messages aside,
`TokenAdded` events and then one `TransitionCompleted` naming the firing's transition. -/
def evt007_line1 (E : EvExec N T) : Prop :=
  ∀ C H i evs, on (fun s s' => E.step C H s (.commit i) evs s'), shall (fun s _ =>
    ∀ f, s.fl.find? (·.id == i) = some f →
      ∃ (as : List (NetEvent _ _)) (pl : List (_ × _)) (d : Nat),
              evs.filter (fun e => !e.isLog) =
          as ++ [.transitionCompleted f.t.core.name pl d] ∧
        ∀ e ∈ as, e.kind = .tokenAdded)

/-- Line 2 of `EVT_007` alone: nothing but a commit or a timeout deposit emits a
`TransitionCompleted`, neither the boot nor another step. -/
def evt007_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionCompleted) ∧
    ∀ H l evs, (∀ i, l ≠ .commit i) → (∀ i, l ≠ .tdeposit i) →
      on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
        ∀ e ∈ evs, e.kind ≠ .transitionCompleted)

/-- Line 3 of `EVT_007` alone: a timeout deposit emits no `TransitionCompleted`, or one only,
naming the firing's transition, as its last event other than log messages. -/
def evt007_line3 (E : EvExec N T) : Prop :=
  ∀ C H i evs, on (fun s s' => E.step C H s (.tdeposit i) evs s'), shall (fun s _ =>
    ∀ f, s.fl.find? (·.id == i) = some f →
      (∀ e ∈ evs, e.kind ≠ .transitionCompleted) ∨
      ∃ (pre : List (NetEvent _ _)) (pl : List (_ × _)) (d : Nat),
              evs.filter (fun e => !e.isLog) =
          pre ++ [.transitionCompleted f.t.core.name pl d] ∧
        ∀ e ∈ pre, e.kind ≠ .transitionCompleted)

omit [Ord N] in
/-- `EVT_007` is its three lines. -/
theorem evt007_iff (E : EvExec N T) :
    EVT_007 E ↔ evt007_line1 E ∧ evt007_line2 E ∧ evt007_line3 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2 C⟩⟩

/-- Lines 2 and 3 of `EVT_007`: what an executor keeps that breaks line 1 only. -/
def evt007_but1 (E : EvExec N T) : Prop := evt007_line2 E ∧ evt007_line3 E

/-- Lines 1 and 3 of `EVT_007`: what an executor keeps that breaks line 2 only. -/
def evt007_but2 (E : EvExec N T) : Prop := evt007_line1 E ∧ evt007_line3 E

/-- Lines 1 and 2 of `EVT_007`: what an executor keeps that breaks line 3 only. -/
def evt007_but3 (E : EvExec N T) : Prop := evt007_line1 E ∧ evt007_line2 E

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
omit [DecidableEq N] [Ord N] in
/-- `TokenAdded` events are not log messages. -/
theorem filter_nonLog_addedEvs (e : List (N × T)) :
    (addedEvs e).filter (fun x : NetEvent N T => !x.isLog) = addedEvs e := by
  rw [List.filter_eq_self]
  intro x hx
  simp [NetEvent.isLog, kind_of_mem_addedEvs hx]

omit [DecidableEq N] [Ord N] in
/-- The `TokenAdded` events of an emission followed by a `TransitionCompleted`, with log messages
filtered out, are themselves. -/
theorem filter_nonLog_added_completed (e : List (N × T)) (n : String) (pl : List (N × T))
    (d : Nat) :
    (addedEvs e ++ [NetEvent.transitionCompleted n pl d]).filter (fun x => !x.isLog) =
      addedEvs e ++ [.transitionCompleted n pl d] := by
  rw [List.filter_append, filter_nonLog_addedEvs]
  simp [NetEvent.isLog, NetEvent.kind]

omit [DecidableEq N] [Ord N] in
/-- The `TokenAdded` events of an emission followed by one `TransitionCompleted` meet the shape of
line 1. -/
theorem evt007_shape1 (e : List (N × T)) (n : String) (pl : List (N × T)) (d : Nat) :
    ∃ (as : List (NetEvent N T)) (pl' : List (N × T)) (d' : Nat),
      (addedEvs e ++ [NetEvent.transitionCompleted n pl d]).filter
        (fun x => !x.isLog) = as ++ [.transitionCompleted n pl' d'] ∧
      ∀ x ∈ as, x.kind = .tokenAdded :=
  ⟨addedEvs e, pl, d, filter_nonLog_added_completed e n pl d,
    fun _ hx => kind_of_mem_addedEvs hx⟩

/-- The events of a reference commit step: the `TokenAdded` events of the emission, then
`TransitionCompleted` with the emission and the time since the start. -/
theorem refEmitW_commit (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s : XSt N T}
    {i : Nat} {f : Firing N T} {e : List (N × T)} (hf : s.fl.find? (·.id == i) = some f)
    (ho : f.out = some (.ok e)) (s' : XSt N T) :
    refEmitW P C H s (.commit i) s' =
      addedEvs e ++ [.transitionCompleted f.t.core.name e (s.now - f.start)] := by
  simp only [refEmitW, hf, ho]

/-- The events of a reference timeout deposit: under the Rust emission an `ActionTimedOut`, then
the `TokenAdded` events of the timeout outcome, then under the Java and TypeScript emission a
`TransitionCompleted` with the outcome and the time since the start. -/
theorem refEmitW_tdeposit (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s : XSt N T}
    {i : Nat} {f : Firing N T} {e : List (N × T)} (hf : s.fl.find? (·.id == i) = some f)
    (ho : f.out = some (.timedOut e)) (s' : XSt N T) :
    refEmitW P C H s (.tdeposit i) s' =
      (if P.atoAtExpire then [] else [.actionTimedOut f.t.core.name]) ++ addedEvs e ++
        (if P.completedAfterTimeout
         then [.transitionCompleted f.t.core.name e (s.now - f.start)] else []) := by
  simp only [refEmitW, hf, ho]

omit [DecidableEq N] [Ord N] in
/-- Two lookups of one identity find one firing. -/
theorem find_unique {s : XSt N T} {i : Nat} {f g : Firing N T}
    (hf : s.fl.find? (·.id == i) = some f) (hg : s.fl.find? (·.id == i) = some g) : g = f :=
  Option.some.inj (hg.symm.trans hf)

/-- Line 1 holds of the events a reference commit step emits. -/
theorem refCommit_line1 (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s s' : XSt N T}
    {i : Nat} (hx : xstep C s (.commit i) = some s') :
    ∀ f, s.fl.find? (·.id == i) = some f →
      ∃ (as : List (NetEvent N T)) (pl : List (N × T)) (d : Nat),
        (refEmitW P C H s (.commit i) s').filter (fun e => !e.isLog) =
          as ++ [.transitionCompleted f.t.core.name pl d] ∧
        ∀ e ∈ as, e.kind = .tokenAdded := by
  obtain ⟨f0, e, hf0, ho, -⟩ := commitStep_some (P := refXPol) hx
  intro f hf
  obtain rfl := find_unique hf0 hf
  rw [refEmitW_commit P C H hf0 ho]
  exact evt007_shape1 _ _ _ _

omit [DecidableEq N] [Ord N] in
/-- The events before the optional `TransitionCompleted` of a timeout deposit are an optional
`ActionTimedOut` and `TokenAdded` events: none is a log message or a `TransitionCompleted`. -/
theorem tdeposit_head_kinds (b : Bool) (n : String) (e : List (N × T)) :
    ∀ x ∈ ((if b then [] else [NetEvent.actionTimedOut n]) ++ addedEvs e : List (NetEvent N T)),
      x.isLog = false ∧ x.kind ≠ .transitionCompleted := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · cases b
    · simp only [Bool.false_eq_true, if_false, List.mem_singleton] at h
      subst h; simp [NetEvent.isLog, NetEvent.kind]
    · simp at h
  · simp [NetEvent.isLog, kind_of_mem_addedEvs h]

/-- Line 3 holds of the events a reference timeout deposit emits, under either emission. -/
theorem refTdeposit_line3 (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s s' : XSt N T}
    {i : Nat} (hx : xstep C s (.tdeposit i) = some s') :
    ∀ f, s.fl.find? (·.id == i) = some f →
      (∀ e ∈ refEmitW P C H s (.tdeposit i) s', e.kind ≠ .transitionCompleted) ∨
      ∃ (pre : List (NetEvent N T)) (pl : List (N × T)) (d : Nat),
        (refEmitW P C H s (.tdeposit i) s').filter (fun e => !e.isLog) =
          pre ++ [.transitionCompleted f.t.core.name pl d] ∧
        ∀ e ∈ pre, e.kind ≠ .transitionCompleted := by
  obtain ⟨f0, e, hf0, ho, -⟩ := tdepositStep_some hx
  intro f hf
  obtain rfl := find_unique hf0 hf
  rw [refEmitW_tdeposit P C H hf0 ho]
  have hk := tdeposit_head_kinds (T := T) P.atoAtExpire f.t.core.name e
  cases P.completedAfterTimeout
  · left
    intro x hx
    simp only [Bool.false_eq_true, if_false, List.append_nil] at hx
    exact (hk x hx).2
  · right
    refine ⟨_, e, s.now - f.start, ?_, fun x hx => (hk x hx).2⟩
    simp only [if_true]
    rw [List.filter_append, List.filter_eq_self.2 (fun x hx => by simp [(hk x hx).1])]
    simp [NetEvent.isLog, NetEvent.kind]

/-- Only a commit or a timeout deposit emits a `TransitionCompleted` in the reference. -/
theorem refEmitW_noCompleted (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (h1 : ∀ i, l ≠ .commit i) (h2 : ∀ i, l ≠ .tdeposit i) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionCompleted := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | commit i => exact h1 i rfl
  | tdeposit i => exact h2 i rfl
  | _ => simp [lblKinds] at this

/-- The reference boot emits no `TransitionCompleted`. -/
theorem refBoot_noCompleted (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .transitionCompleted := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- The reference meets `EVT_007` under every emission variant. -/
theorem evt007_ref (P : EvPol) : EVT_007 (refEvExec (N := N) (T := T) P) :=
  (evt007_iff _).2
    ⟨fun C H i evs s s' hs => by
      obtain ⟨hx, rfl⟩ := hs
      exact refCommit_line1 P C H hx,
     fun C => ⟨refBoot_noCompleted P C, fun H l evs h1 h2 s s' hs => by
      obtain ⟨-, rfl⟩ := hs
      exact refEmitW_noCompleted P C H s h1 h2 s'⟩,
     fun C H i evs s s' hs => by
      obtain ⟨hx, rfl⟩ := hs
      exact refTdeposit_line3 P C H hx⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-007: a completion's
deposit reports its tokens and then one completion naming the transition, a timeout deposit
reports its tokens and then one completion, and no other step reports a completion. -/
@[evidence holds EVT_007]
theorem EVT_007_reference : EVT_007 (refEvExec (N := N) (T := T) polJT) := evt007_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-007 too, although its
timeout deposit reports no completion at all. -/
@[evidence holds EVT_007]
theorem EVT_007_rust : EVT_007 (refEvExec (N := N) (T := T) polRust) := evt007_ref polRust

/-- The companion holds of the reference under every emission variant. -/
theorem evt007_payload_ref (P : EvPol) : EVT_007_payload (refEvExec (N := N) (T := T) P) := by
  intro C H i evs
  refine ⟨fun s s' hs => ?_, fun s s' hs => ?_, fun l hl s s' hs => ?_⟩
  · obtain ⟨hx, rfl⟩ := hs
    intro f e hf ho
    obtain ⟨f0, e0, hf0, ho0, -⟩ := commitStep_some (P := refXPol) hx
    obtain rfl := find_unique hf0 hf
    rw [ho0] at ho
    obtain rfl : e0 = e := by injection ho with h; injection h
    exact ⟨_, by rw [refEmitW_commit P C H hf0 ho0, filter_nonLog_added_completed]⟩
  · obtain ⟨hx, rfl⟩ := hs
    intro f e hf ho m pl d hm
    obtain ⟨f0, e0, hf0, ho0, -⟩ := tdepositStep_some hx
    obtain rfl := find_unique hf0 hf
    rw [ho0] at ho
    obtain rfl : e0 = e := by injection ho with h; injection h
    rw [refEmitW_tdeposit P C H hf0 ho0] at hm
    rcases List.mem_append.1 hm with h | h
    · have := (tdeposit_head_kinds (T := T) P.atoAtExpire f.t.core.name e0 _ h).2
      simp [NetEvent.kind] at this
    · split at h
      · simp only [List.mem_singleton, NetEvent.transitionCompleted.injEq] at h
        exact h.2.1
      · cases h
  · obtain ⟨hx, rfl⟩ := hs
    intro f hf m pl d hm
    rcases hl with rfl | rfl
    · obtain ⟨f0, e0, hf0, ho0, -⟩ := commitStep_some (P := refXPol) hx
      obtain rfl := find_unique hf0 hf
      rw [refEmitW_commit P C H hf0 ho0] at hm
      rcases List.mem_append.1 hm with h | h
      · have := kind_of_mem_addedEvs h
        simp [NetEvent.kind] at this
      · simp only [List.mem_singleton, NetEvent.transitionCompleted.injEq] at h
        omega
    · obtain ⟨f0, e0, hf0, ho0, -⟩ := tdepositStep_some hx
      obtain rfl := find_unique hf0 hf
      rw [refEmitW_tdeposit P C H hf0 ho0] at hm
      rcases List.mem_append.1 hm with h | h
      · have := (tdeposit_head_kinds (T := T) P.atoAtExpire f.t.core.name e0 _ h).2
        simp [NetEvent.kind] at this
      · split at h
        · simp only [List.mem_singleton, NetEvent.transitionCompleted.injEq] at h
          omega
        · cases h

/-- ✓ The reference executor with the Java and TypeScript emission meets the companion: a
completion lists the tokens its deposit reports, in the same order, a timeout deposit's
completion lists the timeout outcome, and the duration is the time since the start. -/
@[evidence holds EVT_007_payload]
theorem EVT_007_payload_reference : EVT_007_payload (refEvExec (N := N) (T := T) polJT) :=
  evt007_payload_ref polJT

/-- ✓ The reference with the Rust and Python emission meets the companion too; after a timeout
outcome it emits no completion, so line 2 holds there with nothing to check. -/
@[evidence holds EVT_007_payload]
theorem EVT_007_payload_rust : EVT_007_payload (refEvExec (N := N) (T := T) polRust) :=
  evt007_payload_ref polRust

end Reference

/-! ## The worked example -/

/-- Transition `t`: takes exactly two tokens from place 0; output spec `Xor(Place(1),
Timeout(d, ForwardInput(0, 2)))`. -/
def evt007_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .exactly 2⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.xor (.place 1) (.timeout (.forward 0 2))) }

/-- The configuration of the example: places 0 to 2 and transition `t`. Output validation
accepts a completion only if it produced a token in place 1; the join-relay check accepts
everything; any emission may be the timeout outcome. -/
def evt007_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [evt007_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ d => d.contains 1, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => true, res := 0 }

/-- The initial marking: 7 and 8 in place 0. -/
def evt007_m0 : QMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- One cycle up to the asynchronous start of `t`. -/
def evt007_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- The run starts at reading 2; `t`'s action writes 50 to place 1 and returns 3 units later. -/
def evt007_returned : Option (XSt Nat Nat) :=
  xrun evt007_cfg (xinit evt007_m0 2) (evt007_pre ++ [.delay 3, .write 0 1 50, .ret 0 true, .endPass])

/-- As `evt007_returned`, but the action returns at the reading it started at. -/
def evt007_returned0 : Option (XSt Nat Nat) :=
  xrun evt007_cfg (xinit evt007_m0 2) (evt007_pre ++ [.write 0 1 50, .ret 0 true, .endPass])

/-- `t`'s budget runs out 4 units after its start, with timeout outcome 7 and 8 for place 2. -/
def evt007_expired : Option (XSt Nat Nat) :=
  xrun evt007_cfg (xinit evt007_m0 2)
    (evt007_pre ++ [.delay 4, .expire 0 [(2, 7), (2, 8)], .endPass])

/-- `t`'s action returns the token 5 for place 2 only, which validation rejects. -/
def evt007_rejected : Option (XSt Nat Nat) :=
  xrun evt007_cfg (xinit evt007_m0 2) (evt007_pre ++ [.write 0 2 5, .ret 0 true, .endPass])

/-- `t`'s action writes 50 to place 1 and publishes it while it still runs; the loop reaches the
publications. -/
def evt007_flushed : Option (XSt Nat Nat) :=
  xrun evt007_cfg (xinit evt007_m0 2)
    (evt007_pre ++ [.write 0 1 50, .flush 0, .endPass, .endCompletions])

/-- Read a decided fact off a step of the reference: the step exists and its events, under
variant `P`, pass `q`. -/
theorem evt007_check (P : EvPol) (C : Cfg Nat Nat) (o : Option (XSt Nat Nat)) (l : XLbl Nat Nat)
    (q : XSt Nat Nat → List (NetEvent Nat Nat) → Bool)
    (h : (o.bind fun s => (xstep C s l).map fun s' => q s (refEmitW P C [] s l s')) = some true) :
    ∃ s s' evs, (refEvExec P).step C [] s l evs s' ∧ q s evs = true := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := C) (o := o) (l := l)
    (p := fun s s' => q s (refEmitW P C [] s l s')) h
  exact ⟨s, s', _, ⟨hs, rfl⟩, hp⟩

/-- ✓ All three lines are exercised by the reference. The run starts at reading 2 and `t` starts
there. When `t`'s action writes 50 to place 1 and returns 3 units later, the deposit emits
`TokenAdded` 1 50 and then `TransitionCompleted t`. When instead its budget runs out, the timeout
deposit emits `TokenAdded` 2 7, `TokenAdded` 2 8 and then `TransitionCompleted t` under the Java
and TypeScript emission, and `ActionTimedOut t` and the two `TokenAdded` events, with no
completion, under the Rust emission. A completion that validation rejects (5 for place 2) is
settled by a fail step that emits events, none a completion, and so is the boot of the run. -/
@[evidence nonvacuous EVT_007]
theorem EVT_007_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.commit 0) evs s' ∧
      evs = [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 3]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.tdeposit 0) evs s' ∧
      evs = [.tokenAdded 2 7, .tokenAdded 2 8, .transitionCompleted "t" [(2, 7), (2, 8)] 4]) ∧
    (∃ s s' evs, (refEvExec polRust).step evt007_cfg [] s (.tdeposit 0) evs s' ∧
      evs = [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.fail 0) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .transitionCompleted) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt007_cfg evt007_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt007_cfg evt007_m0,
        e.kind ≠ .transitionCompleted) := by
  refine ⟨?_, ?_, ?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_returned (.commit 0)
      (fun _ evs => evs == [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 3])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, beq_iff_eq.1 hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_expired (.tdeposit 0)
      (fun _ evs =>
        evs == [.tokenAdded 2 7, .tokenAdded 2 8, .transitionCompleted "t" [(2, 7), (2, 8)] 4])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, beq_iff_eq.1 hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polRust evt007_cfg evt007_expired (.tdeposit 0)
      (fun _ evs => evs == [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, beq_iff_eq.1 hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_rejected (.fail 0)
      (fun _ evs => !evs.isEmpty && evs.all fun e => e.kind != .transitionCompleted)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩

/-- ✓ The produced tokens and the duration, on the example. `t` starts at reading 2, its action
writes 50 to place 1 and returns at reading 5: `TransitionCompleted t` lists (1, 50) with
duration 3. When instead its budget runs out at reading 6, the completion lists the timeout
outcome (2, 7) and (2, 8) with duration 4. -/
@[evidence nonvacuous EVT_007_payload]
theorem EVT_007_payload_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.commit 0) evs s' ∧
      evs = [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 3] ∧
      (s.fl.find? (·.id == 0)).map (·.start) = some 2 ∧
      s.now = 5) ∧
    (∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.tdeposit 0) evs s' ∧
      evs = [.tokenAdded 2 7, .tokenAdded 2 8, .transitionCompleted "t" [(2, 7), (2, 8)] 4] ∧
      (s.fl.find? (·.id == 0)).map (·.start) = some 2 ∧
      s.now = 6) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_returned (.commit 0)
      (fun s evs => evs == [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 3] &&
        (s.fl.find? (·.id == 0)).map (·.start) == some 2 && s.now == 5)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_expired (.tdeposit 0)
      (fun s evs =>
        evs == [.tokenAdded 2 7, .tokenAdded 2 8, .transitionCompleted "t" [(2, 7), (2, 8)] 4] &&
        (s.fl.find? (·.id == 0)).map (·.start) == some 2 && s.now == 6)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1.1, hp.1.2, hp.2⟩

/-! ## Allowed: both readings of a timeout deposit, and a publication after the completion -/

/-- ✓ EVT-007 allows both readings of a timeout deposit (ruling D65 (a)). The reference meets
EVT-007 under both emissions, and at the same timeout deposit of the example (`t`'s budget runs
out, 7 and 8 go to place 2) the Java and TypeScript emission reports `TransitionCompleted t` and
the Rust emission reports no completion. -/
@[evidence allows EVT_007]
theorem EVT_007_allows_timeoutEither :
    EVT_007 (refEvExec (N := Nat) (T := Nat) polJT) ∧
    EVT_007 (refEvExec (N := Nat) (T := Nat) polRust) ∧
    ∃ s s', xstep evt007_cfg s (.tdeposit 0) = some s' ∧
      NetEvent.transitionCompleted "t" [(2, 7), (2, 8)] 4 ∈
        refEmitW polJT evt007_cfg [] s (.tdeposit 0) s' ∧
      ∀ e ∈ refEmitW polRust evt007_cfg [] s (.tdeposit 0) s', e.kind ≠ .transitionCompleted := by
  refine ⟨evt007_ref polJT, evt007_ref polRust, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_expired)
    (l := .tdeposit 0)
    (p := fun s s' =>
      (refEmitW polJT evt007_cfg [] s (.tdeposit 0) s').contains
        (.transitionCompleted "t" [(2, 7), (2, 8)] 4) &&
      (refEmitW polRust evt007_cfg [] s (.tdeposit 0) s').all
        fun e => e.kind != .transitionCompleted)
    (by decide +kernel)
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at hp
  exact ⟨s, s', hs, hp.1, hp.2⟩

/-- The labels of the publication example: `t`'s action writes 50 to place 1 and publishes it,
writes 51, and returns; the loop commits the completion, then deposits the publication. -/
def evt007_pubLabels : List (XLbl Nat Nat) :=
  evt007_pre ++ [.write 0 1 50, .flush 0, .write 0 1 51, .ret 0 true, .endPass, .commit 0,
    .endCompletions, .publish 0]

/-- ✓ EVT-007 allows a token the action published before it completed to be reported after the
completion (ruling D17, [EXEC-020]). In the example `t`'s action publishes 50 for place 1, then
writes 51 and returns. The loop settles completions before publications, so the trace reports
`TokenAdded` 1 51, then `TransitionCompleted t` listing (1, 51) only, and only then `TokenAdded`
1 50. The reference meets EVT-007 all the same. -/
@[evidence allows EVT_007]
theorem EVT_007_allows_publishedAfter :
    EVT_007 (refEvExec (N := Nat) (T := Nat) polRust) ∧
    Trace (refEvExec polRust) evt007_cfg evt007_m0 2
      [.executionStarted, .markingSnapshot [(0, [7, 8])], .transitionEnabled "t",
       .tokenRemoved 0 7, .tokenRemoved 0 8, .transitionStarted "t" [(0, 7), (0, 8)], .tokenAdded 1 51,
       .transitionCompleted "t" [(1, 51)] 0, .tokenAdded 1 50] :=
  ⟨evt007_ref polRust, refTrace_trace polRust (ls := evt007_pubLabels) (by decide +kernel)⟩

/-- ✓ The companion allows a duration of zero. In the example `t` starts at reading 2 and its
action returns at the same reading, so the reference reports `TransitionCompleted t` listing
(1, 50) with duration 0, and it meets the companion: a duration above zero is not required. -/
@[evidence allows EVT_007_payload]
theorem EVT_007_payload_allows_zeroDuration :
    EVT_007_payload (refEvExec (N := Nat) (T := Nat) polJT) ∧
    ∃ s s' evs, (refEvExec polJT).step evt007_cfg [] s (.commit 0) evs s' ∧
      evs = [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 0] := by
  refine ⟨evt007_payload_ref polJT, ?_⟩
  obtain ⟨s, s', evs, hs, hp⟩ := evt007_check polJT evt007_cfg evt007_returned0 (.commit 0)
    (fun _ evs => evs == [.tokenAdded 1 50, .transitionCompleted "t" [(1, 50)] 0])
    (by decide +kernel)
  exact ⟨s, s', evs, hs, beq_iff_eq.1 hp⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- An executor that emits as the Java and TypeScript reference at a commit step keeps line 1,
whatever its boot. -/
theorem evt007_line1_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s i s', emit C H s (.commit i) s' = refEmitW polJT C H s (.commit i) s') :
    evt007_line1 (emitExec boot emit) := by
  intro C H i evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact refCommit_line1 polJT C H hx

/-- An executor with the Java and TypeScript boot that emits as the reference at every step but a
commit or a timeout deposit keeps line 2. -/
theorem evt007_line2_of
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s l s', (∀ i, l ≠ .commit i) → (∀ i, l ≠ .tdeposit i) →
      emit C H s l s' = refEmitW polJT C H s l s') :
    evt007_line2 (emitExec (refBoot polJT) emit) := by
  intro C
  refine ⟨refBoot_noCompleted polJT C, fun H l evs h1 h2 s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  rw [he C H s l s' h1 h2]
  exact refEmitW_noCompleted polJT C H s h1 h2 s'

/-- An executor that emits as the Java and TypeScript reference at a timeout deposit keeps line 3,
whatever its boot. -/
theorem evt007_line3_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s i s', emit C H s (.tdeposit i) s' = refEmitW polJT C H s (.tdeposit i) s') :
    evt007_line3 (emitExec boot emit) := by
  intro C H i evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact refTdeposit_line3 polJT C H hx

/-- The Java and TypeScript emission with the events of a commit step replaced by `g C s i`. -/
def evt007_atCommit (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i => g C s i
  | _ => refEmitW polJT C H s l s'

/-- An executor that only changes what a commit step emits keeps lines 2 and 3. -/
theorem evt007_atCommit_but1 (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) :
    evt007_but1 (emitExec (refBoot polJT) (evt007_atCommit g)) := by
  refine ⟨evt007_line2_of fun C H s l s' h1 _ => ?_, evt007_line3_of fun _ _ _ _ _ => rfl⟩
  cases l with
  | commit i => exact absurd rfl (h1 i)
  | _ => rfl

/-- The Java and TypeScript emission with the events of a timeout deposit replaced by
`g C s i`. -/
def evt007_atTdeposit (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .tdeposit i => g C s i
  | _ => refEmitW polJT C H s l s'

/-- An executor that only changes what a timeout deposit emits keeps lines 1 and 2. -/
theorem evt007_atTdeposit_but3 (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) :
    evt007_but3 (emitExec (refBoot polJT) (evt007_atTdeposit g)) := by
  refine ⟨evt007_line1_of fun _ _ _ _ _ => rfl, evt007_line2_of fun C H s l s' _ h2 => ?_⟩
  cases l with
  | tdeposit i => exact absurd rfl (h2 i)
  | _ => rfl

/-- The Java and TypeScript emission with `extra C s l` appended to the events of every step that
is neither a commit nor a timeout deposit. -/
def evt007_plus (extra : Cfg N T → XSt N T → XLbl N T → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i => refEmitW polJT C H s (.commit i) s'
  | .tdeposit i => refEmitW polJT C H s (.tdeposit i) s'
  | l => refEmitW polJT C H s l s' ++ extra C s l

/-- An executor that only adds events to steps other than a commit or a timeout deposit keeps
lines 1 and 3. -/
theorem evt007_plus_but2 (extra : Cfg N T → XSt N T → XLbl N T → List (NetEvent N T)) :
    evt007_but2 (emitExec (refBoot polJT) (evt007_plus extra)) :=
  ⟨evt007_line1_of fun _ _ _ _ _ => rfl, evt007_line3_of fun _ _ _ _ _ => rfl⟩

/-- The executor that also reports a `TransitionCompleted` at the boot, before any firing, and
otherwise steps and emits as the Java and TypeScript reference. -/
def evt007_bootCompleted : EvExec N T :=
  emitExec (fun C M0 => refBoot polJT C M0 ++ [.transitionCompleted "t" [] 0]) (refEmitW polJT)

/-- The Java and TypeScript emission, with a `TransitionCompleted` at the end of step 1 for the
transition whose failure was the last event before it: the deferred completion of a batch, after
its failed firing was settled. -/
def evt007_lateFailEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .endCompletions =>
    (match H.getLast? with
     | some (.transitionFailed n) => [.transitionCompleted n [] 0]
     | _ => []) ++ refEmitW polJT C H s l s'
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a completion for a failed firing after the fail step settled it. -/
def evt007_completedAfterFail : EvExec N T := emitExec (refBoot polJT) evt007_lateFailEmit

/-- The transition name of the firing with identity `i` in flight in `s`, or the empty name. -/
def evt007_nameOf (s : XSt N T) (i : Nat) : String :=
  match s.fl.find? (·.id == i) with
  | some f => f.t.core.name
  | none => ""

/-- The commit events with the `TransitionCompleted` first, before the deposited tokens. -/
def evt007_firstEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok e) => .transitionCompleted f.t.core.name e (s.now - f.start) :: addedEvs e
    | _ => []
  | none => []

/-- The executor that reports a completion before its deposited tokens. -/
def evt007_first : EvExec N T := emitExec (refBoot polJT) (evt007_atCommit evt007_firstEvs)

/-- The commit events without the `TransitionCompleted`. -/
def evt007_silentEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok e) => addedEvs e
    | _ => []
  | none => []

/-- The executor that deposits a completion and reports no completion. -/
def evt007_silent : EvExec N T := emitExec (refBoot polJT) (evt007_atCommit evt007_silentEvs)

/-- A `TransitionCompleted` with no tokens after the events of a fail step. -/
def evt007_onFailExtra (_C : Cfg N T) (s : XSt N T) (l : XLbl N T) : List (NetEvent N T) :=
  match l with
  | .fail i => [.transitionCompleted (evt007_nameOf s i) [] 0]
  | _ => []

/-- The executor that also reports a failed firing, a rejected completion included, as
completed. -/
def evt007_onFail : EvExec N T := emitExec (refBoot polJT) (evt007_plus evt007_onFailExtra)

/-- A `TransitionCompleted` listing the batch after the events of a publication. -/
def evt007_atPubExtra (_C : Cfg N T) (s : XSt N T) (l : XLbl N T) : List (NetEvent N T) :=
  match l with
  | .publish i =>
    match s.pq with
    | (_, b) :: _ => [.transitionCompleted (evt007_nameOf s i) b 0]
    | [] => []
  | _ => []

/-- The executor that reports a mid-action publication as a completion of its firing. -/
def evt007_atPub : EvExec N T := emitExec (refBoot polJT) (evt007_plus evt007_atPubExtra)

/-- The Java and TypeScript timeout deposit events with the `TransitionCompleted` first. -/
def evt007_tFirstEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) => .transitionCompleted f.t.core.name e (s.now - f.start) :: addedEvs e
    | _ => []
  | none => []

/-- The executor that reports a timeout outcome's completion before its tokens. -/
def evt007_tFirst : EvExec N T := emitExec (refBoot polJT) (evt007_atTdeposit evt007_tFirstEvs)

/-- The Java and TypeScript timeout deposit events with the `TransitionCompleted` twice. -/
def evt007_tTwiceEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) =>
      addedEvs e ++ [.transitionCompleted f.t.core.name e (s.now - f.start),
        .transitionCompleted f.t.core.name e (s.now - f.start)]
    | _ => []
  | none => []

/-- The executor that reports a timeout outcome's completion twice. -/
def evt007_tTwice : EvExec N T := emitExec (refBoot polJT) (evt007_atTdeposit evt007_tTwiceEvs)

omit [DecidableEq N] [Ord N] in
/-- A list whose events other than log messages end with a `TransitionCompleted` has a last such
event of that kind. -/
theorem evt007_lastCompleted {evs as : List (NetEvent N T)} {n : String} {pl : List (N × T)}
    {d : Nat} (h : evs.filter (fun e => !e.isLog) = as ++ [.transitionCompleted n pl d]) :
    ((evs.filter (fun e => !e.isLog)).getLast?.any fun e => e.kind != .transitionCompleted) =
      false := by
  rw [h]; simp [NetEvent.kind]

end Mutants

/-- The test that the last event of `evs` other than a log message is not a
`TransitionCompleted`. -/
def evt007_lastOther (evs : List (NetEvent Nat Nat)) : Bool :=
  (evs.filter (fun e => !e.isLog)).getLast?.any fun e => e.kind != .transitionCompleted

/-- ✗ Reporting a completion before its deposited tokens violates EVT-007 (line 1): when `t`'s
action returns 50 for place 1, the deposit emits `TransitionCompleted t` first and `TokenAdded`
1 50 after it. The executor keeps lines 2 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_completedFirst :
    evt007_but1 (evt007_first (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_first (N := Nat) (T := Nat)) := by
  refine ⟨evt007_atCommit_but1 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_returned)
    (l := .commit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).isSome &&
      evt007_lastOther (evt007_atCommit evt007_firstEvs evt007_cfg [] s (.commit 0) s'))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hp
  obtain ⟨⟨f, hf⟩, hl⟩ := hp
  obtain ⟨as, pl, d, heq, -⟩ := (h evt007_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩ f hf
  have := evt007_lastCompleted heq
  simp only [evt007_lastOther] at hl
  rw [this] at hl
  cases hl

/-- ✗ Depositing a completion without reporting it violates EVT-007 (line 1): when `t`'s action
returns 50 for place 1, the deposit emits `TokenAdded` 1 50 and nothing else. The executor keeps
lines 2 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_silentCommit :
    evt007_but1 (evt007_silent (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_silent (N := Nat) (T := Nat)) := by
  refine ⟨evt007_atCommit_but1 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_returned)
    (l := .commit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).isSome &&
      evt007_lastOther (evt007_atCommit evt007_silentEvs evt007_cfg [] s (.commit 0) s'))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hp
  obtain ⟨⟨f, hf⟩, hl⟩ := hp
  obtain ⟨as, pl, d, heq, -⟩ := (h evt007_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩ f hf
  have := evt007_lastCompleted heq
  simp only [evt007_lastOther] at hl
  rw [this] at hl
  cases hl

/-- ✗ Reporting a rejected completion as completed violates EVT-007 (line 2): `t`'s action
returns 5 for place 2 only, validation rejects it, and the fail step emits `TransitionFailed t`
and then a `TransitionCompleted t` with no tokens. Its commit steps and timeout deposits emit as
the reference, so it keeps lines 1 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_completedOnRejection :
    evt007_but2 (evt007_onFail (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_onFail (N := Nat) (T := Nat)) := by
  refine ⟨evt007_plus_but2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_rejected)
    (l := .fail 0)
    (p := fun s s' => (evt007_plus evt007_onFailExtra evt007_cfg [] s (.fail 0) s').any
      fun e => e.kind == .transitionCompleted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt007_cfg).2.1.2 [] (.fail 0) _ (fun _ => by simp) (fun _ => by simp) s s'
    ⟨hs, rfl⟩ e he hk

/-- ✗ Reporting a completion at the boot violates EVT-007 (line 2): before any transition has
fired, the executor reports `TransitionCompleted t`. Its steps are the reference's, so it keeps
lines 1 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_bootCompleted :
    evt007_but2 (evt007_bootCompleted (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_bootCompleted (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt007_line1_of fun _ _ _ _ _ => rfl, evt007_line3_of fun _ _ _ _ _ => rfl⟩,
    fun h => ?_⟩
  exact (h evt007_cfg).2.1.1 evt007_m0 (.transitionCompleted "t" [] 0)
    (by simp [evt007_bootCompleted, emitExec]) rfl

/-- ✗ Reporting a completion for a failed firing after it was settled violates EVT-007 (line 2):
`t`'s action returns 5 for place 2 only, validation rejects it, the fail step reports
`TransitionFailed t`, and the step that ends step 1 then reports `TransitionCompleted t`, as a
loop that emits a completion for the last firing it polled would. Its commit steps and timeout
deposits emit as the reference, so it keeps lines 1 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_completedAfterFail :
    evt007_but2 (evt007_completedAfterFail (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_completedAfterFail (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt007_line1_of fun _ _ _ _ _ => rfl, evt007_line3_of fun _ _ _ _ _ => rfl⟩,
    fun h => ?_⟩
  obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := evt007_cfg)
    (o := evt007_rejected.bind fun s => xstep evt007_cfg s (.fail 0)) (l := .endCompletions)
    (p := fun _ _ => true) (by decide +kernel)
  exact (h evt007_cfg).2.1.2 [.transitionFailed "t"] .endCompletions _ (fun _ => by simp)
    (fun _ => by simp) s s' ⟨hs, rfl⟩ (.transitionCompleted "t" [] 0)
    (by simp [evt007_lateFailEmit]) rfl

/-- ✗ Reporting a mid-action publication as a completion violates EVT-007 (line 2): `t`'s action
publishes 50 for place 1 while it still runs, and the publication step emits `TokenAdded` 1 50
and then a `TransitionCompleted t` listing it. Its commit steps and timeout deposits emit as the
reference, so it keeps lines 1 and 3. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_completedAtPublish :
    evt007_but2 (evt007_atPub (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_atPub (N := Nat) (T := Nat)) := by
  refine ⟨evt007_plus_but2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_flushed)
    (l := .publish 0)
    (p := fun s s' => (evt007_plus evt007_atPubExtra evt007_cfg [] s (.publish 0) s').any
      fun e => e.kind == .transitionCompleted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt007_cfg).2.1.2 [] (.publish 0) _ (fun _ => by simp) (fun _ => by simp) s s'
    ⟨hs, rfl⟩ e he hk

/-- ✗ Reporting a timeout outcome's completion before its tokens violates EVT-007 (line 3): when
`t`'s budget runs out, the deposit emits `TransitionCompleted t` first and `TokenAdded` 2 7 and
2 8 after it. Its commit steps emit as the reference and no other step reports a completion, so
it keeps lines 1 and 2. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_timeoutCompletedFirst :
    evt007_but3 (evt007_tFirst (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_tFirst (N := Nat) (T := Nat)) := by
  refine ⟨evt007_atTdeposit_but3 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_expired)
    (l := .tdeposit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).isSome &&
      (evt007_atTdeposit evt007_tFirstEvs evt007_cfg [] s (.tdeposit 0) s').any
        (fun e => e.kind == .transitionCompleted) &&
      evt007_lastOther (evt007_atTdeposit evt007_tFirstEvs evt007_cfg [] s (.tdeposit 0) s'))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨f, hf⟩, ⟨e, he, hk⟩⟩, hl⟩ := hp
  rcases (h evt007_cfg).2.2 [] 0 _ s s' ⟨hs, rfl⟩ f hf with hn | ⟨pre, pl, d, heq, -⟩
  · exact hn e he hk
  · have := evt007_lastCompleted heq
    simp only [evt007_lastOther] at hl
    rw [this] at hl
    cases hl

/-- ✗ Reporting a timeout outcome's completion twice violates EVT-007 (line 3): when `t`'s budget
runs out, the deposit emits `TokenAdded` 2 7 and 2 8 and then `TransitionCompleted t` two times.
Both name `t` and come after the tokens, so only "the only one of the deposit" is broken. The
executor keeps lines 1 and 2. -/
@[evidence mutant EVT_007]
theorem EVT_007_mutant_timeoutCompletedTwice :
    evt007_but3 (evt007_tTwice (N := Nat) (T := Nat)) ∧
      ¬ EVT_007 (evt007_tTwice (N := Nat) (T := Nat)) := by
  refine ⟨evt007_atTdeposit_but3 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_expired)
    (l := .tdeposit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).isSome &&
      ((evt007_atTdeposit evt007_tTwiceEvs evt007_cfg [] s (.tdeposit 0) s').filter
        (fun e => !e.isLog)).dropLast.any
        (fun e => e.kind == .transitionCompleted))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨f, hf⟩, ⟨e, he, hk⟩⟩ := hp
  rcases (h evt007_cfg).2.2 [] 0 _ s s' ⟨hs, rfl⟩ f hf with hn | ⟨pre, pl, d, heq, hpre⟩
  · exact hn e (List.mem_of_mem_filter (List.mem_of_mem_dropLast he)) hk
  · rw [heq, List.dropLast_concat] at he
    exact hpre e he hk

/-! ## Wrong executors of the companion: right shape, wrong payload -/

section PayloadMutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Rewrite the produced tokens and the duration of a `TransitionCompleted` event with `g`; every
other event stays. -/
def evt007_repay (g : List (N × T) → Nat → List (N × T) × Nat) : NetEvent N T → NetEvent N T
  | .transitionCompleted n pl d => .transitionCompleted n (g pl d).1 (g pl d).2
  | e => e

omit [DecidableEq N] [Ord N] in
/-- Rewriting the payload keeps the kind. -/
theorem evt007_repay_kind (g : List (N × T) → Nat → List (N × T) × Nat) (e : NetEvent N T) :
    (evt007_repay g e).kind = e.kind := by
  cases e <;> rfl

omit [DecidableEq N] [Ord N] in
/-- Rewriting the payload keeps which events are log messages. -/
theorem evt007_repay_isLog (g : List (N × T) → Nat → List (N × T) × Nat) :
    (fun x : NetEvent N T => !x.isLog) ∘ evt007_repay g = fun x => !x.isLog := by
  funext e
  simp [NetEvent.isLog, evt007_repay_kind]

omit [DecidableEq N] [Ord N] in
/-- Rewriting the payload commutes with filtering out log messages. -/
theorem evt007_repay_filter (g : List (N × T) → Nat → List (N × T) × Nat)
    (evs : List (NetEvent N T)) :
    (evs.map (evt007_repay g)).filter (fun x => !x.isLog) =
      (evs.filter fun x => !x.isLog).map (evt007_repay g) := by
  rw [List.filter_map, evt007_repay_isLog]

/-- The Java and TypeScript emission with the payload of every `TransitionCompleted` rewritten by
`g s l`, which may read the source state and the label. -/
def evt007_repayEmit (g : XSt N T → XLbl N T → List (N × T) → Nat → List (N × T) × Nat)
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) :
    List (NetEvent N T) :=
  (refEmitW polJT C H s l s').map (evt007_repay (g s l))

/-- An executor that only rewrites the payload of the completions meets the first block. -/
theorem evt007_repay_meets (g : XSt N T → XLbl N T → List (N × T) → Nat → List (N × T) × Nat) :
    EVT_007 (emitExec (refBoot polJT) (evt007_repayEmit g)) := by
  have hr := evt007_ref (N := N) (T := T) polJT
  refine (evt007_iff _).2 ⟨fun C H i evs s s' hs => ?_, fun C => ⟨refBoot_noCompleted polJT C,
    fun H l evs h1 h2 s s' hs => ?_⟩, fun C H i evs s s' hs => ?_⟩
  · obtain ⟨hx, rfl⟩ := hs
    intro f hf
    obtain ⟨as, pl, d, heq, has⟩ := (hr C).1 H i _ s s' ⟨hx, rfl⟩ f hf
    refine ⟨as.map (evt007_repay (g s (.commit i))), (g s (.commit i) pl d).1,
      (g s (.commit i) pl d).2, ?_, ?_⟩
    · rw [evt007_repayEmit, evt007_repay_filter, heq, List.map_append]
      rfl
    · intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      rw [evt007_repay_kind]
      exact has a ha
  · obtain ⟨hx, rfl⟩ := hs
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    rw [evt007_repay_kind]
    exact (hr C).2.1.2 H l _ h1 h2 s s' ⟨hx, rfl⟩ a ha
  · obtain ⟨hx, rfl⟩ := hs
    intro f hf
    rcases (hr C).2.2 H i _ s s' ⟨hx, rfl⟩ f hf with hn | ⟨pre, pl, d, heq, hpre⟩
    · left
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      rw [evt007_repay_kind]
      exact hn a ha
    · right
      refine ⟨pre.map (evt007_repay (g s (.tdeposit i))), (g s (.tdeposit i) pl d).1,
        (g s (.tdeposit i) pl d).2, ?_, ?_⟩
      · rw [evt007_repayEmit, evt007_repay_filter, heq, List.map_append]
        rfl
      · intro e he
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
        rw [evt007_repay_kind]
        exact hpre a ha

/-- No tokens listed in the completion of a commit step. -/
def evt007_emptyG (_s : XSt N T) (l : XLbl N T) (pl : List (N × T)) (d : Nat) :
    List (N × T) × Nat :=
  match l with
  | .commit _ => ([], d)
  | _ => (pl, d)

/-- The executor that lists no produced tokens in the completion of an admitted completion. -/
def evt007_producedEmpty : EvExec N T :=
  emitExec (refBoot polJT) (evt007_repayEmit evt007_emptyG)

/-- No tokens listed in the completion of a timeout deposit. -/
def evt007_tEmptyG (_s : XSt N T) (l : XLbl N T) (pl : List (N × T)) (d : Nat) :
    List (N × T) × Nat :=
  match l with
  | .tdeposit _ => ([], d)
  | _ => (pl, d)

/-- The executor that lists no tokens in the completion of a timeout deposit. -/
def evt007_timeoutEmpty : EvExec N T :=
  emitExec (refBoot polJT) (evt007_repayEmit evt007_tEmptyG)

/-- The duration of a commit's completion measured from clock zero: the reading at the
deposit. -/
def evt007_zeroG (s : XSt N T) (l : XLbl N T) (pl : List (N × T)) (d : Nat) :
    List (N × T) × Nat :=
  match l with
  | .commit _ => (pl, s.now)
  | _ => (pl, d)

/-- The executor that reports the reading since clock zero as the duration of a completion. -/
def evt007_fromZero : EvExec N T :=
  emitExec (refBoot polJT) (evt007_repayEmit evt007_zeroG)

end PayloadMutants

/-- ✗ Listing no produced tokens violates the companion (line 1): when `t`'s action returns 50
for place 1, the deposit emits `TokenAdded` 1 50 and then `TransitionCompleted t` with an empty
list. The executor meets the first block of EVT-007, which does not read the list. -/
@[evidence mutant EVT_007_payload]
theorem EVT_007_payload_mutant_producedEmpty :
    EVT_007 (evt007_producedEmpty (N := Nat) (T := Nat)) ∧
      ¬ EVT_007_payload (evt007_producedEmpty (N := Nat) (T := Nat)) := by
  refine ⟨evt007_repay_meets _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_returned)
    (l := .commit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).any fun f => match f.out with
      | some (.ok e) => !e.isEmpty &&
        (((evt007_repayEmit evt007_emptyG evt007_cfg [] s (.commit 0) s').filter
          (fun x => !x.isLog)).getLast?.any fun c => match c with
            | .transitionCompleted _ pl _ => pl.isEmpty
            | _ => false)
      | _ => false)
    (by decide +kernel)
  simp only [Option.any_eq_true] at hp
  obtain ⟨f, hf, hb⟩ := hp
  split at hb
  · rename_i e ho
    obtain ⟨d, hd⟩ := (h evt007_cfg [] 0 _).1 s s' ⟨hs, rfl⟩ f e hf ho
    rw [hd] at hb
    simp at hb
  · cases hb

/-- ✗ Listing no tokens after a timeout outcome violates the companion (line 2): when `t`'s
budget runs out, the deposit emits `TokenAdded` 2 7 and 2 8 and then `TransitionCompleted t`
with an empty list, not the timeout outcome. The executor meets the first block of EVT-007. -/
@[evidence mutant EVT_007_payload]
theorem EVT_007_payload_mutant_timeoutEmpty :
    EVT_007 (evt007_timeoutEmpty (N := Nat) (T := Nat)) ∧
      ¬ EVT_007_payload (evt007_timeoutEmpty (N := Nat) (T := Nat)) := by
  refine ⟨evt007_repay_meets _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_expired)
    (l := .tdeposit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).any fun f => match f.out with
      | some (.timedOut e) => !e.isEmpty &&
        (evt007_repayEmit evt007_tEmptyG evt007_cfg [] s (.tdeposit 0) s').contains
          (.transitionCompleted f.t.core.name [] (s.now - f.start))
      | _ => false)
    (by decide +kernel)
  simp only [Option.any_eq_true] at hp
  obtain ⟨f, hf, hb⟩ := hp
  split at hb
  · rename_i e ho
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.contains_eq_mem, decide_eq_true_eq] at hb
    obtain ⟨hne, hm⟩ := hb
    exact hne ((h evt007_cfg [] 0 _).2.1 s s' ⟨hs, rfl⟩ f e hf ho _ _ _ hm).symm
  · cases hb

/-- ✗ Measuring the duration from clock zero violates the companion (line 3): the run starts at
reading 2, `t` starts there and its action returns at reading 5, and the completion reports a
duration of 5 instead of at most 3. The executor meets the first block of EVT-007. -/
@[evidence mutant EVT_007_payload]
theorem EVT_007_payload_mutant_durationFromZero :
    EVT_007 (evt007_fromZero (N := Nat) (T := Nat)) ∧
      ¬ EVT_007_payload (evt007_fromZero (N := Nat) (T := Nat)) := by
  refine ⟨evt007_repay_meets _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt007_cfg) (o := evt007_returned)
    (l := .commit 0)
    (p := fun s s' => (s.fl.find? (·.id == 0)).any fun f =>
      (evt007_repayEmit evt007_zeroG evt007_cfg [] s (.commit 0) s').any fun c => match c with
        | .transitionCompleted _ _ d => decide (s.now - f.start < d)
        | _ => false)
    (by decide +kernel)
  simp only [Option.any_eq_true, List.any_eq_true] at hp
  obtain ⟨f, hf, c, hc, hb⟩ := hp
  cases c with
  | transitionCompleted m pl d =>
    have := (h evt007_cfg [] 0 _).2.2 (.commit 0) (Or.inl rfl) s s' ⟨hs, rfl⟩ f hf m pl d hc
    simp only [decide_eq_true_eq] at hb
    omega
  | _ => cases hb

end Libpetri.Spec
