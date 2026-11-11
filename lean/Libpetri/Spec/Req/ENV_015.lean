import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# ENV-015: Immediate termination (`spec/06-environment-places.md`)

The immediate termination (`terminateNow()`, Java only, Status Proposed, ruling D47 (c)) over an
abstract executor `R : XRel N T` (glossary `GlossaryExec.lean`), checked against the reference
executor `RefExec` (`Reference/Exec.lean`), whose outside step `terminateNow` sets the lifecycle
mode `stopped`.

The executor enters the stopped mode only by `terminateNow` and never leaves it; `terminateNow`
keeps the marking and the phase, drops the queued events and ends a wait; a stopped executor
accepts no injection request, injects no event, processes no outcome of a firing other than a
synchronous one inside the firing pass, takes no step of its loop at the start of a cycle other
than ending the run, deposits no publication outside a step 1b under way, and does not end the
firing pass with transitions left in its order; the run it ends at the start of a cycle keeps its
marking and drops the queued events.

That the end of the run is offered at once, firings in flight or not, is coverage:
`Env015Covers` below is the conjunct for the consistency theorem's `ExecCoversW5`
(`env015_ref_covers`; the waiting executor `env015_wait` meets every line and fails it).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-015: Immediate Termination -/

requirement ENV_015
  id "ENV-015"
  title "Immediate Termination"
  kind B
  scope "all executors; the operation itself is optional (MAY) and only Java provides it"
  source verbatim "spec/06-environment-places.md"
  quote "An implementation MAY provide an immediate-termination operation (`terminateNow()`) that stops the orchestrator loop **without** waiting for in-flight actions, unlike `close()` ([ENV-013]) which lets them complete."
        "New `inject()` calls are rejected (return error / false), as after [ENV-013]."
        "Queued external events are discarded (completed with false)."
        "The loop stops at the end of its current cycle; it does NOT wait for in-flight actions, and their results are discarded rather than admitted to the marking."
        "In-flight actions keep running where the runtime cannot cancel them ([IO-013]); their consumed tokens are lost ([EXEC-031])."
        "It is an explicit escape hatch and MUST NOT be invoked implicitly by `close()`."
        "The executor is **stopped** from the moment `terminateNow()` takes effect."
        "The call takes effect between two steps of the loop ([EXEC-001]): a call that lands while a step is under way takes effect when that step ends."
        "The current cycle is the one under way when the call takes effect; it ends where the next cycle would start, before its step 1."
        "A request that lands before the call takes effect may still be accepted; its event is then discarded, and its admission completes with `false` ([ENV-004])."
        "*When* `terminateNow()` takes effect, the executor *shall* become stopped, *shall* discard every external event still queued ([ENV-004]) and *shall* end a wait under way in step 6 ([CONC-010])."
        "*When* `terminateNow()` takes effect, the executor *shall not* change the marking and *shall not* move its loop to another step: the tokens that the firings in flight consumed stay consumed ([EXEC-031]), and the current cycle goes on."
        "The executor *shall* become stopped only when `terminateNow()` takes effect, and once stopped it *shall* stay stopped; `close()` *shall not* stop it ([ENV-013])."
        "*While* the executor is stopped, *if* `inject()` is called, *then* it *shall* return an error or `false` ([ENV-006])."
        "*While* the executor is stopped, it *shall not* inject an external event into the marking."
        "*While* the executor is stopped, it *shall not* process the outcome of a firing, except in the firing pass of the current cycle, for a synchronous action that pass waits for ([EXEC-001])."
        "*While* the executor is stopped and its loop is at the start of a cycle, it *shall not* take any step of the loop other than ending the run (answering a snapshot request ([ENV-014]) is not a step of the loop)."
        "*When* the executor is stopped and its loop reaches the start of a cycle, it *shall* end the run without waiting for the actions still in flight."
        "*When* the executor ends a run because it is stopped, it *shall* end it at the start of a cycle, *shall* return the marking it holds at that point without restoring the tokens that the firings in flight consumed, and *shall* discard every external event still queued ([ENV-004])."
        "*While* the executor is stopped, it *shall not* deposit a batch that an action published mid-action ([IO-015]), except to finish a step 1b that was under way when the call took effect."
        "*While* the executor is stopped, it *shall not* end the firing pass of the current cycle while transitions remain in its ready order: the pass still starts each of them that it can start ([EXEC-002], [TIME-014])."
        "Which termination reason the run reports is [EXEC-041]'s."
        "Whether an action left running is cancelled is the runtime's capability ([IO-013]); the executor never deposits its result."
  reading "For every executor R and every configuration C, where an executor state is stopped when its lifecycle mode is stopped:"
          "a step that leads from a state that is not stopped to a stopped state is a terminateNow step;"
          "every step from a stopped state leads to a stopped state;"
          "a terminateNow step leads to a stopped state, leaves the marking and the phase unchanged, empties the queue of external events and clears the parked flag;"
          "a request step from a stopped state is not answered accepted;"
          "while the state is stopped, R takes no inject step;"
          "while the state is stopped, R takes no commit, fail or tdeposit step of a firing i, unless the phase is the firing pass and a synchronous firing with identity i is in flight;"
          "while the state is stopped and its phase is completions (the start of a cycle), R takes no executor step other than a finish, except an answer to a snapshot request;"
          "a finish stopped step starts in phase completions, leaves the marking unchanged and empties the queue of external events;"
          "while the state is stopped and its phase is not publications (step 1b), R takes no publish step;"
          "an endPass step from a stopped state starts with an empty ready order."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A call of terminateNow() is the outside step terminateNow, and 'the executor is stopped' is the lifecycle mode Mode.stopped (ruling D47 (c)). The witness is the reference executor RefExec (Reference/Exec.lean): terminateStep sets the mode stopped, keeps the phase, empties the event queue (Java completes the queued events with false inside terminateNow) and clears the parked flag, which ends the wait; settleOk refuses step 1 and the wait once stopped and lets the pass settle only a synchronous firing, publishStep refuses a stopped wait, endPass needs an empty order, endCompletions refuses a stopped state, and finish stopped is offered at phase completions."
          "Naming: 'takes effect' is the terminateNow step, which sits between two steps of the loop. Java sets its flags at the call and reads stopRequested at the top of its loop (BitmapNetExecutor.executeLoop), so a call that lands during step 1 lets Java finish that step and the rest of the cycle; the model reads such a call as taking effect at the end of the step under way. A request that lands between the call and that point is, in the model, accepted and then dropped by the terminateNow step, which the quoted sentence 'A request that lands before the call takes effect may still be accepted; ...' allows: Java refuses it at once, and the caller learns false either way (ENV-004 reads the terminateNow step as the false answer of every ticket it drops). 'The start of a cycle' is the phase completions (EXEC-001 step 1, entered by endPass after a pass that started a transition, by wake, or by a settle in the wait); the current cycle ends where the next would start. 'The firing pass of the current cycle' is the phase pass: once stopped, line 7 lets no later cycle get past its start, so the only pass a stopped executor is in is the current cycle's. 'A synchronous action that pass waits for' is a firing in flight whose sync flag is set (the pass waits for it, passFree). 'Move its loop to another step' is a change of phase; 'end a wait under way' is clearing the parked flag. 'Step 1b' is the phase publications. 'Process the outcome of a firing' is a settle step (commit, fail, tdeposit, EXEC-020, EXEC-030, EXEC-022). 'Ends a run because it is stopped' is finish stopped. 'Ending the run' in line 7 is any finish: the quoted reason sentence leaves the reason to EXEC-041 (ruling D53 (c): closed and quiescent also conform after an immediate termination), and a terminal place stops the run from any phase (EXEC-042)."
          "Lines 1 and 2 are the shall sentence 'The executor shall become stopped only when terminateNow() takes effect, and once stopped it shall stay stopped; close() shall not stop it' and 'It is an explicit escape hatch and MUST NOT be invoked implicitly by close()'. They pin what EXEC-041's lines 6 and 7 read as 'an immediate termination was requested': the mode of the source state. A close that terminates immediately breaks line 1 (ENV_015_forbids_closeAsStop); a close after the stop that reopens a lifecycle that admits completions breaks line 2 (ENV_015_forbids_closeAfterStop; Java's close() after terminateNow() only sets flags that are already set). That a close itself changes only the mode to closed is ENV-013's line 1."
          "Line 3 is the two shall sentences on the moment terminateNow() takes effect, item 2 ('Queued external events are discarded') and item 4's 'their consumed tokens are lost'. A stop written as a close, which waits for the actions in flight and admits their completions, breaks it (ENV_015_forbids_terminateAsClose), and so does a stop that puts back the tokens the firings in flight consumed (ENV_015_forbids_rollbackAtTerminate). The phase conjunct is 'shall not move its loop to another step' and item 3's 'The loop stops at the end of its current cycle': a stop that ends the run at the call (Java's terminateNow() completing the run future itself) breaks it (ENV_015_forbids_endsAtCall), and so would a stop that jumps to the start of the next cycle. The queue conjunct is 'shall discard every external event still queued': a stop that keeps the queue and drops it later, in step 2 or at the finish, breaks it (ENV_015_forbids_queueKeptAtStop). The parked conjunct is 'shall end a wait under way in step 6': a stop that leaves a parked loop parked breaks it (ENV_015_forbids_stopKeepsWait). A second terminateNow() of a stopped executor is no step of the reference (Java's second call sets flags already set); line 3 does not need it."
          "Line 4 is item 1 and the shall sentence on inject(): a stopped executor answers refused (false) or error, never accepted (ENV_015_forbids_acceptWhileStopped). That a refused request changes nothing is ENV-006's. AC3's 'does not hang' is coverage: the third clause of Env015Covers (a request to a stopped executor is answered), which the reference meets (env015_ref_covers)."
          "Line 5 is item 2 and the shall sentence on injection: no queued event reaches the marking once the executor is stopped. An executor that keeps the queue at the stop and injects what was sent before it (the Rust reading of a close, ENV-013, carried over to the stop) breaks it (ENV_015_forbids_injectWhileStopped). The reference drops the queue at the stop, and line 8 drops what is left at the finish; the admission signal of every dropped event completes with false (ENV-004)."
          "Line 6 is item 3's 'their results are discarded rather than admitted to the marking' and its shall sentence: once stopped, no outcome is processed in step 1 or in the wait (EXEC-001), so a late return is never committed or failed. The firing pass of the current cycle is part of that cycle: a synchronous action it waits for still completes inside it (Java runs it inline on the orchestrator thread and deposits its output there; the Java test that calls terminateNow() from inside an action), and ENV_015_nonvacuous commits such a firing in a stopped pass. The exemption is the synchronous firing only: an asynchronous firing whose outcome is queued when the pass is under way is not settled there (settleOk), so an executor that admits a late completion in the wait (ENV_015_forbids_lateAdmit) or that commits an asynchronous firing's queued outcome in a stopped pass (ENV_015_forbids_asyncInPass) breaks the line."
          "Line 7 is item 3's 'The loop stops at the end of its current cycle' and its shall sentence: at the start of a cycle a stopped executor ends the run and goes no further. An executor that runs on into another cycle once stopped breaks it (ENV_015_forbids_goesOn). Answers to a snapshot request are exempt, as the sentence's parenthesis and EXEC-041's naming say: a snapshot answer reads the state and is not a step of the loop, and what it answers is ENV-014's (the reference offers none at phase completions)."
          "The shall sentence 'When the executor is stopped and its loop reaches the start of a cycle, it shall end the run without waiting for the actions still in flight' and item 3's 'it does NOT wait for in-flight actions' say that the end of the run is offered at once, firings in flight or not (AC1). That is coverage, which a safety line cannot state: Env015Covers below is the conjunct for the consistency theorem, a clause of ExecCoversW5 (ConsistencyExec.lean) (finish stopped offered at a live stopped start of a cycle, wake offered in a live stopped wait, a request answered). An executor whose stop waits for every action in flight to return (env015_wait, the stop written in the shape of a close) meets every line (env015_wait_meets) and fails the conjunct (env015_wait_not_covered). The wait the stop ends: line 3 clears the parked flag, and the second clause offers the wake; the reference still offers a park after the stop (parkStep has no mode guard), which with the wake that follows is a stutter, and 'does not wait' rests on the wake being offered."
          "Line 8 is the last shall sentence: finish stopped happens at the start of a cycle, not in the middle of one (ENV_015_forbids_stopMidCycle), keeps the marking, so the tokens the abandoned firings consumed stay consumed (ENV_015_forbids_rollbackOnStop; EXEC-041 line 1 also keeps the marking at every finish), and drops the queued events (ENV_015_forbids_keepQueued: an executor that keeps them queued past the end never answers them)."
          "Item 4's 'In-flight actions keep running where the runtime cannot cancel them ([IO-013])': no line requires the firings in flight to stay in the list of firings, since a runtime that can cancel an action may; the reference keeps them (finish stopped keeps fl), and their outside steps go on after the finish (ENV_015_nonvacuous returns t's action after the finish). That nothing such a late result does changes the returned marking is EXEC-041's lines 2 and 3; whether the action is stopped is IO-013's."
          "Termination reason: the reference reports stopped. Java reports CLOSED after terminateNow(), because terminateNow() also sets the closed flag, and the reason chain in executeLoop's finally reads closed before STOPPED; EXEC-041 allows closed after an immediate termination. Java's CLOSED with an action still in flight matches no reference finish closed (which needs nothing in flight); that is the reason's question (EXEC-041, ENV-013), not this block's: the sentence 'Which termination reason the run reports is [EXEC-041]'s.' says so."
          "Line 9 is the shall sentence on mid-action publications (IO-015, step 1b) and the sentence 'the executor never deposits its result': once stopped, no flushed batch lands in the wait or anywhere outside step 1b. A step 1b under way when the call took effect still finishes (the call takes effect when that step ends), which the reference allows at phase publications; a stopped executor reaches that phase only that way, since line 7 holds it at the start of a cycle. A Rust or Python wait whose flush arm deposits unconditionally, given a stop flag read at the top of the loop as Java reads it, breaks the line (ENV_015_forbids_publishWhileStopped: the batch t flushed lands on the wake the stop caused, and the run ends stopped with 70 in place 1). Publications are a Rust and Python feature, and only Java has terminateNow(); the line binds a runtime that has both."
          "Line 10 is the shall sentence on the firing pass of the current cycle: the stop does not cut the pass short, so the transitions left in its ready order are still offered, each started or lost as EXEC-002 and TIME-014 say (whether a head can start is theirs). An executor whose pass breaks off at the stop (an early exit in Java's fireReadyTransitions or the TypeScript firing loop) breaks it (ENV_015_forbids_passBreaksOff: stopped with t at the head of the order, the pass ends without starting t, and the run then ends with 7 still in place 0). ENV_015_nonvacuous starts t in a stopped pass."
          "Scope: the Status is Proposed and the operation is a MAY. Rust, TypeScript and Python take no terminateNow step, so lines 3 to 8 say nothing about them, and line 1 holds of them (no step stops them)."
          "AC1 (terminateNow() stops the loop without awaiting an outstanding in-flight action) is lines 3, 6, 7 and 8 with the coverage conjunct; ENV_015_nonvacuous takes terminateNow with t's action in flight, offers no endCompletions at the next start of a cycle and finishes stopped with t still in flight."
          "AC2 (the in-flight action's eventual output is not admitted to the marking) is lines 6 and 9, with EXEC-041's lines 2 and 3 after the finish; ENV_015_nonvacuous offers no commit of t's returned output in a stopped wait or a stopped pass, no publication of its flushed batch in a stopped wait, and t's return after the finish leaves place 1 empty."
          "AC3 (inject() after terminateNow() returns error / false, does not hang) is line 4 with the third coverage clause; ENV_015_nonvacuous answers a request for the environment place refused and one for another place error, and offers no accepted answer. A call made after terminateNow() returns but before the call takes effect is the quoted sentence on a request that lands before the call takes effect: its answer may be accepted, and its admission completes with false (line 3 and ENV-004)."
          "The test derivation (a gated in-flight action, terminateNow(), the loop ends without releasing the gate, the output never reaches the marking) is ENV_015_nonvacuous's run: t starts asynchronously, the executor stops, finishes stopped, and t's later return deposits nothing."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ l, on (fun s s' => s.mode ≠ .stopped ∧ s'.mode = .stopped ∧ R C s l s'),
        shall (fun _ _ => l = .terminateNow)) ∧
      (∀ l, on (fun s s' => s.mode = .stopped ∧ R C s l s'),
        shall (fun _ s' => s'.mode = .stopped)) ∧
      (on (fun s s' => R C s .terminateNow s'),
        shall (fun s s' => s'.mode = .stopped ∧ s'.M = s.M ∧ s'.phase = s.phase ∧ s'.eq = [] ∧
          s'.parked = false)) ∧
      (∀ p x r, on (fun s s' => s.mode = .stopped ∧ R C s (.request p x r) s'),
        shall (fun _ _ => r ≠ .accepted)) ∧
      (while (fun s => s.mode = .stopped), never (fun s s' => ∃ k, R C s (.inject k) s')) ∧
      (while (fun s => s.mode = .stopped), never (fun s s' =>
        ∃ i, ¬ (s.phase = .pass ∧ ∃ f ∈ s.fl, f.id = i ∧ f.sync = true) ∧
          (R C s (.commit i) s' ∨ R C s (.fail i) s' ∨ R C s (.tdeposit i) s'))) ∧
      (while (fun s => s.mode = .stopped ∧ s.phase = .completions), never (fun s s' =>
        ∃ l, l.outside = false ∧ (∀ a, l ≠ .snapshot a) ∧ (∀ c, l ≠ .finish c) ∧ R C s l s')) ∧
      (on (fun s s' => R C s (.finish .stopped) s'),
        shall (fun s s' => s.phase = .completions ∧ s'.M = s.M ∧ s'.eq = [])) ∧
      (while (fun s => s.mode = .stopped ∧ s.phase ≠ .publications), never (fun s s' =>
        ∃ i, R C s (.publish i) s')) ∧
      (on (fun s s' => s.mode = .stopped ∧ R C s .endPass s'),
        shall (fun s _ => s.order = []))

/- The pinned readable form of ENV-015: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_015 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (l : XLbl N T),
        on fun s s' => s.mode ≠ Mode.stopped ∧ s'.mode = Mode.stopped ∧ R C s l s', shall fun x x_1 =>
          l = XLbl.terminateNow) ∧
      (∀ (l : XLbl N T), on fun s s' => s.mode = Mode.stopped ∧ R C s l s', shall fun x s' => s'.mode = Mode.stopped) ∧
        (on fun s s' => R C s XLbl.terminateNow s', shall fun s s' =>
            s'.mode = Mode.stopped ∧ s'.M = s.M ∧ s'.phase = s.phase ∧ s'.eq = [] ∧ s'.parked = false) ∧
          (∀ (p : N) (x : T) (r : Reply),
              on fun s s' => s.mode = Mode.stopped ∧ R C s (XLbl.request p x r) s', shall fun x x_1 =>
                r ≠ Reply.accepted) ∧
            (while fun s => s.mode = Mode.stopped, never fun s s' => ∃ k, R C s (XLbl.inject k) s') ∧
              (while fun s => s.mode = Mode.stopped, never fun s s' =>
                  ∃ i,
                    ¬(s.phase = Phase.pass ∧ ∃ f ∈ s.fl, f.id = i ∧ f.sync = true) ∧
                      (R C s (XLbl.commit i) s' ∨ R C s (XLbl.fail i) s' ∨ R C s (XLbl.tdeposit i) s')) ∧
                (while fun s => s.mode = Mode.stopped ∧ s.phase = Phase.completions, never fun s s' =>
                    ∃ l,
                      l.outside = false ∧
                        (∀ (a : Option Bool), l ≠ XLbl.snapshot a) ∧ (∀ (c : Cause), l ≠ XLbl.finish c) ∧ R C s l s') ∧
                  (on fun s s' => R C s (XLbl.finish Cause.stopped) s', shall fun s s' =>
                      s.phase = Phase.completions ∧ s'.M = s.M ∧ s'.eq = []) ∧
                    (while fun s => s.mode = Mode.stopped ∧ s.phase ≠ Phase.publications, never fun s s' =>
                        ∃ i, R C s (XLbl.publish i) s') ∧
                      on fun s s' => s.mode = Mode.stopped ∧ R C s XLbl.endPass s', shall fun s x => s.order = []
-/
#guard_msgs in #print ENV_015

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- Every step of the reference other than a drain, a close or an immediate termination keeps
the mode: each inversion lemma gives the target as the source with other fields updated. -/
theorem env015_mode_frame {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (hd : l ≠ .drain) (hc : l ≠ .close) (ht : l ≠ .terminateNow) :
    s'.mode = s.mode := by
  cases l with
  | commit i => obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some (P := refXPol) h; rfl
  | fail i => obtain ⟨f, -, -, -, rfl⟩ := failStep_some (P := refXPol) h; rfl
  | tdeposit i => obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h; rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | publish i => obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h; rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | inject k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h; rfl
  | discard k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h; rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; rfl
  | start n sy => obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some (P := refXPol) h; rfl
  | lose n => obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h; rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; rfl
  | delay δ => cases xstepW_delay h; rfl
  | write i p x => obtain ⟨f, -, -, rfl⟩ := writeStep_some h; rfl
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> rfl
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; rfl
  | expire i e => obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; rfl
  | request p x r => obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> rfl
  | drain => exact absurd rfl hd
  | close => exact absurd rfl hc
  | terminateNow => exact absurd rfl ht

omit [DecidableEq N] in
/-- Once stopped, the reference settles a firing only inside the firing pass (`settleOk`). -/
theorem env015_settle_pass {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (h : canSettle C s i f = true) (hm : s.mode = .stopped) : s.phase = .pass := by
  unfold canSettle settleOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  split at h2 <;> simp_all

omit [DecidableEq N] in
/-- Once stopped, the reference settles firing `i` only inside the firing pass, and only when the
firing it finds under `i` is synchronous: the pass waits for it (`settleOk`). -/
theorem env015_settle_sync {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hfind : s.fl.find? (·.id == i) = some f) (h : canSettle C s i f = true)
    (hm : s.mode = .stopped) : s.phase = .pass ∧ ∃ g ∈ s.fl, g.id = i ∧ g.sync = true := by
  have hp := env015_settle_pass h hm
  refine ⟨hp, f, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind, ?_⟩
  unfold canSettle settleOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- A stopped reference state at the start of a cycle takes no executor step other than a finish
or a snapshot answer: settling needs the pass (`env015_settle_pass`), `endCompletions` needs a
mode that is not stopped, and every other rule needs another phase. -/
theorem env015_top {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s')
    (hm : s.mode = .stopped) (hp : s.phase = .completions) (ho : l.outside = false)
    (hsn : ∀ a, l ≠ .snapshot a) (hf : ∀ c, l ≠ .finish c) : False := by
  have hne : ∀ {q : Phase}, q ≠ .completions → s.phase = q → False := fun hq h1 =>
    hq (h1.symm.trans hp)
  cases l with
  | commit i =>
    obtain ⟨f, e, -, -, hc, -⟩ := commitStep_some (P := refXPol) h
    exact hne (by decide) (env015_settle_pass hc hm)
  | fail i =>
    obtain ⟨f, -, hc, -⟩ := failStep_some (P := refXPol) h
    exact hne (by decide) (env015_settle_pass hc hm)
  | tdeposit i =>
    obtain ⟨f, e, -, -, hc, -⟩ := tdepositStep_some h
    exact hne (by decide) (env015_settle_pass hc hm)
  | endCompletions => exact (xstepW_endCompletions h).2.2.2.1 hm
  | publish i =>
    obtain ⟨b, rest, -, -, hph, -⟩ := publishStep_some h
    rcases hph with hph | ⟨hph, -⟩
    · exact hne (by decide) hph
    · exact hne (by decide) hph
  | endPublications => exact hne (by decide) (xstepW_endPublications h).1
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hph, -⟩ := injectStep_some h
    rcases hph with hph | hph
    · exact hne (by decide) hph
    · exact hne (by decide) hph
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hph, -⟩ := discardStep_some h
    rcases hph with hph | hph
    · exact hne (by decide) hph
    · exact hne (by decide) hph
  | endEvents => exact hne (by decide) (xstepW_endEvents h).1
  | snapshot a => exact hsn a rfl
  | update => exact hne (by decide) (xstepW_update h).1
  | deadline ns => exact hne (by decide) (xstepW_deadline h).1
  | begin => exact hne (by decide) (xstepW_begin h).1
  | start n sy =>
    obtain ⟨t, rest, -, hph, -⟩ := startStep_some (P := refXPol) h
    exact hne (by decide) hph
  | lose n =>
    obtain ⟨t, rest, -, hph, -⟩ := loseStep_some (P := refXPol) h
    exact hne (by decide) hph
  | endPass => exact hne (by decide) (xstepW_endPass h).1
  | finish c => exact hf c rfl
  | park tmr => exact hne (by decide) (parkStep_some h).1
  | wake => exact hne (by decide) (wakeStep_some h).1
  | _ => simp [XLbl.outside] at ho

end Reference

/-- ✓ The reference executor satisfies ENV-015: only `terminateNow` sets the stopped mode, and no
rule leaves it (`env015_mode_frame`; drain, close and `terminateNow` need a mode that is not
stopped); `terminateNow` changes only the mode, the event queue and the parked flag
(`terminateStep_some`); a request answers `replyFor`, never accepted unless open
(`requestStep_some`); injection needs a mode that is not closing (`injectStep_some`); settling
needs the pass and a synchronous firing once stopped (`env015_settle_sync`); at the start of a
cycle only a finish is offered (`env015_top`); `finish stopped` needs phase completions and
changes only the phase and the two queues (`xstepW_finishStopped`); a publication needs step 1b
or a wait that is not stopped (`publishStep_some`); and `endPass` needs an empty order
(`xstepW_endPass`). -/
@[evidence holds ENV_015]
theorem ENV_015_reference {N T : Type} [DecidableEq N] :
    ENV_015 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun l s s' ⟨hm, hm', h⟩ => ?_, fun l s s' ⟨hm, h⟩ => ?_, fun s s' h => ?_,
    fun p x r s s' ⟨hm, h⟩ => ?_, fun s s' ⟨k, h⟩ hm => ?_, fun s s' ⟨i, hx, h⟩ hm => ?_,
    fun s s' ⟨l, ho, hsn, hf, h⟩ ⟨hm, hp⟩ => env015_top h hm hp ho hsn hf, fun s s' h => ?_,
    fun s s' ⟨i, h⟩ ⟨hm, hp⟩ => ?_, fun s s' ⟨_, h⟩ => (xstepW_endPass h).2.2.1⟩
  · by_cases ht : l = .terminateNow
    · exact ht
    · exfalso
      by_cases hd : l = .drain
      · subst hd
        obtain ⟨-, rfl⟩ := drainStep_some h
        exact absurd hm' (by simp)
      · by_cases hc : l = .close
        · subst hc
          obtain ⟨-, rfl⟩ := closeStep_some h
          exact absurd hm' (by simp)
        · exact hm ((env015_mode_frame h hd hc ht).symm.trans hm')
  · by_cases hd : l = .drain
    · subst hd
      obtain ⟨h0, -⟩ := drainStep_some h
      rw [hm] at h0
      exact absurd h0 (by decide)
    · by_cases hc : l = .close
      · subst hc
        obtain ⟨h0, -⟩ := closeStep_some h
        rw [hm] at h0
        exact absurd h0 (by decide)
      · by_cases ht : l = .terminateNow
        · subst ht
          obtain ⟨h0, -⟩ := terminateStep_some h
          exact absurd hm h0
        · show s'.mode = .stopped
          rw [env015_mode_frame h hd hc ht]; exact hm
  · obtain ⟨-, rfl⟩ := terminateStep_some h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, ⟨ha, -⟩ | ⟨ha, -⟩⟩ := requestStep_some h
    · rw [ha] at hr
      unfold replyFor at hr
      split at hr
      · exact absurd hr (by simp)
      · rw [hm] at hr
        simp at hr
    · exact ha
  · obtain ⟨p, x, rest, -, -, hcl, -⟩ := injectStep_some h
    rw [hm] at hcl
    exact absurd hcl (by decide)
  · rcases h with h | h | h
    · obtain ⟨f, e, hfd, -, hc, -⟩ := commitStep_some (P := refXPol) h
      exact hx (env015_settle_sync hfd hc hm)
    · obtain ⟨f, hfd, hc, -⟩ := failStep_some (P := refXPol) h
      exact hx (env015_settle_sync hfd hc hm)
    · obtain ⟨f, e, hfd, -, hc, -⟩ := tdepositStep_some h
      exact hx (env015_settle_sync hfd hc hm)
  · obtain ⟨hp, -, -, rfl⟩ := xstepW_finishStopped h
    exact ⟨hp, rfl, rfl⟩
  · obtain ⟨b, rest, -, -, hph, -⟩ := publishStep_some h
    rcases hph with hph | ⟨-, hm'⟩
    · exact hp hph
    · exact hm' hm

/-! ### Coverage: the stop does not wait (AC1, AC3) -/

/-- **The coverage conjunct ENV-015 asks of the consistency theorem's `ExecCoversW5`**: at the start
of a cycle of a live stopped state the run can end (`finish stopped`), whatever is in flight; a
live stopped wait can wake; and a request to a stopped executor is answered. Coverage is never a
line of a block; this is the clause for `ExecCovers`. -/
def Env015Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  (∀ C s, Live C s → s.phase = .completions → s.mode = .stopped →
    ∃ s', E C s (.finish .stopped) s') ∧
  (∀ C s, Live C s → s.phase = .await → s.mode = .stopped → ∃ s', E C s .wake s') ∧
  (∀ C s p x, s.mode = .stopped → ∃ r s', E C s (.request p x r) s')

/-- The reference meets the coverage conjunct. -/
theorem env015_ref_covers {N T : Type} [DecidableEq N] :
    Env015Covers (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s hL hp hm => ?_, fun C s hL hp hm => ?_, fun C s p x hm => ?_⟩
  · have hl : liveB C s = true := hL
    exact ⟨{ s with phase := .done .stopped, eq := [], pq := [] }, by
      simp [RefExec, xstep, xstepW, hp, hl, hm]⟩
  · have hl : liveB C s = true := hL
    exact ⟨{ s with phase := .completions, parked := false }, by
      simp [RefExec, xstep, xstepW, wakeStep, hp, hl]⟩
  · have hr : replyFor C s p ≠ .accepted := by
      unfold replyFor
      split
      · simp
      · rw [hm]; simp
    exact ⟨replyFor C s p, s, by simp [RefExec, xstep, xstepW, requestStep, hr]⟩

/-- Every line of ENV-015 constrains the steps an executor takes, so a sub-relation of an executor
that satisfies ENV-015 satisfies it too. -/
theorem env015_sub {N T : Type} [DecidableEq N] {R R' : XRel N T}
    (hR : ∀ C s l s', R C s l s' → R' C s l s') (h : ENV_015 R') : ENV_015 R := by
  intro C
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h C
  exact ⟨fun l s s' ⟨a, b, hs⟩ => h1 l s s' ⟨a, b, hR _ _ _ _ hs⟩,
    fun l s s' ⟨a, hs⟩ => h2 l s s' ⟨a, hR _ _ _ _ hs⟩,
    fun s s' hs => h3 s s' (hR _ _ _ _ hs),
    fun p x r s s' ⟨a, hs⟩ => h4 p x r s s' ⟨a, hR _ _ _ _ hs⟩,
    fun s s' ⟨k, hs⟩ => h5 s s' ⟨k, hR _ _ _ _ hs⟩,
    fun s s' ⟨i, hx, hs⟩ =>
      h6 s s' ⟨i, hx, hs.imp (hR _ _ _ _) (Or.imp (hR _ _ _ _) (hR _ _ _ _))⟩,
    fun s s' ⟨l, a, b, c, hs⟩ => h7 s s' ⟨l, a, b, c, hR _ _ _ _ hs⟩,
    fun s s' hs => h8 s s' (hR _ _ _ _ hs),
    fun s s' ⟨i, hs⟩ => h9 s s' ⟨i, hR _ _ _ _ hs⟩,
    fun s s' ⟨a, hs⟩ => h10 s s' ⟨a, hR _ _ _ _ hs⟩⟩

/-! ### Examples

Places `0`, `1` and `9`; place `9` is an environment place. Transition `t` takes a token from `0`
and has output `Place 1`. The validator is the reference validator of IO-015. -/

/-- Transition `t`: one token from `0`, output `Place 1`. -/
def env015_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration: environment place `9`, no terminal place, not re-entrant. -/
def env015_C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 9], transitions := [env015_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [9],
    reentrant := false, validate := cfgValidate ioRefValidate, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial marking: `7` in `0`. -/
def env015_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- One cycle up to the firing pass. -/
def env015_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- `t` starts asynchronously; the pass ends at the start of the next cycle with `t` in flight. -/
def env015_runA : List (XLbl Nat Nat) := env015_pre ++ [.start "t" false, .endPass]

/-- The next cycle, with `t` in flight and nothing to start, ends in the wait. -/
def env015_runB : List (XLbl Nat Nat) := env015_runA ++ env015_pre ++ [.endPass]

/-- `t` starts asynchronously and is in flight in the next cycle's pass; it writes `70` to `1`
and returns, and the executor is stopped inside that pass with `t`'s outcome queued. -/
def env015_runAsyncPass : List (XLbl Nat Nat) :=
  env015_runA ++ env015_pre ++ [.write 0 1 70, .ret 0 true, .terminateNow]

/-- `t` starts synchronously; the executor is stopped while its action runs; the action writes
`70` to `1` and returns. -/
def env015_runSync : List (XLbl Nat Nat) :=
  env015_pre ++ [.start "t" true, .terminateNow, .write 0 1 70, .ret 0 true]

/-- The reference state after `ls` from the initial marking. -/
def env015_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  xrun env015_C (xinit env015_m0 0) ls

/-- The run of a step function `g` (a mutant) from the initial marking. -/
def env015_grun (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat)) :
    XSt Nat Nat → List (XLbl Nat Nat) → Option (XSt Nat Nat)
  | s, [] => some s
  | s, l :: ls => (g env015_C s l).bind fun s' => env015_grun g s' ls

/-! ### Every line exercised -/

/-- ✓ Every line of ENV-015 is exercised by the reference. (1) `terminateNow` with `t`'s action
in flight stops the executor and keeps `0` consumed (lines 1 and 3). (2) A stopped executor keeps
its mode across `t`'s return and offers no close (line 2). (3) A request for `9` is answered
refused, one for `0` error, and no request is answered accepted (line 4, AC3). (4) An event
accepted before the stop is dropped by it, and step 2 then offers no injection (line 5). (5) In a
stopped wait with `t`'s outcome queued no commit is offered, and the wait wakes (line 6, AC2).
(6) A synchronous firing of `t` still commits inside the stopped pass of the current cycle (line
6, the exemption). (7) At the start of the next cycle `endCompletions` is not offered, and `finish
stopped` is, with `t` in flight, `0` consumed and `1` empty (lines 7 and 8, AC1). (8) After the
finish, `t`'s action writes `70` and returns, and place `1` stays empty (AC2, item 4). (9) A stop
in a parked wait ends the wait and keeps the phase (line 3). (10) Stopped in a pass with the
asynchronous `t`'s outcome queued, no commit is offered, and the pass ends (line 6, AC2). (11) In
a stopped wait with `t`'s flushed batch queued no publication is offered, and the wait wakes; a
stop that lands in step 1b still lets it publish (line 9). (12) Stopped in the pass with `t` at the
head of the order, the pass starts `t` and offers no `endPass` (line 10). -/
@[evidence nonvacuous ENV_015]
theorem ENV_015_nonvacuous :
    (∃ s s', RefExec env015_C s .terminateNow s' ∧ s.mode ≠ .stopped ∧ s'.mode = .stopped ∧
      s.fl.length = 1 ∧ s'.M 0 = []) ∧
    (∃ s s', RefExec env015_C s (.ret 0 true) s' ∧ s.mode = .stopped ∧ s'.mode = .stopped ∧
      xstep env015_C s .close = none) ∧
    (∃ s s' s'', RefExec env015_C s (.request 9 6 .refused) s' ∧
      RefExec env015_C s (.request 0 6 .error) s'' ∧ s.mode = .stopped ∧
      xstep env015_C s (.request 9 6 .accepted) = none) ∧
    (∃ s s', RefExec env015_C s .terminateNow s' ∧ s.eq.length = 1 ∧ s'.eq = [] ∧
      s'.phase = .events ∧ xstep env015_C s' (.inject 0) = none) ∧
    (∃ s s', RefExec env015_C s .wake s' ∧ s.mode = .stopped ∧ s.phase = .await ∧
      s.cq = [0] ∧ xstep env015_C s (.commit 0) = none) ∧
    (∃ s s', RefExec env015_C s (.commit 0) s' ∧ s.mode = .stopped ∧ s.phase = .pass ∧
      s'.M 1 = [70]) ∧
    (∃ s s', RefExec env015_C s (.finish .stopped) s' ∧ s.mode = .stopped ∧
      s.fl.length = 1 ∧ s'.fl.length = 1 ∧ s'.M 0 = [] ∧ s'.M 1 = [] ∧
      xstep env015_C s .endCompletions = none) ∧
    (∃ s s', RefExec env015_C s (.ret 0 true) s' ∧ s.phase = .done .stopped ∧ s'.M 1 = []) ∧
    (∃ s s', RefExec env015_C s .terminateNow s' ∧ s.phase = .await ∧ s.parked = true ∧
      s'.phase = .await ∧ s'.parked = false) ∧
    (∃ s s', RefExec env015_C s .endPass s' ∧ s.mode = .stopped ∧ s.phase = .pass ∧ s.cq = [0] ∧
      xstep env015_C s (.commit 0) = none) ∧
    (∃ s s' t t', RefExec env015_C s .wake s' ∧ s.mode = .stopped ∧ s.phase = .await ∧
      s.pq.length = 1 ∧ xstep env015_C s (.publish 0) = none ∧
      RefExec env015_C t (.publish 0) t' ∧ t.mode = .stopped ∧ t.phase = .publications) ∧
    (∃ s s', RefExec env015_C s (.start "t" false) s' ∧ s.mode = .stopped ∧ s.phase = .pass ∧
      xstep env015_C s .endPass = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at env015_runA) (l := .terminateNow)
      (p := fun s s' => s.mode != .stopped && s'.mode == .stopped && s.fl.length == 1 &&
        s'.M 0 == []) (by decide)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runA ++ [.terminateNow])) (l := .ret 0 true)
      (p := fun s s' => s.mode == .stopped && s'.mode == .stopped &&
        (xstep env015_C s .close).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at [.terminateNow]) (l := .request 9 6 .refused)
      (p := fun s _ => s.mode == .stopped &&
        (xstep env015_C s (.request 9 6 .accepted)).isNone &&
        (xstep env015_C s (.request 0 6 .error)).isSome) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hp
    obtain ⟨⟨h1, h2⟩, ⟨s'', h3⟩⟩ := hp
    exact ⟨s, s', s'', hs, h3, h1, h2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at [.request 9 5 .accepted, .endCompletions, .endPublications])
      (l := .terminateNow)
      (p := fun s s' => s.eq.length == 1 && s'.eq.isEmpty && s'.phase == .events &&
        (xstep env015_C s' (.inject 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runB ++ [.terminateNow, .write 0 1 70, .ret 0 true]))
      (l := .wake)
      (p := fun s _ => s.mode == .stopped && s.phase == .await && s.cq == [0] &&
        (xstep env015_C s (.commit 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at env015_runSync) (l := .commit 0)
      (p := fun s s' => s.mode == .stopped && s.phase == .pass && s'.M 1 == [70]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runA ++ [.terminateNow])) (l := .finish .stopped)
      (p := fun s s' => s.mode == .stopped && s.fl.length == 1 && s'.fl.length == 1 &&
        s'.M 0 == [] && s'.M 1 == [] && (xstep env015_C s .endCompletions).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runA ++ [.terminateNow, .finish .stopped, .write 0 1 70]))
      (l := .ret 0 true)
      (p := fun s s' => s.phase == .done .stopped && s'.M 1 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runB ++ [.park none])) (l := .terminateNow)
      (p := fun s s' => s.phase == .await && s.parked && s'.phase == .await && !s'.parked)
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at env015_runAsyncPass) (l := .endPass)
      (p := fun s _ => s.mode == .stopped && s.phase == .pass && s.cq == [0] &&
        (xstep env015_C s (.commit 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runB ++ [.write 0 1 70, .flush 0, .terminateNow])) (l := .wake)
      (p := fun s _ => s.mode == .stopped && s.phase == .await && s.pq.length == 1 &&
        (xstep env015_C s (.publish 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    obtain ⟨t, t', -, ht, hq⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_runB ++
        [.write 0 1 70, .flush 0, .wake, .endCompletions, .terminateNow]))
      (l := .publish 0) (p := fun t _ => t.mode == .stopped && t.phase == .publications)
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨s, s', t, t', hs, h1, h2, h3, h4, ht, hq.1, hq.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env015_C)
      (o := env015_at (env015_pre ++ [.terminateNow])) (l := .start "t" false)
      (p := fun s _ => s.mode == .stopped && s.phase == .pass &&
        (xstep env015_C s .endPass).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', hs, h1, h2, h3⟩

/-! ### The waiting executor: every line, no coverage -/

/-- An executor whose stop waits for the actions in flight: `finish stopped` is offered only once
every firing in flight has its outcome set (the stop written in the shape of a close); otherwise
the reference. -/
def env015_waitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .stopped =>
      if s.fl.all (·.out.isSome) then xstep C s (.finish .stopped) else none
  | l => xstep C s l

/-- The executor of `env015_waitStep`. -/
def env015_wait {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env015_waitStep C s l = some s'

/-- The waiting executor is a sub-relation of the reference. -/
theorem env015_wait_ref {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : env015_wait C s l s') : RefExec C s l s' := by
  unfold env015_wait at h
  unfold RefExec
  cases l with
  | finish c =>
    cases c with
    | stopped =>
      unfold env015_waitStep at h
      by_cases hw : (s.fl.all fun x => x.out.isSome) = true
      · rw [if_pos hw] at h; exact h
      · rw [if_neg hw] at h; cases h
    | _ => exact h
  | _ => exact h

/-- The gap the coverage conjunct closes: the waiting executor satisfies every line of ENV-015,
since it only takes fewer steps than the reference. -/
theorem env015_wait_meets {N T : Type} [DecidableEq N] :
    ENV_015 (env015_wait (N := N) (T := T)) :=
  env015_sub (fun _ _ _ _ h => env015_wait_ref h) ENV_015_reference

/-- The waiting executor fails the coverage conjunct: stopped at the start of a cycle with `t`'s
action not returned, it offers no `finish stopped` (AC1). -/
theorem env015_wait_not_covered : ¬ Env015Covers (env015_wait (N := Nat) (T := Nat)) := by
  intro h
  have hd : (env015_at (env015_runA ++ [.terminateNow])).map
      (fun s => liveB env015_C s && s.phase == .completions && s.mode == .stopped &&
        (env015_waitStep env015_C s (.finish .stopped)).isNone) = some true := by decide
  cases hs : env015_at (env015_runA ++ [.terminateNow]) with
  | none => rw [hs] at hd; cases hd
  | some s =>
    rw [hs] at hd
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq,
      Option.isNone_iff_eq_none] at hd
    obtain ⟨⟨⟨hl, hp⟩, hm⟩, hw⟩ := hd
    obtain ⟨s', hs'⟩ := h.1 env015_C s hl hp hm
    exact absurd (hs'.symm.trans hw) (by simp)

/-! ### Violations of lines 1 and 2: the mode -/

/-- An executor whose close terminates immediately (`close()` invoking `terminateNow()`);
otherwise the reference. -/
def env015_closeAsStopStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => (xstep C s .close).map fun s₁ => { s₁ with mode := .stopped }
  | l => xstep C s l

/-- ✗ A close that stops the executor violates ENV-015 (line 1): from the initial state the close
leads to the stopped mode. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_closeAsStop :
    ¬ ENV_015 (fun C s l s' => env015_closeAsStopStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_closeAsStopStep (C := env015_C)
    (o := some (xinit env015_m0 0)) (l := .close)
    (p := fun s s' => s.mode != .stopped && s'.mode == .stopped) (by decide)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
  have := (h env015_C).1 .close s s' ⟨hp.1, hp.2, hs⟩
  cases this

/-- An executor whose close after the stop reopens a closed lifecycle (which admits completions,
ENV-013); otherwise the reference. -/
def env015_closeAfterStopStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => if s.mode = .stopped then some { s with mode := .closed, parked := false }
      else xstep C s .close
  | l => xstep C s l

/-- ✗ Leaving the stopped mode violates ENV-015 (line 2): after `terminateNow`, a close turns the
stopped executor into a closed one. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_closeAfterStop :
    ¬ ENV_015 (fun C s l s' => env015_closeAfterStopStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_closeAfterStopStep (C := env015_C)
    (o := env015_at [.terminateNow]) (l := .close)
    (p := fun s s' => s.mode == .stopped && s'.mode != .stopped) (by decide)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
  exact hp.2 ((h env015_C).2.1 .close s s' ⟨hp.1, hs⟩)

/-! ### Violations of line 3: the stop itself -/

/-- An executor whose immediate termination is a close: the mode becomes closed, so the loop
waits for the actions in flight and admits their completions; otherwise the reference. -/
def env015_terminateAsCloseStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ => { s₁ with mode := .closed }
  | l => xstep C s l

/-- ✗ A stop written as a close violates ENV-015 (line 3): `terminateNow` with `t` in flight leads
to the closed mode. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_terminateAsClose :
    ¬ ENV_015 (fun C s l s' => env015_terminateAsCloseStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_terminateAsCloseStep (C := env015_C)
    (o := env015_at env015_runA) (l := .terminateNow)
    (p := fun _ s' => s'.mode != .stopped) (by decide)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h env015_C).2.2.1 s s' hs).1

/-- The consumed tokens of every firing in flight, put back at the heads of their places. -/
def env015_rollback {N T : Type} (s s₁ : XSt N T) : XSt N T :=
  { s₁ with M := fun p => s.fl.flatMap (·.deliv.inputs p) ++ s₁.M p }

/-- An executor whose immediate termination restores the tokens the firings in flight consumed;
otherwise the reference. -/
def env015_rollbackAtTerminateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map (env015_rollback s)
  | l => xstep C s l

/-- ✗ A stop that restores consumed tokens violates ENV-015 (line 3): `t` is in flight at the
stop, and its consumed `7` goes back to `0`. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_rollbackAtTerminate :
    ¬ ENV_015 (fun C s l s' =>
      env015_rollbackAtTerminateStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_rollbackAtTerminateStep (C := env015_C)
    (o := env015_at env015_runA) (l := .terminateNow)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := ((h env015_C).2.2.1 s s' hs).2
  simp [this] at hp

/-- An executor whose immediate termination ends the run at the call (Java's `terminateNow()`
completing the run future itself); otherwise the reference. -/
def env015_endsAtCallStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ =>
      if isExecPhase s.phase then { s₁ with phase := .done .stopped, pq := [] } else s₁
  | l => xstep C s l

/-- ✗ Ending the run at the call violates ENV-015 (line 3): stopped inside the firing pass with
`t` in flight, the run is over at once, so the current cycle does not go on. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_endsAtCall :
    ¬ ENV_015 (fun C s l s' => env015_endsAtCallStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_endsAtCallStep (C := env015_C)
    (o := env015_at (env015_pre ++ [.start "t" false])) (l := .terminateNow)
    (p := fun s s' => s'.phase != s.phase) (by decide)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h env015_C).2.2.1 s s' hs).2.2.1

/-- An executor whose immediate termination keeps the queued events, which a later step 2 or the
finish drops; otherwise the reference. -/
def env015_queueKeptStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ => { s₁ with eq := s.eq }
  | l => xstep C s l

/-- ✗ Keeping the queue at the stop violates ENV-015 (line 3): an event for `9` accepted before
the stop is still queued after it. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_queueKeptAtStop :
    ¬ ENV_015 (fun C s l s' => env015_queueKeptStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_queueKeptStep (C := env015_C)
    (o := env015_at [.request 9 5 .accepted]) (l := .terminateNow)
    (p := fun _ s' => !s'.eq.isEmpty) (by decide)
  have := ((h env015_C).2.2.1 s s' hs).2.2.2.1
  simp [this] at hp

/-- An executor whose immediate termination leaves a parked loop parked; otherwise the
reference. -/
def env015_keepsWaitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ => { s₁ with parked := s.parked }
  | l => xstep C s l

/-- ✗ A stop that does not end the wait violates ENV-015 (line 3): parked with `t` in flight, the
loop stays parked across `terminateNow`. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_stopKeepsWait :
    ¬ ENV_015 (fun C s l s' => env015_keepsWaitStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_keepsWaitStep (C := env015_C)
    (o := env015_at (env015_runB ++ [.park none])) (l := .terminateNow)
    (p := fun _ s' => s'.parked) (by decide)
  have := ((h env015_C).2.2.1 s s' hs).2.2.2.2
  simp [this] at hp

/-! ### Violation of line 4: a request accepted after the stop (AC3) -/

/-- An executor that answers requests as if it were open after the stop; otherwise the
reference. -/
def env015_acceptStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
      (requestStep C { s with mode := .open } p x r).map fun s₁ => { s₁ with mode := s.mode }
  | l => xstep C s l

/-- ✗ Accepting a request after the stop violates ENV-015 (line 4, AC3): after `terminateNow` a
request for `9` is answered accepted. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_acceptWhileStopped :
    ¬ ENV_015 (fun C s l s' => env015_acceptStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_acceptStep (C := env015_C)
    (o := env015_at [.terminateNow]) (l := .request 9 6 .accepted)
    (p := fun s _ => s.mode == .stopped) (by decide)
  simp only [beq_iff_eq] at hp
  exact (h env015_C).2.2.2.1 9 6 .accepted s s' ⟨hp, hs⟩ rfl

/-! ### Violation of line 5: an event injected after the stop -/

/-- An executor that keeps the queued events at the stop and injects them afterwards (the Rust
reading of a close carried over to the stop); otherwise the reference. -/
def env015_injectStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ => { s₁ with eq := s.eq }
  | .inject k => (injectStep C { s with mode := .open } k).map fun s₁ => { s₁ with mode := s.mode }
  | l => xstep C s l

/-- ✗ Injecting after the stop violates ENV-015 (line 5): an event for `9` accepted before the
stop in step 2 of the cycle is still injected. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_injectWhileStopped :
    ¬ ENV_015 (fun C s l s' => env015_injectStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_injectStep (C := env015_C)
    (o := env015_grun env015_injectStep (xinit env015_m0 0)
      [.request 9 5 .accepted, .endCompletions, .endPublications, .terminateNow])
    (l := .inject 0) (p := fun s _ => s.mode == .stopped) (by decide)
  simp only [beq_iff_eq] at hp
  exact (h env015_C).2.2.2.2.1 s s' ⟨0, hs⟩ hp

/-! ### Violation of line 6: a late result admitted (AC2) -/

/-- An executor whose wait still admits completions after the stop; otherwise the reference. -/
def env015_lateAdmitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i =>
      (commitStep refXPol C { s with mode := .open } i).map fun s₁ => { s₁ with mode := s.mode }
  | l => xstep C s l

/-- ✗ Admitting a late completion violates ENV-015 (line 6, AC2): stopped in the wait, `t`'s
action writes `70` to `1` and returns, and its output is committed. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_lateAdmit :
    ¬ ENV_015 (fun C s l s' => env015_lateAdmitStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_lateAdmitStep (C := env015_C)
    (o := env015_at (env015_runB ++ [.terminateNow, .write 0 1 70, .ret 0 true]))
    (l := .commit 0) (p := fun s _ => s.mode == .stopped && s.phase == .await) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact (h env015_C).2.2.2.2.2.1 s s'
    ⟨0, fun hx => absurd (hp.2.symm.trans hx.1) (by decide), .inl hs⟩ hp.1

/-- An executor whose stopped pass settles any queued outcome, synchronous or not; otherwise the
reference. -/
def env015_asyncInPassStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i =>
      if s.mode = .stopped && s.phase = .pass then
        (commitStep refXPol C { s with mode := .open, phase := .completions } i).map
          fun s₁ => { s₁ with mode := s.mode, phase := s.phase }
      else xstep C s (.commit i)
  | l => xstep C s l

/-- ✗ Admitting an asynchronous firing's late result in the stopped pass violates ENV-015 (line
6, AC2): `t` started asynchronously, wrote `70` to `1` and returned during the next cycle's pass,
and the stop lands there; its output is committed. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_asyncInPass :
    ¬ ENV_015 (fun C s l s' => env015_asyncInPassStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_asyncInPassStep (C := env015_C)
    (o := env015_at env015_runAsyncPass) (l := .commit 0)
    (p := fun s s' => s.mode == .stopped && s.phase == .pass &&
      s.fl.all (fun f => f.id != 0 || !f.sync) && s'.M 1 == [70]) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨h1, -⟩, h3⟩, -⟩ := hp
  refine (h env015_C).2.2.2.2.2.1 s s' ⟨0, fun ⟨_, f, hf, hid, hsy⟩ => ?_, .inl hs⟩ h1
  rcases h3 f hf with h | h
  · exact h hid
  · rw [hsy] at h; cases h

/-! ### Violation of line 7: the loop goes on after the stop -/

/-- An executor whose step 1 ends whatever the mode, so a stopped loop runs into the next cycle;
otherwise the reference. -/
def env015_goesOnStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endCompletions =>
      if s.phase = .completions && liveB C s && s.cq.isEmpty then
        some { s with phase := .publications } else none
  | l => xstep C s l

/-- ✗ Running on past the end of the current cycle violates ENV-015 (line 7): stopped at the start
of the next cycle, the loop ends step 1 instead of ending the run. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_goesOn :
    ¬ ENV_015 (fun C s l s' => env015_goesOnStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_goesOnStep (C := env015_C)
    (o := env015_at (env015_runA ++ [.terminateNow])) (l := .endCompletions)
    (p := fun s _ => s.mode == .stopped && s.phase == .completions) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact (h env015_C).2.2.2.2.2.2.1 s s'
    ⟨.endCompletions, rfl, (fun _ ha => nomatch ha), (fun _ hc => nomatch hc), hs⟩ hp

/-! ### Violations of line 8: the end of the run -/

/-- An executor whose `finish stopped` step is offered from every running phase of a stopped
state; otherwise the reference. -/
def env015_midCycleStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .stopped =>
      if isExecPhase s.phase && liveB C s && s.mode = .stopped then
        some { s with phase := .done .stopped, eq := [], pq := [] } else none
  | l => xstep C s l

/-- ✗ Ending the run in the middle of the cycle violates ENV-015 (line 8): stopped inside the
firing pass, the run ends there. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_stopMidCycle :
    ¬ ENV_015 (fun C s l s' => env015_midCycleStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_midCycleStep (C := env015_C)
    (o := env015_at (env015_pre ++ [.start "t" false, .terminateNow])) (l := .finish .stopped)
    (p := fun s _ => s.phase != .completions) (by decide)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h env015_C).2.2.2.2.2.2.2.1 s s' hs).1

/-- An executor whose `finish stopped` restores the tokens the firings in flight consumed;
otherwise the reference. -/
def env015_rollbackOnStopStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .stopped => (xstep C s (.finish .stopped)).map (env015_rollback s)
  | l => xstep C s l

/-- ✗ A finish that restores consumed tokens violates ENV-015 (line 8): `t` is in flight at the
finish, and its consumed `7` goes back to `0`. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_rollbackOnStop :
    ¬ ENV_015 (fun C s l s' =>
      env015_rollbackOnStopStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_rollbackOnStopStep (C := env015_C)
    (o := env015_at (env015_runA ++ [.terminateNow])) (l := .finish .stopped)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := ((h env015_C).2.2.2.2.2.2.2.1 s s' hs).2.1
  simp [this] at hp

/-- An executor that keeps the queued events through the stop and its end, so they are never
answered; otherwise the reference. -/
def env015_keepQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .terminateNow => (xstep C s .terminateNow).map fun s₁ => { s₁ with eq := s.eq }
  | .finish .stopped => (xstep C s (.finish .stopped)).map fun s₁ => { s₁ with eq := s.eq }
  | l => xstep C s l

/-- ✗ Keeping queued events past the end violates ENV-015 (line 8): an event for `9` accepted
before the stop is still queued after `finish stopped`. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_keepQueued :
    ¬ ENV_015 (fun C s l s' => env015_keepQueuedStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_keepQueuedStep (C := env015_C)
    (o := env015_grun env015_keepQueuedStep (xinit env015_m0 0)
      [.request 9 5 .accepted, .terminateNow])
    (l := .finish .stopped) (p := fun _ s' => !s'.eq.isEmpty) (by decide)
  have := ((h env015_C).2.2.2.2.2.2.2.1 s s' hs).2.2
  simp [this] at hp

/-! ### Violation of line 9: a publication deposited after the stop -/

/-- An executor whose wait deposits a queued publication whatever the mode (a Rust or Python wait
whose flush arm deposits unconditionally, with a stop flag read at the top of the loop); otherwise
the reference. -/
def env015_publishStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i =>
      (publishStep C { s with mode := .open } i).map fun s₁ => { s₁ with mode := s.mode }
  | l => xstep C s l

/-- ✗ Publishing in a stopped wait violates ENV-015 (line 9, AC2): `t` is in flight in the wait
and flushes `70` to `1`; after the stop, the batch lands. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_publishWhileStopped :
    ¬ ENV_015 (fun C s l s' => env015_publishStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_publishStep (C := env015_C)
    (o := env015_at (env015_runB ++ [.write 0 1 70, .flush 0, .terminateNow])) (l := .publish 0)
    (p := fun s s' => s.mode == .stopped && s.phase == .await && s'.M 1 == [70]) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact (h env015_C).2.2.2.2.2.2.2.2.1 s s' ⟨0, hs⟩
    ⟨hp.1.1, by rw [hp.1.2]; decide⟩

/-! ### Violation of line 10: the pass broken off at the stop -/

/-- An executor whose firing pass breaks off once stopped, with transitions left in its order
(an early exit in the firing loop); otherwise the reference. -/
def env015_passBreaksOffStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPass =>
      if s.phase = .pass && liveB C s && passFree s && (s.order.isEmpty || s.mode = .stopped) then
        some { s with phase := if s.started then .completions else .await, order := [] }
      else none
  | l => xstep C s l

/-- ✗ Breaking off the pass at the stop violates ENV-015 (line 10): stopped in the pass with `t`
at the head of its order, the pass ends without starting `t`; the run then ends stopped with `7`
still in `0`. -/
@[evidence forbids ENV_015]
theorem ENV_015_forbids_passBreaksOff :
    ¬ ENV_015 (fun C s l s' => env015_passBreaksOffStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env015_passBreaksOffStep (C := env015_C)
    (o := env015_at (env015_pre ++ [.terminateNow])) (l := .endPass)
    (p := fun s _ => s.mode == .stopped && !s.order.isEmpty) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact hp.2 ((h env015_C).2.2.2.2.2.2.2.2.2 s s' ⟨hp.1, hs⟩)

end Libpetri.Spec
