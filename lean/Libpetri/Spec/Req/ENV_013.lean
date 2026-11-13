import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Req.EXEC_040

set_option linter.missingDocs true

/-!
# ENV-013: Immediate Close (`spec/06-environment-places.md`)

A close is an outside step of the executor model (`RefExec`, `Reference/Exec.lean`): a caller
closes the executor, and its mode becomes `closed`. The requirement is a predicate over an
abstract executor `R : XRel N T` (glossary `GlossaryExec.lean`): the close changes only the mode
and the parked flag, so it neither stops a firing pass nor moves a clock reading; a closed
executor refuses requests and changes nothing on them; the mode becomes closed only by a close and
is left only for an immediate termination ([ENV-015]); a closed executor injects no queued event
and leaves none queued when it ends; it removes an action in flight only by settling its outcome;
it ends only with nothing in flight, unless a terminal place is marked; at a termination test with
nothing in flight it takes no step but a finish; and it ends step 1b only with no publication
queued.

Ruling D85 (a): a closed executor keeps starting ready transitions while an action is in flight,
so a close alone does not bound a run (`ENV_013_nonvacuous`, the start after the close); an
immediate termination ([ENV-015]) does, and a run budget ([ENV-016]) bounds only the caller's wait. Ruling
D44 (a): Java and TypeScript discard the events still queued at the close; Rust and Python inject
every event sent before the close, which is a run in which those injections come before the close
step. Ruling D53 (c): at a rest reached after a close both `quiescent` and `closed` are offered.
ENVB-R7 item 7 (D20): the lines on in-flight actions are scoped to runs with no terminal place
marked ([EXEC-042]).

The block is checked against the reference and against executors whose close abandons the
actions in flight, whose close stops the firing pass, that accept requests while closed, whose
drain closes, whose drain reopens a closed executor, that inject a queued event after the close,
that end a closed run with events still queued, that end a closed run with an action in flight,
that keep cycling while closed with nothing in flight (a close behaving as a drain), that drop an
action in flight without settling it, and that stop publishing once closed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-013: Immediate Close -/

requirement ENV_013
  id "ENV-013"
  title "Immediate Close"
  kind B
  scope "all executors"
  source verbatim "spec/06-environment-places.md"
  quote "The executor provides a `close()` method for immediate shutdown."
        "In Java and TypeScript the executor takes the close when `close()` sets its closed flag, except that a call that lands while the loop is injecting queued events in the external-events step ([EXEC-001] step 2) is taken when that injection ends: the events it injects come before the close, and the events still queued after it are discarded."
        "Calling `close()` after `drain()` escalates from graceful to immediate shutdown."
        "A close does not stop the firing pass."
        "While an action is in flight, a closed executor keeps running its cycles and may start ready transitions, whose actions are then in flight too; it terminates at the first termination test ([EXEC-040]) that finds no action in flight."
        "A close alone therefore does not bound a run whose firings overlap; an immediate termination ([ENV-015]) does."
        "A run budget ([ENV-016]) bounds only the caller's wait."
        "*When* the executor takes a close, it *shall* enter the closed mode and *shall* leave every part of its state other than its mode and whether its loop waits ([CONC-010]) as it was: the marking, the clock of every transition, the clock reading of the cycle, the actions in flight, the queued outcomes, publications and external events, the supply of identities, the phase of its loop and the rest of a firing pass."
        "*While* the executor is closed, it *shall* reject every `inject()` call, and a rejected call *shall* change nothing."
        "The executor *shall* enter the closed mode only when it takes a close, and *shall* leave it only for an immediate termination ([ENV-015])."
        "*While* the executor is closed, it *shall not* inject a queued external event."
        "*When* a closed executor ends its run, it *shall* leave no external event queued."
        "*While* the executor is closed and no terminal place is marked, it *shall* end its run only when no action is in flight, or on a cancellation it observes in its wait ([EXEC-041])."
        "*While* the executor is closed, no terminal place is marked and no action is in flight, it *shall* take no step at a termination test ([EXEC-040]) other than ending its run."
        "*While* the executor is closed, it *shall* remove an action from the actions in flight only by settling its outcome."
        "*While* the executor is closed, it *shall* end step 1b of a cycle ([EXEC-001]) only when no publication is queued."
  reading "For every executor R and every configuration C:"
          "a close step sets the mode to closed and changes no field of the state but the mode and the parked flag: the marking, the clock readings now and cyc, the clock statuses, the firings in flight, the completion, publication and event queues, the identity supply, the loop phase and the pass's remaining order, hidden tail and started flag stay as they are;"
          "a request step from a closed state is not accepted and leaves the state as it is;"
          "a step that turns a mode other than closed into closed is a close step;"
          "a step that turns the closed mode into another mode is an immediate termination step;"
          "while the mode is closed, no inject step happens;"
          "a finish step from a closed state, whatever its cause, leaves the event queue empty;"
          "a finish step from a closed state with no terminal place marked happens only when no firing is in flight;"
          "while the mode is closed, no terminal place is marked, the phase is the termination test and no firing is in flight, no step happens that is neither an outside step nor a finish (an answer to a snapshot request that leaves the state as it is is not a step of the loop and is allowed);"
          "a step from a closed state after which a firing identity in flight before it is no longer in flight is a commit, fail or tdeposit step of that firing;"
          "an endPublications step (the end of step 1b) from a closed state happens only when the publication queue is empty."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The close is the outside step close; the closed mode is Mode.closed. The witness is the reference executor RefExec (Reference/Exec.lean), whose close rule (closeStep) takes a close from the open or the draining mode."
          "Naming: the markdown's 'the executor takes a close' is the close step. In Java and TypeScript that is the call of close(), which sets the closed flag the loop and inject() read, except for a call that lands while the loop is injecting queued events in step 2: the loop reads the flag once, before that injection (BitmapNetExecutor and PrecompiledNetExecutor processExternalEvents; bitmap-net-executor.ts and precompiled-net-executor.ts processExternalEvents), and does not read it again until the injection ends, so the events it injects after the call (in TypeScript, a close() made from an EventStore append inside the walk; in Java, a close() from another thread during the poll loop) are completed with true. The quoted sentence 'In Java and TypeScript the executor takes the close when ...' places the close step for such a call where that injection ends, before the step 2 discards and endEvents: those injections come before the close step, and line 5 binds what follows it. An inject() call refused in that window (inject() reads the flag itself) changes nothing (line 2), so the model places it after the close step, as it does for Rust below; so does a snapshot() call refused in that window (ENV-014). In Rust it is the executor reading the Close signal in Phase 2 (executor_core/executor.rs handle_signal, Close arm); the handle refuses injections from the call of close() (executor_handle.rs close sets drained), and every event sent before the call travels the channel ahead of the Close. A Rust run is therefore the model run in which the injections of those events come before the close step and the requests refused by the handle come after it: a refused request changes nothing (line 2), so placing it after the close step changes no state. One injector per run is assumed (Rust's events from a second sender, sent after the Close, are answered true and dropped by the Close arm), as in the reference's own notes on D44 (a)."
          "Item 1 and AC4 ('inject() returns error/false after close') are line 2: a request to a closed executor is refused (an environment place) or an error (not one, Java and TypeScript), never accepted, and queues nothing (ENV_013_forbids_closedAccepts). Which of refused and error, and the false or error value inject() hands the caller, are ENV-002's and ENV-006's subject."
          "Item 2, AC2 and ruling D44 (a): line 5 is the common line, 'a closed executor injects no queued event' (ENV_013_forbids_closedInjects), and line 6 says no event is left queued when a closed run ends (ENV_013_forbids_finishKeepsQueue). An event still queued after the close leaves the queue by a discard step or by the finish. Java completes it with false at loop exit (drainPendingExternalEvents); the reference also offers the discard in step 2 and in the wait, so the markdown's informative sentence on when Java and TypeScript answer such an inject() names no instant and is not a line. That the answer is false exactly at the discard or the finish is ENV-004's line. Which accepted events are still queued at the close is implementation shape, kind N: Java and TypeScript discard every event still queued when they take the close (when the flag is set, or when a step-2 injection under way at the call ends); Rust and Python inject every event sent before the close (the run of the naming assumption) and answer inject() at enqueue time."
          "Item 3, AC3 and the shutdown being a close, not a stop: line 1 keeps the firings in flight, their queued outcomes and their queued publications at the close (ENV_013_forbids_closeAbandons), line 9 says a firing leaves the firings in flight while closed only by being settled (ENV_013_forbids_closedDropsInFlight: a closed executor that abandons its firings at step 1 and then finishes closed with nothing in flight), line 10 says a closed executor ends step 1b only with no publication queued, so a batch an action flushed is still published after the close, as ruling D17 has it for every published token (ENV_013_forbids_closedSkipsPublications: a closed executor that stops publishing and finishes with the batch lost), and line 7 says the run ends, with no terminal place marked, only when none is in flight (ENV_013_forbids_finishInFlight). Together they are 'in-flight actions complete before termination'. Line 9 does not say where a settle happens (step 1, the wait or the pass); that is EXEC-001's. That the actions do return, and that a returned outcome is settled, is coverage, not a line here: ExecCovers (every firing in flight can return) and ValidatedBy (every completion the loop may settle is settled) in the consistency theorem (ConsistencyExec.lean), neither of which depends on the mode; settlement in the closed mode is the reference's commit, as spec/04-execution-model.md says of a close (it waits for the actions in flight and takes their completions up in step 1), exercised by ENV_013_nonvacuous. An executor that takes no step at all after the close passes every line here; it fails that coverage. The seventh shall sentence's 'or on a cancellation it observes in its wait ([EXEC-041])' is out of the model, which has no interrupt (EXEC-041's assumes): line 7 states the sentence without it, and Java's interrupt path (awaitCompletionPolling ending the loop interrupted while closed with actions in flight, BitmapNetExecutor.java 2062-2070) is that cancellation, allowed by EXEC-041 and not a run of the model."
          "Item 4 and ruling D85 (a): line 7 is 'terminates after in-flight actions complete'; line 8 is 'it terminates at the first termination test that finds no action in flight': at such a test, with no terminal place marked, a closed executor takes no executor step but a finish (EXEC-040's line 3 read with nothing in flight in place of Rest), in particular it begins no firing pass (ENV_013_forbids_closeWaitsForQuiescence: a close that behaves as a drain, starting a ready transition with nothing in flight). That a finish is in fact offered at such a test is coverage: Env013Covers, a clause of the consistency theorem's ExecCoversW5 (ConsistencyExec.lean), asks for finish closed at every such test, and the reference offers it (env013_finish_offered). Line 8 alone is safety: an executor that offers no step at such a test (one whose finish closed also waits for the event queue to empty, which no closed step ever empties) passes this block and fails Env013Covers. Line 8 bans loop steps only: answering a snapshot request, which is not a step of the loop (EXEC-041, EXEC-042), is allowed at the test provided it changes nothing (the exemption EXEC-042's line 1 makes). The permission 'may start ready transitions' while an action is in flight is the reference starting a firing after the close (ENV_013_nonvacuous); a close therefore does not bound the run (the quoted 'A close alone therefore does not bound ...' sentence), and the bound is ENV-015's immediate termination; a run budget (ENV-016) bounds only the caller's wait, since its expiry ends the wait and not the loop (EXEC-041; under the close policy it is a close, ENV-016's line 2)."
          "'A close does not stop the firing pass.' is line 1 at the close step: the phase, the pass's remaining order, its hidden tail and its started flag stay (ENV_013_forbids_closeStopsPass: a close taken mid-pass that empties the order, so the ready transitions left in it never start). The steps after the close are EXEC-003's: its endPass line, which reads no mode, ends a pass only with the order exhausted, so an executor that ends a closed pass early breaks EXEC-003, not this block. Line 1 also keeps the clock readings now and cyc, at which steps 4 and 5 judge readiness, and the identity supply."
          "Scope (ENVB-R7 item 7, D20): the markdown's 'unless a terminal place is marked ([EXEC-042])' is the premise Live C s of lines 7 and 8. A terminal stop ends the run whatever is in flight, the firings abandoned (EXEC-042's finish terminal, which keeps them in the state); lines 6 and 9 hold across it (the finish clears the event queue, and an abandoned firing is not removed). The cause the finish reports is EXEC-041's: at a rest reached after a close the reference offers both quiescent and closed (ruling D53 (c), ENV_013_nonvacuous)."
          "The mode lines 3 and 4 pin what EXEC-041's lines 6 and 7 read as 'a close was requested': the mode becomes closed only by a close (ENV_013_forbids_drainCloses) and stays closed until the run ends unless an immediate termination ([ENV-015], Java, Mode.stopped) replaces it (ENV_013_forbids_drainReopens). The escalation sentence 'Calling `close()` after `drain()` escalates from graceful to immediate shutdown.' is the reference's close from the draining mode (ENV_013_nonvacuous), after which every closed line applies. That the close is offered at all, from the open mode ('provides a `close()` method') and from the draining mode (the escalation), is coverage, not a line: inside the consistency theorem ENV-016's coverage clause Env016Covers and its line 2 carry it (an expiry under the close policy is offered in every executing phase and is a close step from the open and the draining mode), and the reference offers the close from both modes in every phase (env013_close_offered). A second close of a closed executor is no step of the reference (Rust and Java return without effect); line 1 does not need it."
          "AC1 ('close() signals immediate shutdown') is line 1: the close step enters the closed mode, which every other line reads. Waking the wait on a close is CONC-010's (the reference's close clears parked), which is why line 1 leaves the parked flag free."
          "The test derivation (an executor with an action in flight is closed; the action completes; queued events are discarded; the executor terminates) is ENV_013_nonvacuous's run: an event queued before the close is discarded, a request after it is refused, the firing in flight is committed after the close, and the run finishes closed with nothing in flight. A second run of ENV_013_nonvacuous publishes, after the close, a batch the action flushed before it."
  signoff "2026-11-13 441f6e161f28b830 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (on (fun s s' => R C s .close s'), shall (fun s s' =>
        s' = { s with mode := .closed, parked := s'.parked })) ∧
      (∀ p x r, on (fun s s' => s.mode = .closed ∧ R C s (.request p x r) s'),
        shall (fun s s' => r ≠ .accepted ∧ s' = s)) ∧
      (∀ l, on (fun s s' => s.mode ≠ .closed ∧ s'.mode = .closed ∧ R C s l s'),
        shall (fun _ _ => l = .close)) ∧
      (∀ l, on (fun s s' => s.mode = .closed ∧ s'.mode ≠ .closed ∧ R C s l s'),
        shall (fun _ _ => l = .terminateNow)) ∧
      (while (fun s => s.mode = .closed), never (fun s s' => ∃ k, R C s (.inject k) s')) ∧
      (∀ c, on (fun s s' => s.mode = .closed ∧ R C s (.finish c) s'),
        shall (fun _ s' => s'.eq = [])) ∧
      (∀ c, on (fun s s' => Live C s ∧ s.mode = .closed ∧ R C s (.finish c) s'),
        shall (fun s _ => s.fl = [])) ∧
      (while (fun s => s.mode = .closed ∧ Live C s ∧ s.phase = .test ∧ s.fl = []),
        never (fun s s' => ∃ l, R C s l s' ∧ l.outside = false ∧
          (∀ a, l = .snapshot a → s' ≠ s) ∧ ∀ c, l ≠ .finish c)) ∧
      (∀ i l, on (fun s s' => s.mode = .closed ∧ i ∈ s.fl.map (·.id) ∧
          i ∉ s'.fl.map (·.id) ∧ R C s l s'),
        shall (fun _ _ => l = .commit i ∨ l = .fail i ∨ l = .tdeposit i)) ∧
      (on (fun s s' => s.mode = .closed ∧ R C s .endPublications s'), shall (fun s _ => s.pq = []))

/- The pinned readable form of ENV-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_013 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (on fun s s' => R C s XLbl.close s', shall fun s s' =>
        s' =
          { M := s.M, now := s.now, cyc := s.cyc, st := s.st, fl := s.fl, nextId := s.nextId, cq := s.cq, pq := s.pq,
            eq := s.eq, mode := Mode.closed, phase := s.phase, order := s.order, delta := s.delta, started := s.started,
            parked := s'.parked }) ∧
      (∀ (p : N) (x : T) (r : Reply),
          on fun s s' => s.mode = Mode.closed ∧ R C s (XLbl.request p x r) s', shall fun s s' =>
            r ≠ Reply.accepted ∧ s' = s) ∧
        (∀ (l : XLbl N T),
            on fun s s' => s.mode ≠ Mode.closed ∧ s'.mode = Mode.closed ∧ R C s l s', shall fun x x_1 =>
              l = XLbl.close) ∧
          (∀ (l : XLbl N T),
              on fun s s' => s.mode = Mode.closed ∧ s'.mode ≠ Mode.closed ∧ R C s l s', shall fun x x_1 =>
                l = XLbl.terminateNow) ∧
            (while fun s => s.mode = Mode.closed, never fun s s' => ∃ k, R C s (XLbl.inject k) s') ∧
              (∀ (c : Cause),
                  on fun s s' => s.mode = Mode.closed ∧ R C s (XLbl.finish c) s', shall fun x s' => s'.eq = []) ∧
                (∀ (c : Cause),
                    on fun s s' => Live C s ∧ s.mode = Mode.closed ∧ R C s (XLbl.finish c) s', shall fun s x =>
                      s.fl = []) ∧
                  (while fun s => s.mode = Mode.closed ∧ Live C s ∧ s.phase = Phase.test ∧ s.fl = [], never fun s s' =>
                      ∃ l,
                        R C s l s' ∧
                          l.outside = false ∧
                            (∀ (a : Option Bool), l = XLbl.snapshot a → s' ≠ s) ∧ ∀ (c : Cause), l ≠ XLbl.finish c) ∧
                    (∀ (i : ℕ) (l : XLbl N T),
                        on fun s s' =>
                          s.mode = Mode.closed ∧
                            i ∈ List.map (fun x => x.id) s.fl ∧ i ∉ List.map (fun x => x.id) s'.fl ∧ R C s l s',
                          shall fun x x_1 => l = XLbl.commit i ∨ l = XLbl.fail i ∨ l = XLbl.tdeposit i) ∧
                      on fun s s' => s.mode = Mode.closed ∧ R C s XLbl.endPublications s', shall fun s x => s.pq = []
-/
#guard_msgs in #print ENV_013

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- Every step of the reference other than a drain, a close or an immediate termination keeps
the mode: each inversion lemma gives the target as the source with other fields updated. -/
theorem env013_mode_frame {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
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
/-- Settling firing `j` keeps every other firing identity in flight. -/
theorem env013_settle_ids {s : XSt N T} {i j : Nat} (hi : i ∈ s.fl.map (·.id)) (hij : i ≠ j) :
    i ∈ (settle s j).fl.map (·.id) := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hf, by simpa using hij⟩, rfl⟩

/-- In the reference, a firing identity leaves the firings in flight only by a settle step of
that firing: every other rule keeps the list, updates records in place, appends a started firing,
or (a finish) keeps the abandoned ones. -/
theorem env013_ids {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {i : Nat}
    (h : RefExec C s l s') (hi : i ∈ s.fl.map (·.id)) (hi' : i ∉ s'.fl.map (·.id)) :
    l = .commit i ∨ l = .fail i ∨ l = .tdeposit i := by
  have hout : l.outside = true → False := fun ho => by
    have := (xstepW_outside_frame h ho).2.2.2.1
    rw [this] at hi'
    exact hi' hi
  cases l with
  | commit j =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some (P := refXPol) h
    by_cases hij : i = j
    · exact Or.inl (by rw [hij])
    · exact absurd (env013_settle_ids hi hij) hi'
  | fail j =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some (P := refXPol) h
    by_cases hij : i = j
    · exact Or.inr (Or.inl (by rw [hij]))
    · exact absurd (env013_settle_ids hi hij) hi'
  | tdeposit j =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    by_cases hij : i = j
    · exact Or.inr (Or.inr (by rw [hij]))
    · exact absurd (env013_settle_ids hi hij) hi'
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact absurd hi hi'
  | publish j => obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h; exact absurd hi hi'
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact absurd hi hi'
  | inject k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h; exact absurd hi hi'
  | discard k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h; exact absurd hi hi'
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact absurd hi hi'
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact absurd hi hi'
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact absurd hi hi'
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact absurd hi hi'
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact absurd hi hi'
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some (P := refXPol) h
    exact (hi' (by rw [List.map_append]; exact List.mem_append_left _ hi)).elim
  | lose n => obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h; exact absurd hi hi'
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact absurd hi hi'
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact absurd hi hi'
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact absurd hi hi'
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact absurd hi hi'
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact absurd hi hi'
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact absurd hi hi'
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact absurd hi hi'
  | _ => exact (hout rfl).elim

end Reference

/-- ✓ The reference executor satisfies ENV-013: its close rule changes only the mode and the
parked flag (`closeStep_some`); a request answers `replyFor`, never accepted unless open
(`requestStep_some`); only drain, close and the immediate termination change the mode
(`env013_mode_frame`); injection needs a mode that is not closing (`injectStep_some`); every
finish clears the event queue; a finish from a live closed state has nothing in flight (the
quiescent finish reads rest, the closed finish reads `fl = []`); at the termination test only
`begin` and a finish are executor steps (`exec040_test_step`), and the begin rule refuses a closed
state with nothing in flight (`xstepW_begin`); only a settle step removes a firing (`env013_ids`);
and step 1b ends only on an empty publication queue, in every mode (`xstepW_endPublications`). -/
@[evidence holds ENV_013]
theorem ENV_013_reference {N T : Type} [DecidableEq N] :
    ENV_013 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun s s' h => ?_, fun p x r s s' ⟨hm, h⟩ => ?_, fun l s s' ⟨hm, hm', h⟩ => ?_,
    fun l s s' ⟨hm, hm', h⟩ => ?_, fun s s' ⟨k, h⟩ hm => ?_, fun c s s' ⟨hm, h⟩ => ?_,
    fun c s s' ⟨hl, hm, h⟩ => ?_, fun s s' ⟨l, h, ho, _, hf⟩ ⟨hm, _, hp, hfl⟩ => ?_,
    fun i l s s' ⟨_, hi, hi', h⟩ => env013_ids h hi hi',
    fun s s' ⟨_, h⟩ => (xstepW_endPublications h).2.2.1⟩
  · obtain ⟨-, rfl⟩ := closeStep_some h
    rfl
  · obtain ⟨hr, ⟨ha, -⟩ | ⟨ha, rfl⟩⟩ := requestStep_some h
    · exfalso
      rw [ha] at hr
      unfold replyFor at hr
      split at hr
      · exact absurd hr (by simp)
      · rw [hm] at hr
        simp at hr
    · exact ⟨ha, rfl⟩
  · by_cases hc : l = .close
    · exact hc
    · exfalso
      by_cases hd : l = .drain
      · subst hd
        obtain ⟨-, rfl⟩ := drainStep_some h
        simp at hm'
      · by_cases ht : l = .terminateNow
        · subst ht
          obtain ⟨-, rfl⟩ := terminateStep_some h
          simp at hm'
        · rw [env013_mode_frame h hd hc ht] at hm'
          exact hm hm'
  · by_cases ht : l = .terminateNow
    · exact ht
    · exfalso
      by_cases hd : l = .drain
      · subst hd
        obtain ⟨h0, -⟩ := drainStep_some h
        rw [hm] at h0
        exact absurd h0 (by decide)
      · by_cases hc : l = .close
        · subst hc
          obtain ⟨h0, -⟩ := closeStep_some h
          rw [hm] at h0
          rcases h0 with h0 | h0 <;> exact absurd h0 (by decide)
        · rw [env013_mode_frame h hd hc ht] at hm'
          exact hm' hm
  · obtain ⟨p, x, rest, -, -, hcl, -, -⟩ := injectStep_some h
    rw [hm] at hcl
    exact absurd hcl (by decide)
  · cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  · cases c with
    | quiescent =>
      obtain ⟨-, -, hq, -⟩ := xstepW_finishQuiescent h
      simp only [finishQ, restB, Bool.and_eq_true, List.isEmpty_iff] at hq
      exact hq.1.1.1.1.2
    | closed => exact (xstepW_finishClosed h).2.2.2.1
    | terminal =>
      obtain ⟨-, hl', -⟩ := xstepW_finishTerminal h
      exact absurd hl (by simp [Live, hl'])
    | stopped =>
      obtain ⟨-, -, hst, -⟩ := xstepW_finishStopped h
      rw [hm] at hst
      exact absurd hst (by decide)
  · rcases exec040_test_step hp h with ho' | rfl | ⟨c, rfl⟩
    · rw [ho] at ho'
      exact absurd ho' (by decide)
    · obtain ⟨-, -, -, hn, -⟩ := xstepW_begin h
      exact hn ⟨by rw [hm]; rfl, hfl⟩
    · exact hf c rfl

/-! ### Examples

One transition `t` takes a token from place `0` and outputs to place `1`, immediately; place `2`
is the environment place; the executor is re-entrant (Rust, Python), so `t` starts again while a
firing of it is in flight. Validation and the relay check accept everything. -/

/-- The transition `t`: one token from `0`, output spec `1`. -/
def env013_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples: `t`, environment place `2`, re-entrant. -/
def env013_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [env013_t] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [2], reentrant := true,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking with `n` tokens (`7`, `8`, ...) in place `0`. -/
def env013_m0 (n : Nat) : QMarking Nat Nat := fun p => if p = 0 then (List.range n).map (· + 7) else []

/-- One cycle up to the end of the firing pass that starts `t` (firing `0`). -/
def env013_cycleStart : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false,
   .endPass]

/-- The steps of a cycle up to the termination test. -/
def env013_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The scenario of the test derivation, before its labelled step `l`, from two tokens in `0`:
`t` starts (firing `0`); an event is queued (ticket `1`); the executor drains, then closes
(escalation); a request is refused; step 1 finds nothing, the event is discarded; `t` starts
again while firing `0` is in flight (firing `2`, ruling D85 (a)); both actions return and are
committed; the next cycle reaches the termination test with nothing in flight. -/
def env013_scenario : List (XLbl Nat Nat) :=
  env013_cycleStart ++
  [.request 2 5 .accepted, .drain, .close, .request 2 6 .refused,
   .endCompletions, .endPublications, .discard 1, .endEvents, .update, .deadline [], .begin,
   .start "t" false, .endPass,
   .write 0 1 70, .ret 0 true, .write 2 1 80, .ret 2 true, .commit 0, .commit 2] ++
  env013_toTest

/-- The reference state after the first `n` labels of the scenario. -/
def env013_at (n : Nat) : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 2) 0) (env013_scenario.take n)

/-- The labels of the scenario, numbered from `0`. -/
def env013_lbl (n : Nat) : XLbl Nat Nat := env013_scenario.getD n .wake

/-- A closed state with one firing in flight (`0`, not returned), at the start of step 1: one
token in `0`, `t` started, then closed. -/
def env013_closedFlight : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 1) 0) (env013_cycleStart ++ [.close])

/-- A closed state at the termination test with one firing in flight. -/
def env013_closedFlightTest : Option (XSt Nat Nat) :=
  env013_closedFlight.bind fun s => xrun env013_cfg s env013_toTest

/-- A closed state at the termination test with nothing in flight and `t` armed: one token in
`0`, closed before the first cycle. -/
def env013_closedArmedTest : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 1) 0) (.close :: env013_toTest)

/-- A closed state at the termination test with an event queued: a request accepted at the test
of an open executor with nothing to do, then a close. -/
def env013_closedQueuedTest : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 0) 0) (env013_toTest ++ [.request 2 5 .accepted, .close])

/-- A closed state in step 2 with an event queued. -/
def env013_closedQueuedEvents : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 0) 0)
    [.request 2 5 .accepted, .close, .endCompletions, .endPublications]

/-- A state inside the firing pass with `t` at the head of the order: one token in `0`, the first
cycle up to its `begin`. -/
def env013_inPass : Option (XSt Nat Nat) :=
  xrun env013_cfg (xinit (env013_m0 1) 0) (env013_toTest ++ [.begin])

/-- Firing `0` of `t` starts, its action writes `70` to place `1` and flushes the batch, the
executor closes, the action returns, and the next cycle commits it and ends step 1. -/
def env013_flushedPre : List (XLbl Nat Nat) :=
  env013_cycleStart ++ [.write 0 1 70, .flush 0, .close, .ret 0 true, .commit 0, .endCompletions]

/-- Run a step function over a list of labels from `s`, under `env013_cfg`. -/
def env013_runWith (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat))
    (s : XSt Nat Nat) : List (XLbl Nat Nat) → Option (XSt Nat Nat)
  | [] => some s
  | l :: ls => (g env013_cfg s l).bind fun s' => env013_runWith g s' ls

/-! ### Coverage lemmas

The two lemmas the coverage conjuncts of the consistency theorem are proved from (assumes of the
block): the reference offers a close from the open and the draining modes in every phase, and a
closed finish at every termination test of a live closed executor with nothing in flight. -/

section Coverage

variable {N T : Type} [DecidableEq N]

/-- The reference offers a close from the open and from the draining mode, in every phase. -/
theorem env013_close_offered (C : Cfg N T) (s : XSt N T) (hm : s.mode = .open ∨ s.mode = .draining) :
    ∃ s', RefExec C s .close s' := by
  refine ⟨{ s with mode := .closed, parked := false }, ?_⟩
  rcases hm with hm | hm <;> simp [RefExec, xstep, xstepW, closeStep, hm]

/-- The reference offers a closed finish at every termination test of a live closed executor
with nothing in flight. -/
theorem env013_finish_offered (C : Cfg N T) (s : XSt N T) (hL : Live C s) (hp : s.phase = .test)
    (hm : s.mode = .closed) (hfl : s.fl = []) :
    ∃ s', RefExec C s (.finish .closed) s' := by
  have hl : liveB C s = true := hL
  exact ⟨{ s with phase := .done .closed, eq := [] }, by
    simp [RefExec, xstep, xstepW, hp, hl, hm, hfl, Mode.closing]⟩

end Coverage

/-! ### Every line exercised -/

/-- Every line of ENV-013 is exercised by the reference on the scenario of the test derivation:
the close is taken from the draining mode (escalation) with a firing in flight and an event
queued, and both stay; a request to the closed executor is refused; the queued event is
discarded; `t` starts again while firing `0` is in flight (ruling D85 (a): a closed executor may
start ready transitions while an action is in flight, so the begin and the start happen in the
closed mode); firing `0` returns and is committed in the closed mode (the action completes and
its result is deposited); the run reaches the termination test with nothing in flight and finishes
closed, and quiescent is offered there too (ruling D53 (c)); a closed run with an event still
queued finishes with the queue empty. A close taken inside a firing pass keeps the rest of the
order, and a closed executor publishes a batch its action flushed before the close. -/
@[evidence nonvacuous ENV_013]
theorem ENV_013_nonvacuous :
    (∃ s s', RefExec env013_cfg s .close s' ∧ s.mode = .draining ∧ s.fl ≠ [] ∧ s.eq ≠ [] ∧
      s'.fl = s.fl ∧ s'.eq = s.eq) ∧
    (∃ s s', RefExec env013_cfg s (.request 2 6 .refused) s' ∧ s.mode = .closed) ∧
    (∃ s s', RefExec env013_cfg s (.discard 1) s' ∧ s.mode = .closed) ∧
    (∃ s s', RefExec env013_cfg s .begin s' ∧ s.mode = .closed ∧ s.fl ≠ []) ∧
    (∃ s s', RefExec env013_cfg s (.start "t" false) s' ∧ s.mode = .closed ∧ s.fl ≠ []) ∧
    (∃ s s', RefExec env013_cfg s (.commit 0) s' ∧ s.mode = .closed ∧ s'.M 1 = [70]) ∧
    (∃ s s', RefExec env013_cfg s (.finish .closed) s' ∧ s.mode = .closed ∧ s'.M 1 = [70, 80] ∧
      ∃ s'', RefExec env013_cfg s (.finish .quiescent) s'') ∧
    (∃ s s', RefExec env013_cfg s (.finish .closed) s' ∧ s.mode = .closed ∧ s.eq ≠ [] ∧
      s'.eq = []) ∧
    (∃ s s', RefExec env013_cfg s .close s' ∧ s.phase = .pass ∧ s.order ≠ [] ∧
      s'.order = s.order) ∧
    (∃ s s', RefExec env013_cfg s (.publish 0) s' ∧ s.mode = .closed ∧ s'.M 1 = [70]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 10)
      (l := .close)
      (p := fun s _ => s.mode == .draining && !s.fl.isEmpty && !s.eq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨-, rfl⟩ := closeStep_some hs
    exact ⟨s, _, hs, hp.1.1, hp.1.2, hp.2, rfl, rfl⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 11)
      (l := .request 2 6 .refused) (p := fun s _ => s.mode == .closed) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 14)
      (l := .discard 1) (p := fun s _ => s.mode == .closed) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 18)
      (l := .begin) (p := fun s _ => s.mode == .closed && !s.fl.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 19)
      (l := .start "t" false) (p := fun s _ => s.mode == .closed && !s.fl.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_at 25)
      (l := .commit 0) (p := fun s s' => s.mode == .closed && s'.M 1 == [70]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env013_cfg)
      (o := env013_at env013_scenario.length)
      (l := .finish .closed) (p := fun s s' => s.mode == .closed && s'.M 1 == [70, 80] &&
        (xstep env013_cfg s (.finish .quiescent)).isSome) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_closedQueuedTest)
      (l := .finish .closed) (p := fun s s' => s.mode == .closed && !s.eq.isEmpty && s'.eq.isEmpty)
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.isEmpty_iff] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg) (o := env013_inPass)
      (l := .close) (p := fun s _ => decide (s.phase = .pass) && !s.order.isEmpty) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at hp
    obtain ⟨-, rfl⟩ := closeStep_some hs
    exact ⟨s, _, hs, hp.1, hp.2, rfl⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env013_cfg)
      (o := xrun env013_cfg (xinit (env013_m0 1) 0) env013_flushedPre) (l := .publish 0)
      (p := fun s s' => s.mode == .closed && s'.M 1 == [70]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩

/-! ### Violation: a close that abandons the actions in flight (line 1) -/

/-- An executor whose close also drops the firings in flight and their queued outcomes (an
implicit immediate termination at the close); otherwise the reference. -/
def env013_closeAbandonsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => (xstep C s .close).map fun s₁ => { s₁ with fl := [], cq := [] }
  | l => xstep C s l

/-- The executor of `env013_closeAbandonsStep`. -/
def env013_closeAbandons {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closeAbandonsStep C s l = some s'

/-- ✗ A close that abandons the actions in flight violates ENV-013 (line 1, item 3): with firing
`0` in flight, the close drops it. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closeAbandons :
    ¬ ENV_013 (env013_closeAbandons (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closeAbandonsStep (C := env013_cfg)
    (o := xrun env013_cfg (xinit (env013_m0 1) 0) env013_cycleStart) (l := .close)
    (p := fun s s' => s'.fl.length != s.fl.length) (by decide)
  have hf : s'.fl = s.fl := by rw [(h env013_cfg).1 s s' hs]
  simp [hf] at hp

/-! ### Violation: a close that stops the firing pass (line 1) -/

/-- An executor whose close also drops the rest of the pass's ready order, so the ready
transitions left in it are not started (a close read as "fire nothing more"); otherwise the
reference. -/
def env013_closeStopsPassStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => (xstep C s .close).map fun s₁ => { s₁ with order := [] }
  | l => xstep C s l

/-- The executor of `env013_closeStopsPassStep`. -/
def env013_closeStopsPass {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closeStopsPassStep C s l = some s'

/-- ✗ A close that stops the firing pass violates ENV-013 (line 1, 'A close does not stop the
firing pass.'): closed inside the pass of `env013_inPass` with `t` at the head of the order, the
order is emptied, so the pass can end without starting `t`. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closeStopsPass :
    ¬ ENV_013 (env013_closeStopsPass (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closeStopsPassStep (C := env013_cfg)
    (o := env013_inPass) (l := .close) (p := fun s s' => s'.order.length != s.order.length)
    (by decide)
  have ho : s'.order = s.order := by rw [(h env013_cfg).1 s s' hs]
  simp [ho] at hp

/-! ### Violation: accepting requests while closed (line 2) -/

/-- An executor that accepts and queues a request to an environment place while the loop runs,
whatever its mode; otherwise the reference. -/
def env013_closedAcceptsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x .accepted =>
    if p ∈ C.envs ∧ isExecPhase s.phase = true then
      some { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1, parked := false }
    else none
  | l => xstep C s l

/-- The executor of `env013_closedAcceptsStep`. -/
def env013_closedAccepts {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closedAcceptsStep C s l = some s'

/-- ✗ Accepting an injection after the close violates ENV-013 (line 2, item 1, AC4): the closed
executor of `env013_closedFlight` accepts the event `5` for place `2`. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closedAccepts :
    ¬ ENV_013 (env013_closedAccepts (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closedAcceptsStep (C := env013_cfg)
    (o := env013_closedFlight) (l := .request 2 5 .accepted)
    (p := fun s _ => s.mode == .closed) (by decide)
  exact ((h env013_cfg).2.1 2 5 .accepted s s' ⟨by simpa using hp, hs⟩).1 rfl

/-! ### Violation: a drain that closes (line 3) -/

/-- An executor whose drain closes the executor; otherwise the reference. -/
def env013_drainClosesStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => (xstep C s .drain).map fun s₁ => { s₁ with mode := .closed }
  | l => xstep C s l

/-- The executor of `env013_drainClosesStep`. -/
def env013_drainCloses {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_drainClosesStep C s l = some s'

/-- ✗ A drain that closes violates ENV-013 (line 3): the open executor enters the closed mode by a
drain, so the queued events of a graceful drain would be discarded. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_drainCloses :
    ¬ ENV_013 (env013_drainCloses (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_drainClosesStep (C := env013_cfg)
    (o := some (xinit (env013_m0 1) 0)) (l := .drain)
    (p := fun s s' => s.mode == .open && s'.mode == .closed) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have := (h env013_cfg).2.2.1 .drain s s' ⟨by rw [hp.1]; decide, hp.2, hs⟩
  nomatch this

/-! ### Violation: a drain that reopens a closed executor (line 4) -/

/-- An executor whose drain of a closed executor puts it back in the draining mode; otherwise the
reference. -/
def env013_drainReopensStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => if s.mode = .closed then some { s with mode := .draining } else xstep C s .drain
  | l => xstep C s l

/-- The executor of `env013_drainReopensStep`. -/
def env013_drainReopens {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_drainReopensStep C s l = some s'

/-- ✗ Leaving the closed mode by a drain violates ENV-013 (line 4): after the drain, a queued
event would be injected again. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_drainReopens :
    ¬ ENV_013 (env013_drainReopens (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_drainReopensStep (C := env013_cfg)
    (o := env013_closedFlight) (l := .drain)
    (p := fun s s' => s.mode == .closed && s'.mode == .draining) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have := (h env013_cfg).2.2.2.1 .drain s s' ⟨hp.1, by rw [hp.2]; decide, hs⟩
  nomatch this

/-! ### Violation: injecting a queued event after the close (line 5) -/

/-- An executor that injects queued events whatever its mode (it reads the close only at its
termination test); otherwise the reference. -/
def env013_closedInjectsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k =>
    (injectStep C { s with mode := .open } k).map fun s₁ => { s₁ with mode := s.mode }
  | l => xstep C s l

/-- The executor of `env013_closedInjectsStep`. -/
def env013_closedInjects {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closedInjectsStep C s l = some s'

/-- ✗ Injecting after the close violates ENV-013 (line 5, item 2, AC2): the event `5` queued
before the close is injected in step 2 of the closed executor. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closedInjects :
    ¬ ENV_013 (env013_closedInjects (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closedInjectsStep (C := env013_cfg)
    (o := env013_closedQueuedEvents) (l := .inject 0)
    (p := fun s _ => s.mode == .closed) (by decide)
  exact (h env013_cfg).2.2.2.2.1 s s' ⟨0, hs⟩ (by simpa using hp)

/-! ### Violation: ending a closed run with events still queued (line 6) -/

/-- An executor whose closed finish leaves the event queue as it is (the awaited `inject()` of a
queued event is never answered); otherwise the reference. -/
def env013_finishKeepsQueueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .closed => (xstep C s (.finish .closed)).map fun s₁ => { s₁ with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env013_finishKeepsQueueStep`. -/
def env013_finishKeepsQueue {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_finishKeepsQueueStep C s l = some s'

/-- ✗ Ending a closed run with an event still queued violates ENV-013 (line 6, item 2): the event
accepted just before the close is still queued after the finish. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_finishKeepsQueue :
    ¬ ENV_013 (env013_finishKeepsQueue (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_finishKeepsQueueStep (C := env013_cfg)
    (o := env013_closedQueuedTest) (l := .finish .closed)
    (p := fun s s' => s.mode == .closed && !s'.eq.isEmpty) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact hp.2 ((h env013_cfg).2.2.2.2.2.1 .closed s s' ⟨hp.1, hs⟩)

/-! ### Violation: ending a closed run with an action in flight (line 7) -/

/-- An executor whose closed finish does not wait for the firings in flight (the close read as an
immediate termination); otherwise the reference. -/
def env013_finishInFlightStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .closed =>
    if s.phase = .test ∧ liveB C s = true ∧ s.mode.closing = true then
      some { s with phase := .done .closed, eq := [] }
    else none
  | l => xstep C s l

/-- The executor of `env013_finishInFlightStep`. -/
def env013_finishInFlight {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_finishInFlightStep C s l = some s'

/-- ✗ Ending a closed run with an action in flight violates ENV-013 (line 7, items 3 and 4,
AC3): the closed executor of `env013_closedFlightTest` finishes with firing `0` in flight and no
terminal place marked. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_finishInFlight :
    ¬ ENV_013 (env013_finishInFlight (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_finishInFlightStep (C := env013_cfg)
    (o := env013_closedFlightTest) (l := .finish .closed)
    (p := fun s _ => s.mode == .closed && liveB env013_cfg s && !s.fl.isEmpty) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact hp.2 ((h env013_cfg).2.2.2.2.2.2.1 .closed s s' ⟨hp.1.2, hp.1.1, hs⟩)

/-! ### Violation: a close that waits for quiescence, as a drain does (line 8) -/

/-- An executor whose termination test ignores the close: with nothing in flight it begins a
firing pass while anything is armed, ending only at rest (a close read as a drain); otherwise the
reference. -/
def env013_closeWaitsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin =>
    if s.phase = .test ∧ liveB C s = true ∧ finishQ C s = false then
      some { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                    started := false }
    else none
  | l => xstep C s l

/-- The executor of `env013_closeWaitsStep`. -/
def env013_closeWaits {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closeWaitsStep C s l = some s'

/-- ✗ A close that waits for quiescence violates ENV-013 (line 8, item 4, ruling D85 (a)): the
closed executor of `env013_closedArmedTest`, with nothing in flight and `t` armed, begins a
firing pass instead of ending its run. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closeWaitsForQuiescence :
    ¬ ENV_013 (env013_closeWaits (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closeWaitsStep (C := env013_cfg)
    (o := env013_closedArmedTest) (l := .begin)
    (p := fun s _ => s.mode == .closed && liveB env013_cfg s && decide (s.phase = .test) &&
      s.fl.isEmpty) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff] at hp
  exact (h env013_cfg).2.2.2.2.2.2.2.1 s s' ⟨.begin, hs, rfl, (fun _ => nofun), fun _ => nofun⟩
    ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-! ### Violation: dropping an action in flight without settling it (line 9) -/

/-- An executor that, once closed, abandons its firings in flight at the end of step 1 (the
results of a stop, [ENV-015], given to a close); otherwise the reference. -/
def env013_closedDropsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endCompletions =>
    (xstep C s .endCompletions).map fun s₁ =>
      if s.mode = .closed then { s₁ with fl := [], cq := [] } else s₁
  | l => xstep C s l

/-- The executor of `env013_closedDropsStep`. -/
def env013_closedDrops {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closedDropsStep C s l = some s'

/-- ✗ Dropping an action in flight without settling it violates ENV-013 (line 9, item 3): in the
closed executor of `env013_closedFlight`, step 1 drops firing `0`. Line 7 alone does not catch
it, as the run can then finish closed with nothing in flight. -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closedDropsInFlight :
    ¬ ENV_013 (env013_closedDrops (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closedDropsStep (C := env013_cfg)
    (o := env013_closedFlight) (l := .endCompletions)
    (p := fun s s' => s.mode == .closed && s.fl.any (·.id == 0) && !s'.fl.any (·.id == 0))
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨hm, hi⟩, hi'⟩ := hp
  have hmem : (0 : Nat) ∈ s.fl.map (·.id) := by
    obtain ⟨f, hf, hf0⟩ := List.any_eq_true.mp hi
    exact List.mem_map.mpr ⟨f, hf, by simpa using hf0⟩
  have hnot : (0 : Nat) ∉ s'.fl.map (·.id) := by
    intro hm'
    obtain ⟨f, hf, hf0⟩ := List.mem_map.mp hm'
    have := List.any_eq_false.mp hi' f hf
    simp [hf0] at this
  have := (h env013_cfg).2.2.2.2.2.2.2.2.1 0 .endCompletions s s' ⟨hm, hmem, hnot, hs⟩
  rcases this with h1 | h1 | h1 <;> nomatch h1

/-! ### Violation: a closed executor that stops publishing (line 10) -/

/-- An executor that, once closed, publishes nothing and ends step 1b with the publication queue
as it is (the flush channel read under the same guard as the signal channel); otherwise the
reference. -/
def env013_closedSkipsPublicationsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i => if s.mode = .closed then none else xstep C s (.publish i)
  | .endPublications =>
    if s.mode = .closed then
      (if s.phase = .publications ∧ liveB C s = true then some { s with phase := .events }
       else none)
    else xstep C s .endPublications
  | l => xstep C s l

/-- The executor of `env013_closedSkipsPublicationsStep`. -/
def env013_closedSkipsPublications {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env013_closedSkipsPublicationsStep C s l = some s'

/-- ✗ A closed executor that stops publishing violates ENV-013 (line 10, item 3, ruling D17):
the batch `[(1, 70)]` that firing `0` flushed before the close is still queued when the closed
executor ends step 1b. Every other line accepts this executor: its commit settles the firing, and
the run then finishes closed with nothing in flight, the batch lost
(`env013_closedSkipsPublications_loses`). -/
@[evidence forbids ENV_013]
theorem ENV_013_forbids_closedSkipsPublications :
    ¬ ENV_013 (env013_closedSkipsPublications (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env013_closedSkipsPublicationsStep (C := env013_cfg)
    (o := env013_runWith env013_closedSkipsPublicationsStep (xinit (env013_m0 1) 0)
      env013_flushedPre)
    (l := .endPublications) (p := fun s _ => s.mode == .closed && !s.pq.isEmpty) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact hp.2 ((h env013_cfg).2.2.2.2.2.2.2.2.2 s s' ⟨hp.1, hs⟩)

/-- What the violation costs: the executor of `env013_closedSkipsPublications` reaches the
termination test and finishes closed with the batch still queued and place `1` empty, where the
reference publishes it and finishes with `70` in place `1`. -/
theorem env013_closedSkipsPublications_loses :
    (∃ s s', env013_runWith env013_closedSkipsPublicationsStep (xinit (env013_m0 1) 0)
        (env013_flushedPre ++ [.endPublications, .endEvents, .update, .deadline []]) = some s ∧
      env013_closedSkipsPublicationsStep env013_cfg s (.finish .closed) = some s' ∧
      s'.pq = [(0, [(1, 70)])] ∧ s'.M 1 = []) ∧
    (∃ s s', xrun env013_cfg (xinit (env013_m0 1) 0)
        (env013_flushedPre ++ [.publish 0, .endPublications, .endEvents, .update, .deadline []])
        = some s ∧
      xstep env013_cfg s (.finish .closed) = some s' ∧ s'.M 1 = [70] ∧ s'.pq = []) := by
  constructor
  · obtain ⟨s, s', hs, h, hp⟩ := step_of_check env013_closedSkipsPublicationsStep
      (C := env013_cfg)
      (o := env013_runWith env013_closedSkipsPublicationsStep (xinit (env013_m0 1) 0)
        (env013_flushedPre ++ [.endPublications, .endEvents, .update, .deadline []]))
      (l := .finish .closed) (p := fun _ s' => s'.pq == [(0, [(1, 70)])] && s'.M 1 == [])
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, h, hp.1, hp.2⟩
  · obtain ⟨s, s', hs, h, hp⟩ := step_of_check xstep (C := env013_cfg)
      (o := xrun env013_cfg (xinit (env013_m0 1) 0)
        (env013_flushedPre ++ [.publish 0, .endPublications, .endEvents, .update, .deadline []]))
      (l := .finish .closed) (p := fun _ s' => s'.M 1 == [70] && s'.pq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
    exact ⟨s, s', hs, h, hp.1, hp.2⟩

end Libpetri.Spec
