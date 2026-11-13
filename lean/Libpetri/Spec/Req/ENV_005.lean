import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.ENV_005

set_option linter.missingDocs true

/-!
# ENV-005: inject() Wake-Up (`spec/06-environment-places.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). An accepted injection waits in
the event queue (`XSt.eq`) until step 2 of a cycle puts its token into the marking (`inject k`)
or, once the executor is closed or stopped, discards it (`discard k`); an immediate termination
or the end of the run drops the queue. The requirement is a predicate over an abstract executor
`R : XRel N T` (glossary `GlossaryExec.lean`) with five lines:

* no block while an injection is queued: no `park` step (line 1), and no other step that takes
  the loop from unblocked to blocked (line 2: answering a snapshot in the wait and blocking again
  is a block too);
* the wake-up: an accepted request clears the block marker (line 3, the observable park state that
  CONC-010's arrival line and ENV-014's foreign reader read);
* step 2 does not end (`endEvents`, line 4), and no step enters the enablement update from
  another phase (line 5), while an injection is queued: a loop that skips step 2 cannot get
  around line 4.

The offer, that in a live wait with an injection queued the executor has a way out of the wait (a
`wake` or the injection or discard of a queued ticket), so that leaving the wait never needs a
timer, is coverage: `Env005Covers`, a clause of the consistency theorem's `ExecCoversW5`, never a
line. Lines 1 and 3 are [CONC-010]'s park guard and arrival line restricted to injections; the
consequence theorem from the CONC-010 block is `conc010_env005_lines` (`ConsistencyExec.lean`). The evidence checks the
block against the reference executor and five wrong executors, one per line; a sixth, whose
inject() never signals the wait, meets every line and fails only the coverage clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-005: inject() Wake-Up -/

requirement ENV_005
  id "ENV-005"
  title "inject() Wake-Up"
  kind T
  scope "all executors"
  source verbatim "spec/06-environment-places.md"
  covers ENV_005.s1, ENV_005.s2, ENV_005.s3, ENV_005.s4, ENV_005.s5, ENV_005.s6, ENV_005.s7,
        ENV_005.s8, ENV_005.s9, ENV_005.s10, ENV_005.s11, ENV_005.s12
  reading "For every executor R and every configuration C:"
          "(1) no park step starts in a state whose event queue is not empty;"
          "(2) no step of any label goes from a state that is not parked to a parked one when the event queue of its start state is not empty;"
          "(3) for every place p and token x, a request step for (p, x) answered accepted ends in a state that is not parked;"
          "(4) no step that ends the external-events step (endEvents) starts in a state whose event queue is not empty;"
          "(5) no step goes from a state outside the enablement update phase into it when the event queue of its start state is not empty."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The outside step request p x r is a call of inject(); r = accepted is the call accepting the token, which queues it with a ticket in XSt.eq (ENV-003). Step 2 of a cycle takes queued injections into the marking one at a time (inject k, at the tail of the place, FIFO by ticket) or, once closed or stopped, discards them (discard k, ENV-013), and ends with endEvents, after which the enablement update (phase update) runs. The wait is the loop phase await; park is the loop blocking in it and XSt.parked marks the block; wake is its end (a timer, a spurious wake-up or an arrival), after which the loop runs step 1 again; an injection may also be taken straight from the wait (inject k or discard k from phase await). The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor."
          "Definition of queued: an injection is queued while its ticket is in XSt.eq. The reference takes a ticket out by inject k (into the marking), by discard k (closed or stopped, ENV-013), by terminateNow (ENV-015, the queue dropped at once) and by a finish step (the end of the run: quiescent, closed, or a marked terminal place, EXEC-042). The linearization sentence is how a run places a request: the request is an atomic outside step whose place in a run is the moment the runtime's step 2 can see the event. Java polls its external queue until it is empty and Rust drains its channel with try_recv until it is empty, so an event sent after the last read is a request after endEvents; TypeScript walks the prefix queued when step 2 begins, and an inject() made inside that step (from an event store append) is likewise a request after endEvents. Such an event goes to the next cycle, which lines 1 and 2 and the coverage clause Env005Covers make the loop reach without blocking."
          "AC1 (the orchestrator is idle, no ready transitions) is the precondition of the lines, not a criterion of its own, and the lines drop it: they bind every accepted injection, idle or not. The idle orchestrator is the loop in its wait, blocked (parked) or about to block. Its blocking is constrained by lines 1 and 2: it may block only with nothing queued, and the rest of the park guard (nothing Ready or Expired at the cycle reading, the timer bound) is CONC-010's."
          "Its offers are in ExecCoversW5.Env005Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). The third EARS sentence (the executor shall be able to leave the wait at once) demands an answer and is quoted whole; it has no safety half among the lines, and its existence half is that clause. AC2 and the first description sentence's 'wakes the orchestrator' are line 3 and Env005Covers. Line 3 is the observable block marker: an accepted request clears it (ENV_005_forbids_deafRequest: an executor whose request leaves the marker set breaks it). Env005Covers is the behaviour: a live wait with an injection queued can always be left by the executor's own step, a wake or the injection or discard of a queued ticket, so leaving it never needs a timer; the reference meets it (env005_ref_covers). An inject() that queues the token but never signals the wait, so that only a completion, a drain, a close or a timer could end it, meets every line and fails that clause (env005_covers_unsignalled). Lines 1 and 2 keep the loop from blocking again while the token is queued (ENV_005_forbids_parkWithQueued: a polling executor that blocks with the token queued; ENV_005_forbids_reblock: a wait that answers a snapshot and blocks again). Together they are the second description sentence: no timer and no poll is needed to find the token. Line 3 holds for every accepted request, whether or not the loop was blocked; a request answered refused or error queues nothing and is ENV-006's and ENV-002's."
          "AC3 is lines 4 and 5 for 'within one cycle': step 2 does not end, and the enablement update does not start, while an injection is queued, so a token accepted while the loop waits has left the queue before the enablement update of the cycle the wake-up starts, and while the executor is open it is in the marking then and the transitions it enables are judged in that cycle (ENV_005_nonvacuous part 4). An executor that ends step 2 with an injection still queued, for instance one event per cycle, breaks line 4 (ENV_005_forbids_leavesQueued); one that skips step 2 and takes injections only from the wait reaches the update with the token queued and breaks line 5 (ENV_005_forbids_skipsEvents). EXEC-001 line 5 states the phase-entry form (the tickets queued when step 2 begins leave the queue before the next update); lines 4 and 5 read it on every queued ticket, as the markdown says, so no cap on the events per cycle is allowed. The consequence sentence ('Read with the definition of queued above') is lines 4 and 5 with the definition of queued; it is a reading, not a separate line."
          "Kind Q, outside the lines: 'immediately' and 'promptly' in AC2 and AC3, 'at once' in the EARS sentences, and 'within milliseconds' in the test derivation, are latencies; the model gives steps no duration, so they are tested, not proven, as the markdown says. The lines say that nothing in the executor waits between the acceptance and the injection: no block, no missing way out of the wait, no deferral to a later cycle."
          "Closed, stopped and ended runs: all five lines hold in every mode. Once the executor is closed or stopped a queued injection is discarded instead of put into the marking (ENV-013), an immediate termination drops the queue at once (ENV-015), and a finish clears it (EXEC-042 for a marked terminal place); these are the exits of the definition of queued and the 'unless' clause of the consequence sentence. Env005Covers asks nothing once a terminal place is marked: the loop then finishes (finish terminal). A request after a drain or a close is refused (ENV-006) and queues nothing. Java and TypeScript keep a pre-close event in their queue, unanswered, until the loop ends, and may block in the wait for the action in flight meanwhile; the sentence 'Once the executor is closed, an event that Java or TypeScript still holds in its queue counts as discarded from the first external-events step or wait after the close, though its inject() is answered only when the loop ends ([ENV-013], [ENV-004]).' is the reading: a Java or TypeScript run is the model run whose discard steps for those events come in the first step 2 or wait after the close, so the queue the lines read is empty before the wait blocks. The late answer is ENV-004's."
          "Host clock (TIME-015, clash env-a#9): under an injected host clock an implementation may stop raising its own wake-up (Java returns before releasing its wake-up semaphore when a host clock is installed) and leave the wait to the host, whose wait returns when the readiness predicate holds; Java's predicate reads the external queue. The model has one wait for both cases: under a host clock, the wait and its block marker stand for the host's wait, and line 3 and Env005Covers are met when the predicate reports the queued injection, which TIME-015's visibility duty requires. The host's own wait and the predicate are TIME-015's and outside the model; the markdown sentence is informative and puts the duty on TIME-015."
          "Depends on: CONC-010 (lines 1 and 3 are its park guard and arrival line restricted to the event queue), ENV-003 (acceptance and the queue), EXEC-001 (steps 2, 3 and 6), and, for the definition of queued and the consequence sentence, ENV-013, ENV-015 and EXEC-042; TIME-015 for the host-clock sentence. The test derivation (start an executor with an environment place, wait for quiescence, inject a token, check that it is processed) is ENV_005_nonvacuous: the loop blocks with nothing queued, a request is accepted and clears the block, a wake-up is offered, step 2 of the next cycle injects the token, and the transition it enables starts in that cycle."
  signoff "2026-11-13 29befa0357c21bc6 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (while (fun s => s.eq ≠ []), never (fun s s' => ∃ tmr, R C s (.park tmr) s')) ∧
      (while (fun s => s.eq ≠ []),
        never (fun s s' => s.parked = false ∧ s'.parked = true ∧ ∃ l, R C s l s')) ∧
      (∀ p x, on (fun s s' => R C s (.request p x .accepted) s'),
        shall (fun _ s' => s'.parked = false)) ∧
      (while (fun s => s.eq ≠ []), never (fun s s' => R C s .endEvents s')) ∧
      (while (fun s => s.eq ≠ []),
        never (fun s s' => s.phase ≠ .update ∧ s'.phase = .update ∧ ∃ l, R C s l s'))

/- The pinned readable form of ENV-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_005 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (while fun s => s.eq ≠ [], never fun s s' => ∃ tmr, R C s (XLbl.park tmr) s') ∧
      (while fun s => s.eq ≠ [], never fun s s' => s.parked = false ∧ s'.parked = true ∧ ∃ l, R C s l s') ∧
        (∀ (p : N) (x : T),
            on fun s s' => R C s (XLbl.request p x Reply.accepted) s', shall fun x s' => s'.parked = false) ∧
          (while fun s => s.eq ≠ [], never fun s s' => R C s XLbl.endEvents s') ∧
            while fun s => s.eq ≠ [], never fun s s' =>
              s.phase ≠ Phase.update ∧ s'.phase = Phase.update ∧ ∃ l, R C s l s'
-/
#guard_msgs in #print ENV_005

/-! ### The reference -/

/-- Only `park` takes the reference from a state that is not parked into a parked one. -/
theorem env005_onlyParkBlocks {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : xstep C s l = some s') (hs : s.parked = false) (hp : s'.parked = true) :
    ∃ tmr, l = .park tmr := by
  cases l with
  | park tmr => exact ⟨tmr, rfl⟩
  | _ =>
    exfalso
    simp only [xstep, xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, publishStep, injectStep,
      discardStep, snapshotStep, startStep, loseStep, wakeStep, onOpen, depositAt, settle] at h
    repeat' (first | (split at h) | (cases h))
    all_goals simp_all

/-- Only `endEvents` takes the reference into the enablement update from another phase. -/
theorem env005_onlyEndEventsUpdates {N T : Type} [DecidableEq N] {C : Cfg N T}
    {s s' : XSt N T} {l : XLbl N T} (h : xstep C s l = some s') (hs : s.phase ≠ .update)
    (hp : s'.phase = .update) : l = .endEvents := by
  cases l with
  | endEvents => rfl
  | _ =>
    exfalso
    simp only [xstep, xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, publishStep, injectStep,
      discardStep, snapshotStep, startStep, loseStep, wakeStep, parkStep, onOpen, depositAt,
      settle] at h
    repeat' (first | (split at h) | (cases h))
    all_goals simp_all

/-- ✓ The reference executor satisfies ENV-005: its park guard requires an empty event queue
(`parkStep_some`) and no other step sets the parked flag (`env005_onlyParkBlocks`); an accepted
request clears the flag (`requestStep_some`); the end of step 2 requires an empty event queue
(`xstepW_endEvents`) and is the only way into the enablement update
(`env005_onlyEndEventsUpdates`). -/
@[evidence holds ENV_005]
theorem ENV_005_reference {N T : Type} [DecidableEq N] :
    ENV_005 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun s s' ⟨tmr, h⟩ => ?_, fun s s' ⟨hs, hp, l, h⟩ => ?_, fun p x s s' h => ?_,
    fun s s' h => ?_, fun s s' ⟨hs, hp, l, h⟩ => ?_⟩
  · obtain ⟨-, -, -, -, -, he, -, -, -⟩ := parkStep_some h
    exact fun hne => hne he
  · obtain ⟨tmr, rfl⟩ := env005_onlyParkBlocks h hs hp
    obtain ⟨-, -, -, -, -, he, -, -, -⟩ := parkStep_some h
    exact fun hne => hne he
  · obtain ⟨-, hr⟩ := requestStep_some h
    rcases hr with ⟨-, rfl⟩ | ⟨hne, -⟩
    · rfl
    · exact absurd rfl hne
  · obtain ⟨-, -, he, -⟩ := xstepW_endEvents h
    exact fun hne => hne he
  · have hl := env005_onlyEndEventsUpdates h hs hp
    subst hl
    obtain ⟨-, -, he, -⟩ := xstepW_endEvents h
    exact fun hne => hne he

/-- **The coverage conjunct ENV-005 asks of the consistency theorem's `ExecCoversW5`**: in every
wait (phase `await`) with no terminal place marked and an injection queued, the executor offers a
way out of the wait, a `wake` or the injection or discard of a queued ticket, so leaving the wait
never needs a timer (the third EARS sentence, AC2). Offers are never a line of a block (glossary
`GlossaryExec.lean`). -/
def Env005Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  ∀ C s, s.phase = .await → Live C s → s.eq ≠ [] →
    ∃ s', E C s .wake s' ∨ ∃ k, E C s (.inject k) s' ∨ E C s (.discard k) s'

/-- The reference meets ENV-005's coverage conjunct: `wake` is offered in every live wait
(`wakeStep`). -/
theorem env005_ref_covers {N T : Type} [DecidableEq N] :
    Env005Covers (RefExec (N := N) (T := T)) := by
  intro C s hph hl _
  have hl' : liveB C s = true := hl
  exact ⟨{ s with phase := .completions, parked := false }, .inl (by
    show wakeStep C s = some _
    unfold wakeStep
    rw [if_pos (by simp [hph, hl'])])⟩

/-! ### Examples

One environment place `0` and a transition `t` that takes a token from it and outputs to place
`1`. The net starts empty, so the loop finds nothing to do and waits. -/

/-- Transition `t`: one token from the environment place `0`, output `1`. -/
def env005_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples: place `0` is an environment place. -/
def env005_c : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [env005_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial state: every place empty. -/
def env005_s0 : XSt Nat Nat := xinit (fun _ => []) 0

/-- The first cycle: nothing is enabled, the pass starts nothing and the loop enters its wait. -/
def env005_toWait : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass]

/-- The loop blocks in its wait with no timer (no timing boundary ahead). -/
def env005_parked : List (XLbl Nat Nat) := env005_toWait ++ [.park none]

/-- The wake-up and the next cycle up to its firing pass: step 2 injects ticket `0`. -/
def env005_resume : List (XLbl Nat Nat) :=
  [.wake, .endCompletions, .endPublications, .inject 0, .endEvents, .update, .deadline [], .begin]

/-- The reference state after `ls` from `env005_s0`. -/
def env005_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) := xrun env005_c env005_s0 ls

/-- Read a state off a decided check of a run. -/
theorem env005_of_map {o : Option (XSt Nat Nat)} {p : XSt Nat Nat → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => exact ⟨s, rfl, by simpa [ho] using h⟩

/-! ### Violation: blocking with an injection queued (line 1) -/

/-- An executor whose park guard does not look at the event queue: it blocks with an injection
queued and finds it only when its timer or another arrival ends the wait (a polling executor). -/
def env005_parkWithQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr => (xstep C { s with eq := [] } (.park tmr)).map fun s' => { s' with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env005_parkWithQueuedStep`. -/
def env005_parkWithQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_parkWithQueuedStep C s l = some s'

/-- ✗ Blocking with an injection queued violates ENV-005 (line 1, AC2, "does not need to wait for
a timer or poll"): a request is accepted while the loop is in its wait but not yet blocked, and
the loop then blocks with the token queued. -/
@[evidence forbids ENV_005]
theorem ENV_005_forbids_parkWithQueued :
    ¬ ENV_005 (env005_parkWithQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_parkWithQueuedStep (C := env005_c)
    (o := env005_at (env005_toWait ++ [.request 0 7 .accepted])) (l := .park none)
    (p := fun s _ => !s.eq.isEmpty) (by decide)
  exact (h env005_c).1 s s' ⟨none, hs⟩ (by simpa using hp)

/-! ### Violation: answering in the wait and blocking again (line 2) -/

/-- An executor whose wait answers a snapshot request and blocks again, without a `park` step.
The Java shape: `awaitExternalEvent` loops on `acquire(); drainPermits();` and, when a marking
request is pending, answers it and `continue`s; `drainPermits` folds the `inject()` permit and the
snapshot permit into one wake-up. The Rust shape: a `loop { select! }` whose snapshot arm does
`continue`. -/
def env005_reblockStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .snapshot a => (xstep C s (.snapshot a)).map fun s' =>
      if s.phase = .await then { s' with parked := true } else s'
  | l => xstep C s l

/-- The executor of `env005_reblockStep`. -/
def env005_reblock {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_reblockStep C s l = some s'

/-- ✗ Blocking again after answering in the wait violates ENV-005 (line 2, "neither at the end
of a cycle nor again after it has answered something during the wait"): the loop blocks with
nothing queued, a request into place `0` is accepted and ends the block, a snapshot request is
answered in the wait, and the loop is blocked again with the token queued. Lines 1, 3, 4 and 5
do not see it (its `park`, `request`, `endEvents` and update entry are the reference's). -/
@[evidence forbids ENV_005]
theorem ENV_005_forbids_reblock :
    ¬ ENV_005 (env005_reblock (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_reblockStep (C := env005_c)
    (o := env005_at (env005_parked ++ [.request 0 7 .accepted])) (l := .snapshot (some true))
    (p := fun s s' => !s.eq.isEmpty && !s.parked && s'.parked) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact (h env005_c).2.1 s s' ⟨hp.1.2, hp.2, _, hs⟩ hp.1.1

/-! ### Violation: the request leaves the block marker set (line 3) -/

/-- An executor whose accepted request queues the token but leaves the wait marked blocked. -/
def env005_deafRequestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s' => { s' with parked := s.parked }
  | l => xstep C s l

/-- The executor of `env005_deafRequestStep`. -/
def env005_deafRequest {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_deafRequestStep C s l = some s'

/-- ✗ A request that does not end the block violates ENV-005 (line 3, AC2): the loop is blocked
with no timer, a request into place `0` is accepted, and the loop is still marked blocked, the
park state that CONC-010's arrival line and ENV-014's foreign reader observe. -/
@[evidence forbids ENV_005]
theorem ENV_005_forbids_deafRequest :
    ¬ ENV_005 (env005_deafRequest (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_deafRequestStep (C := env005_c)
    (o := env005_at env005_parked) (l := .request 0 7 .accepted)
    (p := fun _ s' => s'.parked) (by decide)
  have := (h env005_c).2.2.1 0 7 s s' hs
  simp [this] at hp

/-! ### Coverage: the wait is never signalled (Env005Covers) -/

/-- The wait is signalled: nothing is queued that only an injection's wake-up would report, or a
completion is queued (a completing action still signals the wait). -/
def env005_signalled {N T : Type} (s : XSt N T) : Bool :=
  s.eq.isEmpty || !s.cq.isEmpty

/-- An executor whose `inject()` queues the token and clears the block marker but never signals
the wait: the wait is left (`wake`, or an injection taken in the wait) only when it was
signalled. The Java shape: `inject()` updates the observable park state but no longer calls
`wakeUp()`, so the loop stays in `wakeUpSignal.acquire()` until a completion, a drain, a close or
its timer; the TypeScript shape: `inject()` sets the latch meant for a loop that is not parked
instead of resolving the installed wake-up. -/
def env005_unsignalledStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .wake => if env005_signalled s then xstep C s .wake else none
  | .inject k =>
      if s.phase = .await && !env005_signalled s then none else xstep C s (.inject k)
  | l => xstep C s l

/-- The executor of `env005_unsignalledStep`. -/
def env005_unsignalled {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_unsignalledStep C s l = some s'

/-- Every step of `env005_unsignalled` is a step of the reference: it only withholds steps. -/
theorem env005_unsignalled_sub {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : env005_unsignalled C s l s') : RefExec C s l s' := by
  show xstep C s l = some s'
  unfold env005_unsignalled env005_unsignalledStep at h
  split at h
  · split at h
    · exact h
    · cases h
  · split at h
    · cases h
    · exact h
  · exact h

/-- The way out of the wait is coverage, not a line: a wait that an accepted request does not
signal meets every line of ENV-005 (it only withholds steps of the reference, and the lines are
safety) and fails its coverage conjunct `Env005Covers` (the third EARS sentence, "without waiting
for a timer"): the loop blocks with nothing queued, a request into place `0` is accepted and
clears the block marker, and the loop is in its live wait with the token queued and no way out
(no `wake`, no `inject k`, and no `discard k` since the executor is open). -/
@[evidence cites "ENV-005" "While an accepted injection is queued and the executor is in its wait with no terminal place marked, the executor shall be able to leave the wait at once, by waking up or by taking a queued injection from the queue, without waiting for a timer: an executor whose inject() never signals the wait meets every line of the block and fails its coverage clause Env005Covers in ExecCoversW5"]
theorem env005_covers_unsignalled :
    ENV_005 (env005_unsignalled (N := Nat) (T := Nat)) ∧
      ¬ Env005Covers (env005_unsignalled (N := Nat) (T := Nat)) := by
  refine ⟨fun C => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ENV_005_reference (N := Nat) (T := Nat) C
    exact ⟨fun s s' ⟨tmr, hs⟩ => h1 s s' ⟨tmr, env005_unsignalled_sub hs⟩,
      fun s s' ⟨ha, hb, l, hs⟩ => h2 s s' ⟨ha, hb, l, env005_unsignalled_sub hs⟩,
      fun p x s s' hs => h3 p x s s' (env005_unsignalled_sub hs),
      fun s s' hs => h4 s s' (env005_unsignalled_sub hs),
      fun s s' ⟨ha, hb, l, hs⟩ => h5 s s' ⟨ha, hb, l, env005_unsignalled_sub hs⟩⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_unsignalledStep (C := env005_c)
    (o := env005_at env005_parked) (l := .request 0 7 .accepted)
    (p := fun _ s' => s'.phase == .await && liveB env005_c s' && !s'.eq.isEmpty &&
      !env005_signalled s' && !s'.mode.closing) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  obtain ⟨⟨⟨⟨hph, hl⟩, hne⟩, hsig⟩, hcl⟩ := hp
  obtain ⟨s'', hw | ⟨k, hi | hd⟩⟩ := h env005_c s' hph hl hne
  · have : env005_unsignalledStep env005_c s' .wake = some s'' := hw
    simp [env005_unsignalledStep, hsig] at this
  · have : env005_unsignalledStep env005_c s' (.inject k) = some s'' := hi
    simp [env005_unsignalledStep, hph, hsig] at this
  · have : env005_unsignalledStep env005_c s' (.discard k) = some s'' := hd
    simp only [env005_unsignalledStep, xstep, xstepW, discardStep] at this
    split at this
    · simp [hcl] at this
    · cases this

/-! ### Violation: step 2 ends with an injection queued (line 4) -/

/-- An executor whose step 2 may end with injections still queued and leave them to a later
cycle; one event per cycle is one such schedule. -/
def env005_leavesQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents =>
      if s.phase = .events && liveB C s then some { s with phase := .update } else none
  | l => xstep C s l

/-- The executor of `env005_leavesQueuedStep`. -/
def env005_leavesQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_leavesQueuedStep C s l = some s'

/-- ✗ Ending step 2 with an injection queued violates ENV-005 (line 4, AC3 "within one cycle"):
two requests are accepted while the loop is blocked, step 2 injects the first, and the step ends
with the second still queued. -/
@[evidence forbids ENV_005]
theorem ENV_005_forbids_leavesQueued :
    ¬ ENV_005 (env005_leavesQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_leavesQueuedStep (C := env005_c)
    (o := env005_at (env005_parked ++ [.request 0 7 .accepted, .request 0 8 .accepted, .wake,
      .endCompletions, .endPublications, .inject 0]))
    (l := .endEvents) (p := fun s _ => !s.eq.isEmpty) (by decide)
  exact (h env005_c).2.2.2.1 s s' hs (by simpa using hp)

/-! ### Violation: step 2 skipped, injections taken only in the wait (line 5) -/

/-- An executor that skips step 2: the end of step 1b goes straight to the enablement update, and
injections are taken only from the wait. The Rust shape: the step 2 drain `while let Ok(signal)
= signal_rx.try_recv()` removed on the reading that the wait's `select!` already handles every
signal; the Java shape: `processExternalEvents()` called only from `awaitWork()`. -/
def env005_skipsEventsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPublications =>
      if s.phase = .publications && liveB C s && s.pq.isEmpty then
        some { s with phase := .update } else none
  | l => xstep C s l

/-- The executor of `env005_skipsEventsStep`. -/
def env005_skipsEvents {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env005_skipsEventsStep C s l = some s'

/-- The skipping executor's run, as a fold. -/
def env005_skipsEventsRun {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    List (XLbl N T) → Option (XSt N T)
  | [] => some s
  | l :: ls => (env005_skipsEventsStep C s l).bind fun s' => env005_skipsEventsRun C s' ls

/-- ✗ Starting the enablement update with an injection queued violates ENV-005 (line 5, AC3
"within one cycle"): the skipping executor blocks, a request into place `0` is accepted, the
wake-up starts a cycle, and that cycle enters its enablement update from step 1b with the token
still queued. It never takes `endEvents`, so line 4 does not see it. -/
@[evidence forbids ENV_005]
theorem ENV_005_forbids_skipsEvents :
    ¬ ENV_005 (env005_skipsEvents (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env005_skipsEventsStep (C := env005_c)
    (o := env005_skipsEventsRun env005_c env005_s0
      [.endCompletions, .endPublications, .update, .deadline [], .begin, .endPass, .park none,
        .request 0 7 .accepted, .wake, .endCompletions])
    (l := .endPublications)
    (p := fun s s' => !s.eq.isEmpty && s.phase != .update && s'.phase == .update) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, bne_iff_ne, ne_eq,
    beq_iff_eq] at hp
  exact (h env005_c).2.2.2.2 s s' ⟨hp.1.2, hp.2, _, hs⟩ hp.1.1

/-! ### Every line exercised -/

/-- Every line of ENV-005 is exercised by the reference, on the test derivation's run: (1) with
nothing queued the loop blocks in its wait, so the step lines 1 and 2 ban does occur; (2) a
request into the environment place is accepted while the loop is blocked, and it ends the block
with the token queued and the loop still in its live wait (the trigger of lines 1 to 3 and of the
coverage clause `Env005Covers`), where a `wake` is offered (the clause's conclusion); (3) after
the wake-up, step 2 is entered with the token queued (the trigger of lines 4 and 5); (4) step 2 injects the token, and `t`, which it enables,
starts in the same cycle (AC3, the test derivation). -/
@[evidence nonvacuous ENV_005]
theorem ENV_005_nonvacuous :
    (∃ s s', env005_at env005_toWait = some s ∧ RefExec env005_c s (.park none) s' ∧
      s.eq = [] ∧ s'.parked = true) ∧
    (∃ s s', env005_at env005_parked = some s ∧
      RefExec env005_c s (.request 0 7 .accepted) s' ∧
      s.parked = true ∧ s'.parked = false ∧ s'.phase = .await ∧ Live env005_c s' ∧
      s'.eq ≠ [] ∧ ∃ s'', RefExec env005_c s' .wake s'') ∧
    (∃ s, env005_at (env005_parked ++
        [.request 0 7 .accepted, .wake, .endCompletions, .endPublications]) = some s ∧
      s.phase = .events ∧ s.eq ≠ []) ∧
    (∃ s s', env005_at (env005_parked ++ .request 0 7 .accepted :: env005_resume) = some s ∧
      RefExec env005_c s (.start "t" false) s') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env005_c)
      (o := env005_at env005_toWait) (l := .park none)
      (p := fun s s' => s.eq.isEmpty && s'.parked) (by decide)
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hp
    exact ⟨s, s', ho, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env005_c)
      (o := env005_at env005_parked) (l := .request 0 7 .accepted)
      (p := fun s s' => s.parked && !s'.parked && s'.phase == .await && liveB env005_c s' &&
        !s'.eq.isEmpty && (xstep env005_c s' .wake).isSome)
      (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_eq_false_iff,
      Option.isSome_iff_exists] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, s'', h6⟩ := hp
    exact ⟨s, s', ho, hs, h1, h2, h3, h4, h5, s'', h6⟩
  · obtain ⟨s, ho, hp⟩ := env005_of_map (o := env005_at (env005_parked ++
        [.request 0 7 .accepted, .wake, .endCompletions, .endPublications]))
      (p := fun s => s.phase == .events && !s.eq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_eq_false_iff] at hp
    exact ⟨s, ho, hp.1, hp.2⟩
  · obtain ⟨s, s', ho, hs, -⟩ := step_of_check xstep (C := env005_c)
      (o := env005_at (env005_parked ++ .request 0 7 .accepted :: env005_resume))
      (l := .start "t" false) (p := fun _ _ => true) (by decide)
    exact ⟨s, s', ho, hs⟩

end Libpetri.Spec
