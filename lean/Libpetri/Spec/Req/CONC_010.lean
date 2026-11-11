import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# CONC-010: Orchestrator Wake-Up (`spec/05-concurrency.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). Step 6 of the loop is the
wait (phase `await`); `park tmr` is the loop blocking in it with timer `tmr` (`XSt.parked`
becomes true), and `wake` is its end. The requirement is a predicate over an abstract executor
`R : XRel N T` (glossary `GlossaryExec.lean`) with five lines:

* the loop does not block while a finished action's outcome, a flushed publication or an
  accepted injection is queued (line 1);
* the loop does not block while a transition is Ready or Expired at the cycle reading, the
  firing-clock reading the cycle's deadline step took, not earlier than its enablement update's
  (line 2, ruling D61 (c));
* every arrival ends a block at once: a return, a budget expiry, a flush that queues a
  publication, an accepted request, a drain, a close and an immediate termination; the state it
  leads to is not blocked (line 3, ruling D13 (a));
* a block taken while an armed transition has a timing boundary ahead sets a timer, no longer
  than the wait from the cycle reading to the nearest boundary plus the timer resolution
  (line 4);
* a return and a budget expiry queue the firing's outcome (line 5), which is what line 1 reads.

Time passing (`delay`) is never restricted (ruling D3: the reference may be late by any amount),
so the lines speak of the park decision and of the arrival steps, never of a delay. That a wake
back to step 1 is offered at once after an arrival taken in the wait is an offer, so it is no
line: it is `Conc010Covers`, a clause of the consistency theorem's `ExecCoversW5`.

The evidence checks the block against the reference executor and against seven wrong executors:
two that block with work queued (a completion; a publication), one that blocks with a transition
Ready, two whose arrivals leave the wait blocked (a completion; a drain), one that blocks without
a timer while a `Delayed` transition is armed, and one that keeps a returned outcome on the firing
record instead of the completion queue. One more, whose arrivals clear the flag but whose wait can
only be left when its sleep is over, meets every line and fails only the coverage clause. One allows-theorem shows the reading of ruling D61 (c): the
reference blocks on the cycle reading although the transition is Ready at the host's present, as
Rust does. `CONC_010_env005_lines` derives ENV-005's lines 1 and 3.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The terms the lines read -/

namespace Conc010

variable {N T : Type}

/-- Work is queued for the loop: a finished action's outcome, a flushed publication or an
accepted injection that the loop has not processed. -/
def WorkQueued (s : XSt N T) : Prop := s.cq ≠ [] ∨ s.pq ≠ [] ∨ s.eq ≠ []

/-- Some transition of the net is Ready or Expired at the cycle reading (glossary: Ready,
Expired; `viewAt s s.cyc` is the state the deadline step, the pass and the park decision judge). -/
def DueAtCycle [DecidableEq N] (C : Cfg N T) (s : XSt N T) : Prop :=
  ∃ u ∈ C.X.net.transitions, Ready C.X (viewAt s s.cyc) u ∨ Expired C.X (viewAt s s.cyc) u

/-- The step `s ⟶ s'` labelled `l` is an arrival the wait must not sleep through: an action
returns or its budget expires (its outcome is queued), an action's flush queues a publication,
`inject()` accepts a token, or the executor is drained, closed or terminated immediately. A
flush the join-relay check rejects queues nothing and is no arrival; a request answered refused
or error queues nothing either. -/
def Arrival : XLbl N T → XSt N T → XSt N T → Prop
  | .ret _ _, _, _ => True
  | .expire _ _, _, _ => True
  | .flush _, s, s' => s'.pq ≠ s.pq
  | .request _ _ .accepted, _, _ => True
  | .drain, _, _ => True
  | .close, _, _ => True
  | .terminateNow, _, _ => True
  | _, _, _ => False

/-- Every arrival is an outside step ([CONC-001]): it happens beside the loop, not in it. -/
theorem outside_of_arrival {l : XLbl N T} {s s' : XSt N T} (h : Arrival l s s') :
    l.outside = true := by
  cases l <;> first | rfl | exact h.elim

/-- The park timer `tmr` reaches no further than the nearest timing boundary of an armed
transition (`nextBoundary`, from the cycle reading) plus the timer resolution: with a boundary
ahead the timer is set and bounded; with none ahead any timer, or none, will do. -/
def TimerWithin (C : Cfg N T) (s : XSt N T) (tmr : Option Nat) : Prop :=
  ∀ b, nextBoundary C s = some b → ∃ x, tmr = some x ∧ x ≤ b + C.res

/-- The reference's park guard `nothingDue` excludes every transition Ready or Expired at the
cycle reading. -/
theorem not_dueAtCycle_of_nothingDue [DecidableEq N] {C : Cfg N T} {s : XSt N T}
    (h : nothingDue C s = true) : ¬ DueAtCycle C s := by
  rintro ⟨u, hu, hd⟩
  have hu' := List.all_eq_true.1 h u hu
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hu'
  rcases hd with hr | hx
  · exact hu'.1 hr
  · rw [(expired_iff _ _ _)] at hx
    rw [hu'.2] at hx
    exact Bool.false_ne_true hx

/-- A transition Ready at the cycle reading makes the reference's `nothingDue` false. -/
theorem dueAtCycle_of_nothingDue_false [DecidableEq N] {C : Cfg N T} {s : XSt N T}
    (h : nothingDue C s = false) : DueAtCycle C s := by
  unfold nothingDue at h
  obtain ⟨u, hu, hn⟩ := List.all_eq_false.1 h
  simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at hn
  refine ⟨u, hu, ?_⟩
  rcases hn with hr | hx
  · exact Or.inl hr
  · exact Or.inr ((expired_iff _ _ _).2 hx)

/-- The reference's timer check `timerOk` is `TimerWithin`. -/
theorem timerWithin_of_timerOk {C : Cfg N T} {s : XSt N T} {tmr : Option Nat}
    (h : timerOk C s tmr = true) : TimerWithin C s tmr := by
  intro b hb
  unfold timerOk at h
  rw [hb] at h
  cases tmr with
  | none => simp at h
  | some x => exact ⟨x, rfl, by simpa using h⟩

/-- A park without a timer while a boundary is ahead breaks `TimerWithin`. -/
theorem not_timerWithin_none {C : Cfg N T} {s : XSt N T} {b : Nat}
    (hb : nextBoundary C s = some b) : ¬ TimerWithin C s none := by
  intro h
  obtain ⟨x, hx, -⟩ := h b hb
  cases hx

end Conc010

open Conc010

/-! ## CONC-010: Orchestrator Wake-Up -/

requirement CONC_010
  id "CONC-010"
  title "Orchestrator Wake-Up"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  quote "When the orchestrator is idle (no transitions ready, waiting for work), it must be woken by each of these causes:"
        "**Action completion:** an action returns, or its timeout expires ([EXEC-022]), and its outcome is queued for the orchestrator."
        "**External event injection:** `inject()` accepts a token for an environment place ([ENV-003])."
        "**Timer expiry:** the timer the wait set for a timing boundary of an armed transition runs out."
        "**Lifecycle:** the executor is drained ([ENV-011]), closed ([ENV-013]) or terminated immediately ([ENV-015])."
        "**Publication:** an action's flush queues a batch of outputs before the action returns ([IO-015]), in an implementation with mid-action publication."
        "A flush that the join-relay check rejects ([NU-054]) queues nothing and is no wake cause; the firing then ends with an error when its action returns."
        "A timing boundary of an armed transition is its earliest bound, while its elapsed time has not reached it, and, for a reapable transition, the reading at which it becomes expired ([TIME-013])."
        "The orchestrator judges Ready, Expired and the timing boundaries for its wait at the firing-clock reading its deadline step took in the current cycle ([EXEC-001] step 4), which is not earlier than the reading of its enablement update ([TIME-010])."
        "*While* the outcome of an action, a flushed publication or an accepted injection is queued and not yet processed, the executor *shall not* block in its wait ([EXEC-001] step 6)."
        "*While* a transition is Ready or Expired at the reading of the cycle's deadline step, the executor *shall not* block in its wait."
        "*When* an action's outcome is queued, an action's flush queues a publication, `inject()` accepts a token, or the executor is drained, closed or terminated immediately, the executor *shall* end any block of its wait at once and be ready to leave the wait for the start of its loop ([EXEC-001] step 1) without waiting for a timer."
        "*When* the executor blocks in its wait while an armed transition has a timing boundary ahead, it *shall* set a timer no longer than the time from the reading of the cycle's deadline step to the nearest such boundary, plus the timer resolution."
        "*When* an action returns or its timeout expires, the executor *shall* queue the action's outcome for the orchestrator."
        "So no queued work waits for a timer or a poll, and a wait with a timing boundary ahead carries a timer that runs out no later than that boundary, within timer resolution, counted from the reading of the cycle's deadline step."
  reading "For every executor R and every configuration C:"
          "no park step starts in a state whose completion, publication or event queue is not empty;"
          "no park step starts in a state in which a transition of the net is Ready or Expired at the cycle reading;"
          "every arrival step (a return, a budget expiry, a flush that queues a publication, an accepted request, a drain, a close, an immediate termination) ends in a state that is not parked;"
          "every park step with timer tmr starts in a state where, if a timing boundary is ahead at the cycle reading, tmr is set and is at most the nearest boundary plus the timer resolution C.res;"
          "every return or budget expiry of firing i ends in a state whose completion queue holds i."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The wait is the loop phase await (EXEC-001 step 6); park tmr is the loop blocking in it (XSt.parked becomes true) with a timer tmr (none: no timer), and wake is the end of the wait, by its timer, by an arrival or for no reason, after which the loop runs step 1 again. The outside steps ret, expire, flush, request, drain, close and terminateNow are the arrivals; the loop may also take a queued completion, publication or injection straight from the wait (EXEC-001, ruling D70 (a)). The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor, whose wait is a select over its completion, flush and signal channels and a timer from cycle_now."
          "Its offers are in ExecCoversW5.Conc010Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). The third EARS sentence demands an answer and is quoted whole; its safety half is line 3, and its existence half is that clause. Lines 1, 3 and 5 make up 'no lost wake-up', together with Conc010Covers. Line 1 is the check before the block: the loop blocks only with nothing queued, so an arrival before the block is never slept through (CONC_010_forbids_parkWithCompletion: a check-then-park executor that blocks with a returned action's outcome queued; CONC_010_forbids_parkWithPublication: one that blocks with a flushed publication queued; for the event queue, ENV-005's ENV_005_forbids_parkWithQueued). Line 5 makes line 1 read the right thing: a return or a budget expiry puts the firing's outcome on the completion queue, the queue the park check reads (CONC_010_forbids_outcomeOnRecord: an executor that keeps the outcome on the firing record only, so its park check sees an empty queue and blocks again with the outcome unprocessed). An accepted injection is queued by ENV-003 line 1, and a flush is an arrival only when it queues its batch, by the definition of the arrival. The wake during the block has two parts: line 3, the arrival leaves the state unblocked (CONC_010_forbids_deafCompletion: a return that leaves the wait blocked, noticed only when the timer fires; CONC_010_forbids_deafLifecycle: a drain that leaves it blocked), and Conc010Covers, the way out of the wait, a wake back to step 1, is offered at once after an arrival taken in the wait with no terminal place marked (the reference meets it, conc010_ref_covers; an executor whose arrivals clear the flag but whose wait can be left only when its sleep is over, a poll, meets every line and fails that clause, conc010_covers_sleepyWait). Rust meets line 1 by its select, which returns at once when a channel holds an item, Java by its semaphore permit, TypeScript by its latched wake-up (wakeUpPending) and its queue re-check on entry to the wait."
          "Line 2 is the first description sentence's 'no transitions ready' read at the cycle reading (ruling D61 (c)): the loop does not block while a transition it could act on without new work is Ready or Expired at the reading its deadline step took, which is not earlier than its enablement update's (CONC_010_forbids_parkWhileDue: a wait that looks only at the queues and blocks with a transition Ready). The reference meets it by its park guard (nothingDue); on its own runs the guard never bites, since a pass started every Ready transition or took its clock and the deadline step reaped every expired one, but the line constrains every executor. Judging at a later reading of the same cycle is stricter (a transition Ready or Expired at the cycle reading is Ready or Expired later too) and also satisfies the line; judging at the cycle reading is what Rust does (cycle_now), and the reference blocks while a transition is already Ready at the host's present (CONC_010_allows_staleReading). That transition is judged by the next cycle, which the timer starts."
          "Line 4 is AC3 under ruling D13 (a) (conc-b clash CB-6): a timing boundary of an armed transition is its earliest bound while not reached and, for a reapable transition, the reading at which it becomes expired (nextBoundary, glossary GlossaryExec.lean); a block with a boundary ahead sets a timer of at most that wait plus the timer resolution C.res, and with none ahead any timer or none (Rust re-checks after 60 s, Java after its poll interval). An executor that blocks without a timer while a Delayed transition is armed breaks it (CONC_010_forbids_untimedPark). The resolution is a configuration value of the model (Cfg.res): Java rounds a wait below one millisecond up to one millisecond, Rust truncates to whole milliseconds, and the runtimes wake at the latest bound of a transition with a deadline, earlier than the expiry boundary, which a shorter timer allows. The timer is a duration counted from the cycle reading: a runtime that starts it at its present reading, as Rust does, may end the wait later than the boundary by the time the cycle took since its update, which ruling D3 allows (the executor may be late by any amount)."
          "AC1 and AC2 are line 3 and Conc010Covers for an accepted injection and for an action's return or budget expiry, together with line 1 for the arrival that comes before the block and, for AC2, line 5 for the queueing (CONC_010_nonvacuous part 6 runs an accepted injection that ends a block and is injected from the wait). AC3 is line 4 for its timer, with the readiness it promises left to the cycle the timer starts, and only if the transition is still armed then: there TIME-010 and TIME-014 make a Delayed transition Ready once its earliest bound is reached and TIME-013 reaps an expired one (CONC_010_nonvacuous part 4 runs the timer, the next cycle and the start). AC4 is line 3 and Conc010Covers for a drain, a close and an immediate termination (ruling D13 (a): drain and close are wake causes, and the list is 'must wake on')."
          "Kind Q, outside the lines: 'immediately' in AC1, 'must be responsive' and 'does not depend on a poll interval', and the latency the test derivation measures, are latencies of the host's wake-up; the model gives steps no duration, so they are tested, not proven. The third cause, the timer running out, and the sentence 'Ending the wait when that timer runs out is the work of the host timer ([TIME-015]).' are Q as well: line 4 bounds the timer the park step sets, and no line makes a wake happen when it runs out, since delay is never restricted (ruling D3). The lines say that nothing in the executor waits between an arrival and its processing: no block with work queued, an outcome always on the queue the check reads, and no block that survives an arrival, and, by Conc010Covers, the way out of the wait offered at once; that the host takes that way promptly is Q."
          "Allowed and outside the lines: the wait may end for no reason (a spurious wake-up, or Java's and Rust's periodic re-check behind the direct wake-up, TIME-015's 'the wait MAY complete early'), since wake is offered in every state of the wait and delay is never restricted (ruling D3). A snapshot request (ENV-014) may be answered from the wait without ending it: the model's snapshot step in the wait leaves the state unchanged, the flag included, and ENV-014 states the answer. A flush that the join-relay check of NU-054 rejects queues nothing, so it is no arrival and the reference keeps the block (flushStep); the firing's return then reports the error. Under an injected host clock (TIME-015) the host's wait carries the wake-up; parked stands for it."
          "Not covered by the lines, and said so in the markdown: a drain, a close or an immediate termination taken after the termination test and before the loop blocks. The reference park guard reads the queues and the timing state but not the lifecycle mode, so it may still block after such a step although the termination test would now finish the run; the runtimes do not (Rust's select finds the signal on its channel, Java finds the semaphore permit, TypeScript the latched wake-up), and their tests check it. An executor that wakes the wait on a lifecycle signal only when it is already blocked, as TypeScript's wakeUp() did before it latched the signal, meets every line. A line on this case waits for the model's park guard to read the lifecycle mode."
          "Depends on EXEC-001 (the loop, its steps 1 and 6), ENV-003 (an accepted injection is queued), ENV-005 (lines 1 and 3 of ENV-005 are line 1 restricted to the event queue and line 3 restricted to an accepted request, conc010_env005_lines of ConsistencyExec.lean), TIME-010 and TIME-013 (Ready, Expired, the boundaries), and TIME-015 (the host's wait). The test derivation (inject a token while the orchestrator is idle and measure the latency to its processing) is CONC_010_nonvacuous's runs for its order, with the latency left Q."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (while (fun s => WorkQueued s), never (fun s s' => ∃ tmr, R C s (.park tmr) s')) ∧
      (while (fun s => DueAtCycle C s), never (fun s s' => ∃ tmr, R C s (.park tmr) s')) ∧
      (∀ l, on (fun s s' => R C s l s' ∧ Arrival l s s'), shall (fun _ s' => s'.parked = false)) ∧
      (∀ tmr, on (fun s s' => R C s (.park tmr) s'), shall (fun s _ => TimerWithin C s tmr)) ∧
      (∀ i ok, on (fun s s' => R C s (.ret i ok) s'), shall (fun _ s' => i ∈ s'.cq)) ∧
      (∀ i e, on (fun s s' => R C s (.expire i e) s'), shall (fun _ s' => i ∈ s'.cq))

/- The pinned readable form of CONC-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_010 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (while fun s => WorkQueued s, never fun s s' => ∃ tmr, R C s (XLbl.park tmr) s') ∧
      (while fun s => DueAtCycle C s, never fun s s' => ∃ tmr, R C s (XLbl.park tmr) s') ∧
        (∀ (l : XLbl N T), on fun s s' => R C s l s' ∧ Arrival l s s', shall fun x s' => s'.parked = false) ∧
          (∀ (tmr : Option ℕ), on fun s s' => R C s (XLbl.park tmr) s', shall fun s x => TimerWithin C s tmr) ∧
            (∀ (i : ℕ) (ok : Bool), on fun s s' => R C s (XLbl.ret i ok) s', shall fun x s' => i ∈ s'.cq) ∧
              ∀ (i : ℕ) (e : List (N × T)), on fun s s' => R C s (XLbl.expire i e) s', shall fun x s' => i ∈ s'.cq
-/
#guard_msgs in #print CONC_010

/-! ### The reference -/

/-- ✓ The reference executor satisfies CONC-010: its park guard requires empty queues, nothing
Ready or Expired at the cycle reading and a timer within the bound (`parkStep_some`); every
arrival rule clears the parked flag (`retStep_some`, `expireStep_some`, `flushStep_some`,
`requestStep_some`, `drainStep_some`, `closeStep_some`, `terminateStep_some`); and its return and
expiry rules append the firing to the completion queue. -/
@[evidence holds CONC_010]
theorem CONC_010_reference {N T : Type} [DecidableEq N] :
    CONC_010 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun s s' ⟨tmr, h⟩ => ?_, fun s s' ⟨tmr, h⟩ => ?_, fun l s s' ⟨h, ha⟩ => ?_,
    fun tmr s s' h => ?_, fun i ok s s' h => ?_, fun i e s s' h => ?_⟩
  · obtain ⟨-, -, -, hcq, hpq, heq, -, -, -⟩ := parkStep_some h
    rintro (hne | hne | hne)
    · exact hne hcq
    · exact hne hpq
    · exact hne heq
  · obtain ⟨-, -, -, -, -, -, hd, -, -⟩ := parkStep_some h
    exact not_dueAtCycle_of_nothingDue hd
  · cases l with
    | ret i ok =>
      obtain ⟨f, -, -, rfl⟩ := retStep_some h
      rfl
    | expire i e =>
      obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
      rfl
    | flush i =>
      obtain ⟨f, -, -, -, -, hc⟩ := flushStep_some h
      rcases hc with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
      · rfl
      · exact absurd rfl ha
    | request p x r =>
      cases r with
      | accepted =>
        obtain ⟨-, hr⟩ := requestStep_some h
        rcases hr with ⟨-, rfl⟩ | ⟨hne, -⟩
        · rfl
        · exact absurd rfl hne
      | refused => exact ha.elim
      | error => exact ha.elim
    | drain =>
      obtain ⟨-, rfl⟩ := drainStep_some h
      rfl
    | close =>
      obtain ⟨-, rfl⟩ := closeStep_some h
      rfl
    | terminateNow =>
      obtain ⟨-, rfl⟩ := terminateStep_some h
      rfl
    | _ => exact ha.elim
  · obtain ⟨-, -, -, -, -, -, -, ht, -⟩ := parkStep_some h
    exact timerWithin_of_timerOk ht
  · obtain ⟨f, -, -, rfl⟩ := retStep_some h
    simp
  · obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    simp

/-- **The coverage conjunct CONC-010 asks of the consistency theorem's `ExecCoversW5`**: after an
arrival taken in the wait with no terminal place marked, a wake back to step 1 (phase
`completions`) is offered at once from the state the arrival leads to (the existence half of the
third EARS sentence: 'be ready to leave the wait for the start of its loop without waiting for a
timer'). Offers are never a line of a block (glossary `GlossaryExec.lean`). -/
def Conc010Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  ∀ C l s s', E C s l s' → Arrival l s s' → s.phase = .await → liveB C s = true →
    ∃ s'', E C s' .wake s'' ∧ s''.phase = .completions

/-- The reference meets CONC-010's coverage conjunct: an arrival is an outside step, which keeps
the phase and the marking (`xstepW_outside_frame`), so the wake rule (`wakeStep`) stays offered. -/
theorem conc010_ref_covers {N T : Type} [DecidableEq N] :
    Conc010Covers (RefExec (N := N) (T := T)) := by
  intro C l s s' h ha hph hl
  obtain ⟨hM, -, hp, -, -⟩ := xstepW_outside_frame h (outside_of_arrival ha)
  refine ⟨{ s' with phase := .completions, parked := false }, ?_, rfl⟩
  show wakeStep C s' = some _
  have hl' : liveB C s' = true := by unfold liveB at hl ⊢; rw [hM]; exact hl
  simp [wakeStep, hp, hph, hl']

/-- ENV-005's lines 1 and 3 follow from CONC-010: line 1 restricted to the event queue, and
line 3 restricted to an accepted request. -/
theorem CONC_010_env005_lines {N T : Type} [DecidableEq N] {R : XRel N T} (h : CONC_010 R)
    (C : Cfg N T) :
    (while (fun s => s.eq ≠ []), never (fun s s' => ∃ tmr, R C s (.park tmr) s')) ∧
    (∀ p x, on (fun s s' => R C s (.request p x .accepted) s'),
      shall (fun _ s' => s'.parked = false)) :=
  ⟨WhileNever.mono_pre (fun _ he => Or.inr (Or.inr he)) (h C).1,
   fun p x s s' hs => (h C).2.2.1 (.request p x .accepted) s s' ⟨hs, trivial⟩⟩

/-! ### Examples

Transition `t` takes a token from place `0` and outputs to place `1`; place `0` is an
environment place. -/

/-- Transition `t`: one token from place `0`, output `1`. -/
def conc010_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration with timing `tm` for `t`; place `0` is an environment place. -/
def conc010_cfg (tm : Libpetri.Novel.TimedScg.Timing) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [conc010_t] },
           timing := fun _ => tm, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- `t` is `Immediate`. -/
def conc010_c : Cfg Nat Nat := conc010_cfg .immediate

/-- `t` is `Delayed(10)`. -/
def conc010_cd : Cfg Nat Nat := conc010_cfg (.delayed 10)

/-- One token in place `0`, nothing else. -/
def conc010_m1 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- The first cycle up to the termination test. -/
def conc010_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- `t` starts asynchronously in the first cycle; the second cycle finds nothing to do while the
firing is in flight and enters the wait. -/
def conc010_busy : List (XLbl Nat Nat) :=
  conc010_toTest ++ [.begin, .start "t" false, .endPass] ++ conc010_toTest ++ [.begin, .endPass]

/-- With nothing marked, the first cycle finds nothing to do and enters the wait. -/
def conc010_idle : List (XLbl Nat Nat) := conc010_toTest ++ [.begin, .endPass]

/-- The reference state after `ls` from `M0` under `C`. -/
def conc010_at (C : Cfg Nat Nat) (M0 : QMarking Nat Nat) (ls : List (XLbl Nat Nat)) :
    Option (XSt Nat Nat) := xrun C (xinit M0 0) ls

/-- Read a state off a decided check of a run. -/
theorem conc010_of_map {o : Option (XSt Nat Nat)} {p : XSt Nat Nat → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => exact ⟨s, rfl, by simpa [ho] using h⟩

/-! ### Violations: blocking with work queued (line 1) -/

/-- A check-then-park executor: its park guard does not look at the completion queue, so it
blocks with a returned action's outcome queued. -/
def conc010_parkWithCompletionStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr => (xstep C { s with cq := [] } (.park tmr)).map fun s' => { s' with cq := s.cq }
  | l => xstep C s l

/-- The executor of `conc010_parkWithCompletionStep`. -/
def conc010_parkWithCompletion {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_parkWithCompletionStep C s l = some s'

/-- ✗ Blocking with a returned action's outcome queued violates CONC-010 (line 1, AC2): the
action of `t` returns while the loop is in its wait but not yet blocked, and the loop blocks. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_parkWithCompletion :
    ¬ CONC_010 (conc010_parkWithCompletion (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_parkWithCompletionStep (C := conc010_c)
    (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.ret 0 true])) (l := .park none)
    (p := fun s _ => !s.cq.isEmpty) (by decide)
  exact (h conc010_c).1 s s' ⟨none, hs⟩ (Or.inl (by simpa using hp))

/-- An executor whose park guard does not look at the publication queue: it blocks with a
flushed publication queued. -/
def conc010_parkWithPublicationStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr => (xstep C { s with pq := [] } (.park tmr)).map fun s' => { s' with pq := s.pq }
  | l => xstep C s l

/-- The executor of `conc010_parkWithPublicationStep`. -/
def conc010_parkWithPublication {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_parkWithPublicationStep C s l = some s'

/-- ✗ Blocking with a flushed publication queued violates CONC-010 (line 1): the action of `t`
writes and flushes while the loop is in its wait, and the loop blocks. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_parkWithPublication :
    ¬ CONC_010 (conc010_parkWithPublication (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_parkWithPublicationStep (C := conc010_c)
    (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.write 0 1 5, .flush 0]))
    (l := .park none) (p := fun s _ => !s.pq.isEmpty) (by decide)
  exact (h conc010_c).1 s s' ⟨none, hs⟩ (Or.inr (Or.inl (by simpa using hp)))

/-! ### Violation: blocking with a transition Ready (line 2) -/

/-- A wait that looks only at the queues and the timer: its park guard does not judge the timing
state at the cycle reading. -/
def conc010_parkWhileDueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr =>
      if s.phase = .await && liveB C s && !s.parked && s.cq.isEmpty && s.pq.isEmpty &&
          s.eq.isEmpty && timerOk C s tmr
      then some { s with parked := true } else none
  | l => xstep C s l

/-- The executor of `conc010_parkWhileDueStep`. -/
def conc010_parkWhileDue {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_parkWhileDueStep C s l = some s'

/-- ✗ Blocking with a transition Ready violates CONC-010 (line 2): in the wait of a loop that
reached it with `t` armed and Ready at the cycle reading (the state of the first termination
test, put in phase `await`), the executor blocks. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_parkWhileDue :
    ¬ CONC_010 (conc010_parkWhileDue (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_parkWhileDueStep (C := conc010_c)
    (o := (conc010_at conc010_c conc010_m1 conc010_toTest).map fun s => { s with phase := .await })
    (l := .park none) (p := fun s _ => !nothingDue conc010_c s) (by decide)
  exact (h conc010_c).2.1 s s' ⟨none, hs⟩ (dueAtCycle_of_nothingDue_false (by simpa using hp))

/-! ### Violations: an arrival that leaves the wait blocked (line 3) -/

/-- An executor whose returning action queues its outcome but leaves the wait blocked, so that
only the timer, or no timer at all, ends the wait. -/
def conc010_deafCompletionStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s' => { s' with parked := s.parked }
  | l => xstep C s l

/-- The executor of `conc010_deafCompletionStep`. -/
def conc010_deafCompletion {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_deafCompletionStep C s l = some s'

/-- ✗ A return that does not end the block violates CONC-010 (line 3, AC2): the loop blocks with
no timer while the action of `t` is in flight, the action returns, and the loop stays blocked. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_deafCompletion :
    ¬ CONC_010 (conc010_deafCompletion (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_deafCompletionStep (C := conc010_c)
    (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none])) (l := .ret 0 true)
    (p := fun _ s' => s'.parked) (by decide)
  have := (h conc010_c).2.2.1 (.ret 0 true) s s' ⟨hs, trivial⟩
  simp [this] at hp

/-- An executor whose drain, close and immediate termination change the mode but leave the wait
blocked. -/
def conc010_deafLifecycleStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => (xstep C s .drain).map fun s' => { s' with parked := s.parked }
  | .close => (xstep C s .close).map fun s' => { s' with parked := s.parked }
  | .terminateNow => (xstep C s .terminateNow).map fun s' => { s' with parked := s.parked }
  | l => xstep C s l

/-- The executor of `conc010_deafLifecycleStep`. -/
def conc010_deafLifecycle {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_deafLifecycleStep C s l = some s'

/-- ✗ A drain that does not end the block violates CONC-010 (line 3, AC4): an idle executor with
an environment place blocks with no timer, it is drained, and it stays blocked instead of
finishing. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_deafLifecycle :
    ¬ CONC_010 (conc010_deafLifecycle (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_deafLifecycleStep (C := conc010_c)
    (o := conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none])) (l := .drain)
    (p := fun _ s' => s'.parked) (by decide)
  have := (h conc010_c).2.2.1 .drain s s' ⟨hs, trivial⟩
  simp [this] at hp

/-! ### Coverage: a wait that only a poll can leave (`Conc010Covers`) -/

/-- The steps by which the loop leaves the wait: the wake, and the settle, publish and inject
steps it may take straight from the wait (ruling D70 (a)). -/
def conc010_waitExit {N T : Type} : XLbl N T → Bool
  | .wake | .commit _ | .fail _ | .tdeposit _ | .publish _ | .inject _ | .discard _ => true
  | _ => false

/-- The sleep the loop started is over: its timer (the nearest boundary from the cycle reading)
or, with none ahead, a 60 unit re-check has run out. -/
def conc010_sleepOver {N T : Type} (C : Cfg N T) (s : XSt N T) : Bool :=
  decide (s.cyc + (nextBoundary C s).getD 60 ≤ s.now)

/-- An uninterruptible sleep, a poll: every arrival queues its item and clears the flag as the
reference does, but the loop can leave the wait only when its sleep is over. The slips it stands
for: a TypeScript `wakeUp()` that only sets `wakeUpPending` and never resolves the waiter, so the
timeout decides the race in `awaitWork`; a Java wait that calls `Thread.sleep(pollMs)` instead
of `tryAcquire`; a Rust wait that sleeps and then calls `try_recv` instead of selecting. -/
def conc010_sleepyWaitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (l : XLbl N T) : Option (XSt N T) :=
  if conc010_waitExit l && decide (s.phase = .await) && !conc010_sleepOver C s then none
  else xstep C s l

/-- The executor of `conc010_sleepyWaitStep`. -/
def conc010_sleepyWait {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_sleepyWaitStep C s l = some s'

/-- Every step of `conc010_sleepyWait` is a step of the reference: it only withholds steps. -/
theorem conc010_sleepyWait_sub {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : conc010_sleepyWait C s l s') : RefExec C s l s' := by
  unfold conc010_sleepyWait conc010_sleepyWaitStep at h
  split at h
  · cases h
  · exact h

/-- The sleepy wait meets every line of CONC-010: its steps are steps of the reference
(`conc010_sleepyWait_sub`), and every line constrains only the steps an executor takes. -/
theorem conc010_sleepyWait_meets {N T : Type} [DecidableEq N] :
    CONC_010 (conc010_sleepyWait (N := N) (T := T)) := by
  intro C
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := CONC_010_reference (N := N) (T := T) C
  exact ⟨fun s s' ⟨tmr, h⟩ => h1 s s' ⟨tmr, conc010_sleepyWait_sub h⟩,
    fun s s' ⟨tmr, h⟩ => h2 s s' ⟨tmr, conc010_sleepyWait_sub h⟩,
    fun l s s' ⟨h, ha⟩ => h3 l s s' ⟨conc010_sleepyWait_sub h, ha⟩,
    fun tmr s s' h => h4 tmr s s' (conc010_sleepyWait_sub h),
    fun i ok s s' h => h5 i ok s s' (conc010_sleepyWait_sub h),
    fun i e s s' h => h6 i e s s' (conc010_sleepyWait_sub h)⟩

/-- The wake after an arrival is coverage, not a line: a wait that only a poll can leave meets
every line of CONC-010 (`conc010_sleepyWait_meets`) and fails its coverage conjunct
`Conc010Covers` (the third EARS sentence, AC2): the loop blocks with no timer while the action of
`t` is in flight, the action returns and the flag drops, but no wake is offered until the 60 unit
sleep is over. -/
@[evidence cites "CONC-010" "the executor shall end any block of its wait at once and be ready to leave the wait for the start of its loop without waiting for a timer: an executor whose wait can be left only when its sleep is over meets every line of the block and fails its coverage clause Conc010Covers in ExecCoversW5"]
theorem conc010_covers_sleepyWait :
    CONC_010 (conc010_sleepyWait (N := Nat) (T := Nat)) ∧
      ¬ Conc010Covers (conc010_sleepyWait (N := Nat) (T := Nat)) := by
  refine ⟨conc010_sleepyWait_meets, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_sleepyWaitStep (C := conc010_c)
    (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none])) (l := .ret 0 true)
    (p := fun s s' => s.phase == .await && liveB conc010_c s &&
      (conc010_sleepyWaitStep conc010_c s' .wake).isNone) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
  obtain ⟨s'', hw, -⟩ := h conc010_c (.ret 0 true) s s' hs trivial hp.1.1 hp.1.2
  have hw' : conc010_sleepyWaitStep conc010_c s' .wake = some s'' := hw
  rw [hp.2] at hw'
  cases hw'

/-! ### Violation: an outcome kept off the completion queue (line 5) -/

/-- Firing `i` is in flight with its outcome set. -/
def conc010_outcomeSet {N T : Type} (s : XSt N T) (i : Nat) : Bool :=
  (s.fl.find? (·.id == i)).any (·.out.isSome)

/-- A settle step that reads the firing record instead of the completion queue. -/
def conc010_settleFromRecord {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) (i : Nat)
    (l : XLbl N T) : Option (XSt N T) :=
  if conc010_outcomeSet s i then xstep C { s with cq := if s.cq.contains i then s.cq else s.cq ++ [i] } l
  else none

/-- An executor that records a returned or expired outcome on the firing record only and settles
from the record, while its park check reads the completion queue. The slip it stands for: a Java
park check that looks only at `completionQueue` while the durable record of a completion is the
in-flight future, without the loop over the done futures; or a TypeScript `awaitWork` re-check of
the same queue-only shape. -/
def conc010_outcomeOnRecordStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (retStep s i ok).map fun s' => { s' with cq := s.cq }
  | .expire i e => (expireStep C s i e).map fun s' => { s' with cq := s.cq }
  | .commit i => conc010_settleFromRecord C s i (.commit i)
  | .fail i => conc010_settleFromRecord C s i (.fail i)
  | .tdeposit i => conc010_settleFromRecord C s i (.tdeposit i)
  | l => xstep C s l

/-- The executor of `conc010_outcomeOnRecordStep`. -/
def conc010_outcomeOnRecord {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_outcomeOnRecordStep C s l = some s'

/-- ✗ A return whose outcome is not queued violates CONC-010 (line 5, AC2): the loop blocks with
no timer while the action of `t` is in flight, the action returns, and the completion queue stays
empty, so the park check lets the loop block again with the outcome unprocessed. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_outcomeOnRecord :
    ¬ CONC_010 (conc010_outcomeOnRecord (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_outcomeOnRecordStep (C := conc010_c)
    (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none])) (l := .ret 0 true)
    (p := fun _ s' => !s'.cq.contains 0) (by decide)
  have := (h conc010_c).2.2.2.2.1 0 true s s' hs
  simp [this] at hp

/-- The lost completion of `conc010_outcomeOnRecord`, as a run: after the return the loop blocks
again with no timer, the outcome set on the record and the completion queue empty. -/
example : ((conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none])).bind fun s =>
    (conc010_outcomeOnRecordStep conc010_c s (.ret 0 true)).bind fun s =>
      (conc010_outcomeOnRecordStep conc010_c s (.park none)).map fun s =>
        (s.parked, s.cq.isEmpty, conc010_outcomeSet s 0)) = some (true, true, true) := by
  decide

/-! ### Violation: blocking without a timer while a boundary is ahead (line 4) -/

/-- An executor whose wait sets no timer, or any timer, whatever is armed. -/
def conc010_untimedParkStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr =>
      if s.phase = .await && liveB C s && !s.parked && s.cq.isEmpty && s.pq.isEmpty &&
          s.eq.isEmpty && nothingDue C s
      then some { s with parked := true } else (xstep C s (.park tmr))
  | l => xstep C s l

/-- The executor of `conc010_untimedParkStep`. -/
def conc010_untimedPark {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc010_untimedParkStep C s l = some s'

/-- ✗ Blocking without a timer while a `Delayed(10)` transition is armed violates CONC-010
(line 4, AC3): `t` is armed at reading `0` with its earliest bound `10` ahead, the pass starts
nothing, and the loop blocks with no timer. -/
@[evidence forbids CONC_010]
theorem CONC_010_forbids_untimedPark :
    ¬ CONC_010 (conc010_untimedPark (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc010_untimedParkStep (C := conc010_cd)
    (o := conc010_at conc010_cd conc010_m1 conc010_idle) (l := .park none)
    (p := fun s _ => nextBoundary conc010_cd s == some 10) (by decide +kernel)
  exact not_timerWithin_none (by simpa using hp) ((h conc010_cd).2.2.2.1 none s s' hs)

/-! ### The cycle reading (ruling D61 (c)) -/

/-- ✓ The park decision judges at the cycle reading, as Rust does (`cycle_now`): `Delayed(10)`
`t` is armed at reading `0`, the pass starts nothing, `15` time units pass, and the reference
blocks with the timer `10` from the cycle reading although `t` is Ready at the host's present
reading. -/
@[evidence allows CONC_010]
theorem CONC_010_allows_staleReading :
    ∃ s s', conc010_at conc010_cd conc010_m1 (conc010_idle ++ [.delay 15]) = some s ∧
      RefExec conc010_cd s (.park (some 10)) s' ∧ Ready conc010_cd.X (viewAt s s.now) conc010_t ∧
      ¬ DueAtCycle conc010_cd s := by
  obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_cd)
    (o := conc010_at conc010_cd conc010_m1 (conc010_idle ++ [.delay 15])) (l := .park (some 10))
    (p := fun s _ => decide (Ready conc010_cd.X (viewAt s s.now) conc010_t) && nothingDue conc010_cd s)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨s, s', ho, hs, hp.1, not_dueAtCycle_of_nothingDue hp.2⟩

/-! ### Every line exercised -/

/-- Every line of CONC-010 is exercised by the reference: (1) the loop blocks while the action of
`t` is in flight (ruling D13 (a): the wait is entered while actions run), so the step lines 1, 2
and 4 constrain does occur; (2) the action returns while the loop is blocked, the block ends with
its outcome queued, and the loop takes it from the wait (AC2); (3) an idle executor with an
environment place blocks with no timer, a drain ends the block, and the run finishes quiescent
(AC4); (4) with `Delayed(10)` `t` armed, the loop blocks with the timer `10` (a boundary is
ahead, the trigger of line 4), and after `10` time units the wake-up starts a cycle that starts
`t` (AC3); (5) a transition Ready at the cycle reading, the trigger of line 2, occurs on a
reference run (at the first termination test, where the loop does not wait); (6) an idle
executor with an environment place blocks with no timer, `inject()` accepts a token for place
`0`, the block ends with the injection queued and a wake offered (the offer of `Conc010Covers`), and
the loop injects the token straight from the wait (AC1). -/
@[evidence nonvacuous CONC_010]
theorem CONC_010_nonvacuous :
    (∃ s s', conc010_at conc010_c conc010_m1 conc010_busy = some s ∧
      RefExec conc010_c s (.park none) s' ∧ s.fl ≠ [] ∧ s'.parked = true) ∧
    (∃ s s', conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none]) = some s ∧
      RefExec conc010_c s (.ret 0 true) s' ∧ s.parked = true ∧ s'.parked = false ∧
      s'.phase = .await ∧ s'.cq ≠ [] ∧
      (conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none, .ret 0 true, .commit 0])).isSome) ∧
    (∃ s s', conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none]) = some s ∧
      RefExec conc010_c s .drain s' ∧ s.parked = true ∧ s'.parked = false ∧
      (conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none, .drain, .wake] ++
        conc010_toTest ++ [.finish .quiescent])).map (·.phase) = some (.done .quiescent)) ∧
    (∃ s s', conc010_at conc010_cd conc010_m1 conc010_idle = some s ∧
      RefExec conc010_cd s (.park (some 10)) s' ∧ nextBoundary conc010_cd s = some 10 ∧
      (conc010_at conc010_cd conc010_m1 (conc010_idle ++ [.park (some 10), .delay 10, .wake] ++
        conc010_toTest ++ [.begin, .start "t" false])).isSome) ∧
    (∃ s, conc010_at conc010_c conc010_m1 conc010_toTest = some s ∧ DueAtCycle conc010_c s) ∧
    (∃ s s', conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none]) = some s ∧
      RefExec conc010_c s (.request 0 1 .accepted) s' ∧ s.parked = true ∧ s'.parked = false ∧
      s'.eq ≠ [] ∧ (xstep conc010_c s' .wake).isSome ∧
      (conc010_at conc010_c (fun _ => [])
        (conc010_idle ++ [.park none, .request 0 1 .accepted, .inject 0])).map (·.M 0) =
        some [1]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_c)
      (o := conc010_at conc010_c conc010_m1 conc010_busy) (l := .park none)
      (p := fun s s' => !s.fl.isEmpty && s'.parked) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', ho, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_c)
      (o := conc010_at conc010_c conc010_m1 (conc010_busy ++ [.park none])) (l := .ret 0 true)
      (p := fun s s' => s.parked && !s'.parked && s'.phase == .await && !s'.cq.isEmpty)
      (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', ho, hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2, by decide⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_c)
      (o := conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none])) (l := .drain)
      (p := fun s s' => s.parked && !s'.parked) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨s, s', ho, hs, hp.1, hp.2, by decide⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_cd)
      (o := conc010_at conc010_cd conc010_m1 conc010_idle) (l := .park (some 10))
      (p := fun s _ => nextBoundary conc010_cd s == some 10) (by decide +kernel)
    exact ⟨s, s', ho, hs, by simpa using hp, by decide +kernel⟩
  · obtain ⟨s, ho, hp⟩ := conc010_of_map (o := conc010_at conc010_c conc010_m1 conc010_toTest)
      (p := fun s => !nothingDue conc010_c s) (by decide)
    exact ⟨s, ho, dueAtCycle_of_nothingDue_false (by simpa using hp)⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := conc010_c)
      (o := conc010_at conc010_c (fun _ => []) (conc010_idle ++ [.park none]))
      (l := .request 0 1 .accepted)
      (p := fun s s' => s.parked && !s'.parked && !s'.eq.isEmpty &&
        (xstep conc010_c s' .wake).isSome) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', ho, hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2, by decide⟩

end Libpetri.Spec
