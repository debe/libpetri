import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.ENV_006

set_option linter.missingDocs true

/-!
# ENV-006: inject() rejection on a closed or draining executor (`spec/06-environment-places.md`)

What an injection request gets once the executor no longer takes new injections, over the
executor model (`RefExec`, `Reference/Exec.lean`). A caller's `inject()` is the outside step
`request p x r`: the caller asks to inject token `x` into place `p` and the executor answers `r`
(`accepted`, `refused`, or `error` for a place that is not an environment place, [ENV-002]). An
accepted request queues the event with a ticket, the executor's next identity (`XSt.nextId`); the
orchestrator then injects it (`inject k`), discards it on a close (`discard k`), or drops it with
the rest of the queue on an immediate termination (`terminateNow`) or a finish (`finish c`).

Ruling D44 (a) fixes the contract: no acceptance and no change of state while draining, closed,
stopped or finished, under one injector per executor; a reply to every such request; a ticket of
its own for every accepted injection; and AC3 read as "where an admission signal exists, every
accepted injection completes it". The last line is a liveness line over the runs that reach
their finish (`IdealRun`, an assumption of kind A). The offer, a reply to every request in a
refusing state, is coverage: `Env006Covers`, a clause of the consistency theorem's
`ExecCoversW5`, never a line.

The requirement is a predicate over an abstract executor `R : XRel N T` (glossary
`GlossaryExec.lean`), checked against the reference executor and against executors that answer
`accepted` and drop the token while draining (the silent drop), that accept and queue while
draining, that refuse and queue all the same, that accept a second injection under the ticket of
a queued one (the shared ticket), that accept while open and never queue the event (accept and
forget), and whose finish leaves the queued events queued. One more, that never answers a request
once draining (the hang), meets every line and fails only the coverage clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The states and steps the lines read -/

namespace Env006

variable {N T : Type}

/-- The executor takes no new injections: it is draining, closed or stopped (its mode is not
open, [ENV-011], [ENV-013], [ENV-015]), or its run has finished. -/
def Refusing (s : XSt N T) : Prop := s.mode ≠ .open ∨ isExecPhase s.phase = false

/-- The step answers ticket `k`, the moment an admission signal completes ([ENV-004]): it
injects the event with ticket `k` (`true`), or it takes the event with ticket `k` out of the
event queue without injecting it (`false`), as a discard on a close, an immediate termination or
a finish does. This is ENV-004's reading of an answer (`env004_answers`): a finish that leaves the
event queued does not answer it. -/
def answersTicket (k : Nat) (e : XStep N T) : Bool :=
  (match e.2.1 with
   | .inject j => j == k
   | _ => false) ||
    (decide (k ∈ e.1.eq.map (·.1)) && !decide (k ∈ e.2.2.eq.map (·.1)))

end Env006

open Env006

/-! ## ENV-006: inject() Rejection on Closed or Draining Executor -/

requirement ENV_006
  id "ENV-006"
  title "inject() Rejection on Closed or Draining Executor"
  kind B
  scope "all executors with environment places"
  source verbatim "spec/06-environment-places.md"
  covers ENV_006.s1, ENV_006.s2, ENV_006.s3, ENV_006.s4, ENV_006.s5
  reading "For every executor R and every configuration C:"
          "while the executor is draining, closed or stopped, or its run has finished, it accepts no injection request;"
          "an injection request made in such a state leaves the executor state unchanged, whatever it answers;"
          "on every run of R, at most one injection request is accepted with a given ticket k (the next identity of the state it is made in);"
          "on every run of R under C that reaches its finish, every injection request accepted with ticket k is followed by a step that answers k: the injection of k, or a step that takes the event with ticket k out of the event queue (a discard on a close, an immediate termination, or a finish)."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A call of inject() is the outside step request p x r: the caller asks to inject token x into place p and the executor answers r, which is accepted, refused (false) or error. An accepted request queues the event in the event queue (XSt.eq) with a ticket, the executor's next identity (XSt.nextId, the one supply of firing identities and event tickets), and the orchestrator later injects it (inject k), discards it once closed (discard k), or drops it with the whole queue on an immediate termination (terminateNow) or a finish (finish c). The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor: ExecutorHandle::inject (executor_handle.rs) refuses once the handle drained or closed, and the Event arm of handle_signal injects."
          "'Draining, closed or stopped, or finished' is the glossary-free predicate Refusing of this block: the mode is not open (draining, closed, or stopped by the immediate termination of ENV-015), or the loop phase is done. The body's 'execution has completed' is the finished run (phase done, after any finish step). The markdown's scope note on a terminal place (EXEC-042) says the same: a run whose terminal place is marked but whose finish step has not yet been taken is still running, a request there is accepted, and the finish terminal step that follows drops the event, which answers it false (line 4). TypeScript refuses at the call already once a terminal place is marked; that answer is false as well, so the two shapes agree on what the caller learns."
          "Ruling D44 (a), one injector per executor: lines 1 and 2 read the lifecycle as shared by every injector, as in Java, TypeScript and Python (one handle per executor). In Rust the drained flag belongs to the ExecutorHandle: a second sender on the same channel is answered true after another handle drained or closed, and the executor drops that event on receipt (the draining Event arm of handle_signal, executor_core/executor.rs), unreported. The markdown's scope note says so; the model has one injector, an assumption of kind A for Rust, under which a handle's own drain or close is the executor's. The token still never reaches the marking in Rust, which is the part of line 2 every sender keeps."
          "Line 1 is the first shall sentence: no request is answered accepted in a refusing state, so the answer is error (a place that is not an environment place, ENV-002's subject) or refused (false). AC1 (after a close, inject() returns error or false) and AC2 (after drain(), inject() returns error or false) are line 1 at a closed and at a draining state; ENV_006_nonvacuous exercises both, and a finished run as well. An executor that answers accepted while draining and drops the token, the silent drop the body sentence forbids, breaks line 1 (ENV_006_forbids_silentDrop); one that treats draining as open and queues the event breaks lines 1 and 2 (ENV_006_forbids_acceptWhileDraining)."
          "Line 2 is the second shall sentence, read as 'changes nothing': the state after the request is the state before it, so the token reaches neither the marking nor the event queue, nor any other queue a later step would deposit from. An executor that answers refused and queues the event all the same, so that the orchestrator injects it while draining, breaks line 2 alone (ENV_006_forbids_refusedButQueued). Java refuses after the run ended by queueing the event and discarding it at once; at the grain of the model that is one refused request that changes nothing."
          "Its offers are in ExecCoversW5.Env006Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). The body sentence and the first EARS sentence demand an answer and are quoted whole; their safety half is line 1, and their existence half is that clause. The 'shall return' of the first shall sentence is Env006Covers: from every refusing state a request into any place with any token has a step, so inject() returns an answer rather than blocking (ENV-015 AC3 says the same after an immediate termination). With line 1 that answer is error or refused, with line 2 it changes nothing. Env006Covers reads every refusing state, reachable or not; the reference's request rule answers in every state (env006_ref_covers). An executor whose inject() blocks once the executor drains, closes or finishes has no request step there, so it meets every line (lines 1 and 2 with no refusing request at all) and fails that clause (env006_covers_hang)."
          "Line 3 is the third shall sentence: an accepted injection is told apart by its ticket, so 'an event of its own' reads as at most one acceptance per ticket on every run. Without it line 4 could not tell two acceptances under one ticket apart, and one answer would pay for both. The reference draws tickets from a supply that no step lowers and an accepted request raises (env006_nextId_le). An executor that does not raise the supply on an accepted request, and so accepts a second injection under the ticket of a queued one and forgets it, meets line 4 (the injection of that ticket answers both acceptances) and breaks line 3 (ENV_006_forbids_sharedTicket): the second token never reaches the marking."
          "Line 4 is the fourth shall sentence and AC3, which ruling D44 (a) rewords to 'where an admission signal exists, every accepted injection completes it'. A step answers ticket k when it injects k (the signal completes with true) or takes the event with ticket k out of the queue without injecting it (false): the discard of k on a close, an immediate termination, or a finish, each of which empties the queue in the reference. That is ENV-004's reading of an answer (env004_answers); the values of the signal, and which steps may drop an event, are ENV-004's lines, as the sentence says ('with the value ENV-004 gives'), and this line says that every accepted injection reaches one of those steps. It reads only runs that reach their finish (IdealRun, an assumption of kind A: every action returns and the executor is drained, closed or quiescent); a net that never finishes has no ideal run, so ENV_006_nonvacuous decides four ideal runs, one per kind of answer. An executor that answers accepted while open and never queues the event (accept and forget) meets lines 1 to 3 and breaks line 4 on a run that drains and finishes (ENV_006_forbids_forget). So does an executor whose finish leaves the queued events queued, the slip of dropping the end-of-run completion of what is still queued (Java's drainPendingExternalEvents() in the executeLoop finally block, TypeScript's after the loop of run): the future or promise of such an event stays pending forever (ENV_006_forbids_finishKeepsQueue)."
          "Scope of line 4: Java and TypeScript return an admission signal. Rust and Python report acceptance only (ENV-004, ruling D44 (a)), so an accepted event that a stop on a terminal place drops is not reported to their caller; the model still requires the executor to inject, discard or drop every accepted event by the finish, which is the step a signal would complete at, and the markdown's scope note says so for Rust and Python. The result-less forms (TypeScript's injectNoAwait, Java's injectAsync) report nothing and are outside this requirement, as the scope note says; on a draining, closed or finished executor they drop the token without an answer, which at the grain of the model is lines 1 and 2 and Env006Covers with an answer nobody reads."
          "The test derivation (run to completion, inject, error; drain, inject, error) is ENV_006_nonvacuous's refused requests after a finish and after a drain."
  signoff "2026-11-13 f763b1af231c3340 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (while (fun s => Refusing s), never (fun s s' => ∃ p x, R C s (.request p x .accepted) s')) ∧
      (on (fun s s' => Refusing s ∧ ∃ p x r, R C s (.request p x r) s'), shall (fun s s' => s' = s)) ∧
      (∀ s0 k tr, XRun R C s0 tr → (at-most-once (acceptsTicket k)) tr) ∧
      (∀ s0 k, on-ideal-runs (IdealRun R C s0), shall
        (fun tr => (when acceptsTicket k, shall answersTicket k) tr))

/- The pinned readable form of ENV-006: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_006 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (while fun s => Refusing s, never fun s s' => ∃ p x, R C s (XLbl.request p x Reply.accepted) s') ∧
      (on fun s s' => Refusing s ∧ ∃ p x r, R C s (XLbl.request p x r) s', shall fun s s' => s' = s) ∧
        (∀ (s0 : XSt N T) (k : ℕ) (tr : List (XStep N T)), XRun R C s0 tr → (at-most-once acceptsTicket k) tr) ∧
          ∀ (s0 : XSt N T) (k : ℕ),
            on-ideal-runs IdealRun R C s0, shall fun tr => (when acceptsTicket k, shall answersTicket k) tr
-/
#guard_msgs in #print ENV_006

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- An accepted reply needs an open executor whose run has not finished (`replyFor`). -/
theorem env006_replyFor_accepted {C : Cfg N T} {s : XSt N T} {p : N}
    (h : replyFor C s p = .accepted) : s.mode = .open ∧ isExecPhase s.phase = true := by
  unfold replyFor at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc
    · cases h

/-- Line 1 for the reference: an accepted request needs `replyFor` to accept, which needs an
open, running executor. -/
theorem env006_line1 (C : Cfg N T) :
    while (fun s => Refusing s), never
      (fun s s' => ∃ p x, RefExec C s (.request p x .accepted) s') := by
  rintro s s' ⟨p, x, h⟩ hr
  obtain ⟨hrep, -⟩ := requestStep_some (C := C) h
  obtain ⟨hm, hph⟩ := env006_replyFor_accepted hrep.symm
  rcases hr with hr | hr
  · exact hr hm
  · rw [hph] at hr
    cases hr

/-- Line 2 for the reference: a request that is not accepted returns the state unchanged, and a
refusing state accepts none. -/
theorem env006_line2 (C : Cfg N T) :
    on (fun s s' => Refusing s ∧ ∃ p x r, RefExec C s (.request p x r) s'),
      shall (fun s s' => s' = s) := by
  rintro s s' ⟨hr, p, x, r, h⟩
  obtain ⟨hrep, ⟨ha, -⟩ | ⟨-, rfl⟩⟩ := requestStep_some (C := C) h
  · exact absurd ⟨p, x, ha ▸ h⟩ (fun hs => env006_line1 C s s' hs hr)
  · rfl

/-- The offer of `Env006Covers` for the reference: the request rule answers every request with
`replyFor`, which in a refusing state is not `accepted`, and such a request returns the state
unchanged. -/
theorem env006_answers_refusing (C : Cfg N T) :
    ∀ s, Refusing s → ∀ (p : N) (x : T), ∃ r s', RefExec C s (.request p x r) s' := by
  intro s hs p x
  refine ⟨replyFor C s p, s, ?_⟩
  have hna : replyFor C s p ≠ .accepted := fun ha => by
    obtain ⟨hm, hph⟩ := env006_replyFor_accepted ha
    rcases hs with hs | hs
    · exact hs hm
    · rw [hph] at hs
      cases hs
  show requestStep C s p x (replyFor C s p) = some s
  simp [requestStep, hna]

/-- The ticket supply of the reference never goes down: only an accepted request and a start
raise it, and no step lowers it. -/
theorem env006_nextId_le {C : Cfg N T} {s s2 : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s2) : s.nextId ≤ s2.nextId := by
  unfold RefExec xstep at h
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact Nat.le_refl _
  | write i p x => obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact Nat.le_refl _
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact Nat.le_refl _
  | ret i ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact Nat.le_refl _
  | expire i e => obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact Nat.le_refl _
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact Nat.le_succ _
    · exact Nat.le_refl _
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact Nat.le_refl _
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact Nat.le_refl _
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact Nat.le_refl _
  | commit i => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact Nat.le_refl _
  | fail i => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact Nat.le_refl _
  | tdeposit i => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact Nat.le_refl _
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact Nat.le_refl _
  | publish i => obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h; exact Nat.le_refl _
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact Nat.le_refl _
  | inject j => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact Nat.le_refl _
  | discard j => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact Nat.le_refl _
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact Nat.le_refl _
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact Nat.le_refl _
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact Nat.le_refl _
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact Nat.le_refl _
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact Nat.le_refl _
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact Nat.le_refl _
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact Nat.le_refl _
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact Nat.le_refl _
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact Nat.le_refl _
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h; exact Nat.le_succ _
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact Nat.le_refl _
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact Nat.le_refl _
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact Nat.le_refl _
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact Nat.le_refl _

/-- An accepted request of the reference takes ticket `k` and raises the supply past it. -/
theorem env006_accepts {C : Cfg N T} {s s2 : XSt N T} {l : XLbl N T} {k : Nat}
    (h : RefExec C s l s2) (ht : acceptsTicket k (s, l, s2) = true) :
    s.nextId = k ∧ s2.nextId = s.nextId + 1 := by
  cases l with
  | request p x r =>
    simp only [acceptsTicket, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨rfl, hk⟩ := ht
    obtain ⟨-, ⟨-, rfl⟩ | ⟨ha, -⟩⟩ := requestStep_some (C := C) h
    · exact ⟨hk, rfl⟩
    · exact absurd rfl ha
  | _ => simp [acceptsTicket] at ht

/-- Line 3 for the reference, as a scan: once ticket `k` is accepted the supply is past `k` and
stays there, so no later request is accepted with ticket `k`. -/
theorem env006_once {C : Cfg N T} {k : Nat} :
    ∀ (tr : List (XStep N T)) (s : XSt N T) (fired : Bool), XRun RefExec C s tr →
      (fired = true → k < s.nextId) →
      (afterNever (acceptsTicket k) (acceptsTicket k)).scan fired tr = true
  | [], _, _, _, _ => rfl
  | (s1, l, s2) :: rest, s, fired, hrun, hinv => by
    obtain ⟨he1, hstep, hrest⟩ := hrun
    simp only at he1 hstep hrest
    subst he1
    have hle := env006_nextId_le hstep
    simp only [Watch.scan, afterNever, Bool.and_eq_true]
    refine ⟨?_, env006_once rest s2 _ hrest ?_⟩
    · cases hf : fired
      · rfl
      · cases ha : acceptsTicket k (s1, l, s2)
        · rfl
        · have h1 := hinv hf
          have h2 := (env006_accepts hstep ha).1
          omega
    · intro hf
      cases ha : acceptsTicket k (s1, l, s2)
      · rw [ha, Bool.or_false] at hf
        exact Nat.lt_of_lt_of_le (hinv hf) hle
      · obtain ⟨h1, h2⟩ := env006_accepts hstep ha
        omega

/-- A step of the reference that does not answer ticket `k` keeps the event with ticket `k`
queued (a step that takes it out of the queue answers it) and the run going: only a finish ends
the run, and every finish empties the queue. -/
theorem env006_keep {C : Cfg N T} {s s2 : XSt N T} {l : XLbl N T} {k : Nat}
    (h : RefExec C s l s2) (hk : k ∈ s.eq.map (·.1)) (hph : isExecPhase s.phase = true)
    (hna : answersTicket k (s, l, s2) = false) :
    k ∈ s2.eq.map (·.1) ∧ isExecPhase s2.phase = true := by
  have hq : k ∈ s2.eq.map (·.1) := by
    have h2 := (Bool.or_eq_false_iff.mp hna).2
    simp only [hk, decide_true, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq] at h2
    exact h2
  refine ⟨hq, ?_⟩
  unfold RefExec xstep at h
  cases l with
  | delay δ => cases xstepW_delay h; exact hph
  | write i p x => obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact hph
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact hph
  | ret i ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact hph
  | expire i e => obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact hph
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact hph
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact hph
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact hph
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact hph
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; simp at hq
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; simp at hq
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; simp at hq
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; simp at hq
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    simp only [depositAt, settle]
    split <;> simp_all [isExecPhase]
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    simp only [settle]
    split <;> simp_all [isExecPhase]
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    simp only [depositAt, settle]
    split <;> simp_all [isExecPhase]
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | publish i =>
    obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
    simp only
    split <;> simp_all [isExecPhase]
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | inject j =>
    obtain ⟨p, x, rest, -, -, -, hph', rfl⟩ := injectStep_some h
    rcases hph' with h' | h' <;> simp [h', isExecPhase]
  | discard j =>
    obtain ⟨p, x, rest, -, -, -, hph', rfl⟩ := discardStep_some h
    rcases hph' with h' | h' <;> simp [h', isExecPhase]
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hph
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; rfl
  | start n sy => obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h; exact hph
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact hph
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    simp only
    split <;> rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact hph
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; rfl

omit [DecidableEq N] in
/-- The end of a run with a first step is the end of the run after it. -/
theorem env006_last_cons (s0 : XSt N T) (e : XStep N T) (rest : List (XStep N T)) :
    XRun.last s0 (e :: rest) = XRun.last e.2.2 rest := by
  cases rest with
  | nil => rfl
  | cons x xs => simp [XRun.last, List.getLast?_cons]

/-- Line 4 for the reference, as a scan: while a response is owed, the event with ticket `k` is
queued and the run goes on, so a run that reaches its finish answers it (only a finish ends the
run, and a finish with `k` queued answers `k`). -/
theorem env006_scan {C : Cfg N T} {k : Nat} :
    ∀ (tr : List (XStep N T)) (s : XSt N T) (owed : Bool), XRun RefExec C s tr →
      (owed = true → k ∈ s.eq.map (·.1) ∧ isExecPhase s.phase = true) →
      isExecPhase (XRun.last s tr).phase = false →
      (whenShall (acceptsTicket k) (answersTicket k)).scan owed tr = true
  | [], s, owed, _, hinv, hend => by
    cases owed
    · rfl
    · have := (hinv rfl).2
      simp only [XRun.last, List.getLast?_nil, Option.map_none, Option.getD_none] at hend
      rw [this] at hend
      cases hend
  | (s1, l, s2) :: rest, s, owed, hrun, hinv, hend => by
    obtain ⟨he1, hstep, hrest⟩ := hrun
    simp only at he1 hstep hrest
    subst he1
    simp only [Watch.scan, whenShall, Bool.true_and]
    refine env006_scan rest s2 _ hrest ?_ (by rwa [env006_last_cons] at hend)
    intro ho
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ho
    obtain ⟨ho | ht, hna⟩ := ho
    · obtain ⟨hk, hph⟩ := hinv ho
      exact env006_keep hstep hk hph hna
    · cases l with
      | request p x r =>
        simp only [acceptsTicket, Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        obtain ⟨hrep, ⟨-, rfl⟩ | ⟨ha, -⟩⟩ := requestStep_some (C := C) hstep
        · refine ⟨?_, (env006_replyFor_accepted hrep.symm).2⟩
          simp
        · exact absurd rfl ha
      | _ => simp [acceptsTicket] at ht

end Reference

/-- ✓ The reference executor satisfies ENV-006: `replyFor` accepts only while open and running,
a request it does not accept returns the state unchanged (`requestStep_some`), the ticket supply
never goes down and an acceptance raises it (`env006_nextId_le`), and every step that does not
answer a queued ticket keeps it queued and the run going (`env006_keep`). -/
@[evidence holds ENV_006]
theorem ENV_006_reference {N T : Type} [DecidableEq N] :
    ENV_006 (RefExec (N := N) (T := T)) := by
  intro C
  exact ⟨env006_line1 C, env006_line2 C,
    fun s0 k tr hr => env006_once tr s0 false hr (fun h => by cases h), fun s0 k tr htr =>
    env006_scan tr s0 false htr.1 (fun h => by cases h) htr.2⟩

/-- **The coverage conjunct ENV-006 asks of the consistency theorem's `ExecCoversW5`**: in every
state where the executor takes no new injections (draining, closed or stopped, or a finished run),
an injection request into any place with any token has a step, so `inject()` returns an answer
rather than blocking (the 'shall return' of the first EARS sentence). Offers are never a line of
a block (glossary `GlossaryExec.lean`). -/
def Env006Covers {N T : Type} (E : XRel N T) : Prop :=
  ∀ C s, Refusing s → ∀ (p : N) (x : T), ∃ r s', E C s (.request p x r) s'

/-- The reference meets ENV-006's coverage conjunct: its request rule answers every request with
`replyFor`, in every state (`env006_answers_refusing`). -/
theorem env006_ref_covers {N T : Type} [DecidableEq N] :
    Env006Covers (RefExec (N := N) (T := T)) :=
  fun C => env006_answers_refusing C

/-! ### Examples

One environment place `0`, no transitions; the injected token is `5`. -/

/-- The configuration of the examples: environment place `0`, no transition. -/
def env006_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [] }, timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => true,
    res := 0 }

/-- The initial state: an empty marking at reading `0`. -/
def env006_s0 : XSt Nat Nat := xinit (fun _ => []) 0

/-- The trace of a label run of a step function `g`, if every label is a step. -/
def env006_trace {N T : Type} (g : XSt N T → XLbl N T → Option (XSt N T)) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g s l).bind fun s' => (env006_trace g s' ls).map ((s, l, s') :: ·)

/-- A trace `env006_trace g` builds is a run of every executor that contains `g`'s steps. -/
theorem env006_trace_run {N T : Type} {g : XSt N T → XLbl N T → Option (XSt N T)}
    {E : XRel N T} {C : Cfg N T} (hg : ∀ s l s', g s l = some s' → E C s l s') :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      env006_trace g s ls = some tr → XRun E C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [env006_trace] at h
    cases hs : g s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : env006_trace g s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hg s l s' hs, env006_trace_run hg ht⟩

/-- Read a decided fact `p` off the trace of a label run. -/
theorem env006_trace_of_check {N T : Type} {g : XSt N T → XLbl N T → Option (XSt N T)}
    {s0 : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (env006_trace g s0 ls).map p = some true) :
    ∃ tr, env006_trace g s0 ls = some tr ∧ p tr = true := by
  cases ht : env006_trace g s0 ls with
  | none => simp [ht] at h
  | some tr => simp only [ht, Option.map_some, Option.some.injEq] at h; exact ⟨tr, rfl, h⟩

/-- The kind of answer a step gives a ticket: 1 an injection, 2 a discard, 3 a finish, 4 an
immediate termination, 0 none. -/
def env006_kind {N T : Type} (e : XStep N T) : Nat :=
  match e.2.1 with
  | .inject _ => 1
  | .discard _ => 2
  | .finish _ => 3
  | .terminateNow => 4
  | _ => 0

/-- The decided check of an ideal run that accepts ticket `0` and answers it with a step of kind
`kd`: the run finishes, ticket `0` is accepted and answered as line 3 says, and the answer is of
kind `kd`. -/
def env006_answered (kd : Nat) (tr : List (XStep Nat Nat)) : Bool :=
  !isExecPhase (XRun.last env006_s0 tr).phase && tr.any (acceptsTicket 0) &&
    decide (WhenShall (acceptsTicket 0) (answersTicket 0) tr) &&
    tr.any (fun e => answersTicket 0 e && env006_kind e == kd)

/-- Accept, drain, inject, finish quiescent: the token lands in place `0`. -/
def env006_runInject : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .drain, .endCompletions, .endPublications, .inject 0, .endEvents,
   .update, .deadline [], .finish .quiescent]

/-- Accept, close, discard, finish closed. -/
def env006_runDiscard : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .close, .endCompletions, .endPublications, .discard 0, .endEvents,
   .update, .deadline [], .finish .closed]

/-- Accept after step 2, close, finish closed with the event still queued. -/
def env006_runCleared : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .request 0 5 .accepted, .update, .close,
   .deadline [], .finish .closed]

/-- Accept, terminate immediately, finish stopped. -/
def env006_runStopped : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .terminateNow, .finish .stopped]

/-- An ideal run of the reference whose decided check is `p`. -/
theorem env006_ideal_of_check {ls : List (XLbl Nat Nat)} {kd : Nat}
    (h : (env006_trace (xstep env006_cfg) env006_s0 ls).map (env006_answered kd) = some true) :
    ∃ tr, IdealRun RefExec env006_cfg env006_s0 tr ∧ Occurs (acceptsTicket 0) tr ∧
      WhenShall (acceptsTicket 0) (answersTicket 0) tr ∧
      Occurs (fun e => answersTicket 0 e && env006_kind e == kd) tr := by
  obtain ⟨tr, htr, hp⟩ := env006_trace_of_check h
  simp only [env006_answered, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
  exact ⟨tr, ⟨env006_trace_run (fun _ _ _ h => h) htr, hp.1.1.1⟩, hp.1.1.2, hp.1.2, hp.2⟩

/-- Every line of ENV-006 is exercised by the reference: a request is refused after a drain
(AC2, the test derivation), after a close (AC1) and after the run finished (the test derivation);
and four ideal runs accept ticket `0` and answer it, one per kind of answer: the injection that
lands the token in place `0`, the discard after a close, the finish closed with the event still
queued, and the immediate termination (line 4, AC3). -/
@[evidence nonvacuous ENV_006]
theorem ENV_006_nonvacuous :
    (∃ s s', RefExec env006_cfg s (.request 0 5 .refused) s' ∧ s.mode = .draining) ∧
    (∃ s s', RefExec env006_cfg s (.request 0 5 .refused) s' ∧ s.mode = .closed) ∧
    (∃ s s', RefExec env006_cfg s (.request 0 5 .refused) s' ∧ isExecPhase s.phase = false) ∧
    (∃ tr, IdealRun RefExec env006_cfg env006_s0 tr ∧ Occurs (acceptsTicket 0) tr ∧
      WhenShall (acceptsTicket 0) (answersTicket 0) tr ∧
      Occurs (fun e => answersTicket 0 e && env006_kind e == 1) tr ∧
      (XRun.last env006_s0 tr).M 0 = [5]) ∧
    (∃ tr, IdealRun RefExec env006_cfg env006_s0 tr ∧ Occurs (acceptsTicket 0) tr ∧
      WhenShall (acceptsTicket 0) (answersTicket 0) tr ∧
      Occurs (fun e => answersTicket 0 e && env006_kind e == 2) tr) ∧
    (∃ tr, IdealRun RefExec env006_cfg env006_s0 tr ∧ Occurs (acceptsTicket 0) tr ∧
      WhenShall (acceptsTicket 0) (answersTicket 0) tr ∧
      Occurs (fun e => answersTicket 0 e && env006_kind e == 3) tr) ∧
    (∃ tr, IdealRun RefExec env006_cfg env006_s0 tr ∧ Occurs (acceptsTicket 0) tr ∧
      WhenShall (acceptsTicket 0) (answersTicket 0) tr ∧
      Occurs (fun e => answersTicket 0 e && env006_kind e == 4) tr) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env006_cfg)
      (o := xrun env006_cfg env006_s0 [.drain]) (l := .request 0 5 .refused)
      (p := fun s _ => s.mode == .draining) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env006_cfg)
      (o := xrun env006_cfg env006_s0 [.close]) (l := .request 0 5 .refused)
      (p := fun s _ => s.mode == .closed) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env006_cfg)
      (o := xrun env006_cfg env006_s0
        [.drain, .endCompletions, .endPublications, .endEvents, .update, .deadline [],
         .finish .quiescent])
      (l := .request 0 5 .refused) (p := fun s _ => !isExecPhase s.phase) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨tr, htr, hp⟩ := env006_trace_of_check (g := xstep env006_cfg) (s0 := env006_s0)
      (ls := env006_runInject)
      (p := fun tr => env006_answered 1 tr && (XRun.last env006_s0 tr).M 0 == [5]) (by decide)
    simp only [env006_answered, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      beq_iff_eq] at hp
    exact ⟨tr, ⟨env006_trace_run (fun _ _ _ h => h) htr, hp.1.1.1.1⟩, hp.1.1.1.2, hp.1.1.2,
      hp.1.2, hp.2⟩
  · exact env006_ideal_of_check (ls := env006_runDiscard) (by decide)
  · exact env006_ideal_of_check (ls := env006_runCleared) (by decide)
  · exact env006_ideal_of_check (ls := env006_runStopped) (by decide)

/-! ### Violation: the silent drop (answers `accepted` while draining, drops the token) -/

/-- An executor that answers `accepted` to a request into an environment place while it refuses
injections and drops the token (TypeScript's result-less form with a reply attached, Rust's
second sender); otherwise the reference. -/
def env006_silentDropStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if decide (p ∈ C.envs) && (s.mode != .open || !isExecPhase s.phase) && r == .accepted
    then some s else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `env006_silentDropStep`. -/
def env006_silentDrop {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_silentDropStep C s l = some s'

/-- ✗ The silent drop violates ENV-006 (line 1, the body sentence's "rather than silently
dropping the token"): after a drain, a request into place `0` is answered `accepted`. -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_silentDrop : ¬ ENV_006 (env006_silentDrop (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env006_silentDropStep (C := env006_cfg)
    (o := xrun env006_cfg env006_s0 [.drain]) (l := .request 0 5 .accepted)
    (p := fun s _ => s.mode == .draining) (by decide)
  have hm : s.mode = .draining := by simpa using hp
  exact (h env006_cfg).1 s s' ⟨0, 5, hs⟩ (Or.inl (by rw [hm]; decide))

/-! ### Violation: accepting while draining (the draining executor treated as open) -/

/-- An executor whose request rule reads a draining executor as open: it accepts and queues the
event, and the orchestrator injects it while draining; otherwise the reference. -/
def env006_acceptWhileDrainingStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    (requestStep C { s with mode := if s.mode = .draining then .open else s.mode } p x r).map
      fun s' => { s' with mode := s.mode }
  | l => xstep C s l

/-- The executor of `env006_acceptWhileDrainingStep`. -/
def env006_acceptWhileDraining {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_acceptWhileDrainingStep C s l = some s'

/-- ✗ Accepting while draining violates ENV-006 (line 1, AC2): after a drain, a request into place
`0` is answered `accepted` and queued. -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_acceptWhileDraining :
    ¬ ENV_006 (env006_acceptWhileDraining (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env006_acceptWhileDrainingStep (C := env006_cfg)
    (o := xrun env006_cfg env006_s0 [.drain]) (l := .request 0 5 .accepted)
    (p := fun s s' => s.mode == .draining && s'.eq.length == 1) (by decide)
  have hm : s.mode = .draining := by simp at hp; exact hp.1
  exact (h env006_cfg).1 s s' ⟨0, 5, hs⟩ (Or.inl (by rw [hm]; decide))

/-! ### Violation: refusing, and queueing all the same -/

/-- An executor that answers a refusing state's request into an environment place with `refused`
and queues the event all the same; the orchestrator then injects it while draining. Otherwise the
reference. -/
def env006_refusedButQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if decide (p ∈ C.envs) && (s.mode != .open || !isExecPhase s.phase) && r == .refused
    then some { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1, parked := false }
    else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `env006_refusedButQueuedStep`. -/
def env006_refusedButQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_refusedButQueuedStep C s l = some s'

/-- ✗ Refusing and queueing all the same violates ENV-006 (line 2): after a drain, the refused
request into place `0` queues the event, which a later step 2 would inject. Its reply is
`refused`, so line 1 alone does not reject it. -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_refusedButQueued :
    ¬ ENV_006 (env006_refusedButQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env006_refusedButQueuedStep (C := env006_cfg)
    (o := xrun env006_cfg env006_s0 [.drain]) (l := .request 0 5 .refused)
    (p := fun s s' => s.mode == .draining && s'.eq.length != s.eq.length) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  have he := (h env006_cfg).2.1 s s' ⟨Or.inl (by rw [hp.1]; decide), 0, 5, .refused, hs⟩
  exact hp.2 (by rw [he])

/-! ### Violation: accept and forget -/

/-- An executor that answers `accepted` while open and draws the ticket, but never queues the
event; otherwise the reference. -/
def env006_forgetStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s' => { s' with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env006_forgetStep`. -/
def env006_forget {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_forgetStep C s l = some s'

/-- Accept, drain, and finish quiescent: under accept and forget nothing is queued, so the run
finishes without answering ticket `0`. -/
def env006_runForget : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .drain, .endCompletions, .endPublications, .endEvents, .update,
   .deadline [], .finish .quiescent]

/-- ✗ Accept and forget violates ENV-006 (line 4, AC3): the request into place `0` is accepted
while open, the executor drains and finishes quiescent, and ticket `0` is never injected,
discarded or dropped by a finish. Lines 1 and 2 speak only of refusing states, and it raises the
ticket supply as the reference does (line 3), so they do not reject it. -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_forget : ¬ ENV_006 (env006_forget (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, htr, hp⟩ := env006_trace_of_check (g := env006_forgetStep env006_cfg)
    (s0 := env006_s0) (ls := env006_runForget)
    (p := fun tr => !isExecPhase (XRun.last env006_s0 tr).phase &&
      !decide (WhenShall (acceptsTicket 0) (answersTicket 0) tr)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp.2 ((h env006_cfg).2.2.2 env006_s0 0 tr
    ⟨env006_trace_run (fun _ _ _ h => h) htr, hp.1⟩)

/-! ### Coverage: the hang (no answer once draining, closed or finished) -/

/-- An executor whose `inject()` blocks once the executor takes no new injections: it has no
request step from a draining, closed, stopped or finished state; otherwise the reference. -/
def env006_hangStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if s.mode != .open || !isExecPhase s.phase then none else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `env006_hangStep`. -/
def env006_hang {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_hangStep C s l = some s'

/-- Every step of the hang is a step of the reference. -/
theorem env006_hang_ref {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : env006_hang C s l s') : RefExec C s l s' := by
  unfold env006_hang at h
  unfold RefExec
  cases l with
  | request p x r =>
    simp only [env006_hangStep] at h
    split at h
    · cases h
    · exact h
  | _ => exact h

/-- Every run of the hang is a run of the reference. -/
theorem env006_hang_run {N T : Type} [DecidableEq N] {C : Cfg N T} :
    ∀ {s : XSt N T} {tr : List (XStep N T)}, XRun env006_hang C s tr → XRun RefExec C s tr
  | _, [], _ => trivial
  | _, _ :: _, ⟨he, hs, hr⟩ => ⟨he, env006_hang_ref hs, env006_hang_run hr⟩

/-- The answer is coverage, not a line: the hang has no step for a request from a draining,
closed, stopped or finished state, so the call never returns. Every step of it is a step of the
reference, so it meets every line of ENV-006 (lines 1 and 2 with no refusing request at all), and
it fails the coverage conjunct `Env006Covers` (the 'shall return' of the first EARS sentence): a
draining executor has no step for a request into place `0`. -/
@[evidence cites "ENV-006" "If inject() is called while the executor is draining, closed or stopped, or after the run has finished, then it shall return an error or false: an executor with no request step in such a state meets every line of the block and fails its coverage clause Env006Covers in ExecCoversW5"]
theorem env006_covers_hang :
    ENV_006 (env006_hang (N := Nat) (T := Nat)) ∧
      ¬ Env006Covers (env006_hang (N := Nat) (T := Nat)) := by
  refine ⟨fun C => ⟨fun s s' ⟨p, x, hs⟩ hr => env006_line1 C s s' ⟨p, x, env006_hang_ref hs⟩ hr,
    fun s s' ⟨hr, p, x, r, hs⟩ => env006_line2 C s s' ⟨hr, p, x, r, env006_hang_ref hs⟩,
    fun s0 k tr hr => env006_once tr s0 false (env006_hang_run hr) (fun h => by cases h),
    fun s0 k tr htr =>
      env006_scan tr s0 false (env006_hang_run htr.1) (fun h => by cases h) htr.2⟩, fun h => ?_⟩
  obtain ⟨r, s', hs⟩ := h env006_cfg { env006_s0 with mode := .draining } (Or.inl (by decide)) 0 5
  simp [env006_hang, env006_hangStep] at hs

/-! ### Violation: the shared ticket (a second injection under a queued ticket, forgotten) -/

/-- An executor that does not raise the ticket supply on an accepted request: an accepted request
takes ticket `nextId` and queues the event, unless an event with that ticket is already queued,
in which case it forgets the event; otherwise the reference. -/
def env006_sharedTicketStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s' =>
      if r = .accepted then
        { s' with nextId := s.nextId,
                  eq := if s.eq.any (·.1 == s.nextId) then s.eq else s'.eq }
      else s'
  | l => xstep C s l

/-- The executor of `env006_sharedTicketStep`. -/
def env006_sharedTicket {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_sharedTicketStep C s l = some s'

/-- Accept token `5`, accept token `6`, drain, inject, and finish quiescent. -/
def env006_runShared : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .request 0 6 .accepted, .drain, .endCompletions, .endPublications,
   .inject 0, .endEvents, .update, .deadline [], .finish .quiescent]

/-- ✗ The shared ticket violates ENV-006 (line 3, the third shall sentence): two requests into
place `0` are accepted with ticket `0`, the second event is never queued, and the run finishes
with only token `5` in place `0`. Line 4 alone does not reject it: the injection of ticket `0`
answers both acceptances, so the run meets line 4 (decided below). -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_sharedTicket : ¬ ENV_006 (env006_sharedTicket (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, htr, hp⟩ := env006_trace_of_check (g := env006_sharedTicketStep env006_cfg)
    (s0 := env006_s0) (ls := env006_runShared)
    (p := fun tr => !isExecPhase (XRun.last env006_s0 tr).phase &&
      decide (WhenShall (acceptsTicket 0) (answersTicket 0) tr) &&
      (XRun.last env006_s0 tr).M 0 == [5] &&
      !decide (AtMostOnce (acceptsTicket 0) tr)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp.2 ((h env006_cfg).2.2.1 env006_s0 0 tr (env006_trace_run (fun _ _ _ h => h) htr))

/-! ### Violation: the finish leaves the queued events queued -/

/-- An executor whose finish steps leave the event queue as it was, the slip of dropping the
end-of-run completion of what is still queued (Java's `drainPendingExternalEvents()` in the
`executeLoop` `finally` block, TypeScript's after the loop of `run`); otherwise the reference. -/
def env006_finishKeepsQueueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish c => (xstep C s (.finish c)).map fun s' => { s' with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env006_finishKeepsQueueStep`. -/
def env006_finishKeepsQueue {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env006_finishKeepsQueueStep C s l = some s'

/-- ✗ A finish that keeps the queue violates ENV-006 (line 4, AC3): the request into place `0` is
accepted after step 2, the executor closes and finishes closed with the event still queued, and
no step takes it out of the queue, so its future or promise stays pending forever. Its requests
are the reference's, so lines 1 to 3 do not reject it. -/
@[evidence forbids ENV_006]
theorem ENV_006_forbids_finishKeepsQueue :
    ¬ ENV_006 (env006_finishKeepsQueue (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, htr, hp⟩ := env006_trace_of_check (g := env006_finishKeepsQueueStep env006_cfg)
    (s0 := env006_s0) (ls := env006_runCleared)
    (p := fun tr => !isExecPhase (XRun.last env006_s0 tr).phase &&
      ((XRun.last env006_s0 tr).eq.map (·.1)).contains 0 &&
      !decide (WhenShall (acceptsTicket 0) (answersTicket 0) tr)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp.2 ((h env006_cfg).2.2.2 env006_s0 0 tr
    ⟨env006_trace_run (fun _ _ _ h => h) htr, hp.1.1⟩)

end Libpetri.Spec
