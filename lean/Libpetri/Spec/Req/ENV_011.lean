import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Req.EXEC_040
import Libpetri.Spec.Text.ENV_011

set_option linter.missingDocs true

/-!
# ENV-011: Graceful drain (`spec/06-environment-places.md`)

The drain of an executor, over the executor model (`RefExec`, `Reference/Exec.lean`). The outside
step `drain` (a caller drains the executor) moves an open executor into the mode `draining`
(glossary `GlossaryExec.lean`: `Mode`). The requirement is a predicate over an abstract executor
`R : XRel N T`, checked against the reference executor and against executors that drop the queued
events on a drain, keep their wait asleep on a drain, reopen a closed executor on a drain, accept
an injection while draining, queue a refused injection while draining, discard queued events while
draining, stop injecting them while draining, terminate with an action in flight, terminate from
the wait, keep running at quiescence after a drain, or skip the cycle when a drained wait at
quiescence ends. A mutant reading of the literal "`drain()` is a no-op" sentence is told apart from
the requirement (ruling D20, clash env-b#6).

The comparison with an open executor (line 4) is the heart of "processed normally" and "allowed to
complete": a draining executor takes every step of its cycle exactly as the same state in mode
`open` would, except the answers to requests and snapshot requests, the lifecycle calls, and the
wait and the termination test of an executor with environment places at quiescence
(`Env011.sameAsOpen`). Lines 5 and 6 fix that termination test: a draining executor with no
terminal place marked ends only at a termination test at rest, and at such a test it takes no
executor step but a finish. Line 7 fixes the effect of the wait at rest. That the wait at rest
ends, that a finish is offered at a test at rest and that a drain is offered at all are coverage
(`Env011Covers`), for the consistency theorem's `ExecCoversW5`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The steps line 4 compares -/

namespace Env011

variable {N T : Type}

/-- The steps a draining executor takes as the same state in mode `open` does (line 4): every
label except a request, a snapshot request and the lifecycle calls (`drain`, `close`,
`terminateNow`); the termination test's `begin` and `finish` steps and the wait's `park` and
`wake` steps only away from rest (`restB`) or without environment places, since at rest an open
executor with environment places waits for an arrival ([ENV-010]) where a draining one ends its
wait and terminates. -/
def sameAsOpen [DecidableEq N] (C : Cfg N T) (s : XSt N T) : XLbl N T → Bool
  | .request _ _ _ | .snapshot _ | .drain | .close | .terminateNow => false
  | .begin | .finish _ | .park _ | .wake => !restB C s || C.envs.isEmpty
  | _ => true

/-- The effect of a step of the wait (line 7): a `park` sets the parked flag, a `wake` clears it
and goes back to step 1 of the cycle; nothing else changes. `none` for every other label. -/
def waitEffect (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .park _ => some { s with parked := true }
  | .wake => some { s with phase := .completions, parked := false }
  | _ => none

/-- The state `s` with mode `m`, everything else unchanged. -/
def withMode (m : Mode) (s : XSt N T) : XSt N T := { s with mode := m }

/-- The state `s` after a drain: mode `draining`, the wait woken ([CONC-010]), everything else
unchanged. -/
def drained (s : XSt N T) : XSt N T := { s with mode := .draining, parked := false }

end Env011

open Env011

/-! ## ENV-011: Graceful Drain -/

requirement ENV_011
  id "ENV-011"
  title "Graceful Drain"
  kind B
  scope "executors with a drain operation"
  source verbatim "spec/06-environment-places.md"
  covers ENV_011.s1, ENV_011.s2, ENV_011.s3, ENV_011.s4, ENV_011.s5, ENV_011.s6, ENV_011.s7,
        ENV_011.s8, ENV_011.s9, ENV_011.s10, ENV_011.s11, ENV_011.s12, ENV_011.s13, ENV_011.s14,
        ENV_011.s15, ENV_011.s16, ENV_011.s17, ENV_011.s18
  reading "For every executor R and every configuration C:"
          "a drain step from an open state enters mode draining, wakes the wait and changes nothing else; a drain step from any other mode (draining, closed or stopped) changes nothing;"
          "a request step from a draining state is answered with something other than accepted and changes nothing;"
          "no discard step starts in a draining state;"
          "from a draining state s, every step whose label is not a request, a snapshot, a lifecycle call (drain, close, terminateNow), or, at rest with environment places, a begin, finish, park or wake step, leads to s' exactly when the same label leads from s in mode open to some s'' and s' is s'' in mode draining;"
          "a finish step from a draining state with no terminal place marked starts at the termination test and at rest: no transition armed, no firing in flight, and the completion, publication and event queues empty;"
          "in a draining state with no terminal place marked, at the termination test and at rest, every executor step is a finish step (outside steps such as the clock advancing are still possible, and an answer to a snapshot request that leaves the state as it is is not a step of the loop and is allowed);"
          "a park or wake step from a draining state at rest has the effect of the wait and nothing else: a park sets the parked flag, a wake clears it and returns to step 1 of the cycle."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The executor state carries a lifecycle mode (open, draining, closed, stopped); drain is the outside step of a caller calling drain(), request p x r a caller's inject() of x into p answered r (accepted, refused or error), discard k the executor dropping queued event k unapplied, park and wake the start and the end of the wait of step 6, and finish c a termination with cause c (EXEC-041). The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor: ExecutorHandle::drain and inject (executor_handle.rs), the Drain arm of handle_signal, the draining termination check and the draining exit before the wait (handle_signal and run_async, executor_core/executor.rs); Java BitmapNetExecutor.drain, shouldTerminate and awaitWork, TypeScript drain, its termination check and its latched wake run the same rules."
          "Scope (ruling D20, clash env-b#4, ENVB-R7 item 7): items 2 to 4 hold while no terminal place is marked; a marked terminal place stops the executor at once and abandons the actions in flight, and the run ends with the queued events unapplied (EXEC-042), in every runtime whatever the mode. That end is the finish terminal, not a discard step, so it does not touch line 3. Lines 5 and 6 carry the premise (Live). Lines 1 to 4 and 7 need none: the reference's rules are mode-blind there too, and EXEC-042's own lines govern the terminal stop."
          "'After drain() is called' is the mode draining: the drain step sets it, and only a close (ENV-013) or an immediate termination (ENV-015) leaves it, both lifecycle steps with their own requirements; the quoted sentence on a close or an immediate termination of a draining executor says so, and line 4 leaves the lifecycle calls out of its comparison for that reason. A drained executor that later closes is governed by ENV-013 from that step on. After the run ends the mode stays draining, so line 2 also answers a request to a drained executor that has finished; ENV-006 states the replies in every mode."
          "The first and second shall sentences are line 1. A drain wakes the wait (CONC-010, ruling D13 (a): a drain is a wake reason), which is the parked flag of the state; nothing else changes. An executor whose drain also drops the queued events breaks line 1 (ENV_011_forbids_drainDrops), and so does one whose drain leaves a parked wait asleep (ENV_011_forbids_drainKeepsParked). A drain of an executor that is not open, whether draining, closed or stopped (ENV-015), changes nothing: Rust's drain() returns false and sends no signal once the handle is drained, Java and TypeScript set a flag that is already set (a closed executor stays closed, closed is tested first, and a stopped one stays stopped). The reference has no drain step there, which line 1's second half allows; an executor whose drain reopens a closed executor into draining breaks it (ENV_011_forbids_reopenClosed)."
          "The third shall sentence and item 1 (AC2) are line 2: while draining, an inject() is not accepted (it is refused, or error for a place that is not an environment place) and changes nothing. An executor that accepts it breaks the first half (ENV_011_forbids_acceptWhileDraining), one that answers refused and queues the event anyway breaks the second (ENV_011_forbids_queueRefused). In Rust the draining flag is a field of the handle (the drained field of ExecutorHandle, which inject reads first, executor_handle.rs), and an event sent through a second sender after the Drain signal is answered true and discarded (executor_core/executor.rs, the Event arm with draining set); the model has one injector per executor, an assumption for Rust and Python (ruling D44 (a), ENVB-R3). Events accepted before the drain were queued before the Drain signal in the one channel, so they are 'already queued'."
          "The fourth shall sentence and item 2 (AC3) are lines 3, 4 and 5. Line 3: a draining executor never discards a queued event (ENV_011_forbids_discardWhileDraining). Line 4 for the inject label: a queued event is injected while draining exactly as while open (ENV_011_forbids_stallEvents, an executor that stops injecting once drained). Line 5: a draining executor terminates only with the event queue empty, so no queued event is lost to the finish. 'Processed before termination' as liveness is an ideal run (IdealRun, kind A: every action returns) together with coverage; ENV_011_nonvacuous decides one."
          "The fifth shall sentence is line 4, and with it item 3 (AC4) and the no-op sentence. Line 4 compares a draining state with the same state in mode open, label by label: the steps an action takes (write, flush, return, expiry of its budget), the settle steps (commit, fail, tdeposit), the publication steps, injection, the update, the deadline step, the firing pass and, away from rest, the wait. 'Allowed to complete' is that the actions' own steps and the settle steps are those of an open executor; line 5 adds that a draining executor does not terminate before they are settled. The answers that do differ are named in the sentence: a request is refused (line 2), a snapshot request is rejected (ENV-014 AC4, which every runtime applies after a drain, with or without environment places), and at rest an executor with environment places ends its wait and terminates where an open one waits for an arrival (ENV-010, lines 5 to 7)."
          "Line 4 restates an open-mode requirement where the two modes agree: without environment places begin, finish, park and wake are compared at rest too, so with line 6 an open executor without environment places takes no executor step at a termination test at rest but a finish. That is EXEC-040's own line, which the no-op sentence presupposes."
          "The no-op sentence (ruling D20, clash env-b#6, ENVB-R7 item 2) is line 4 without environment places: then begin, finish, park and wake are compared at rest too, so a drained executor without environment places terminates exactly where it would have terminated had it not been drained. The literal reading 'drain() is a no-op', a drain step that changes nothing, is the mutant ENV_011_mutant_noop: it is told apart from the requirement by an executor that ignores the drain of an executor without environment places, which meets the literal reading and breaks line 1. The rewording is what every runtime does: after a drain, snapshot() is rejected whatever the net (ENV-014 AC4), so the state does change."
          "The sixth shall sentence is line 5 and item 4 read with 'armed' for 'enabled' (ruling D5, ENVB-R7 item 1): quiescent is the glossary term Rest of GlossaryExec (restB), nothing armed, nothing in flight, nothing queued (ruling D13 (a)), and the finish is taken at the termination test of a cycle (EXEC-001), not elsewhere in the cycle. A firing counts as in flight until it is settled and its publications are deposited (EXEC-040). An executor that terminates while an action is in flight breaks line 5 (ENV_011_forbids_finishInFlight), and so does one that terminates from its wait (ENV_011_forbids_finishInWait). Rust leaves its loop from step 6 when it is draining and quiescent (the draining exit before the Phase 6 wait of run_async, executor_core/executor.rs); the model reads that exit as the wake and the next cycle's termination test, which change nothing at rest. The cause of a draining finish is not fixed here: ENV-011 alone admits a draining executor that finishes with cause closed at quiescence, and EXEC-041 excludes it (a finish closed needs a closing mode, a finish stopped a stopped one, a finish terminal a marked terminal place), leaving quiescent."
          "The seventh shall sentence and AC5 are line 6: at a termination test with no terminal place marked and at rest, a draining executor takes no executor step but a finish (in particular no firing pass, begin). An executor that treats a draining executor with environment places as an open one there, beginning a pass where it should terminate, breaks it (ENV_011_forbids_neverEnds). Java's draining termination check reads no external event queue: it is empty there because step 2 of the same cycle emptied it and a draining executor accepts no new event."
          "The eighth shall sentence is line 7: a draining executor at rest that enters its wait changes only the parked flag, and one that ends it changes only that flag and the phase, which returns to step 1 of the cycle; an executor whose drained wait at rest skips to the termination test, past the enablement update, breaks it (ENV_011_forbids_wakeSkipsCycle). The reference may park a draining executor at rest (parkStep does not read the mode), where no runtime waits: Rust leaves the loop before its wait, Java's awaitWork does not wait when draining (BitmapNetExecutor.awaitWork, hasEnvironmentPlaces && !draining.get()), TypeScript returns on the latched wake. That is harmless because the reference's wake is offered in every live wait, so line 7 constrains the effect of such a park and does not forbid it."
          "Existence is coverage, not a line, and belongs to the consistency theorem: Env011Covers below is the conjunct ENV-011 asks of it, a clause of ExecCoversW5 (ConsistencyExec.lean), with three clauses. AC1 (drain() is available): a drain step is offered from every open state. The seventh shall sentence and AC5 ('shall terminate'): finish quiescent is offered at every termination test of a draining executor with no terminal place marked and at rest. The ninth shall sentence (the wait ends at once): a wake is offered in every wait of a draining executor with no terminal place marked and at rest. The reference meets all three (env011_ref_covers, from env011_drain_offered, env011_finish_offered and env011_wake_offered). AC1, AC5's 'shall terminate' and the ninth shall sentence are therefore enforced by the consistency theorem and not by this block's lines: an executor with an edge-triggered wait, whose parked loop wakes only after an arrival cleared its flag or on a timer (the hazard TypeScript's latched wake guards against, the wakeUpPending field of bitmap-net-executor.ts), meets every line (env011_lostWake_meets) while a drain raised before it parks leaves it asleep for good; it fails Env011Covers (env011_lostWake_not_covered, on the run: the open executor with an environment place reaches its wait at rest, is drained, then parks)."
          "The test derivation (inject, drain, the queued event processed, a new inject rejected, termination at quiescence) is ENV_011_nonvacuous's run."
          "The model reads one executor per configuration with its own queue; Rust's run_sync and the exits of a dropped handle (the handle's Drop sends a Drain) are ENV-010's notes (ruling D73 (a))."
  signoff "2026-11-13 7f4f71d351ffaeea ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (on (fun s s' => R C s .drain s'), shall (fun s s' =>
        (s.mode = .open ∧ s' = drained s) ∨
          (s.mode ≠ .open ∧ s' = s))) ∧
      (∀ p x r, on (fun s s' => s.mode = .draining ∧ R C s (.request p x r) s'),
        shall (fun s s' => r ≠ .accepted ∧ s' = s)) ∧
      (∀ k, while (fun s => s.mode = .draining), never (fun s s' => R C s (.discard k) s')) ∧
      (∀ s l s', s.mode = .draining → sameAsOpen C s l = true →
        (R C s l s' ↔ ∃ s'', R C (withMode .open s) l s'' ∧ s' = withMode .draining s'')) ∧
      (on (fun s s' => (s.mode = .draining ∧ Live C s) ∧ ∃ c, R C s (.finish c) s'),
        shall (fun s _ => s.phase = .test ∧ Rest C s)) ∧
      (while (fun s => s.mode = .draining ∧ Live C s ∧ s.phase = .test ∧ Rest C s),
        never (fun s s' => ∃ l, R C s l s' ∧ l.outside = false ∧
          (∀ a, l = .snapshot a → s' ≠ s) ∧ ∀ c, l ≠ .finish c)) ∧
      (∀ l, on (fun s s' => (s.mode = .draining ∧ Rest C s) ∧ (waitEffect s l).isSome = true ∧
          R C s l s'),
        shall (fun s s' => waitEffect s l = some s'))

/- The pinned readable form of ENV-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_011 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (on fun s s' => R C s XLbl.drain s', shall fun s s' =>
        s.mode = Mode.open ∧ s' = drained s ∨ s.mode ≠ Mode.open ∧ s' = s) ∧
      (∀ (p : N) (x : T) (r : Reply),
          on fun s s' => s.mode = Mode.draining ∧ R C s (XLbl.request p x r) s', shall fun s s' =>
            r ≠ Reply.accepted ∧ s' = s) ∧
        (∀ (k : ℕ), while fun s => s.mode = Mode.draining, never fun s s' => R C s (XLbl.discard k) s') ∧
          (∀ (s : XSt N T) (l : XLbl N T) (s' : XSt N T),
              s.mode = Mode.draining →
                sameAsOpen C s l = true →
                  (R C s l s' ↔ ∃ s'', R C (withMode Mode.open s) l s'' ∧ s' = withMode Mode.draining s'')) ∧
            (on fun s s' => (s.mode = Mode.draining ∧ Live C s) ∧ ∃ c, R C s (XLbl.finish c) s', shall fun s x =>
                s.phase = Phase.test ∧ Rest C s) ∧
              (while fun s => s.mode = Mode.draining ∧ Live C s ∧ s.phase = Phase.test ∧ Rest C s, never fun s s' =>
                  ∃ l,
                    R C s l s' ∧
                      l.outside = false ∧
                        (∀ (a : Option Bool), l = XLbl.snapshot a → s' ≠ s) ∧ ∀ (c : Cause), l ≠ XLbl.finish c) ∧
                ∀ (l : XLbl N T),
                  on fun s s' => (s.mode = Mode.draining ∧ Rest C s) ∧ (waitEffect s l).isSome = true ∧ R C s l s',
                    shall fun s s' => waitEffect s l = some s'
-/
#guard_msgs in #print ENV_011

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

namespace Env011

/-! The derived terms the rules read do not read the mode. -/

variable {C : Cfg N T} {s : XSt N T} {m : Mode}

omit [DecidableEq N] in private theorem liveB_wm : liveB C (withMode m s) = liveB C s := rfl
omit [DecidableEq N] in private theorem passFree_wm : passFree (withMode m s) = passFree s := rfl
private theorem nothingDue_wm : nothingDue C (withMode m s) = nothingDue C s := rfl
omit [DecidableEq N] in
private theorem timerOk_wm (x : Option Nat) : timerOk C (withMode m s) x = timerOk C s x := rfl
private theorem readyOrder_wm : readyOrder C (withMode m s) = readyOrder C s := rfl
private theorem updSt_wm : updSt refXPol C (withMode m s) = updSt refXPol C s := rfl
omit [DecidableEq N] in private theorem expiredNames_wm (P : XPol N T) :
    expiredNames P C (withMode m s) = expiredNames P C s := rfl
omit [DecidableEq N] in private theorem expiredNamesAt_wm (P : XPol N T) :
    expiredNames P C (atDeadline (withMode m s)) = expiredNames P C (atDeadline s) := rfl
omit [DecidableEq N] in private theorem cyc_wm : (withMode m s).cyc = s.cyc := rfl
private theorem liveAfter_wm (t : Reference.Trans N) : liveAfter (withMode m s) t = liveAfter s t :=
  rfl
private theorem afterStart_wm (t : Reference.Trans N) :
    afterStart refXPol C (withMode m s) t = afterStart refXPol C s t := rfl
private theorem recheckOn_wm :
    (refXPol (N := N) (T := T)).recheckOn (withMode m s) = refXPol.recheckOn s := rfl
omit [DecidableEq N] in private theorem restB_wm : restB C (withMode m s) = restB C s := rfl
omit [DecidableEq N] in private theorem M_wm : (withMode m s).M = s.M := rfl
omit [DecidableEq N] in private theorem fl_wm : (withMode m s).fl = s.fl := rfl
omit [DecidableEq N] in private theorem cq_wm : (withMode m s).cq = s.cq := rfl
omit [DecidableEq N] in private theorem pq_wm : (withMode m s).pq = s.pq := rfl
omit [DecidableEq N] in private theorem eq_wm : (withMode m s).eq = s.eq := rfl
omit [DecidableEq N] in private theorem phase_wm : (withMode m s).phase = s.phase := rfl
omit [DecidableEq N] in private theorem order_wm : (withMode m s).order = s.order := rfl
omit [DecidableEq N] in private theorem mode_wm : (withMode m s).mode = m := rfl
omit [DecidableEq N] in private theorem st_wm : (withMode m s).st = s.st := rfl
omit [DecidableEq N] in private theorem parked_wm : (withMode m s).parked = s.parked := rfl
omit [DecidableEq N] in private theorem now_wm : (withMode m s).now = s.now := rfl
omit [DecidableEq N] in private theorem nextId_wm : (withMode m s).nextId = s.nextId := rfl
omit [DecidableEq N] in private theorem started_wm : (withMode m s).started = s.started := rfl

/-- The class of line 4 reads the state only through `restB`, which does not read the mode. -/
theorem sameAsOpen_wm (l : XLbl N T) : sameAsOpen C (withMode m s) l = sameAsOpen C s l := by
  cases l <;> rfl

omit [DecidableEq N] in
/-- Putting back the mode a state had. -/
theorem withMode_withMode (h : s.mode = m) (m' : Mode) : withMode m (withMode m' s) = s := by
  cases s
  simp only [withMode] at h ⊢
  rw [h]

end Env011

/-- **A draining reference executor steps as an open one**: on every label of the class of line 4
the reference's step from the state in mode `draining` is its step from the same state in mode
`open`, with the mode put back. Every rule reads the mode only as `closing`, `stopped` or `open`
in the termination test; draining and open agree on the first two, and the class leaves out the
termination test at rest with environment places. -/
theorem env011_xstep_draining (C : Cfg N T) (s : XSt N T) (hs : s.mode = .open) (l : XLbl N T)
    (hl : sameAsOpen C s l = true) :
    xstep C (withMode .draining s) l = (xstep C s l).map (withMode .draining) := by
  cases l <;> simp [sameAsOpen] at hl
  all_goals simp only [xstep, xstepW, writeStep, onOpen, flushStep, retStep, expireStep, commitStep,
    failStep, tdepositStep, publishStep, injectStep, discardStep, startStep, loseStep, parkStep,
    wakeStep, canSettle, settleOk, finishQ, liveB_wm, passFree_wm, nothingDue_wm, timerOk_wm,
    readyOrder_wm, updSt_wm, expiredNamesAt_wm, expiredNames_wm, liveAfter_wm, afterStart_wm, recheckOn_wm, restB_wm,
    M_wm, fl_wm, cq_wm, pq_wm, eq_wm, phase_wm, order_wm, mode_wm, st_wm, parked_wm, now_wm, cyc_wm,
    nextId_wm, started_wm, hs, Mode.closing]
  all_goals (repeat' split) <;> (try rfl) <;> (try simp_all)

/-- Line 4 for the reference. -/
theorem env011_line4 (C : Cfg N T) {s s' : XSt N T} {l : XLbl N T} (hs : s.mode = .draining)
    (hl : sameAsOpen C s l = true) :
    RefExec C s l s' ↔ ∃ s'', RefExec C (withMode .open s) l s'' ∧ s' = withMode .draining s'' := by
  have h1 : s = withMode .draining (withMode .open s) := (withMode_withMode hs _).symm
  have h2 := env011_xstep_draining C (withMode .open s) rfl l (by rwa [sameAsOpen_wm])
  simp only [RefExec]
  conv_lhs => rw [h1, h2]
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [ha]
    rfl

/-- The reference meets the lines of ENV-011. -/
theorem env011_ref (C : Cfg N T) :
    (on (fun s s' => RefExec C s .drain s'), shall (fun s s' =>
      (s.mode = .open ∧ s' = drained s) ∨ (s.mode ≠ .open ∧ s' = s))) ∧
    (∀ p x r, on (fun s s' => s.mode = .draining ∧ RefExec C s (.request p x r) s'),
      shall (fun s s' => r ≠ .accepted ∧ s' = s)) ∧
    (∀ k, while (fun s => s.mode = .draining), never (fun s s' => RefExec C s (.discard k) s')) ∧
    (∀ s l s', s.mode = .draining → sameAsOpen C s l = true →
      (RefExec C s l s' ↔ ∃ s'', RefExec C (withMode .open s) l s'' ∧
        s' = withMode .draining s'')) ∧
    (on (fun s s' => (s.mode = .draining ∧ Live C s) ∧ ∃ c, RefExec C s (.finish c) s'),
      shall (fun s _ => s.phase = .test ∧ Rest C s)) ∧
    (while (fun s => s.mode = .draining ∧ Live C s ∧ s.phase = .test ∧ Rest C s),
      never (fun s s' => ∃ l, RefExec C s l s' ∧ l.outside = false ∧
        (∀ a, l = .snapshot a → s' ≠ s) ∧ ∀ c, l ≠ .finish c)) ∧
    (∀ l, on (fun s s' => (s.mode = .draining ∧ Rest C s) ∧ (waitEffect s l).isSome = true ∧
        RefExec C s l s'),
      shall (fun s s' => waitEffect s l = some s')) := by
  refine ⟨fun s s' h => ?_, fun p x r s s' ⟨hs, h⟩ => ?_, fun k s s' h hs => ?_,
    fun s l s' hs hl => env011_line4 C hs hl, fun s s' ⟨⟨hs, hL⟩, c, h⟩ => ?_,
    fun s s' ⟨l, h, ho, _, hf⟩ ⟨hs, hL, hp, hr⟩ => ?_, fun l s s' ⟨_, hw, h⟩ => ?_⟩
  · obtain ⟨hm, rfl⟩ := drainStep_some h
    exact .inl ⟨hm, rfl⟩
  · obtain ⟨hr, ⟨rfl, -⟩ | h2⟩ := requestStep_some h
    · simp [replyFor, hs] at hr
      split at hr <;> simp at hr
    · exact h2
  · obtain ⟨p, x, rest, -, -, hc, -⟩ := discardStep_some h
    simp [hs, Mode.closing] at hc
  · have hl : liveB C s = true := hL
    cases c with
    | quiescent =>
      obtain ⟨hp, -, hq, -⟩ := xstepW_finishQuiescent h
      simp only [finishQ, Bool.and_eq_true] at hq
      exact ⟨hp, hq.1⟩
    | closed =>
      obtain ⟨-, -, hc, -⟩ := xstepW_finishClosed h
      simp [hs, Mode.closing] at hc
    | terminal =>
      obtain ⟨-, hc, -⟩ := xstepW_finishTerminal h
      simp [hl] at hc
    | stopped =>
      obtain ⟨-, -, hc, -⟩ := xstepW_finishStopped h
      simp [hs] at hc
  · rcases exec040_test_step hp h with h1 | rfl | ⟨c, rfl⟩
    · simp [h1] at ho
    · obtain ⟨-, -, hq, -⟩ := xstepW_begin h
      have hr' : restB C s = true := hr
      simp [finishQ, hr', hs] at hq
    · exact hf c rfl
  · cases l with
    | park tmr =>
      obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
      rfl
    | wake =>
      obtain ⟨-, -, rfl⟩ := wakeStep_some h
      rfl
    | _ => simp [waitEffect] at hw

end Reference

/-- ✓ The reference executor satisfies ENV-011 (`env011_ref`). -/
@[evidence holds ENV_011]
theorem ENV_011_reference {N T : Type} [DecidableEq N] :
    ENV_011 (RefExec (N := N) (T := T)) :=
  fun C => env011_ref C

/-! ### Coverage lemmas (for the consistency theorem) -/

section Coverage

variable {N T : Type} [DecidableEq N]

/-- AC1: the reference offers a drain step from every open state. -/
theorem env011_drain_offered (C : Cfg N T) (s : XSt N T) (hs : s.mode = .open) :
    ∃ s', RefExec C s .drain s' :=
  ⟨drained s, by simp [RefExec, xstep, xstepW, drainStep, hs, drained]⟩

/-- AC5: the reference offers `finish quiescent` at every termination test of a draining
executor with no terminal place marked and at rest. -/
theorem env011_finish_offered (C : Cfg N T) (s : XSt N T) (hs : s.mode = .draining)
    (hL : Live C s) (hp : s.phase = .test) (hr : Rest C s) :
    ∃ s', RefExec C s (.finish .quiescent) s' := by
  have hl : liveB C s = true := hL
  have hr' : restB C s = true := hr
  exact ⟨{ s with phase := .done .quiescent, eq := [] }, by
    simp [RefExec, xstep, xstepW, hp, hl, finishQ, hr', hs]⟩

/-- The ninth shall sentence: the reference offers a wake in every live wait (in particular in
the wait of a draining executor with no terminal place marked and at rest). -/
theorem env011_wake_offered (C : Cfg N T) (s : XSt N T) (hL : Live C s) (hp : s.phase = .await) :
    ∃ s', RefExec C s .wake s' := by
  have hl : liveB C s = true := hL
  exact ⟨{ s with phase := .completions, parked := false }, by
    show wakeStep C s = some _
    simp [wakeStep, hp, hl]⟩

/-- **The coverage conjunct ENV-011 asks of the consistency theorem's `ExecCoversW5`**: a drain is
offered from every open state (AC1); `finish quiescent` is offered at every termination test of a
draining executor with no terminal place marked and at rest (the seventh shall sentence, AC5); a
wake is offered in every wait of such an executor at rest (the ninth shall sentence). Coverage is
never a line of a block; this is the clause for `ExecCovers`. -/
def Env011Covers (E : XRel N T) : Prop :=
  (∀ C s, s.mode = .open → ∃ s', E C s .drain s') ∧
  (∀ C s, s.mode = .draining → Live C s → s.phase = .test → Rest C s →
    ∃ s', E C s (.finish .quiescent) s') ∧
  (∀ C s, s.mode = .draining → Live C s → s.phase = .await → Rest C s → ∃ s', E C s .wake s')

/-- The reference meets ENV-011's coverage conjunct. -/
theorem env011_ref_covers : Env011Covers (RefExec (N := N) (T := T)) :=
  ⟨fun C s hs => env011_drain_offered C s hs,
    fun C s hs hL hp hr => env011_finish_offered C s hs hL hp hr,
    fun C s _ hL hp _ => env011_wake_offered C s hL hp⟩

omit [DecidableEq N] in
/-- Read a decided fact off a state `o`: if the check `p` evaluates to `true`, the state exists. -/
theorem env011_state_of_check {o : Option (XSt N T)} {p : XSt N T → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => simp only [ho, Option.map_some, Option.some.injEq] at h; exact ⟨s, rfl, h⟩

end Coverage

/-! ### Examples

One transition `t : 0 → 1`, Immediate, output `Out.place 1`; validation and the relay check accept
everything. `env011_C` registers place `0` as an environment place, `env011_C0` registers none. -/

/-- The transition `t : 0 → 1`. -/
def env011_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples, with environment places `envs`. -/
def env011_cfg (envs : List Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [env011_t] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := envs, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- Place `0` is an environment place. -/
def env011_C : Cfg Nat Nat := env011_cfg [0]

/-- No environment place. -/
def env011_C0 : Cfg Nat Nat := env011_cfg []

/-- The empty marking. -/
def env011_e0 : QMarking Nat Nat := fun _ => []

/-- The token `7` in place `0`. -/
def env011_m7 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- A caller injects `7` into `0` (accepted, ticket `0`) and drains the executor. -/
def env011_drained : List (XLbl Nat Nat) := [.request 0 7 .accepted, .drain]

/-- Up to step 2 of the first cycle: draining, the event `7` still queued. -/
def env011_events : List (XLbl Nat Nat) := env011_drained ++ [.endCompletions, .endPublications]

/-- The queued `7` is injected while draining and `t` starts (firing `1`): its action runs. -/
def env011_fired : List (XLbl Nat Nat) :=
  env011_events ++ [.inject 0, .endEvents, .update, .deadline [], .begin, .start "t" false, .endPass]

/-- The next termination test while `t`'s action is still running. -/
def env011_testInFlight : List (XLbl Nat Nat) :=
  env011_fired ++ [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- A request while draining is refused; `t`'s action writes `70` to `1` and returns; its
completion is admitted while draining; the next termination test finds the executor at rest. -/
def env011_toRest : List (XLbl Nat Nat) :=
  env011_fired ++ [.request 0 8 .refused, .write 1 1 70, .ret 1 true, .commit 1, .endCompletions,
    .endPublications, .endEvents, .update, .deadline []]

/-- Without environment places: drained at once, `t` fires on the token `7` (firing `0`), and the
next termination test finds the executor at rest. -/
def env011_toRest0 : List (XLbl Nat Nat) :=
  [.drain, .endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
    .start "t" false, .endPass, .ret 0 true, .commit 0, .endCompletions, .endPublications,
    .endEvents, .update, .deadline []]

/-- The open executor with nothing queued (place `0` an environment place) reaches its wait at
rest: the termination test begins an empty pass, since an open executor with environment places
waits at rest ([ENV-010]). -/
def env011_toAwait : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass]

/-- The open executor parks in its wait at rest. -/
def env011_toPark : List (XLbl Nat Nat) := env011_toAwait ++ [.park none]

/-- The open executor in its wait at rest is drained before it parks. -/
def env011_toWait : List (XLbl Nat Nat) := env011_toAwait ++ [.drain]

/-- The drained executor then parks in its wait at rest. -/
def env011_toHang : List (XLbl Nat Nat) := env011_toWait ++ [.park none]

/-! ### Violation: a drain that drops the queued events -/

/-- An executor whose drain also drops the queued events (a drain treated as a close for the
event queue); otherwise the reference. -/
def env011_drainDropsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => (xstep C s .drain).map fun s' => { s' with eq := [] }
  | l => xstep C s l

/-- The executor of `env011_drainDropsStep`. -/
def env011_drainDrops {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_drainDropsStep C s l = some s'

/-- ✗ A drain that drops the queued events violates ENV-011 (line 1): the event `7` is queued when
the open executor is drained, and the drain empties the queue. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_drainDrops : ¬ ENV_011 (env011_drainDrops (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_drainDropsStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) [.request 0 7 .accepted]) (l := .drain)
    (p := fun s s' => decide (s.mode = .open) && s'.eq.length != s.eq.length) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  rcases (h env011_C).1 s s' hs with ⟨-, rfl⟩ | ⟨hm, -⟩
  · exact hp.2 rfl
  · exact hm hp.1

/-! ### Violation: an injection accepted while draining -/

/-- An executor that answers a request while draining as an open one would; otherwise the
reference. -/
def env011_acceptStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if s.mode = .draining then (xstep C (withMode .open s) (.request p x r)).map (withMode .draining)
    else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `env011_acceptStep`. -/
def env011_accept {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_acceptStep C s l = some s'

/-- ✗ Accepting an injection while draining violates ENV-011 (line 2, AC2): after the drain the
request of `8` into `0` is accepted. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_acceptWhileDraining :
    ¬ ENV_011 (env011_accept (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_acceptStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_drained) (l := .request 0 8 .accepted)
    (p := fun s _ => decide (s.mode = .draining)) (by decide)
  exact ((h env011_C).2.1 0 8 .accepted s s' ⟨by simpa using hp, hs⟩).1 rfl

/-! ### Violation: queued events discarded while draining -/

/-- An executor that discards queued events in every mode (a drain read as a close); otherwise
the reference. -/
def env011_discardStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .discard k => (discardStep C (withMode .closed s) k).map (withMode s.mode)
  | l => xstep C s l

/-- The executor of `env011_discardStep`. -/
def env011_discard {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_discardStep C s l = some s'

/-- ✗ Discarding a queued event while draining violates ENV-011 (line 3, AC3): the event `7`,
accepted before the drain, is discarded in step 2. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_discardWhileDraining :
    ¬ ENV_011 (env011_discard (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_discardStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_events) (l := .discard 0)
    (p := fun s _ => decide (s.mode = .draining)) (by decide)
  exact (h env011_C).2.2.1 0 s s' hs (by simpa using hp)

/-! ### Violation: queued events left unprocessed while draining -/

/-- An executor that stops injecting once drained; otherwise the reference. -/
def env011_stallStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k => if s.mode = .draining then none else xstep C s (.inject k)
  | l => xstep C s l

/-- The executor of `env011_stallStep`. -/
def env011_stall {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_stallStep C s l = some s'

/-- ✗ Not injecting the queued events while draining violates ENV-011 (line 4, AC3, "processed
normally"): in step 2 after the drain the open executor injects the queued `7`, the draining one
does not. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_stallEvents : ¬ ENV_011 (env011_stall (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, -, hp⟩ := env011_state_of_check (o := xrun env011_C (xinit env011_e0 0) env011_events)
    (p := fun s => decide (s.mode = .draining) && (xstep env011_C (withMode .open s) (.inject 0)).isSome)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hp
  obtain ⟨hm, s'', h''⟩ := hp
  have hR : env011_stall env011_C (withMode .open s) (.inject 0) s'' := by
    simpa [env011_stall, env011_stallStep, withMode] using h''
  have := ((h env011_C).2.2.2.1 s (.inject 0) (withMode .draining s'') hm rfl).2 ⟨s'', hR, rfl⟩
  simp [env011_stall, env011_stallStep, hm] at this

/-! ### Violation: terminating with an action in flight -/

/-- An executor whose quiescence test ignores the firings in flight, in every mode; otherwise the
reference. -/
def env011_inFlightStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    (xstep C { s with fl := [] } (.finish .quiescent)).map fun s' => { s' with fl := s.fl }
  | l => xstep C s l

/-- The executor of `env011_inFlightStep`. -/
def env011_inFlight {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_inFlightStep C s l = some s'

/-- ✗ Terminating with an action in flight violates ENV-011 (line 5, AC4): after the drain `t`'s
action is still running at the next termination test, nothing else is armed or queued, and the
executor terminates. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_finishInFlight : ¬ ENV_011 (env011_inFlight (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_inFlightStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_testInFlight) (l := .finish .quiescent)
    (p := fun s _ => decide (s.mode = .draining) && liveB env011_C s && !restB env011_C s)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  have := (h env011_C).2.2.2.2.1 s s' ⟨⟨hp.1.1, hp.1.2⟩, .quiescent, hs⟩
  have h5 : restB env011_C s = true := this.2
  simp [hp.2] at h5

/-! ### Violation: a draining executor that keeps running at quiescence -/

/-- An executor whose termination test treats a draining executor as an open one (with
environment places it then waits at quiescence, and begins a pass); otherwise the reference. -/
def env011_neverEndsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin =>
    if s.mode = .draining then (xstep C (withMode .open s) .begin).map (withMode .draining)
    else xstep C s .begin
  | .finish .quiescent =>
    if s.mode = .draining then
      (xstep C (withMode .open s) (.finish .quiescent)).map (withMode .draining)
    else xstep C s (.finish .quiescent)
  | l => xstep C s l

/-- The executor of `env011_neverEndsStep`. -/
def env011_neverEnds {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_neverEndsStep C s l = some s'

/-- ✗ Not terminating at quiescence after a drain violates ENV-011 (line 6, AC5): the drained
executor reaches a termination test at rest and begins a firing pass instead of terminating. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_neverEnds : ¬ ENV_011 (env011_neverEnds (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_neverEndsStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_toRest) (l := .begin)
    (p := fun s _ => decide (s.mode = .draining) && liveB env011_C s &&
      decide (s.phase = .test) && restB env011_C s)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact (h env011_C).2.2.2.2.2.1 s s' ⟨.begin, hs, rfl, (fun _ hc => nomatch hc), fun c hc => nomatch hc⟩
    ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-! ### Violation: a drain that leaves a parked wait asleep -/

/-- An executor whose drain does not wake a parked wait; otherwise the reference. -/
def env011_keepParkedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => (xstep C s .drain).map fun s' => { s' with parked := s.parked }
  | l => xstep C s l

/-- The executor of `env011_keepParkedStep`. -/
def env011_keepParked {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_keepParkedStep C s l = some s'

/-- ✗ A drain that leaves a parked wait asleep violates ENV-011 (line 1, "apart from waking its
wait"): the open executor parked in its wait at rest is drained and stays parked. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_drainKeepsParked :
    ¬ ENV_011 (env011_keepParked (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_keepParkedStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_toPark) (l := .drain)
    (p := fun s s' => decide (s.mode = .open) && s'.parked) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rcases (h env011_C).1 s s' hs with ⟨-, rfl⟩ | ⟨hm, -⟩
  · simp [drained] at hp
  · exact hm hp.1

/-! ### Violation: a drain that reopens a closed executor -/

/-- An executor whose drain of a closed executor puts it into the draining mode; otherwise the
reference. -/
def env011_reopenStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => if s.mode = .closed then some (drained s) else xstep C s .drain
  | l => xstep C s l

/-- The executor of `env011_reopenStep`. -/
def env011_reopen {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_reopenStep C s l = some s'

/-- ✗ A drain that reopens a closed executor violates ENV-011 (line 1, a drain of an executor
that is not open changes nothing): the closed executor is drained and leaves the closed mode. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_reopenClosed : ¬ ENV_011 (env011_reopen (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_reopenStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) [.close]) (l := .drain)
    (p := fun s s' => decide (s.mode = .closed) && decide (s'.mode = .draining)) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rcases (h env011_C).1 s s' hs with ⟨hm, -⟩ | ⟨-, rfl⟩
  · rw [hp.1] at hm; cases hm
  · rw [hp.1] at hp; cases hp.2

/-! ### Violation: a refused injection queued anyway while draining -/

/-- An executor that answers a request while draining as the reference does (refused) and queues
the event all the same; otherwise the reference. -/
def env011_queueRefusedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if s.mode = .draining then
      (xstep C s (.request p x r)).map fun s' =>
        { s' with eq := s'.eq ++ [(s'.nextId, p, x)], nextId := s'.nextId + 1 }
    else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `env011_queueRefusedStep`. -/
def env011_queueRefused {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_queueRefusedStep C s l = some s'

/-- ✗ Queuing a refused injection while draining violates ENV-011 (line 2, "and shall change
nothing"): after the drain the request of `8` into `0` is answered refused and `8` is queued. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_queueRefused : ¬ ENV_011 (env011_queueRefused (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_queueRefusedStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_drained) (l := .request 0 8 .refused)
    (p := fun s s' => decide (s.mode = .draining) && s'.eq.length != s.eq.length) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨-, rfl⟩ := (h env011_C).2.1 0 8 .refused s s' ⟨hp.1, hs⟩
  exact hp.2 rfl

/-! ### Violation: terminating from the wait -/

/-- An executor that ends a draining run from its wait at quiescence, without going round to the
termination test of a cycle; otherwise the reference. -/
def env011_finishInWaitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.mode = .draining ∧ s.phase = .await ∧ restB C s = true ∧ liveB C s = true then
      some { s with phase := .done .quiescent, eq := [] }
    else xstep C s (.finish .quiescent)
  | l => xstep C s l

/-- The executor of `env011_finishInWaitStep`. -/
def env011_finishInWait {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_finishInWaitStep C s l = some s'

/-- ✗ Terminating from the wait violates ENV-011 (line 5, "except at the termination test of a
cycle"): the open executor in its wait at rest is drained and terminates there. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_finishInWait : ¬ ENV_011 (env011_finishInWait (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_finishInWaitStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_toWait) (l := .finish .quiescent)
    (p := fun s _ => decide (s.mode = .draining) && liveB env011_C s && decide (s.phase = .await))
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := ((h env011_C).2.2.2.2.1 s s' ⟨⟨hp.1.1, hp.1.2⟩, .quiescent, hs⟩).1
  rw [hp.2] at this; cases this

/-! ### Violation: a drained wait at quiescence that skips the cycle -/

/-- An executor whose wait, when it is draining and at rest, ends straight at the termination
test, past steps 1 to 4 of the cycle (the enablement update among them); otherwise the
reference. -/
def env011_wakeSkipsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .wake =>
    if s.mode = .draining ∧ restB C s = true then
      (xstep C s .wake).map fun s' => { s' with phase := .test }
    else xstep C s .wake
  | l => xstep C s l

/-- The executor of `env011_wakeSkipsStep`. -/
def env011_wakeSkips {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_wakeSkipsStep C s l = some s'

/-- ✗ A drained wait at quiescence that skips the cycle violates ENV-011 (line 7, "ending the
wait shall take it to the first step of the next cycle"): the open executor in its wait at rest
is drained and its wake lands on the termination test. -/
@[evidence forbids ENV_011]
theorem ENV_011_forbids_wakeSkipsCycle : ¬ ENV_011 (env011_wakeSkips (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_wakeSkipsStep (C := env011_C)
    (o := xrun env011_C (xinit env011_e0 0) env011_toWait) (l := .wake)
    (p := fun s s' => decide (s.mode = .draining) && restB env011_C s && decide (s'.phase = .test))
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h env011_C).2.2.2.2.2.2 .wake s s' ⟨⟨hp.1.1, hp.1.2⟩, rfl, hs⟩
  simp only [waitEffect, Option.some.injEq] at this
  rw [← this] at hp
  cases hp.2

/-! ### Accepted by the lines, refused by coverage: an edge-triggered wait -/

/-- The guard of an edge-triggered wait: a parked loop with no timing boundary ahead does not
wake; only an arrival, which clears the parked flag, lets it out. -/
def env011_lostWakeGuard {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Bool
  | .wake => s.parked && (nextBoundary C s).isNone
  | _ => false

/-- An executor with an edge-triggered wait (the hazard TypeScript's latched wake guards against,
the `wakeUpPending` field of `bitmap-net-executor.ts`): the reference, except that a parked loop with no timer does
not wake. A drain raised before the loop parks is lost: the park that follows sets the flag
again. -/
def env011_lostWakeStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (l : XLbl N T) : Option (XSt N T) :=
  if env011_lostWakeGuard C s l then none else xstep C s l

/-- The executor of `env011_lostWakeStep`. -/
def env011_lostWake {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_lostWakeStep C s l = some s'

section LostWake

variable {N T : Type} [DecidableEq N]

theorem env011_lostWake_iff {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} :
    env011_lostWake C s l s' ↔ env011_lostWakeGuard C s l = false ∧ RefExec C s l s' := by
  unfold env011_lostWake env011_lostWakeStep RefExec
  by_cases hg : env011_lostWakeGuard C s l = true
  · simp [hg]
  · simp only [Bool.not_eq_true] at hg
    simp [hg]

theorem env011_lostWake_sub {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : env011_lostWake C s l s') : RefExec C s l s' := (env011_lostWake_iff.mp h).2

theorem env011_lostWakeGuard_wm {C : Cfg N T} {s : XSt N T} {m : Mode} {l : XLbl N T} :
    env011_lostWakeGuard C (withMode m s) l = env011_lostWakeGuard C s l := by
  cases l <;> rfl

end LostWake

/-- The edge-triggered wait meets every line of ENV-011: its steps are reference steps, and its
guard does not read the mode, so a draining and an open executor lose the same wakes (line 4). -/
theorem env011_lostWake_meets : ENV_011 (env011_lostWake (N := Nat) (T := Nat)) := by
  intro C
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := env011_ref C
  refine ⟨fun s s' h => h1 s s' (env011_lostWake_sub h),
    fun p x r s s' ⟨hs, h⟩ => h2 p x r s s' ⟨hs, env011_lostWake_sub h⟩,
    fun k s s' h hs => h3 k s s' (env011_lostWake_sub h) hs,
    fun s l s' hs hl => ?_,
    fun s s' ⟨hL, c, h⟩ => h5 s s' ⟨hL, c, env011_lostWake_sub h⟩,
    fun s s' ⟨l, h, ho, hn, hf⟩ hw => h6 s s' ⟨l, env011_lostWake_sub h, ho, hn, hf⟩ hw,
    fun l s s' ⟨hd, hw, h⟩ => h7 l s s' ⟨hd, hw, env011_lostWake_sub h⟩⟩
  simp only [env011_lostWake_iff, env011_lostWakeGuard_wm, env011_line4 C hs hl]
  constructor
  · rintro ⟨hg, s'', h, rfl⟩
    exact ⟨s'', ⟨hg, h⟩, rfl⟩
  · rintro ⟨s'', ⟨hg, h⟩, rfl⟩
    exact ⟨hg, s'', h, rfl⟩

/-- The edge-triggered wait fails ENV-011's coverage conjunct: the open executor in its wait at
rest is drained before it parks, then parks; it is draining, live and at rest in its wait with no
timing boundary ahead, and no wake is offered, so it never reaches the termination test that
would end the run. -/
theorem env011_lostWake_not_covered : ¬ Env011Covers (env011_lostWake (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, -, hp⟩ := env011_state_of_check
    (o := xrun env011_C (xinit env011_e0 0) env011_toHang)
    (p := fun s => decide (s.mode = .draining) && liveB env011_C s && decide (s.phase = .await) &&
      restB env011_C s && (env011_lostWakeStep env011_C s .wake).isNone) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hp
  obtain ⟨s', hs'⟩ := h.2.2 env011_C s hp.1.1.1.1 hp.1.1.1.2 hp.1.1.2 hp.1.2
  have h' : env011_lostWakeStep env011_C s .wake = some s' := hs'
  rw [hp.2] at h'
  cases h'

/-! ### Mutant reading: "`drain()` is a no-op" without environment places (ruling D20) -/

/-- The literal reading of the markdown's former sentence "For executors without environment
places, `drain()` is a no-op": without environment places a drain step changes nothing. -/
def ENV_011_mutant_noop {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ C, C.envs = [] → on (fun s s' => R C s .drain s'), shall (fun s s' => s' = s)

/-- An executor that ignores the drain of an executor without environment places; otherwise the
reference. -/
def env011_noopStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .drain => if C.envs.isEmpty then (if s.mode = .open then some s else none) else xstep C s .drain
  | l => xstep C s l

/-- The executor of `env011_noopStep`. -/
def env011_noop {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env011_noopStep C s l = some s'

/-- The literal no-op reading and ENV-011 are told apart: the executor that ignores the drain
of an executor without environment places meets the literal reading and breaks line 1 (the drain
of the open executor leaves it open). The reworded sentence (ruling D20, clash env-b#6) is what
every runtime does: after a drain, `snapshot()` is rejected whatever the net ([ENV-014] AC4). -/
@[evidence mutant ENV_011]
theorem ENV_011_mutant_noop_killed :
    ENV_011_mutant_noop (env011_noop (N := Nat) (T := Nat)) ∧
      ¬ ENV_011 (env011_noop (N := Nat) (T := Nat)) := by
  refine ⟨fun C hE s s' h => ?_, fun h => ?_⟩
  · simp only [env011_noop, env011_noopStep, hE, List.isEmpty_nil, if_true] at h
    split at h
    · exact (Option.some.inj h).symm
    · simp at h
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check env011_noopStep (C := env011_C0)
      (o := some (xinit env011_m7 0)) (l := .drain)
      (p := fun s s' => decide (s.mode = .open) && decide (s'.mode = .open)) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases (h env011_C0).1 s s' hs with ⟨-, rfl⟩ | ⟨hm, -⟩
    · simp [drained] at hp
    · exact hm hp.1

/-! ### Every line exercised -/

/-- Every line of ENV-011 is exercised by the reference, on the test derivation's run (place `0`
an environment place): an open executor with the event `7` queued is drained and keeps it
(line 1); a request of `8` while draining is refused (line 2, AC2); the queued `7` is injected
while draining (lines 3 and 4, AC3); `t`'s action writes `70` and its completion is admitted while
draining (line 4, AC4); the drained executor terminates at the next termination test at rest, with
`70` in `1` (lines 5 and 6, AC5). Without environment places, a drained executor terminates at the
same test as the open one (line 4, the no-op sentence). An open executor drained in its wait at
rest ends the wait and goes back to step 1 (line 7). -/
@[evidence nonvacuous ENV_011]
theorem ENV_011_nonvacuous :
    (∃ s s', RefExec env011_C s .wake s' ∧ s.mode = .draining ∧ Rest env011_C s ∧
      s'.phase = .completions) ∧
    (∃ s s', RefExec env011_C s .drain s' ∧ s.mode = .open ∧ s'.eq.length = 1) ∧
    (∃ s s', RefExec env011_C s (.request 0 8 .refused) s' ∧ s.mode = .draining) ∧
    (∃ s s', RefExec env011_C s (.inject 0) s' ∧ s.mode = .draining ∧ s'.M 0 = [7]) ∧
    (∃ s s', RefExec env011_C s (.commit 1) s' ∧ s.mode = .draining ∧ s'.M 1 = [70]) ∧
    (∃ s s', RefExec env011_C s (.finish .quiescent) s' ∧ s.mode = .draining ∧
      Live env011_C s ∧ s.phase = .test ∧ Rest env011_C s ∧ s'.M 1 = [70]) ∧
    (∃ s s', RefExec env011_C0 s (.finish .quiescent) s' ∧ s.mode = .draining ∧
      ∃ s'', RefExec env011_C0 (withMode .open s) (.finish .quiescent) s'') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0) env011_toWait) (l := .wake)
      (p := fun s s' => decide (s.mode = .draining) && restB env011_C s &&
        decide (s'.phase = .completions)) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0) [.request 0 7 .accepted]) (l := .drain)
      (p := fun s s' => decide (s.mode = .open) && s'.eq.length == 1) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0) env011_fired) (l := .request 0 8 .refused)
      (p := fun s _ => decide (s.mode = .draining)) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0) env011_events) (l := .inject 0)
      (p := fun s s' => decide (s.mode = .draining) && s'.M 0 == [7]) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0)
        (env011_fired ++ [.request 0 8 .refused, .write 1 1 70, .ret 1 true]))
      (l := .commit 1)
      (p := fun s s' => decide (s.mode = .draining) && s'.M 1 == [70]) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C)
      (o := xrun env011_C (xinit env011_e0 0) env011_toRest) (l := .finish .quiescent)
      (p := fun s s' => decide (s.mode = .draining) && liveB env011_C s &&
        decide (s.phase = .test) && restB env011_C s && s'.M 1 == [70]) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env011_C0)
      (o := xrun env011_C0 (xinit env011_m7 0) env011_toRest0) (l := .finish .quiescent)
      (p := fun s _ => decide (s.mode = .draining) &&
        (xstep env011_C0 (withMode .open s) (.finish .quiescent)).isSome) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hp
    exact ⟨s, s', hs, hp⟩

end Libpetri.Spec
