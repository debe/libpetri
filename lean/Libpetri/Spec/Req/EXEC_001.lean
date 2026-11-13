import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Enablement
import Libpetri.Spec.Text.EXEC_001

set_option linter.missingDocs true

/-!
# EXEC-001: Orchestrator loop steps (`spec/04-execution-model.md`)

The order of the orchestrator loop, over the executor model (`RefExec`, `Reference/Exec.lean`).
The block states the partial order every runtime keeps (rulings D70 (a) and D13 (a)), not a
strict order of labels per cycle: Rust's wait processes the completion, publication or event
that ends it, and a synchronous firing may be admitted inside its own pass. Lines 1 to 7 are
trace forms `after T, until G, never B` (glossary `Ears.lean`) read on the steps of a run, and
line 8 is a step form `on R, shall Q` read on the update steps of the executor:

* a cycle that begins, or a deposit made outside a firing pass, is followed by an enablement
  update before any deadline step (line 1) and by a deadline step before any start (line 2);
* a cycle that begins ends step 2 before its enablement update (line 3);
* the finished actions queued when a cycle begins or step 1 is entered are processed before any
  publication, injection or start (line 4);
* the external events queued when step 2 begins, the executor neither closed nor stopped, are
  injected or discarded before the next enablement update (line 5);
* a transition the deadline step reaps does not start before the next enablement update
  (line 6);
* the loop does not wait while a deposit, or a consuming start, since the last enablement update
  is unprocessed (line 7, step 6 under ruling D13 (a));
* the enablement update leaves every transition whose enablement check passes armed or reaped,
  unless it may not start again while in flight, and every other one without a clock (line 8,
  step 3).

The evidence: the reference executor satisfies every line from every state (`EXEC_001_reference`,
through one invariant per trace line, `Exec001.aun_of_inv`); one decided mutant run per line
violates it, and lines 1 and 7 have a second one for their second trigger; five decided reference
runs exercise every trigger and every banned step of the lines, and every release a line names.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The steps the lines read -/

namespace Exec001

variable {N T : Type}

/-- The label deposits tokens: a commit, a timeout deposit, a publication or an injection. -/
def depositLabel : XLbl N T → Bool
  | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

/-- The step deposits tokens outside a firing pass: a deposit label taken in any phase other
than the firing pass (step 1, step 1b, step 2, or the wait of step 6). -/
def depositOutsidePass (e : XStep N T) : Bool := depositLabel e.2.1 && e.1.phase != .pass

/-- The step deposits tokens inside a firing pass that has started a transition (a synchronous
completion admitted inside its own pass, after its start). -/
def depositInPass (e : XStep N T) : Bool :=
  depositLabel e.2.1 && e.1.phase == .pass && e.1.started

/-- The step is a deadline step (step 4). -/
def isDeadline (e : XStep N T) : Bool :=
  match e.2.1 with
  | .deadline _ => true
  | _ => false

/-- The step parks the loop: it waits for work (step 6). -/
def isPark (e : XStep N T) : Bool :=
  match e.2.1 with
  | .park _ => true
  | _ => false

/-- The step ends step 2. -/
def isEndEvents (e : XStep N T) : Bool :=
  match e.2.1 with
  | .endEvents => true
  | _ => false

/-- The step starts the transition named `n`. -/
def startsName (n : String) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .start m _ => m == n
  | _ => false

/-- The step is a deadline step that reaps the transition named `n`. -/
def reapsName (n : String) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .deadline ns => ns.contains n
  | _ => false

/-- The step begins a cycle: it leaves the firing pass or the wait for a running phase that is
neither (in the order of the step list, step 1). -/
def beginsCycle (e : XStep N T) : Bool :=
  (e.1.phase == .pass || e.1.phase == .await) && e.2.2.phase != .pass &&
    e.2.2.phase != .await && isExecPhase e.2.2.phase

/-- The step begins a cycle or deposits tokens outside a firing pass: the triggers of lines 1
and 2. -/
def opensCycle (e : XStep N T) : Bool := beginsCycle e || depositOutsidePass e

/-- The step enters step 1 (phase `completions`) with the finished firing `i` in the completion
queue. -/
def entersStep1With (i : Nat) (e : XStep N T) : Bool :=
  e.2.2.phase == .completions && e.1.phase != .completions && e.2.2.cq.contains i

/-- The step begins a cycle or enters step 1, with the finished firing `i` in the completion
queue. -/
def queuedAtStep1 (i : Nat) (e : XStep N T) : Bool :=
  entersStep1With i e || (beginsCycle e && e.2.2.cq.contains i)

/-- The step processes the finished firing `i`: a commit, a fail or a timeout deposit of `i`. -/
def settlesFiring (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .commit j | .fail j | .tdeposit j => j == i
  | _ => false

/-- The step goes past step 1: it deposits a publication (step 1b), injects an external event
(step 2) or starts a transition (step 5). -/
def passesStep1 (e : XStep N T) : Bool :=
  match e.2.1 with
  | .publish _ | .inject _ | .start _ _ => true
  | _ => false

/-- The step enters step 2 (phase `events`) of an executor that is neither closed nor stopped
(mode open or draining), with the event of ticket `k` in the event queue. -/
def entersStep2With (k : Nat) (e : XStep N T) : Bool :=
  e.2.2.phase == .events && e.1.phase != .events && !e.2.2.mode.closing &&
    (e.2.2.eq.map Prod.fst).contains k

/-- The step takes the event of ticket `k` off the queue: it injects or discards it, or an
immediate termination ([ENV-015]) discards the whole queue. -/
def dequeuesEvent (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j | .discard j => j == k
  | .terminateNow => true
  | _ => false

/-- `t` has an input arc or a reset arc: its start consumes or clears tokens. -/
def consumes (t : Trans N) : Bool := !(t.core.inputs.isEmpty && t.core.resets.isEmpty)

/-- The step starts a transition of the net (found by name, ruling D10) with an input or reset
arc. -/
def startsConsuming (C : Cfg N T) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .start n _ => (findT C n).any consumes
  | _ => false

/-- The step writes the marking in a way the next enablement update must see: a deposit outside
a firing pass, a deposit inside a pass that has started a transition, or the start of a
transition of the net with an input or reset arc. -/
def writesMarking (C : Cfg N T) (e : XStep N T) : Bool :=
  depositOutsidePass e || depositInPass e || startsConsuming C e

/-- The state an enablement update leaves is exact (step 3): every transition of the net (found
by name, ruling D10) that is enabled at the marking is armed or reaped, unless the executor is
not re-entrant and a firing of it is in flight; every transition that is not enabled holds no
clock. -/
def UpdateExact (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ n u, findT C n = some u →
    (enabledNA (qCount s.M) u.core = true → (C.reentrant = true ∨ ¬ InFlight s n) →
      ArmedE s u ∨ ReapedE s u) ∧
    (enabledNA (qCount s.M) u.core = false → stampOf (s.st n) = none)

end Exec001

open Exec001

/-! ## EXEC-001: Orchestrator Loop Steps -/

requirement EXEC_001
  id "EXEC-001"
  title "Orchestrator Loop Steps"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_001.s1, EXEC_001.s2, EXEC_001.s3, EXEC_001.s4, EXEC_001.s5, EXEC_001.s6, EXEC_001.s7,
        EXEC_001.s8
  reading "For every executor R and every configuration C, every run of R under C from any state satisfies lines 1 to 7, and every update step of R under C satisfies line 8:"
          "after each step that begins a cycle (leaves the firing pass or the wait for a running phase that is neither) or deposits tokens outside a firing pass (a commit, a timeout deposit, a publication or an injection taken in a phase other than the firing pass), no deadline step happens before the next enablement update;"
          "after each such step, no start happens before the next deadline step;"
          "after each step that begins a cycle, no enablement update happens before the next end of step 2;"
          "for every firing identity i: after each step that begins a cycle or enters step 1 with i in the completion queue, no publication, injection or start happens before a commit, a fail or a timeout deposit of i;"
          "for every ticket k: after each step that enters step 2 of an executor that is neither closed nor stopped, with the event of ticket k in the event queue, no enablement update happens before that event is injected or discarded, or an immediate termination discards the queue;"
          "for every transition name n: after each deadline step that reaps n, no start of n happens before the next enablement update;"
          "after each deposit outside a firing pass, each deposit inside a firing pass that has started a transition, and each start of a transition of the net that has an input or reset arc, no park step happens before the next enablement update;"
          "every update step from s to s' leaves, for every name n and the transition u the net holds under n, u armed or reaped in s' if its enablement check passes at the marking of s' (u is enabled there) and the executor is re-entrant or no firing of n is in flight, and n without a stamp if its enablement check fails (u is not enabled)."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A run (XRun) is a list of consecutive steps (source, label, target) of R, from any state, so every trace line also holds of a run observed from the middle. The labels are the steps of EXEC-001: step 1 settles finished firings (commit, fail, tdeposit) and ends with endCompletions; step 1b deposits mid-action publications (publish, Rust and Python, the markdown sentence 'Between steps 1 and 2'); step 2 injects or discards queued external events (inject, discard) and ends with endEvents; step 3 is update; step 4 is deadline ns, which reaps exactly the names ns; the termination test is finish or begin; step 5 is start, lose and endPass; step 6 is park (the loop blocks) and wake. The loop phase of the state says which step the loop is in, and each phase is entered by the step that ends the one before, so 'enters step 1' is a step whose target is in phase completions and whose source is not, and 'begins a cycle' is a step whose source is the pass or the wait and whose target is a running phase that is neither. The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor."
          "Every line is a prohibition or, for line 8, a condition on the state an update leaves: nothing here obliges a step to happen. That the loop goes on (the wait wakes on each arrival, a run ends only on its termination test) is CONC-010's and EXEC-040's subject, and a run with no trigger is unconstrained by lines 1 to 7."
          "Transition names are taken to be pairwise distinct (ruling D10, Cfg.WF.names, which the statement does not assume): lines 6 to 8 work on names, and lines 7 and 8 judge the transition the net holds under the name (findT, the first one with that name). On a net with distinct names this is the transition the start label started; the clock status is kept per name in every runtime."
          "Ruling D70 (a): the steps run in order, but the wait may itself process the completion, publication or event that ends it (Rust settles, publishes or injects in phase await and then runs step 1), and a synchronous firing may be admitted inside its own pass. The block therefore states the partial order every runtime keeps and no strict order of labels per cycle (R-EXEC-9). The literal acceptance criterion 'No transition fires before completions are processed' is false of Rust read over an admission inside the pass: Rust keeps starting the pass after an inline commit of a synchronous firing (executor_core/executor.rs, the firing loop of Phase 5), the decided run runPass of the design spike. The deposit trigger of lines 1 and 2 reads it 'since the last deposit made outside a firing pass' (design NR-3), which every runtime keeps. A synchronous deposit inside the pass is invisible to the rest of the pass, which is EXEC-003's subject."
          "The first two EARS sentences are lines 1 and 2: after a cycle begins or a deposit is made outside a pass, a deadline step needs an update first (line 1) and a start needs a deadline step first (line 2), so the update, then the deadline step, then the starts. An executor that skips the update after step 2 and reaps on stale statuses breaks line 1 (EXEC_001_forbids_skipUpdate), and so does one whose wait jumps to the deadline step (EXEC_001_forbids_wakeToDeadline); one whose pass may begin before the deadline step (fire before reap, the run clash013_refresh_rescue of ClashesTime lifts to it) breaks line 2 (EXEC_001_forbids_fireBeforeReap)."
          "The third EARS sentence is line 3: a cycle that begins ends step 2 (endEvents) before its update, so no cycle skips steps 1, 1b and 2. A timer wake that goes straight back to the enablement update (the fast path a Java or TypeScript loop takes if it continues to updateDirtyTransitions when awaitWork returns on its timer, or Rust's Phase 6 timer arm jumping to Phase 3) breaks it (EXEC_001_forbids_wakeToUpdate)."
          "The fourth EARS sentence is line 4, the reading of AC2's first clause and of AC1's first clause: the finished firings queued when a cycle begins or step 1 is entered are processed (committed, failed or their timeout outcome deposited, EXEC-020, EXEC-021, EXEC-022, EXEC-030) before any publication, injection or start, so step 1 comes before steps 1b and 2 and before the pass. The cycle trigger catches an executor that skips step 1; the step 1 trigger one that enters it from elsewhere. A firing that finishes later, while step 1 runs, is a new item; the reference processes it too, as Rust drains its completion channel, but the line does not ask for it. A run that ends step 1 with a firing still queued and then starts a transition breaks the line (EXEC_001_forbids_endWithQueued)."
          "The fifth EARS sentence is line 5, the phase-entry reading of AC3's first sentence: an event queued when step 2 begins, with the executor neither closed nor stopped (mode open or draining, Mode.closing false), is injected (ENV-003) or, when a close comes before its injection, discarded (ENV-013), before the next update. An immediate termination (ENV-015, Java) discards the whole queue at once (the label terminateNow), which releases the line as a discard does. An update that runs with an event still queued, the executor open, breaks the line (EXEC_001_forbids_updateBeforeInject). A step 2 entered while the executor is already closed or stopped does not trigger the line, which is AC3's second sentence: Java and TypeScript then return from step 2 at once and leave the queued events in the queue (BitmapNetExecutor.java processExternalEvents, 'if (closed.get()) return', and the same test in PrecompiledNetExecutor.java; bitmap-net-executor.ts and precompiled-net-executor.ts processExternalEvents), they go on running enablement updates while an action is in flight (shouldTerminate waits for the firings in flight), and they discard the events when the loop ends (drainPendingExternalEvents in the finally block of the Java loop, after the loop in TypeScript). That every event still queued at a close is discarded, at the latest when the loop ends, is ENV-013's line, not this block's. The reference discards them in step 2 (discardStep), which the line allows as well. The decided run exec001_closedStep2_run shows a step 2 of that kind: a request is accepted, a caller closes the executor, step 2 ends with the event queued and the update follows; line 5 holds on it, and the reading without the closed exemption fails on it. Once step 2 has begun with the executor open, a close that comes during it leaves the line in force: Java and TypeScript test the close only on entry to step 2 and inject the rest of the queue, and the reference discards it."
          "The sixth EARS sentence is line 6, the reading of AC4. With the reference ready order a transition that is expired at the cycle reading is not Ready (glossary: Ready, the wording of step 5), so it is not in the order of that pass; the line is what stops a deadline step that only reports the reap and keeps the clock, so that the transition stays armed and an order that tests only the earliest bound would start it in the same cycle: EXEC_001_forbids_reapWithoutDisarm. When a reaped transition may be armed again (only after a write of one of its arc places, ruling D6) is TIME-013's companion line, not this block."
          "The seventh EARS sentence is line 7, the reading of AC5 and of step 6 under ruling D13 (a): the loop may wait while actions are in flight, but not while a deposit or a consuming start since the last update is unprocessed. Rust runs another cycle after any start and after any dirty bit (fired_any or has_dirty_bits), Java and TypeScript after any dirty bit (hasDirtyBits), and all mark dirty the places a firing consumes from and the places a deposit writes. The start trigger is restricted to transitions with an input or reset arc (a reset arc on an empty place counts, as its start is a write): after a pass whose starts consume nothing, Java and TypeScript may wait at once and Rust runs one more cycle first; no marking, status or event tells the two apart, and both are allowed. A deposit inside a pass counts when the pass has started a transition, which every synchronous deposit inside its own pass does (it follows the start of its firing); the state of an arbitrary executor may hold a firing that is settled inside a pass before any start, and the line does not speak of it. A settle in the wait that goes back to sleep without a new cycle breaks the line (EXEC_001_forbids_parkAfterSettle), and so does a pass that ends in the wait after a synchronous deposit when no transition of the net consumes (the dirty bit of the deposit lost, EXEC_001_forbids_passDepositPark). Which arrivals wake the wait, and that nothing Ready or Expired at the cycle reading may be waited on, are CONC-010's."
          "The eighth EARS sentence is line 8, the reading of AC6 and of step 3 ('re-evaluate which transitions are enabled based on current marking'). The sentence speaks of the enablement check (glossary: Enablement check), which the line reads as Enabled (enabledNA): the transitions of the model (Reference.Trans) carry no match specification (rulings D16 and D30), and for a transition without one the enablement check passes exactly when the transition is enabled (CONC-008). For a transition with a match specification the enablement check also needs a name every correlated input holds (the ν-match check of NU-020); every runtime arms a ν join only when that check finds a name (Rust bitmap_backend.rs can_enable with find_match_binding, Java canEnable with its MatchEngine), so a count-enabled ν join with no matching name holds no clock, as the sentence says. That case is NU-020's and is not encoded here. After an update, a transition enabled at the marking is armed or reaped (an update keeps a reaped transition reaped until a write of one of its arc places, ruling D6) unless the executor is not re-entrant and a firing of it is in flight (Cfg.reentrant, ruling D8 (b), CONC-002), and a transition that is not enabled holds no clock. Which stamp an armed transition holds (kept, fresh, or fresh after a restart) is TIME-010's and TIME-012's. An update that re-evaluates nothing, for instance a dirty set cleared before it is read, breaks the line (EXEC_001_forbids_emptyUpdate)."
          "Where the wait sits: no line forbids a park between an update and the end of the next firing pass when nothing was deposited since; CONC-010's park guard (nothing Ready or Expired at the cycle reading, nothing queued) makes such a park indistinguishable from an empty pass followed by the wait."
          "Ruling D61 (c) and ruling D13 (a), the markdown paragraph on two further points about the cycle: the model takes the update's reading, which stamps what it newly arms, and a reading of its own at the deadline step, never an earlier one (XSt.cyc, atDeadline); the deadline step, the ready order of the pass and the park decision judge at the deadline step's reading. A runtime that takes one reading per cycle (Rust and Java, whose update, deadline step, firing pass and decision to wait share cycle_now and cycleNanos) or a second one after its update that steps 4 and 5 and the decision to wait share (TypeScript's cycleNowMs) is a run of the model; a firing pass that judges readiness at a reading of its own, which the ruling does not allow, is the behaviour RD-16 in spec/runtime-defects.md recorded for Java. Those reading lines are TIME-010's companion, TIME-013's companion, TIME-014 line 3 and CONC-010's, and the termination test (finish or begin) made after the update and the deadline step is EXEC-040's and EXEC-041's subject. A terminal place stops the run from any phase (EXEC-042), so a finish may end a cycle anywhere; no line asks for a step after it."
          "Step 3's clause 'Only transitions affected by token changes need re-evaluation' is a permission, kind Q: the reference re-evaluates every name at the update, the runtimes only the dirty ones, and the dirty scan restores exact enablement (exec001_dirty_set_exact, a citation of updateEnablement_sync); the agreement with RefExec's full re-evaluation is link L9 of ExecLink. The step 3 text cites CONC-005 for the clause (the dirty set), not CONC-004 (the bitmask check). Step 5's ready order is EXEC-002's and TIME-014's; step 1's validation is EXEC-021's; the events each step emits are the EVT blocks'."
          "AC1 (each cycle runs steps 1 to 5 in order, except as the two exceptions allow) is lines 1 to 4 under ruling D70 (a): queued completions before step 1b, step 2 and the pass (line 4), step 2 ended before the update (line 3), the update before the deadline step (line 1) and the deadline step before any start (line 2), from every cycle that begins. AC2 is line 4 for its first clause and lines 1 and 2 for a deposit made outside a pass. AC3 is line 5 for its first sentence, and its second sentence (a step 2 entered while the executor is closed or terminated may leave the queued events in place, to be discarded by the end of the run) is the exemption of line 5's trigger, with ENV-013 for the discard; AC4 is line 6, AC5 line 7 and AC6 line 8. The test derivation (trace a simple net and check the step order on the event log) is EXEC_001_nonvacuous, five decided reference runs that exercise every trigger and every banned step of the lines, and every release they name: the update, the deadline step, the end of step 2, the commit of a queued firing, the injection, the discard and the immediate termination of a queued event, and the update after a reap followed by the start of the reaped transition."
  signoff "2026-11-13 e0db038ae801add5 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ s0 tr, XRun R C s0 tr →
        (after opensCycle, until isUpdate, never isDeadline) tr ∧
        (after opensCycle, until isDeadline, never isStart) tr ∧
        (after beginsCycle, until isEndEvents, never isUpdate) tr ∧
        (∀ i, (after queuedAtStep1 i, until settlesFiring i, never passesStep1) tr) ∧
        (∀ k, (after entersStep2With k, until dequeuesEvent k, never isUpdate) tr) ∧
        (∀ n, (after reapsName n, until isUpdate, never startsName n) tr) ∧
        (after writesMarking C, until isUpdate, never isPark) tr) ∧
      (on (fun s s' => R C s .update s'), shall (fun _ s' => UpdateExact C s'))

/- The pinned readable form of EXEC-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_001 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (s0 : XSt N T) (tr : List (XStep N T)),
        XRun R C s0 tr →
          (after opensCycle, until isUpdate, never isDeadline) tr ∧
            (after opensCycle, until isDeadline, never isStart) tr ∧
              (after beginsCycle, until isEndEvents, never isUpdate) tr ∧
                (∀ (i : ℕ), (after queuedAtStep1 i, until settlesFiring i, never passesStep1) tr) ∧
                  (∀ (k : ℕ), (after entersStep2With k, until dequeuesEvent k, never isUpdate) tr) ∧
                    (∀ (n : String), (after reapsName n, until isUpdate, never startsName n) tr) ∧
                      (after writesMarking C, until isUpdate, never isPark) tr) ∧
      on fun s s' => R C s XLbl.update s', shall fun x s' => UpdateExact C s'
-/
#guard_msgs in #print EXEC_001

/-! ### The reference

Each trace line (1 to 7) is proved by one invariant of the banned states
(`Exec001.aun_of_inv`): the trigger leads into it, every step that is not the release keeps it,
and the banned step cannot leave it. The invariants read the loop phase (`Exec001.move`: which
phases each label moves between), the completion queue, the event queue, the clock status of a
name, or the pass's `started` flag. Line 8 reads the update rule (`updSt`). -/

namespace Exec001

variable {N T : Type}

/-- A line `after T, until G, never B` holds of every run of `E` when some invariant `I` of the
states holds after every `T` step, is kept by every step that is not a `G` step, and admits no
`B` step. -/
theorem aun_of_inv {E : XRel N T} {C : Cfg N T} (I : XSt N T → Prop)
    {trig go bad : XStep N T → Bool}
    (hbad : ∀ s l s', E C s l s' → I s → bad (s, l, s') = false)
    (hkeep : ∀ s l s', E C s l s' → I s → go (s, l, s') = false → I s')
    (htrig : ∀ s l s', E C s l s' → trig (s, l, s') = true → I s') :
    ∀ s0 tr, XRun E C s0 tr → AfterUntilNever trig go bad tr := by
  suffices H : ∀ (tr : List (XStep N T)) (s0 : XSt N T) (b : Bool), XRun E C s0 tr →
      (b = true → I s0) → (afterUntilNever trig go bad).scan b tr = true from
    fun s0 tr h => H tr s0 false h (by simp)
  intro tr
  induction tr with
  | nil => intro _ _ _ _; rfl
  | cons e rest ih =>
    intro s0 b hr hb
    obtain ⟨s, l, s'⟩ := e
    obtain ⟨he, hE, hr'⟩ := hr
    simp only at he hE hr'
    subst he
    simp only [Watch.scan, afterUntilNever, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih s' _ hr' ?_⟩
    · cases b
      · simp
      · simp [hbad _ _ _ hE (hb rfl)]
    · intro hn
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hn
      rcases hn with ⟨h1, h2⟩ | h1
      · exact hkeep _ _ _ hE (hb h1) h2
      · exact htrig _ _ _ hE h1

/-- The phase moves of a settle step: in step 1 or the wait into step 1, inside the pass in
place. -/
def settleMove (p p' : Phase) : Bool :=
  (p == .completions || p == .await) && p' == .completions || p == .pass && p' == .pass

/-- The phases each label may move the loop between (source, target). Outside steps keep the
phase. -/
def move : XLbl N T → Phase → Phase → Bool
  | .commit _, p, p' | .fail _, p, p' | .tdeposit _, p, p' => settleMove p p'
  | .endCompletions, p, p' => p == .completions && p' == .publications
  | .publish _, p, p' => p == .publications && p' == .publications ||
      p == .await && p' == .completions
  | .endPublications, p, p' => p == .publications && p' == .events
  | .inject _, p, p' | .discard _, p, p' => p == .events && p' == .events ||
      p == .await && p' == .completions
  | .endEvents, p, p' => p == .events && p' == .update
  | .snapshot _, p, p' => (p == .events || p == .update || p == .await) && p' == p
  | .update, p, p' => p == .update && p' == .deadline
  | .deadline _, p, p' => p == .deadline && p' == .test
  | .finish .quiescent, p, p' => p == .test && p' == .done .quiescent
  | .finish .closed, p, p' => p == .test && p' == .done .closed
  | .finish .terminal, p, p' => isExecPhase p && p' == .done .terminal
  | .finish .stopped, p, p' => p == .completions && p' == .done .stopped
  | .begin, p, p' => p == .test && p' == .pass
  | .start _ _, p, p' | .lose _, p, p' => p == .pass && p' == .pass
  | .endPass, p, p' => p == .pass && (p' == .completions || p' == .await)
  | .park _, p, p' => p == .await && p' == .await
  | .wake, p, p' => p == .await && p' == .completions
  | _, p, p' => p' == p

/-- A settle step is taken in step 1, in the wait or inside the pass. -/
theorem canSettle_phase' {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (h : canSettle C s i f = true) :
    s.phase = .completions ∨ s.phase = .await ∨ s.phase = .pass := by
  unfold canSettle at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  unfold settleOk at h2
  split at h2 <;> simp_all

/-- The phase move of a settle. -/
theorem settle_move {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (h : canSettle C s i f = true) : settleMove s.phase (settle s i).phase = true := by
  rcases canSettle_phase' h with hp | hp | hp <;> simp [settleMove, settle, hp]

variable [DecidableEq N]

/-- Every step of the executor with judgement points `P` moves the phase as `move` allows. -/
theorem move_of_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') : move l s.phase s'.phase = true := by
  cases l with
  | commit j =>
    obtain ⟨f, e, -, -, hc, -, -, rfl⟩ := commitStep_some h
    exact settle_move hc
  | fail j =>
    obtain ⟨f, -, hc, -, rfl⟩ := failStep_some h
    exact settle_move hc
  | tdeposit j =>
    obtain ⟨f, e, -, -, hc, -, rfl⟩ := tdepositStep_some h
    exact settle_move hc
  | endCompletions =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endCompletions h
    simp [move, hp]
  | publish j =>
    obtain ⟨b, rest, -, -, hp, rfl⟩ := publishStep_some h
    rcases hp with hp | ⟨hp, -⟩ <;> simp [move, hp]
  | endPublications =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endPublications h
    simp [move, hp]
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hp, rfl⟩ := injectStep_some h
    rcases hp with hp | hp <;> simp [move, hp]
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hp, rfl⟩ := discardStep_some h
    rcases hp with hp | hp <;> simp [move, hp]
  | endEvents =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endEvents h
    simp [move, hp]
  | snapshot a =>
    obtain ⟨-, hp, -, rfl⟩ := snapshotStep_some h
    rcases hp with hp | hp | hp <;> simp [move, hp]
  | update =>
    obtain ⟨hp, -, rfl⟩ := xstepW_update h
    simp [move, hp]
  | deadline ns =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_deadline h
    simp [move, hp]
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨hp, -, -, rfl⟩ := xstepW_finishQuiescent h
      simp [move, hp]
    | closed =>
      obtain ⟨hp, -, -, -, rfl⟩ := xstepW_finishClosed h
      simp [move, hp]
    | terminal =>
      obtain ⟨hp, -, rfl⟩ := xstepW_finishTerminal h
      simp [move, hp]
    | stopped =>
      obtain ⟨hp, -, -, rfl⟩ := xstepW_finishStopped h
      simp [move, hp]
  | begin =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_begin h
    simp [move, hp]
  | start n sy =>
    obtain ⟨t, rest, -, hp, -, -, -, -, -, rfl⟩ := startStep_some h
    simp [move, hp]
  | lose n =>
    obtain ⟨t, rest, -, hp, -, -, -, -, rfl⟩ := loseStep_some h
    simp [move, hp]
  | endPass =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endPass h
    simp only [move, hp, beq_self_eq_true, Bool.true_and]
    split <;> simp
  | park tmr =>
    obtain ⟨hp, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    simp [move, hp]
  | wake =>
    obtain ⟨hp, -, rfl⟩ := wakeStep_some h
    simp [move, hp]
  | delay _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | write _ _ _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | flush _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | ret _ _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | expire _ _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | request _ _ _ => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | drain => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | close => simp [move, (xstepW_outside_frame h rfl).2.2.1]
  | terminateNow => simp [move, (xstepW_outside_frame h rfl).2.2.1]

/-- The phases of a cycle before its enablement update, and the finished run. -/
def preUpdate : Phase → Bool
  | .completions | .publications | .events | .update | .done _ => true
  | _ => false

/-- The phases of a cycle before its deadline step, and the finished run. -/
def preDeadline : Phase → Bool
  | .deadline => true
  | p => preUpdate p

omit [DecidableEq N] in
/-- A step other than the update keeps the loop before the update. -/
theorem keep_preUpdate {s s' : XSt N T} (l : XLbl N T) (p p' : Phase)
    (hm : move l p p' = true) (hgo : isUpdate (s, l, s') = false) (hp : preUpdate p = true) :
    preUpdate p' = true := by
  cases l <;> simp only [isUpdate] at hgo
  case finish c =>
    cases c <;> cases p <;> simp [move, preUpdate, isExecPhase] at hm hgo hp ⊢ <;>
      (try subst hm) <;> (try simp)
  all_goals
    cases p <;> simp [move, settleMove, preUpdate] at hm hgo hp ⊢ <;>
      (try subst hm) <;> (try simp)

omit [DecidableEq N] in
/-- A step other than a deadline step keeps the loop before the deadline step. -/
theorem keep_preDeadline {s s' : XSt N T} (l : XLbl N T) (p p' : Phase)
    (hm : move l p p' = true) (hgo : isDeadline (s, l, s') = false)
    (hp : preDeadline p = true) : preDeadline p' = true := by
  cases l <;> simp only [isDeadline] at hgo
  case finish c =>
    cases c <;> cases p <;> simp [move, preDeadline, preUpdate, isExecPhase] at hm hgo hp ⊢ <;>
      (try subst hm) <;> (try simp)
  all_goals
    cases p <;> simp [move, settleMove, preDeadline, preUpdate] at hm hgo hp ⊢ <;>
      (try subst hm) <;> (try simp)

omit [DecidableEq N] in
/-- A deposit outside the pass leaves the loop in step 1, 1b or 2. -/
theorem preUpdate_of_deposit (l : XLbl N T) (p p' : Phase) (hm : move l p p' = true)
    (hd : depositLabel l = true) (hp : p ≠ .pass) : preUpdate p' = true := by
  cases l <;> simp [depositLabel] at hd <;> cases p <;>
    simp [move, settleMove] at hm hp ⊢ <;> (try subst hm) <;> (try simp [preUpdate])

omit [DecidableEq N] in
/-- No executor step leaves the finished run. -/
theorem keep_done (l : XLbl N T) (p p' : Phase) (hm : move l p p' = true)
    (hp : isExecPhase p = false) : isExecPhase p' = false := by
  cases p <;> simp [isExecPhase] at hp
  cases l
  case finish c => cases c <;> simp [move, isExecPhase] at hm ⊢
  all_goals simp [move, settleMove] at hm ⊢ <;> (try subst hm) <;> (try simp [isExecPhase])

/-- The outside steps keep the pass's `started` flag and every queued completion and event
(an immediate termination drops the events). -/
theorem outside_frame {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (ho : l.outside = true) :
    s'.started = s.started ∧ (∀ i ∈ s.cq, i ∈ s'.cq) ∧
      ((match l with | .terminateNow => true | _ => false) = false →
        ∀ k ∈ s.eq.map Prod.fst, k ∈ s'.eq.map Prod.fst) := by
  cases l with
  | delay δ => cases xstepW_delay h; exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;>
      exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    exact ⟨rfl, fun _ h => List.mem_append_left _ h, fun _ _ h => h⟩
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact ⟨rfl, fun _ h => List.mem_append_left _ h, fun _ _ h => h⟩
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · refine ⟨rfl, fun _ h => h, fun _ _ h => ?_⟩
      simp only [List.map_append, List.mem_append]
      exact Or.inl h
    · exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | drain =>
    obtain ⟨-, rfl⟩ := drainStep_some h
    exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | close =>
    obtain ⟨-, rfl⟩ := closeStep_some h
    exact ⟨rfl, fun _ h => h, fun _ _ h => h⟩
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h
    exact ⟨rfl, fun _ h => h, fun h => by simp at h⟩
  | _ => simp [XLbl.outside] at ho

/-- A write keeps a name without a stamp without one. -/
theorem unreap_none {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    (h : stampOf (st n) = none) : stampOf (unreap C ps st n) = none := by
  unfold unreap
  split
  · split <;> rfl
  · simpa using h

/-- A start keeps a name without a stamp without one. -/
theorem afterStart_none {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N} {n : String}
    (h : stampOf (s.st n) = none) : stampOf (afterStart P C s t n) = none := by
  unfold afterStart
  split
  · rfl
  · split <;> simp_all [stampOf]

/-- Before the update means before the deadline step. -/
theorem preDeadline_of_preUpdate {p : Phase} (h : preUpdate p = true) : preDeadline p = true := by
  cases p <;> simp_all [preDeadline, preUpdate]

/-- The executor with judgement points `P`, as an executor relation. -/
abbrev rel (P : XPol N T) : XRel N T := fun C s l s' => xstepW P C s l = some s'

/-- Step 1's queue: a step that does not process firing `i` keeps `i` queued in step 1, unless
the run finishes. -/
theorem keep_cq {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {i : Nat}
    (h : xstepW P C s l = some s') (hp : s.phase = .completions) (hi : i ∈ s.cq)
    (hgo : settlesFiring i (s, l, s') = false) :
    (s'.phase = .completions ∧ i ∈ s'.cq) ∨ isExecPhase s'.phase = false := by
  have hm := move_of_step h
  cases l
  case commit j =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    have hj : j ≠ i := by simpa [settlesFiring] using hgo
    exact Or.inl ⟨by simp [depositAt, settle, hp], (List.mem_erase_of_ne (Ne.symm hj)).2 hi⟩
  case fail j =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    have hj : j ≠ i := by simpa [settlesFiring] using hgo
    exact Or.inl ⟨by simp [settle, hp], (List.mem_erase_of_ne (Ne.symm hj)).2 hi⟩
  case tdeposit j =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    have hj : j ≠ i := by simpa [settlesFiring] using hgo
    exact Or.inl ⟨by simp [depositAt, settle, hp], (List.mem_erase_of_ne (Ne.symm hj)).2 hi⟩
  case endCompletions =>
    obtain ⟨-, -, hcq, -, -⟩ := xstepW_endCompletions h
    simp [hcq] at hi
  case finish c =>
    cases c
    case terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact Or.inr rfl
    case stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact Or.inr rfl
    all_goals simp [move, hp] at hm
  all_goals first
    | (simp [move, hp] at hm; done)
    | exact Or.inl ⟨((xstepW_outside_frame h rfl).2.2.1).trans hp, (outside_frame h rfl).2.1 i hi⟩

/-- Step 2's queue: a step that does not take the event of ticket `k` off the queue keeps it
queued in step 2, unless the run finishes. -/
theorem keep_eq {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {k : Nat}
    (h : xstepW P C s l = some s') (hp : s.phase = .events) (hk : k ∈ s.eq.map Prod.fst)
    (hgo : dequeuesEvent k (s, l, s') = false) :
    (s'.phase = .events ∧ k ∈ s'.eq.map Prod.fst) ∨ isExecPhase s'.phase = false := by
  have hm := move_of_step h
  cases l
  case inject j =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
    have hj : j ≠ k := by simpa [dequeuesEvent] using hgo
    rw [he, List.map_cons, List.mem_cons] at hk
    refine Or.inl ⟨by simp [hp], ?_⟩
    rcases hk with hk | hk
    · exact absurd hk.symm hj
    · exact hk
  case discard j =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := discardStep_some h
    have hj : j ≠ k := by simpa [dequeuesEvent] using hgo
    rw [he, List.map_cons, List.mem_cons] at hk
    refine Or.inl ⟨by simp [hp], ?_⟩
    rcases hk with hk | hk
    · exact absurd hk.symm hj
    · exact hk
  case snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact Or.inl ⟨hp, hk⟩
  case endEvents =>
    obtain ⟨-, -, heq, -⟩ := xstepW_endEvents h
    simp [heq] at hk
  case terminateNow => simp [dequeuesEvent] at hgo
  case finish c =>
    cases c
    case terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact Or.inr rfl
    all_goals simp [move, hp] at hm
  all_goals first
    | (simp [move, settleMove, hp] at hm; done)
    | exact Or.inl ⟨((xstepW_outside_frame h rfl).2.2.1).trans hp,
        (outside_frame h rfl).2.2 rfl k hk⟩

/-- A name without a stamp gets one only at the enablement update. -/
theorem keep_st {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {n : String}
    (h : xstepW P C s l = some s') (hgo : isUpdate (s, l, s') = false)
    (hn : stampOf (s.st n) = none) : stampOf (s'.st n) = none := by
  cases l
  case commit j =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact unreap_none hn
  case tdeposit j =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact unreap_none hn
  case fail j =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact hn
  case publish j =>
    obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
    exact unreap_none hn
  case inject k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h
    exact unreap_none hn
  case discard k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h
    exact hn
  case snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact hn
  case update => simp [isUpdate] at hgo
  case deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    simp only
    split
    · rfl
    · exact hn
  case start m sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact unreap_none (afterStart_none hn)
  case lose m =>
    obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    simp only
    split
    · rfl
    · exact hn
  case endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact hn
  case endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact hn
  case endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    exact hn
  case finish c =>
    cases c
    case quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact hn
    case closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact hn
    case terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact hn
    case stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact hn
  case begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact hn
  case endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact hn
  case park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact hn
  case wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact hn
  all_goals rw [(xstepW_outside_frame h rfl).2.1]; exact hn

/-- The states line 7 bans the wait in: before the update, or inside a pass that started a
transition. -/
def waitBanned (s : XSt N T) : Prop :=
  preUpdate s.phase = true ∨ (s.phase = .pass ∧ s.started = true)

/-- A step other than the update keeps the loop out of the wait once it is banned. -/
theorem keep_wait {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hgo : isUpdate (s, l, s') = false) (hI : waitBanned s) :
    waitBanned s' := by
  rcases hI with hp | ⟨hp, hst⟩
  · exact Or.inl (keep_preUpdate l _ _ (move_of_step h) hgo hp)
  · have hm := move_of_step h
    cases l
    case commit j =>
      obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
      exact Or.inr ⟨by simp [depositAt, settle, hp], hst⟩
    case fail j =>
      obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
      exact Or.inr ⟨by simp [settle, hp], hst⟩
    case tdeposit j =>
      obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
      exact Or.inr ⟨by simp [depositAt, settle, hp], hst⟩
    case start m sy =>
      obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
      exact Or.inr ⟨hp, rfl⟩
    case lose m =>
      obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some h
      exact Or.inr ⟨hp, hst⟩
    case endPass =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
      exact Or.inl (by simp [hst, preUpdate])
    case finish c =>
      cases c
      case terminal =>
        obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
        exact Or.inl rfl
      all_goals simp [move, hp] at hm
    all_goals first
      | (simp [move, hp] at hm; done)
      | exact Or.inr ⟨((xstepW_outside_frame h rfl).2.2.1).trans hp,
          ((outside_frame h rfl).1).trans hst⟩

/-- A step out of the pass or the wait that begins a cycle lands on step 1. -/
theorem leave_completions {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hb : beginsCycle (s, l, s') = true) :
    s'.phase = .completions := by
  have hm := move_of_step h
  simp only [beginsCycle, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at hb
  obtain ⟨⟨⟨hp, h1⟩, h2⟩, h3⟩ := hb
  revert hm h1 h2 h3
  generalize s'.phase = p'
  rcases hp with hp | hp <;> rw [hp] <;> intro hm h1 h2 h3 <;>
    cases l <;> (try cases ‹Cause›) <;> cases p' <;>
      simp_all [move, settleMove, isExecPhase]

/-- A step that begins a cycle or deposits outside the pass leaves the loop before the update. -/
theorem opens_preUpdate {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (ht : opensCycle (s, l, s') = true) :
    preUpdate s'.phase = true := by
  simp only [opensCycle, Bool.or_eq_true] at ht
  rcases ht with hb | hd
  · simp [preUpdate, leave_completions h hb]
  · simp only [depositOutsidePass, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    exact preUpdate_of_deposit l _ _ (move_of_step h) hd.1 hd.2

/-- Line 1 holds of the executor of every `P`. -/
theorem line1 (P : XPol N T) (C : Cfg N T) :
    ∀ s0 tr, XRun (rel P) C s0 tr → AfterUntilNever opensCycle isUpdate isDeadline tr :=
  aun_of_inv (fun s => preUpdate s.phase = true)
    (fun s l s' h hI => by
      cases hb : isDeadline (s, l, s')
      · rfl
      · have hm := move_of_step h
        cases l <;> simp [isDeadline] at hb
        simp only [move, Bool.and_eq_true, beq_iff_eq] at hm
        rw [hm.1] at hI
        simp [preUpdate] at hI)
    (fun s l s' h hI hgo => keep_preUpdate l _ _ (move_of_step h) hgo hI)
    (fun _ _ _ h ht => opens_preUpdate h ht)

/-- Line 2 holds of the executor of every `P`. -/
theorem line2 (P : XPol N T) (C : Cfg N T) :
    ∀ s0 tr, XRun (rel P) C s0 tr → AfterUntilNever opensCycle isDeadline isStart tr :=
  aun_of_inv (fun s => preDeadline s.phase = true)
    (fun s l s' h hI => by
      cases hb : isStart (s, l, s')
      · rfl
      · have hm := move_of_step h
        cases l <;> simp [isStart] at hb
        simp only [move, Bool.and_eq_true, beq_iff_eq] at hm
        rw [hm.1] at hI
        simp [preDeadline, preUpdate] at hI)
    (fun s l s' h hI hgo => keep_preDeadline l _ _ (move_of_step h) hgo hI)
    (fun _ _ _ h ht => preDeadline_of_preUpdate (opens_preUpdate h ht))

/-- The phases of a cycle before the end of step 2, and the finished run. -/
def preEvents : Phase → Bool
  | .completions | .publications | .events | .done _ => true
  | _ => false

/-- Line 3 holds of the executor of every `P`. -/
theorem line3 (P : XPol N T) (C : Cfg N T) :
    ∀ s0 tr, XRun (rel P) C s0 tr → AfterUntilNever beginsCycle isEndEvents isUpdate tr :=
  aun_of_inv (fun s => preEvents s.phase = true)
    (fun s l s' h hI => by
      cases hb : isUpdate (s, l, s')
      · rfl
      · have hm := move_of_step h
        cases l <;> simp [isUpdate] at hb
        simp only [move, Bool.and_eq_true, beq_iff_eq] at hm
        rw [hm.1] at hI
        simp [preEvents] at hI)
    (fun s l s' h hI hgo => by
      have hm := move_of_step h
      revert hm hI hgo
      generalize s.phase = p
      generalize s'.phase = p'
      intro hm hI hgo
      cases l <;> (try cases ‹Cause›) <;> cases p <;> cases p' <;>
        simp_all [isEndEvents, move, settleMove, preEvents, isExecPhase])
    (fun s l s' h ht => by
      simp [preEvents, leave_completions h ht])

/-- Line 4 holds of the executor of every `P`. -/
theorem line4 (P : XPol N T) (C : Cfg N T) (i : Nat) :
    ∀ s0 tr, XRun (rel P) C s0 tr →
      AfterUntilNever (queuedAtStep1 i) (settlesFiring i) passesStep1 tr :=
  aun_of_inv (fun s => (s.phase = .completions ∧ i ∈ s.cq) ∨ isExecPhase s.phase = false)
    (fun s l s' h hI => by
      cases hb : passesStep1 (s, l, s')
      · rfl
      · have hm := move_of_step h
        have hp : s.phase = .completions ∨ ∃ c, s.phase = .done c := by
          rcases hI with ⟨hp, -⟩ | hp
          · exact Or.inl hp
          · right
            revert hp
            cases s.phase <;> simp [isExecPhase]
        cases l <;> simp [passesStep1] at hb <;>
          rcases hp with hp | ⟨c, hp⟩ <;> simp [move, hp] at hm)
    (fun s l s' h hI hgo => by
      rcases hI with ⟨hp, hi⟩ | hp
      · exact keep_cq h hp hi hgo
      · exact Or.inr (keep_done l _ _ (move_of_step h) hp))
    (fun s l s' h ht => by
      simp only [queuedAtStep1, entersStep1With, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        bne_iff_ne, ne_eq, List.contains_iff_mem] at ht
      rcases ht with ⟨⟨hp, -⟩, hi⟩ | ⟨hb, hi⟩
      · exact Or.inl ⟨hp, hi⟩
      · exact Or.inl ⟨leave_completions h hb, hi⟩)

/-- Line 5 holds of the executor of every `P`. -/
theorem line5 (P : XPol N T) (C : Cfg N T) (k : Nat) :
    ∀ s0 tr, XRun (rel P) C s0 tr →
      AfterUntilNever (entersStep2With k) (dequeuesEvent k) isUpdate tr :=
  aun_of_inv (fun s => (s.phase = .events ∧ k ∈ s.eq.map Prod.fst) ∨ isExecPhase s.phase = false)
    (fun s l s' h hI => by
      cases hb : isUpdate (s, l, s')
      · rfl
      · have hm := move_of_step h
        cases l <;> simp [isUpdate] at hb
        simp only [move, Bool.and_eq_true, beq_iff_eq] at hm
        rcases hI with ⟨hp, -⟩ | hp <;> rw [hm.1] at hp <;> simp [isExecPhase] at hp)
    (fun s l s' h hI hgo => by
      rcases hI with ⟨hp, hk⟩ | hp
      · exact keep_eq h hp hk hgo
      · exact Or.inr (keep_done l _ _ (move_of_step h) hp))
    (fun s l s' h ht => by
      simp only [entersStep2With, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        List.contains_iff_mem] at ht
      exact Or.inl ⟨ht.1.1.1, ht.2⟩)

/-- Line 6 holds of the executor of every `P`. -/
theorem line6 (P : XPol N T) (C : Cfg N T) (n : String) :
    ∀ s0 tr, XRun (rel P) C s0 tr → AfterUntilNever (reapsName n) isUpdate (startsName n) tr :=
  aun_of_inv (fun s => stampOf (s.st n) = none)
    (fun s l s' h hI => by
      cases hb : startsName n (s, l, s')
      · rfl
      · cases l <;> simp [startsName] at hb
        subst hb
        obtain ⟨t, rest, -, -, -, -, -, hst, -, -⟩ := startStep_some h
        simp [hI] at hst)
    (fun s l s' h hI hgo => keep_st h hgo hI)
    (fun s l s' h ht => by
      cases l <;> simp [reapsName] at ht
      obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
      simp [ht, stampOf])

/-- Line 7 holds of the executor of every `P`. -/
theorem line7 (P : XPol N T) (C : Cfg N T) :
    ∀ s0 tr, XRun (rel P) C s0 tr → AfterUntilNever (writesMarking C) isUpdate isPark tr :=
  aun_of_inv waitBanned
    (fun s l s' h hI => by
      cases hb : isPark (s, l, s')
      · rfl
      · have hm := move_of_step h
        cases l <;> simp [isPark] at hb
        simp only [move, Bool.and_eq_true, beq_iff_eq] at hm
        rcases hI with hp | ⟨hp, -⟩ <;> rw [hm.1] at hp <;> simp [preUpdate] at hp)
    (fun s l s' h hI hgo => keep_wait h hgo hI)
    (fun s l s' h ht => by
      simp only [writesMarking, Bool.or_eq_true] at ht
      rcases ht with (hd | hq) | hc
      · simp only [depositOutsidePass, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
        exact Or.inl (preUpdate_of_deposit l _ _ (move_of_step h) hd.1 hd.2)
      · simp only [depositInPass, Bool.and_eq_true, beq_iff_eq] at hq
        obtain ⟨⟨hd, hp⟩, hst⟩ := hq
        cases l <;> simp [depositLabel] at hd
        case commit i =>
          obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
          exact Or.inr ⟨by simp [depositAt, settle, hp], hst⟩
        case tdeposit i =>
          obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
          exact Or.inr ⟨by simp [depositAt, settle, hp], hst⟩
        case publish i =>
          obtain ⟨b, rest, -, -, hp', -⟩ := publishStep_some h
          rcases hp' with hp' | ⟨hp', -⟩ <;> rw [hp] at hp' <;> cases hp'
        case inject k =>
          obtain ⟨p, x, rest, -, -, -, hp', -⟩ := injectStep_some h
          rcases hp' with hp' | hp' <;> rw [hp] at hp' <;> cases hp'
      · cases l <;> simp [startsConsuming] at hc
        obtain ⟨t, rest, -, hp, -, -, -, -, -, rfl⟩ := startStep_some h
        exact Or.inr ⟨hp, rfl⟩)

omit [DecidableEq N] in
/-- The transition the net holds under name `n` is named `n`. -/
theorem findT_name {C : Cfg N T} {n : String} {u : Trans N} (hu : findT C n = some u) :
    u.core.name = n := by
  have := List.find?_some hu
  simpa using this

/-- Line 8 holds of the update of every `P`. -/
theorem line8 (P : XPol N T) (C : Cfg N T) {s s' : XSt N T}
    (h : xstepW P C s .update = some s') : UpdateExact C s' := by
  obtain ⟨-, -, rfl⟩ := xstepW_update h
  intro n u hu
  have hn := findT_name hu
  constructor
  · intro he hfree
    replace hfree : C.reentrant = true ∨ inFlightN s n = false := by
      simpa [InFlight, inFlightN] using hfree
    have hne : updSt P C s n ≠ .off := by
      simp only [updSt, hu]
      simp only at he
      cases hst : s.st n <;> cases hP : P.updReaped <;> simp_all <;> split <;> simp_all
    simp only [ArmedE, ReapedE, armedB, hn]
    revert hne
    simp only at he ⊢
    cases updSt P C s n <;> simp_all [stampOf]
  · intro he
    simp only [updSt, hu]
    simp only at he
    cases hst : s.st n <;> cases hP : P.updReaped <;> simp_all [stampOf]

/-- The executor of every `P` satisfies EXEC-001. -/
theorem holds (P : XPol N T) : EXEC_001 (rel P) := by
  intro C
  refine ⟨fun s0 tr hr => ?_, fun s s' h => line8 P C h⟩
  exact ⟨line1 P C s0 tr hr, line2 P C s0 tr hr, line3 P C s0 tr hr,
    fun i => line4 P C i s0 tr hr, fun k => line5 P C k s0 tr hr, fun n => line6 P C n s0 tr hr,
    line7 P C s0 tr hr⟩

end Exec001

/-- ✓ The reference executor satisfies EXEC-001: every trace line holds of every run from every
state, and line 8 of every update step (`Exec001.holds` at `refXPol`). -/
@[evidence holds EXEC_001]
theorem EXEC_001_reference {N T : Type} [DecidableEq N] :
    EXEC_001 (RefExec (N := N) (T := T)) :=
  Exec001.holds refXPol

/-! ### Runs of a step function -/

namespace Exec001

variable {N T : Type}

/-- The trace of steps of a run of the step function `g`, if every label is a step (the
`xtrace` of `Reference/Exec.lean` for any step function, so that a mutant's run is decided the
same way). -/
def gtrace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (gtrace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `gtrace` builds is a run of `g`'s relation. -/
theorem gtrace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      gtrace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [gtrace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : gtrace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, gtrace_run ht⟩

/-- Read a decided fact `q` off the run of `g` from `s` with labels `ls`. -/
theorem run_of_check {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T}
    {s : XSt N T} {ls : List (XLbl N T)} {q : List (XStep N T) → Bool}
    (h : (gtrace g C s ls).map q = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ q tr = true := by
  cases ht : gtrace g C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, gtrace_run ht, h⟩

/-- Every step of a run is a step of its executor. -/
theorem run_mem {E : XRel N T} {C : Cfg N T} :
    ∀ {s : XSt N T} {tr : List (XStep N T)}, XRun E C s tr → ∀ e ∈ tr, E C e.1 e.2.1 e.2.2
  | _, [], _, e, he => by simp at he
  | _, _ :: _, ⟨_, hx, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact hx
    · exact run_mem hr e he

/-- Some step satisfies `p` and a later step satisfies `q`. -/
def thenLater (p q : XStep N T → Bool) (tr : List (XStep N T)) : Bool :=
  match tr.dropWhile (fun e => !p e) with
  | [] => false
  | _ :: rest => rest.any q

end Exec001

/-! ### Examples

Three nets. The untimed one: transition `t` takes the token of place `0` and puts one in place
`1` (its action writes `8` there), transition `w` takes the token of place `1`; place `2` is an
environment place nobody reads. The timed one: transition `u`, `Window(3, 5)`, tolerance `0`,
takes the token of place `0` (with place `0` an environment place in `exec001_cWe`). The
non-consuming one: a source transition `g` and a transition `r` that reads place `1`; no
transition has an input or reset arc. -/

/-- `t`: one token from `0`, output `Place(1)`. -/
def exec001_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `w`: one token from `1`, no output. -/
def exec001_w : Trans Nat :=
  { core := { name := "w", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The untimed configuration, re-entrant or not; `2` is an environment place. -/
def exec001_cfg (re : Bool) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [exec001_t, exec001_w] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [2], reentrant := re,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- One token `7` in place `0`. -/
def exec001_m1 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- Two tokens `7`, `9` in place `0`. -/
def exec001_m2 : QMarking Nat Nat := fun p => if p = 0 then [7, 9] else []

/-- The empty marking. -/
def exec001_m0 : QMarking Nat Nat := fun _ => []

/-- `u`: one token from `0`, no output. -/
def exec001_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timed configuration: `u` alone, `Window(3, 5)`, tolerance `0`. -/
def exec001_cW : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [exec001_u] },
           timing := fun _ => .window 3 5, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The timed configuration with place `0` an environment place. -/
def exec001_cWe : Cfg Nat Nat := { exec001_cW with envs := [0] }

/-- `g`: a source transition, inhibited by place `1`, output `Place(1)`. -/
def exec001_g : Trans Nat :=
  { core := { name := "g", inputs := [], inhibitors := [1], reads := [], resets := [] },
    out := some (.place 1) }

/-- `r`: reads place `1`, inhibited by place `2`, output `Place(2)`. -/
def exec001_r : Trans Nat :=
  { core := { name := "r", inputs := [], inhibitors := [2], reads := [1], resets := [] },
    out := some (.place 2) }

/-- The untimed net of `g` and `r`: no transition has an input or reset arc. -/
def exec001_cNC : Cfg Nat Nat :=
  { X := { net := { places := [1, 2], transitions := [exec001_g, exec001_r] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- Steps 1 to 4 of a cycle with nothing to settle, publish, inject or reap. -/
def exec001_quiet : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The first cycle of the untimed net: `t` starts, its action writes `8` to `1` and returns
before the pass ends, so the firing `0` is queued when the next cycle begins. -/
def exec001_cycle1 : List (XLbl Nat Nat) :=
  exec001_quiet ++ [.begin, .start "t" false, .write 0 1 8, .ret 0 true, .endPass]

/-- The main reference run: the first cycle; the next cycle begins with firing `0` queued, and
step 1 commits `t`'s `8` (a deposit outside the pass); a request queues `5` for place `2` with
ticket `1`; step 2 injects it; the update arms `w`, which starts; the next cycle starts nothing,
and the loop parks. -/
def exec001_runA : List (XLbl Nat Nat) :=
  exec001_cycle1 ++
    [.commit 0, .request 2 5 .accepted, .endCompletions, .endPublications, .inject 1,
     .endEvents, .update, .deadline [], .begin, .start "w" false, .endPass] ++
    exec001_quiet ++ [.begin, .endPass, .park none]

/-- The checks of the main run: the triggers, releases and banned steps of lines 1 to 5 and 7
occur, and the first update arms the enabled `t` and leaves the disabled `w` without a clock. -/
def exec001_exercised (tr : List (XStep Nat Nat)) : Bool :=
  tr.any beginsCycle && tr.any depositOutsidePass && tr.any isDeadline && tr.any isUpdate &&
    tr.any isStart && tr.any isEndEvents && tr.any (queuedAtStep1 0) && tr.any (settlesFiring 0) &&
    tr.any passesStep1 && tr.any (entersStep2With 1) && tr.any (dequeuesEvent 1) &&
    tr.any (writesMarking (exec001_cfg false)) && tr.any isPark &&
    tr.any (fun e => isUpdate e && (stampOf (e.2.2.st "t")).isSome &&
      (stampOf (e.2.2.st "w")).isNone)

/-- The synchronous run: `t` starts synchronously, its action writes `8` to `1` and returns, the
pass commits it (a deposit inside the pass that started `t`), and the next cycle's update
follows. -/
def exec001_runS : List (XLbl Nat Nat) :=
  exec001_quiet ++ [.begin, .start "t" true, .write 0 1 8, .ret 0 true, .commit 0, .endPass] ++
    exec001_quiet

/-- The reap run on the timed net with place `0` an environment place: `u` is armed at `0` and
not yet ready; the clock jumps to `6`; the deadline step reaps `u`; a caller injects `5` into
place `0`; the wait injects it, which writes `u`'s arc place (ruling D6); the next update arms `u`
again at `6`, and three units later the pass starts it. -/
def exec001_runW : List (XLbl Nat Nat) :=
  exec001_quiet ++ [.begin, .endPass, .delay 6, .wake, .endCompletions, .endPublications,
    .endEvents, .update, .deadline ["u"], .request 0 5 .accepted, .begin, .endPass, .inject 0] ++
    exec001_quiet ++ [.begin, .endPass, .delay 3, .wake] ++ exec001_quiet ++
    [.begin, .start "u" false]

/-- The discard run: a request queues `5` for place `2` with ticket `0`, step 2 begins with the
executor open, a caller closes the executor, and step 2 discards the event before the update. -/
def exec001_runD : List (XLbl Nat Nat) :=
  [.request 2 5 .accepted, .endCompletions, .endPublications, .close, .discard 0, .endEvents,
   .update]

/-- The termination run: a request queues `5` for place `2` with ticket `0`, step 2 begins, and
an immediate termination discards the queue before the update. -/
def exec001_runT : List (XLbl Nat Nat) :=
  [.request 2 5 .accepted, .endCompletions, .endPublications, .terminateNow, .endEvents, .update]

/-- The step is the label `l`. -/
def exec001_is (l : XLbl Nat Nat) (e : XStep Nat Nat) : Bool :=
  match l, e.2.1 with
  | .discard k, .discard j => k == j
  | .terminateNow, .terminateNow => true
  | _, _ => false

/-- ✓ Every line of EXEC-001 is exercised by the reference. On the untimed net (`exec001_runA`):
the second cycle begins with firing `0` queued, step 1 commits it (a deposit outside the pass)
before the injection of ticket `1` and the start of `w` (line 4), and the update and then the
deadline step come before that start (lines 1 and 2); step 2 ends before every update (line 3);
the event of ticket `1` is queued when step 2 begins and is injected before the update (line 5);
the starts of `t` and `w` consume, and the loop parks only after the next update (line 7); the
first update arms the enabled `t` and leaves `w` without a clock (line 8). The synchronous run
(`exec001_runS`) deposits inside the pass that started `t`, and an update follows (line 7's
second trigger). On the timed net (`exec001_runW`) the deadline step reaps `u` (line 6), and `u`
starts only after an injection into its place and the next update. The runs `exec001_runD` and
`exec001_runT` release line 5 by a discard after a close during step 2 and by an immediate
termination. -/
@[evidence nonvacuous EXEC_001]
theorem EXEC_001_nonvacuous :
    (∃ tr, XRun RefExec (exec001_cfg false) (xinit exec001_m1 0) tr ∧
      exec001_exercised tr = true) ∧
    (∃ tr, XRun RefExec (exec001_cfg false) (xinit exec001_m1 0) tr ∧
      thenLater depositInPass isUpdate tr = true) ∧
    (∃ tr, XRun RefExec exec001_cWe (xinit exec001_m1 0) tr ∧
      thenLater (reapsName "u") isUpdate tr = true ∧
      thenLater (reapsName "u") (startsName "u") tr = true) ∧
    (∃ tr, XRun RefExec (exec001_cfg false) (xinit exec001_m1 0) tr ∧
      thenLater (entersStep2With 0) (exec001_is (.discard 0)) tr = true) ∧
    (∃ tr, XRun RefExec (exec001_cfg false) (xinit exec001_m1 0) tr ∧
      thenLater (entersStep2With 0) (exec001_is .terminateNow) tr = true) := by
  refine ⟨Exec001.run_of_check (g := fun C s l => xstep C s l) (ls := exec001_runA)
      (by decide +kernel),
    Exec001.run_of_check (g := fun C s l => xstep C s l) (ls := exec001_runS) (by decide +kernel),
    ?_,
    Exec001.run_of_check (g := fun C s l => xstep C s l) (ls := exec001_runD) (by decide +kernel),
    Exec001.run_of_check (g := fun C s l => xstep C s l) (ls := exec001_runT) (by decide +kernel)⟩
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := fun C s l => xstep C s l)
    (C := exec001_cWe) (s := xinit exec001_m1 0) (ls := exec001_runW)
    (q := fun tr => thenLater (reapsName "u") isUpdate tr &&
      thenLater (reapsName "u") (startsName "u") tr) (by decide +kernel)
  simp only [Bool.and_eq_true] at hq
  exact ⟨tr, hr, hq⟩

/-! ### Violation: a deadline step without an update after a deposit (line 1) -/

/-- An executor that goes from step 2 straight to the deadline step, reaping on the statuses of
the last update. -/
def exec001_skipUpdateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents => (xstep C s .endEvents).map fun s' => { s' with phase := .deadline }
  | l => xstep C s l

/-- The executor of `exec001_skipUpdateStep`. -/
def exec001_skipUpdate {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_skipUpdateStep C s l = some s'

/-- ✗ Skipping the update violates EXEC-001 (line 1): a request for place `2` is accepted, step 2
injects it, and the deadline step follows with no update since the deposit. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_skipUpdate : ¬ EXEC_001 (exec001_skipUpdate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_skipUpdateStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := [.request 2 5 .accepted, .endCompletions, .endPublications, .inject 0, .endEvents,
      .deadline []])
    (q := fun tr => !decide (AfterUntilNever opensCycle isUpdate isDeadline tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).1] at hq

/-! ### Violation: the wait wakes into a later step (lines 1 and 3) -/

/-- An executor whose wait, when it wakes, goes to phase `p` instead of step 1 ("only the clock
moved"): with `p = update` the timer-wake fast path of a loop that continues to the enablement
update; with `p = deadline` one that continues to the deadline step. -/
def exec001_wakeToStep {N T : Type} [DecidableEq N] (p : Phase) (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .wake => (xstep C s .wake).map fun s' => { s' with phase := p }
  | l => xstep C s l

/-- The executor of `exec001_wakeToStep p`. -/
def exec001_wakeTo {N T : Type} [DecidableEq N] (p : Phase) : XRel N T :=
  fun C s l s' => exec001_wakeToStep p C s l = some s'

/-- ✗ A wait that wakes into the deadline step violates EXEC-001 (line 1): the first cycle
starts nothing and the loop waits; it wakes into the deadline step, which runs with no update
since the cycle began. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_wakeToDeadline :
    ¬ EXEC_001 (exec001_wakeTo (N := Nat) (T := Nat) .deadline) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_wakeToStep .deadline)
    (C := exec001_cfg false) (s := xinit exec001_m0 0)
    (ls := exec001_quiet ++ [.begin, .endPass, .wake, .deadline []])
    (q := fun tr => !decide (AfterUntilNever opensCycle isUpdate isDeadline tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).1] at hq

/-- ✗ A wait that wakes into the enablement update violates EXEC-001 (line 3): the first cycle
starts nothing and the loop waits; it wakes into the update, which runs before step 2 ends, so
the cycle skips steps 1, 1b and 2 with whatever they had queued. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_wakeToUpdate :
    ¬ EXEC_001 (exec001_wakeTo (N := Nat) (T := Nat) .update) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_wakeToStep .update)
    (C := exec001_cfg false) (s := xinit exec001_m0 0)
    (ls := exec001_quiet ++ [.begin, .endPass, .wake, .update])
    (q := fun tr => !decide (AfterUntilNever beginsCycle isEndEvents isUpdate tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.1] at hq

/-! ### Violation: the pass begins before the deadline step (line 2) -/

/-- An executor whose pass may begin right after the update, before the deadline step (fire
before reap: the run `clash013_refresh_rescue` of `ClashesTime.lean` is of this kind). -/
def exec001_fireBeforeReapStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin => if s.phase = .deadline then xstep C { s with phase := .test } .begin
              else xstep C s .begin
  | l => xstep C s l

/-- The executor of `exec001_fireBeforeReapStep`. -/
def exec001_fireBeforeReap {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_fireBeforeReapStep C s l = some s'

/-- ✗ A pass that begins before the deadline step violates EXEC-001 (line 2): after step 1
commits `t`'s `8`, the update arms `w` and the pass starts it with no deadline step since the
deposit. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_fireBeforeReap :
    ¬ EXEC_001 (exec001_fireBeforeReap (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_fireBeforeReapStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := exec001_cycle1 ++ [.commit 0, .endCompletions, .endPublications, .endEvents, .update,
      .begin, .start "w" false])
    (q := fun tr => !decide (AfterUntilNever opensCycle isDeadline isStart tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.1] at hq

/-! ### Violation: step 1 ends with a finished firing still queued (line 4, AC2) -/

/-- An executor whose step 1 may end while finished firings are still queued (they stay queued
for a later cycle). -/
def exec001_endWithQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endCompletions =>
      (xstep C { s with cq := [] } .endCompletions).map fun s' => { s' with cq := s.cq }
  | l => xstep C s l

/-- The executor of `exec001_endWithQueuedStep`. -/
def exec001_endWithQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_endWithQueuedStep C s l = some s'

/-- ✗ Ending step 1 with a finished firing queued violates EXEC-001 (line 4): on the re-entrant
net with two tokens in `0`, the firing `0` of `t` is queued when the next cycle begins, step 1
ends without it, and the next pass starts `t` again. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_endWithQueued :
    ¬ EXEC_001 (exec001_endWithQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_endWithQueuedStep)
    (C := exec001_cfg true) (s := xinit exec001_m2 0)
    (ls := exec001_cycle1 ++ exec001_quiet ++ [.begin, .start "t" false])
    (q := fun tr => !decide (AfterUntilNever (queuedAtStep1 0) (settlesFiring 0) passesStep1 tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.2.1 0] at hq

/-! ### Violation: the update runs with an event still queued (line 5, AC3) -/

/-- An executor whose step 2 may end while events are still queued. -/
def exec001_updateBeforeInjectStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents => (xstep C { s with eq := [] } .endEvents).map fun s' => { s' with eq := s.eq }
  | l => xstep C s l

/-- The executor of `exec001_updateBeforeInjectStep`. -/
def exec001_updateBeforeInject {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_updateBeforeInjectStep C s l = some s'

/-- ✗ An update before the queued event is injected violates EXEC-001 (line 5): a request for
place `2` is accepted with ticket `0`, step 2 ends without injecting it, and the update runs. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_updateBeforeInject :
    ¬ EXEC_001 (exec001_updateBeforeInject (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_updateBeforeInjectStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := [.request 2 5 .accepted, .endCompletions, .endPublications, .endEvents, .update])
    (q := fun tr => !decide (AfterUntilNever (entersStep2With 0) (dequeuesEvent 0) isUpdate tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.2.2.1 0] at hq

/-! ### A step 2 entered while closed (line 5's exemption, AC3) -/

/-- An executor whose step 2 returns at once while the executor is closed or stopped, leaving the
queued events in the queue (Java's and TypeScript's `processExternalEvents`, `if (closed) return`,
the events discarded when the loop ends). -/
def exec001_closedSkipStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents =>
      if s.mode.closing then
        (xstep C { s with eq := [] } .endEvents).map fun s' => { s' with eq := s.eq }
      else xstep C s .endEvents
  | l => xstep C s l

/-- The trigger of line 5 without the closed exemption: the step enters step 2 with the event of
ticket `k` queued, whatever the mode. -/
def exec001_entersStep2Any {N T : Type} (k : Nat) (e : XStep N T) : Bool :=
  e.2.2.phase == .events && e.1.phase != .events && (e.2.2.eq.map Prod.fst).contains k

/-- Line 5's exemption is load-bearing: on the run of a Java-like executor whose step 2 is entered
after a close, with the event of ticket `0` queued, and ends at once with the event still queued,
followed by the update, line 5 holds, and the reading without the exemption (trigger
`exec001_entersStep2Any`) fails. -/
theorem exec001_closedStep2_run :
    ∃ tr, XRun (fun C s l s' => exec001_closedSkipStep C s l = some s') (exec001_cfg false)
        (xinit exec001_m1 0) tr ∧
      AfterUntilNever (entersStep2With 0) (dequeuesEvent 0) isUpdate tr ∧
      ¬ AfterUntilNever (exec001_entersStep2Any 0) (dequeuesEvent 0) isUpdate tr := by
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_closedSkipStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := [.request 2 5 .accepted, .close, .endCompletions, .endPublications, .endEvents,
      .update])
    (q := fun tr => decide (AfterUntilNever (entersStep2With 0) (dequeuesEvent 0) isUpdate tr) &&
      !decide (AfterUntilNever (exec001_entersStep2Any 0) (dequeuesEvent 0) isUpdate tr))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    at hq
  exact ⟨tr, hr, hq⟩

/-! ### Violation: a reap that keeps the clock, and a pass on the earliest bound (line 6) -/

/-- An executor whose deadline step reports the reaped names but keeps their clocks, and whose
pass orders every armed transition past its earliest bound (without the expiry test of the
glossary term Ready). -/
def exec001_reapWithoutDisarmStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .deadline ns => (xstep C s (.deadline ns)).map fun s' => { s' with st := s.st }
  | .begin => (xstep C s .begin).map fun s' =>
      { s' with order := C.X.net.transitions.filter fun u =>
          (viewAt s s.cyc).armed u && decide ((C.X.timing u).earliest ≤ (viewAt s s.cyc).elapsed u) }
  | l => xstep C s l

/-- The executor of `exec001_reapWithoutDisarmStep`. -/
def exec001_reapWithoutDisarm {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_reapWithoutDisarmStep C s l = some s'

/-- ✗ Starting a reaped transition in the cycle that reaped it violates EXEC-001 (line 6): `u`
(`Window(3, 5)`) is armed at `0`, the clock jumps to `6`, the deadline step reaps `u` but keeps its
clock, and the pass starts it. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_reapWithoutDisarm :
    ¬ EXEC_001 (exec001_reapWithoutDisarm (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_reapWithoutDisarmStep)
    (C := exec001_cW) (s := xinit exec001_m1 0)
    (ls := exec001_quiet ++ [.begin, .endPass, .wake, .delay 6, .endCompletions,
      .endPublications, .endEvents, .update, .deadline ["u"], .begin, .start "u" false])
    (q := fun tr => !decide (AfterUntilNever (reapsName "u") isUpdate (startsName "u") tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.2.2.2.1 "u"] at hq

/-! ### Violation: the wait settles a completion and sleeps again (line 7) -/

/-- An executor whose wait, after committing a completion that arrived, goes back to sleep
without a new cycle. -/
def exec001_parkAfterSettleStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s' =>
      if s.phase = .await then { s' with phase := .await } else s'
  | l => xstep C s l

/-- The executor of `exec001_parkAfterSettleStep`. -/
def exec001_parkAfterSettle {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_parkAfterSettleStep C s l = some s'

/-- ✗ Waiting again after a deposit, with no update, violates EXEC-001 (line 7): `t` starts, the
next pass starts nothing and the loop waits; `t` returns `8` for place `1`, the wait commits it
and parks again, with `w` enabled and never armed. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_parkAfterSettle :
    ¬ EXEC_001 (exec001_parkAfterSettle (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_parkAfterSettleStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := exec001_quiet ++ [.begin, .start "t" false, .endPass] ++ exec001_quiet ++
      [.begin, .endPass, .write 0 1 8, .ret 0 true, .commit 0, .park none])
    (q := fun tr => !decide (AfterUntilNever (writesMarking (exec001_cfg false)) isUpdate isPark tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.2.2.2.2] at hq

/-! ### Violation: the pass ends in the wait after a synchronous deposit (line 7) -/

/-- An executor that decides to wait after the pass from the dirty bits consumption sets, and
whose synchronous fast path deposits without marking its place dirty: after a pass that started
something, it goes to the wait when no transition of the net consumes (Java's
`processSyncOutput` if it added the token without `deposit`'s dirty bit, `hasDirtyBits()` then
false). -/
def exec001_passDepositParkStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPass =>
      if s.phase = .pass && liveB C s && s.order.isEmpty && passFree s then
        some { s with phase := if s.started && C.X.net.transitions.any consumes then .completions
                               else .await }
      else none
  | l => xstep C s l

/-- The executor of `exec001_passDepositParkStep`. -/
def exec001_passDepositPark {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_passDepositParkStep C s l = some s'

/-- ✗ Waiting after a synchronous deposit inside the pass violates EXEC-001 (line 7): on the net
where nothing consumes, the update arms `g`, the pass starts it synchronously, its action writes
`8` to place `1` and returns, the pass commits it, and the loop parks with `r` enabled and never
armed. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_passDepositPark :
    ¬ EXEC_001 (exec001_passDepositPark (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_passDepositParkStep)
    (C := exec001_cNC) (s := xinit exec001_m0 0)
    (ls := exec001_quiet ++ [.begin, .start "g" true, .write 0 1 8, .ret 0 true, .commit 0,
      .endPass, .park none])
    (q := fun tr => !decide (AfterUntilNever (writesMarking exec001_cNC) isUpdate isPark tr))
    (by decide +kernel)
  simp [((h _).1 _ tr hr).2.2.2.2.2.2] at hq

/-! ### Violation: an update that re-evaluates nothing (line 8) -/

/-- An executor whose enablement update runs in its place in the cycle but keeps every clock
status (a dirty set cleared before it is read). -/
def exec001_emptyUpdateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s' => { s' with st := s.st }
  | l => xstep C s l

/-- The executor of `exec001_emptyUpdateStep`. -/
def exec001_emptyUpdate {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec001_emptyUpdateStep C s l = some s'

/-- ✗ An update that arms nothing violates EXEC-001 (line 8): on the untimed net with one token
in `0`, the first update leaves `t`, enabled and not in flight, without a clock and not
reaped. -/
@[evidence forbids EXEC_001]
theorem EXEC_001_forbids_emptyUpdate :
    ¬ EXEC_001 (exec001_emptyUpdate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := exec001_emptyUpdateStep)
    (C := exec001_cfg false) (s := xinit exec001_m1 0)
    (ls := [.endCompletions, .endPublications, .endEvents, .update])
    (q := fun tr => tr.any fun e => isUpdate e && e.2.2.st "t" == .off &&
      enabledNA (qCount e.2.2.M) exec001_t.core && !inFlightN e.2.2 "t")
    (by decide +kernel)
  obtain ⟨⟨s, l, s'⟩, he, hb⟩ := List.any_eq_true.1 hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨hu, hoff⟩, hen⟩, hfl⟩ := hb
  have hl : l = .update := by cases l <;> simp_all [isUpdate]
  subst hl
  have hx := (h (exec001_cfg false)).2 s s' (Exec001.run_mem hr _ he) "t" exec001_t rfl
  rcases hx.1 hen (Or.inr (by simp [InFlight, hfl])) with ha | ha
  · simp [ArmedE, armedB, exec001_t, hoff, stampOf] at ha
  · simp [ReapedE, exec001_t, hoff] at ha

/-! ### Step 3's permission (kind Q) -/

/-- Step 3's clause "Only transitions affected by token changes need re-evaluation" is a
permission: after the dirty scan every enabled bit equals the full enablement check, so
re-evaluating only the dirty transitions gives what the reference's full re-evaluation gives. A
citation of `updateEnablement_sync` (`Enablement.lean`). -/
@[evidence cites "EXEC-001" "step 3's permission 'Only transitions affected by token changes need re-evaluation': after the dirty scan every enabled bit equals canEnable, so re-evaluating only the dirty transitions gives the enablement a full re-evaluation gives (the reference update); bit granularity, untimed enablement"]
theorem exec001_dirty_set_exact {net : Libpetri.Net} {st : Libpetri.PBState}
    (hsync : Libpetri.EnabledSync net st) :
    ∀ tid t, net[tid]? = some t →
      (Libpetri.updateEnablement net st).enabled tid = Libpetri.canEnable st.ring t :=
  Libpetri.updateEnablement_sync hsync

end Libpetri.Spec
