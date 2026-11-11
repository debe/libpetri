import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# EXEC-030: Action failure (`spec/04-execution-model.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). A firing that fails settles
in a `fail i` step: its action threw or returned an error, or output validation or the join-relay
check rejected its outcome ([EXEC-021]). The requirement is a predicate over an abstract executor
`R : XRel N T` (glossary `GlossaryExec.lean`): a fail step leaves the marking as it is (no
rollback), takes the failed firing and its queued outcome out, leaves every other firing and
every other queued outcome as it was, and does not end the run, change the lifecycle mode, touch
the clock status of any transition or cut short the firing pass under way.

The evidence checks it against the reference executor and against thirteen wrong executors, one
per part of a line: a rollback, a failed firing kept in flight, a failure that abandons the other
firings of the same transition, one that adds a firing, one that drops the other queued outcomes,
one that leaves the failed firing's own outcome queued, one that ends the run, one that stops the
executor, one that reaps the failed transition's clock, one that leaves the firing pass, one that
abandons the rest of the firing pass, one that hides pass-visible tokens, and one that forgets
that the pass started a transition.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-030: Action Failure -/

requirement EXEC_030
  id "EXEC-030"
  title "Action Failure"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "If an action throws an exception or returns an error, the executor:"
        "Emits a TransitionFailed event with error details."
        "Does NOT restore consumed input tokens (no rollback)."
        "The transition is no longer in-flight."
        "Execution continues with remaining transitions."
        "A firing fails when its action throws an exception or returns an error, or when output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021])."
        "*If* a firing fails, *then* the executor *shall* emit a TransitionFailed event ([EVT-008]) and *shall not* change the marking: it *shall not* restore the tokens the firing consumed and *shall not* deposit any token its action produced at completion."
        "*If* a firing fails, *then* the executor *shall* remove that firing from the firings in flight and its outcome from the queued outcomes, and *shall* leave every other firing in flight as it was and the other queued outcomes as they were, in the order they arrived."
        "*Where* an executor starts a transition again while an earlier firing of it is in flight ([CONC-002]), *if* one of those firings fails, *then* the executor *shall* leave the other firings of that transition in flight."
        "*If* a firing fails, *then* the executor *shall not* end the run and *shall not* change its lifecycle mode, and a failure inside a firing pass *shall* leave the pass to go on with its remaining transitions."
        "*If* a firing fails, *then* the executor *shall* leave the clock of every transition as it was, so that the next enablement update ([EXEC-001] step 3) evaluates the transition of the failed firing as it evaluates any other transition."
        "A fault of the host runtime itself is not an action failure: in Java, a `VirtualMachineError` or a `LinkageError` thrown inside a firing ends the run with that error, which [EXEC-041] requires the caller to be able to tell apart from quiescence."
  reading "For every executor R, every configuration C and every firing identity i, a fail step of i:"
          "leaves the marking unchanged;"
          "leaves no firing with identity i in flight;"
          "leaves every other firing in flight exactly when it was in flight before, with the same record, and leaves as the completion queue the queue before with its first entry i removed, so the failed firing's outcome is no longer queued and the other entries keep their order and number;"
          "leaves the loop running (its phase is not a finished phase), the lifecycle mode as it was and the clock status of every transition as it was, and a fail step taken inside a firing pass leaves the loop in the pass with the same remaining order, the same tokens hidden from the pass and the same record of whether the pass started a transition."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass and settles in a later step (in step 1, on the wake of the wait, or inside the pass for a synchronous action); the outside step ret i false is its action throwing or returning an error. The witness is the reference executor RefExec (Reference/Exec.lean), the graph of a step function checked rule by rule against the Rust executor."
          "Naming: a failed firing is one settled by a fail step (label fail i), the label EXEC-021 also uses. The model has one fail label for the three causes the definition sentence lists: the action failed (outcome err), output validation or the join-relay check rejected a returned emission, or the join-relay check rejected a timeout outcome. Which steps are fail steps and why is EXEC-021's line 3; this block states what a fail step does, whatever its cause, so the lines also hold for a firing failed by validation, as EXEC-021's third shall sentence and AC5 say. 'Firing' is read per firing identity (XSt.nextId gives each firing its own), so 'the firing' is unique in every reachable state."
          "The lead-in and item 1, and the first half of the first shall sentence ('shall emit a TransitionFailed event'): the event kind the fail label carries (design table R-EXEC-8). The event, its payload and that no other step emits it are EVT-008's, on the event model of wave W7. AC1 (TransitionFailed with error message and type) is that event's payload, EVT-008's subject (ruling D38 (a): payload companions for Java and TypeScript; Rust's event carries one error string and no type); not encoded here."
          "Item 2, AC2 and the rest of the first shall sentence are line 1: the fail step leaves the marking as it is, so the tokens the firing consumed at its start stay consumed and nothing the action produced is deposited by it (EXEC_030_forbids_failRestores). That no later step deposits the failed firing's produced tokens follows from line 2 and is EXEC-031's corollary and EXEC-020's companion line; that tokens the action published before it failed stay in the marking, and a publication still queued is still deposited, is EXEC-021's line 2 (ruling D17)."
          "Item 3 and the first half of the second shall sentence are line 2: after the fail step no firing with identity i is in flight (EXEC_030_forbids_staysInFlight; with the failed firing kept in flight the run never reaches rest, EXEC-040). 'The transition is no longer in-flight' is read per firing, as the sentence on re-entrant executors says: with Cfg.reentrant (ruling D8 (b), Rust and Python) a second firing of the same transition stays in flight (EXEC_030_nonvacuous, part 4), and a failure that takes every firing of the transition out of flight violates line 3 (EXEC_030_forbids_abandonsSiblings)."
          "The rest of the second shall sentence and the sentence on re-entrant executors are line 3: every other firing keeps its record and stays in flight (EXEC_030_forbids_abandonsSiblings) and no firing is added (EXEC_030_forbids_addsFiring: a copy of the failed firing put back in flight under another identity), the queued outcome of every other firing stays queued in arrival order, as step 1 settles them (EXEC_030_forbids_dropsQueued: an executor that drops them would leave those firings in flight with an outcome that is never processed), and the failed firing's own outcome leaves the queue with it (EXEC_030_forbids_keepsOwnEntry: an entry with no firing behind it can never be settled, so step 1 never ends and the run neither finishes nor goes on). The queue is pinned as the old queue with the first entry i erased rather than as 'i is not queued': in every reachable state an identity is queued at most once, and the erase form is the one a step can be held to."
          "Item 4, AC3 and the third shall sentence are line 4 and lines 2 and 3 together: the fail step does not finish the run (EXEC_030_forbids_ends), does not move the executor to a closing mode (EXEC_030_forbids_stops: a stopped mode ends the run at the top of the next cycle, ENV-015), and a failure inside the firing pass, a synchronous action failing there, leaves the pass as it was for the transitions still to come: the loop stays in the pass (EXEC_030_forbids_leavesPass: a fail step that returns the loop to step 1 with the order kept), the rest of its order (EXEC_030_forbids_abortsPass), the tokens deposited earlier in the pass that it does not see (EXEC_030_forbids_hidesTokens: hiding more makes the remaining heads lose) and its record that a transition started (EXEC_030_forbids_forgetsStart: the loop would wait instead of running the next cycle, and could park with a transition enabled). That other transitions do go on firing after a failure is a property of runs, not of one step: EXEC_030_nonvacuous decides three reference runs in which a transition starts after a failure, once later in the same pass, once in a later cycle, and once the failed transition itself in the next cycle."
          "The fourth shall sentence is line 4's clock clause: the fail step leaves the clock status of every transition as it was (EXEC_030_forbids_reaps: a failure that marks the failed transition reaped, the Java and TypeScript failure branch without its markTransitionDirty call, keeps it from being armed again until one of its arc places is written, and the run can finish quiescent with that transition enabled). Its 'so that' clause is the consequence on runs, EXEC_030_nonvacuous part 5: non-re-entrant, t fails while its input place still holds a token, and the next cycle starts t again."
          "That an executor offers a fail step at all is coverage, not a line here. The consistency theorem's ValidatedBy offers one for a returned emission that output validation rejects; a clause offering one for an err outcome and for an outcome the join-relay check rejects is ExecFailCovers, a clause of the consistency theorem's coverage conjunct ExecCoversW5 (ConsistencyExec.lean), which the reference meets (refExec_failCovers). The other fields of the state are not fixed by this block: a publication still queued is EXEC-021's line 2, the event queue and the identity supply are the subjects of ENV-003 and EXEC-001."
          "The host fault sentence (ruling D20, R-EXEC-7 (a)): a fault of the host runtime is not an action failure and is outside the model, which has no label for it. Java rethrows a VirtualMachineError or LinkageError from the firing boundary and the run ends (java/src/main/java/org/libpetri/runtime/ExecutorSupport.java:230-234, BitmapNetExecutor.java:1610); that such an end is distinguishable to the caller is EXEC-041's subject. A failure the action reports through its returned future or promise is an action failure in every runtime."
          "Also outside the model: a throw of the host's own callbacks during a start, such as the event store or a correlation-key function throwing while Java consumes the inputs (BitmapNetExecutor.java:1576-1613), which Java contains as a failure of a partly consumed firing, or an event store throwing on TokenAdded while Java deposits a completion (processSyncOutput and processCompletedTransitions, BitmapNetExecutor.java:1788-1817 and 1897-1927), which Java reports as a failure of a partly deposited firing, its deposited prefix left in the marking. No spec sentence describes either case, and the model's start and deposit are atomic, so line 1 reads only the fail steps of the model."
          "A firing abandoned by a stop on a terminal place (EXEC-042) or by an immediate termination (ENV-015) is not settled by a step 1 fail; whether and when an abandoned firing is settled is those requirements' subject. The lines here constrain fail steps only, wherever they occur."
          "The test derivation (an action throws, the failure event is emitted, the consumed tokens are not restored, the net continues) is EXEC_030_nonvacuous: transition t's action fails, place 0 stays empty, and transition u starts afterwards; the event is EVT-008's."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C i,
      (on (fun s s' => R C s (.fail i) s'), shall (fun s s' => s'.M = s.M)) ∧
      (on (fun s s' => R C s (.fail i) s'), shall (fun _ s' => ∀ f ∈ s'.fl, f.id ≠ i)) ∧
      (on (fun s s' => R C s (.fail i) s'), shall (fun s s' =>
        (∀ f, f.id ≠ i → (f ∈ s'.fl ↔ f ∈ s.fl)) ∧ s'.cq = s.cq.erase i)) ∧
      (on (fun s s' => R C s (.fail i) s'), shall (fun s s' =>
        isExecPhase s'.phase = true ∧ s'.mode = s.mode ∧ s'.st = s.st ∧
        (s.phase = .pass → s'.phase = .pass ∧ s'.order = s.order ∧ s'.delta = s.delta ∧
          s'.started = s.started)))

/- The pinned readable form of EXEC-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_030 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (i : ℕ),
    (on fun s s' => R C s (XLbl.fail i) s', shall fun s s' => s'.M = s.M) ∧
      (on fun s s' => R C s (XLbl.fail i) s', shall fun x s' => ∀ f ∈ s'.fl, f.id ≠ i) ∧
        (on fun s s' => R C s (XLbl.fail i) s', shall fun s s' =>
            (∀ (f : Firing N T), f.id ≠ i → (f ∈ s'.fl ↔ f ∈ s.fl)) ∧ s'.cq = s.cq.erase i) ∧
          on fun s s' => R C s (XLbl.fail i) s', shall fun s s' =>
            isExecPhase s'.phase = true ∧
              s'.mode = s.mode ∧
                s'.st = s.st ∧
                  (s.phase = Phase.pass →
                    s'.phase = Phase.pass ∧ s'.order = s.order ∧ s'.delta = s.delta ∧ s'.started = s.started)
-/
#guard_msgs in #print EXEC_030

/-! ### The reference -/

/-- ✓ The reference executor satisfies EXEC-030: its `fail` rule is `settle`
(`failStep_some`), which keeps the marking, the mode and the pass, filters firing `i` out of the
firings in flight and erases `i` from the completion queue, and keeps the clock status, the hidden tokens and the
started flag; the settle guard (`canSettle`)
requires a running loop. -/
@[evidence holds EXEC_030]
theorem EXEC_030_reference {N T : Type} [DecidableEq N] :
    EXEC_030 (RefExec (N := N) (T := T)) := by
  intro C i
  refine ⟨fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_⟩
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    rfl
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    intro g hg
    simp only [settle, List.mem_filter, bne_iff_ne, ne_eq] at hg
    exact hg.2
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    refine ⟨fun g hg => ?_, rfl⟩
    simp [settle, List.mem_filter, hg]
  · obtain ⟨f, -, hc, -, rfl⟩ := failStep_some h
    simp only [canSettle, Bool.and_eq_true] at hc
    have hx := hc.1.1.1
    refine ⟨?_, rfl, rfl, fun hp => ?_⟩
    · simp only [settle]
      split
      · rfl
      · exact hx
    · simp [settle, hp]

/-! ### Examples

Two transitions: `t` takes a token from place `0` and outputs to place `1`, `u` takes a token from
place `2` and outputs to place `3`. Validation and the relay check accept everything, so every
fail step below is an action failure. -/

/-- Transition `t`: one token from `0`, output `1`. -/
def exec030_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- Transition `u`: one token from `2`, output `3`. -/
def exec030_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨2, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 3) }

/-- The configuration of the examples; `re` is re-entrancy (ruling D8 (b)). -/
def exec030_cfg (re : Bool) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [exec030_t, exec030_u] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := re,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The non-re-entrant configuration (Java, TypeScript). -/
def exec030_c : Cfg Nat Nat := exec030_cfg false

/-- The re-entrant configuration (Rust, Python). -/
def exec030_cR : Cfg Nat Nat := exec030_cfg true

/-- The initial state: `7` in place `0`, `8` and `9` in place `2`. -/
def exec030_s0 : XSt Nat Nat :=
  xinit (fun p => if p = 0 then [7] else if p = 2 then [8, 9] else []) 0

/-- One cycle up to the start of the firing pass. -/
def exec030_cyc : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- Both transitions start asynchronously (firings `0` and `1`); `t`'s action fails, `u`'s writes
`5` to `3` and returns. Both outcomes are queued. -/
def exec030_async : List (XLbl Nat Nat) :=
  exec030_cyc ++ [.start "t" false, .start "u" false, .endPass, .ret 0 false, .write 1 3 5,
    .ret 1 true]

/-- `t` starts synchronously (firing `0`) and its action fails inside the pass; `u` is still in
the pass's order. -/
def exec030_sync : List (XLbl Nat Nat) :=
  exec030_cyc ++ [.start "t" true, .ret 0 false]

/-- Re-entrant: `t` and `u` start (firings `0` and `1`); in the next cycle `u` starts again
(firing `2`), and the action of firing `1` fails. -/
def exec030_sib : List (XLbl Nat Nat) :=
  exec030_cyc ++ [.start "t" false, .start "u" false, .endPass] ++ exec030_cyc ++
    [.start "u" false, .endPass, .ret 1 false]

/-- Two tokens in place `0`, nothing elsewhere. -/
def exec030_s2 : XSt Nat Nat := xinit (fun p => if p = 0 then [7, 6] else []) 0

/-- From `exec030_s2`: `t` starts asynchronously (firing `0`) and its action fails. -/
def exec030_again : List (XLbl Nat Nat) :=
  exec030_cyc ++ [.start "t" false, .endPass, .ret 0 false]

/-- The reference state after `ls` from `exec030_s0`. -/
def exec030_at (C : Cfg Nat Nat) (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  xrun C exec030_s0 ls

/-- Read three consecutive reference segments off a decided check: a step `l₁`, a run `mid`,
a step `l₂`. -/
theorem exec030_chain {C : Cfg Nat Nat} {o : Option (XSt Nat Nat)} {l₁ l₂ : XLbl Nat Nat}
    {mid : List (XLbl Nat Nat)}
    (h : (o.bind fun s => (xstep C s l₁).bind fun s₁ => (xrun C s₁ mid).bind fun s₂ =>
      (xstep C s₂ l₂).map fun _ => true) = some true) :
    ∃ s s₁ s₂ s₃, o = some s ∧ RefExec C s l₁ s₁ ∧ xrun C s₁ mid = some s₂ ∧
      RefExec C s₂ l₂ s₃ := by
  cases ho : o with
  | none => simp [ho] at h
  | some s =>
    cases h₁ : xstep C s l₁ with
    | none => simp [ho, h₁] at h
    | some s₁ =>
      cases h₂ : xrun C s₁ mid with
      | none => simp [ho, h₁, h₂] at h
      | some s₂ =>
        cases h₃ : xstep C s₂ l₂ with
        | none => simp [ho, h₁, h₂, h₃] at h
        | some s₃ => exact ⟨s, s₁, s₂, s₃, rfl, h₁, h₂, h₃⟩

/-! ### Violation: rollback -/

/-- An executor whose `fail` step puts the consumed tokens back at the head of their places. -/
def exec030_failRestoresStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with M := fun p => f.deliv.inputs p ++ s₁.M p }
  | l => xstep C s l

/-- The executor of `exec030_failRestoresStep`. -/
def exec030_failRestores {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_failRestoresStep C s l = some s'

/-- ✗ A rollback violates EXEC-030 (line 1, item 2, AC2): `t`'s action fails and the fail step
puts the consumed `7` back into place `0`. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_failRestores :
    ¬ EXEC_030 (exec030_failRestores (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_failRestoresStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := (h exec030_c 0).1 s s' hs
  simp [this] at hp

/-! ### Violation: the failed firing stays in flight -/

/-- An executor whose `fail` step settles the outcome but keeps the firing in flight. -/
def exec030_staysInFlightStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with fl := s.fl }
  | l => xstep C s l

/-- The executor of `exec030_staysInFlightStep`. -/
def exec030_staysInFlight {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_staysInFlightStep C s l = some s'

/-- ✗ Keeping the failed firing in flight violates EXEC-030 (line 2, item 3): after `t`'s
failure, firing `0` is still in flight. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_staysInFlight :
    ¬ EXEC_030 (exec030_staysInFlight (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_staysInFlightStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun _ s' => s'.fl.any (·.id == 0)) (by decide)
  obtain ⟨f, hf, hid⟩ := List.any_eq_true.mp hp
  exact (h exec030_c 0).2.1 s s' hs f hf (by simpa using hid)

/-! ### Violation: the failure abandons the other firings of the same transition -/

/-- An executor whose `fail` step also takes every other firing of the failed firing's
transition out of flight: "the transition is no longer in-flight" read per transition. -/
def exec030_abandonsSiblingsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with fl := s₁.fl.filter (·.t.core.name != f.t.core.name) }
  | l => xstep C s l

/-- The executor of `exec030_abandonsSiblingsStep`. -/
def exec030_abandonsSiblings {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_abandonsSiblingsStep C s l = some s'

/-- ✗ Abandoning the other firings of the transition violates EXEC-030 (line 3): re-entrant,
`u` has firings `1` and `2` in flight, firing `1` fails, and firing `2` leaves the firings in
flight with it. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_abandonsSiblings :
    ¬ EXEC_030 (exec030_abandonsSiblings (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_abandonsSiblingsStep (C := exec030_cR)
    (o := exec030_at exec030_cR exec030_sib) (l := .fail 1)
    (p := fun s s' => s.fl.any (·.id == 2) && !s'.fl.any (·.id == 2)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.any_eq_false,
    beq_iff_eq] at hp
  obtain ⟨⟨f, hf, hid⟩, hn⟩ := hp
  have := ((h exec030_cR 1).2.2.1 s s' hs).1 f (by omega)
  exact hn f (this.mpr hf) hid

/-! ### Violation: the failure drops the other queued outcomes -/

/-- An executor whose `fail` step clears the whole completion queue. -/
def exec030_dropsQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with cq := [] }
  | l => xstep C s l

/-- The executor of `exec030_dropsQueuedStep`. -/
def exec030_dropsQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_dropsQueuedStep C s l = some s'

/-- ✗ Dropping the other queued outcomes violates EXEC-030 (line 3): `u`'s outcome (firing `1`)
is queued when `t`'s failure is processed, and the fail step drops it. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_dropsQueued :
    ¬ EXEC_030 (exec030_dropsQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_dropsQueuedStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s.cq.contains 1 && !s'.cq.contains 1) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have h1 : 1 ∈ s.cq := by simpa using hp.1
  have h2 : 1 ∉ s'.cq := by simpa using hp.2
  rw [((h exec030_c 0).2.2.1 s s' hs).2] at h2
  exact h2 ((List.mem_erase_of_ne (by omega)).mpr h1)

/-! ### Violation: the failed firing's own outcome stays queued -/

/-- An executor whose `fail` step takes the firing out of flight but leaves its entry in the
completion queue: the TypeScript failure branch leaving before the queue bookkeeping (`return`
for `continue`), or a Rust failure handled before its completion message is taken. -/
def exec030_keepsOwnEntryStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with cq := s.cq }
  | l => xstep C s l

/-- The executor of `exec030_keepsOwnEntryStep`. -/
def exec030_keepsOwnEntry {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_keepsOwnEntryStep C s l = some s'

/-- ✗ Leaving the failed firing's outcome queued violates EXEC-030 (line 3): after `t`'s failure
`0` is still queued with no firing behind it, so nothing settles it and step 1 never ends. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_keepsOwnEntry :
    ¬ EXEC_030 (exec030_keepsOwnEntry (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_keepsOwnEntryStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s'.cq != s.cq.erase 0) (by decide)
  simp [((h exec030_c 0).2.2.1 s s' hs).2] at hp

/-! ### Violation: the failure ends the run -/

/-- An executor whose `fail` step finishes the run. -/
def exec030_endsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with phase := .done .quiescent }
  | l => xstep C s l

/-- The executor of `exec030_endsStep`. -/
def exec030_ends {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_endsStep C s l = some s'

/-- ✗ Ending the run on a failure violates EXEC-030 (line 4, item 4, AC3). -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_ends : ¬ EXEC_030 (exec030_ends (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_endsStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun _ s' => !isExecPhase s'.phase) (by decide)
  have := ((h exec030_c 0).2.2.2 s s' hs).1
  simp [this] at hp

/-! ### Violation: the failure stops the executor -/

/-- An executor whose `fail` step moves it to the stopped mode, which ends the run at the top of
the next cycle ([ENV-015]). -/
def exec030_stopsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with mode := .stopped }
  | l => xstep C s l

/-- The executor of `exec030_stopsStep`. -/
def exec030_stops {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_stopsStep C s l = some s'

/-- ✗ Stopping the executor on a failure violates EXEC-030 (line 4, the lifecycle mode). -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_stops : ¬ EXEC_030 (exec030_stops (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_stopsStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s'.mode != s.mode) (by decide)
  have := ((h exec030_c 0).2.2.2 s s' hs).2.1
  simp [this] at hp

/-! ### Violation: the failure reaps the failed transition's clock -/

/-- An executor whose `fail` step marks the failed firing's transition reaped: the Java and
TypeScript failure branch without its `markTransitionDirty` call. Only a write of one of its arc
places turns the status off again (ruling D6), so the transition is not armed again while it
stays enabled. -/
def exec030_reapsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with st := fun n => if n = f.t.core.name then .reaped else s₁.st n }
  | l => xstep C s l

/-- The executor of `exec030_reapsStep`. -/
def exec030_reaps {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_reapsStep C s l = some s'

/-- ✗ Reaping the failed transition's clock violates EXEC-030 (line 4, the clock clause): `t`'s
action fails and the fail step changes `t`'s status from off to reaped. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_reaps : ¬ EXEC_030 (exec030_reaps (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_reapsStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s'.st "t" != s.st "t") (by decide)
  have := ((h exec030_c 0).2.2.2 s s' hs).2.2.1
  simp [this] at hp

/-! ### Violation: the failure abandons the rest of the firing pass -/

/-- An executor whose `fail` step inside the pass drops the rest of the pass's order. -/
def exec030_abortsPassStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with order := [] }
  | l => xstep C s l

/-- The executor of `exec030_abortsPassStep`. -/
def exec030_abortsPass {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_abortsPassStep C s l = some s'

/-- ✗ Abandoning the rest of the pass on a failure violates EXEC-030 (line 4, "execution
continues with remaining transitions"): `t`'s synchronous action fails inside the pass while `u`
is still in the pass's order, and the fail step drops `u` from it. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_abortsPass : ¬ EXEC_030 (exec030_abortsPass (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_abortsPassStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_sync) (l := .fail 0)
    (p := fun s s' => s.phase == .pass && s'.order.length != s.order.length) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  have := (((h exec030_c 0).2.2.2 s s' hs).2.2.2 hp.1).2.1
  exact hp.2 (by rw [this])

/-! ### Violation: the failure hides pass-visible tokens -/

/-- An executor whose `fail` step adds two to the same-pass tail of place `2`, so the pass sees
two tokens fewer there. -/
def exec030_hidesTokensStep {C : Cfg Nat Nat} (s : XSt Nat Nat) :
    XLbl Nat Nat → Option (XSt Nat Nat)
  | .fail i => (xstep C s (.fail i)).map fun s₁ =>
      { s₁ with delta := fun p => if p = 2 then s₁.delta p + 2 else s₁.delta p }
  | l => xstep C s l

/-- The executor of `exec030_hidesTokensStep`. -/
def exec030_hidesTokens : XRel Nat Nat :=
  fun C s l s' => exec030_hidesTokensStep (C := C) s l = some s'

/-- ✗ Hiding tokens from the pass on a failure violates EXEC-030 (line 4, the pass goes on):
`t`'s synchronous action fails inside the pass and the fail step hides both tokens of place `2`,
so `u`, still in the pass's order, would lose. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_hidesTokens : ¬ EXEC_030 exec030_hidesTokens := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (fun C s l => exec030_hidesTokensStep (C := C) s l)
    (C := exec030_c) (o := exec030_at exec030_c exec030_sync) (l := .fail 0)
    (p := fun s s' => s.phase == .pass && s'.delta 2 != s.delta 2) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  have := (((h exec030_c 0).2.2.2 s s' hs).2.2.2 hp.1).2.2.1
  exact hp.2 (by rw [this])

/-! ### Violation: the failure ends the firing pass -/

/-- An executor whose `fail` step moves the loop to step 1 (phase `completions`), keeping the
pass's order. -/
def exec030_leavesPassStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with phase := .completions }
  | l => xstep C s l

/-- The executor of `exec030_leavesPassStep`. -/
def exec030_leavesPass {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_leavesPassStep C s l = some s'

/-- ✗ Leaving the firing pass on a failure violates EXEC-030 (line 4, the phase clause): `t`'s
synchronous action fails inside the pass and the fail step returns the loop to step 1, an
executing phase, with the pass's order kept, so only the phase conjunct catches it. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_leavesPass : ¬ EXEC_030 (exec030_leavesPass (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_leavesPassStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_sync) (l := .fail 0)
    (p := fun s s' => s.phase == .pass && s'.phase != .pass) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  exact hp.2 (((h exec030_c 0).2.2.2 s s' hs).2.2.2 hp.1).1

/-! ### Violation: the failure adds a firing -/

/-- An executor whose `fail` step of `i` puts a copy of the failed firing back in flight under the
identity `i + 100`. -/
def exec030_addsFiringStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with fl := s₁.fl ++ [{ f with id := i + 100 }] }
  | l => xstep C s l

/-- The executor of `exec030_addsFiringStep`. -/
def exec030_addsFiring {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_addsFiringStep C s l = some s'

/-- ✗ Adding a firing on a failure violates EXEC-030 (line 3, its backward direction): `t`'s
action fails and the fail step leaves a firing in flight, with another identity, that was not in
flight before. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_addsFiring : ¬ EXEC_030 (exec030_addsFiring (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_addsFiringStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_async) (l := .fail 0)
    (p := fun s s' => s'.fl.any fun g => g.id != 0 && !(s.fl.map (·.id)).contains g.id)
    (by decide)
  obtain ⟨g, hg, hp⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hp
  have hm := (((h exec030_c 0).2.2.1 s s' hs).1 g hp.1).mp hg
  have hc : (s.fl.map (·.id)).contains g.id = true := by
    simpa using List.mem_map_of_mem (f := (·.id)) hm
  rw [hp.2] at hc
  cases hc

/-! ### Violation: the failure forgets that the pass started a transition -/

/-- An executor whose `fail` step clears the pass's record that a transition started, so the
pass ends in the wait instead of a new cycle. -/
def exec030_forgetsStartStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with started := false }
  | l => xstep C s l

/-- The executor of `exec030_forgetsStartStep`. -/
def exec030_forgetsStart {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec030_forgetsStartStep C s l = some s'

/-- ✗ Forgetting the start on a failure violates EXEC-030 (line 4, the pass goes on): `t`'s
synchronous action fails inside the pass and the fail step clears the started flag its start
set. -/
@[evidence forbids EXEC_030]
theorem EXEC_030_forbids_forgetsStart :
    ¬ EXEC_030 (exec030_forgetsStart (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec030_forgetsStartStep (C := exec030_c)
    (o := exec030_at exec030_c exec030_sync) (l := .fail 0)
    (p := fun s s' => s.phase == .pass && s'.started != s.started) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  have := (((h exec030_c 0).2.2.2 s s' hs).2.2.2 hp.1).2.2.2
  exact hp.2 this

/-! ### Every line exercised -/

/-- Every line of EXEC-030 is exercised by the reference: (1) `t`'s action fails while `u`'s
outcome is queued, and the fail step leaves place `0` empty (nothing restored), takes firing `0`
out of flight and leaves firing `1` in flight with its outcome queued; (2) `u` then commits and,
in the next cycle, starts again (AC3, the test derivation); (3) `t`'s synchronous action fails
inside the pass and `u` starts later in the same pass (item 4); (4) re-entrant, a failure of one
firing of `u` leaves the other firing of `u` in flight (item 3, per firing); (5) non-re-entrant,
`t` fails while place `0` still holds a token, and the next cycle starts `t` again (the clock
clause). -/
@[evidence nonvacuous EXEC_030]
theorem EXEC_030_nonvacuous :
    (∃ s s', RefExec exec030_c s (.fail 0) s' ∧ s'.M 0 = [] ∧
      s'.fl.map (·.id) = [1] ∧ s'.cq = [1]) ∧
    (∃ s s₁ s₂ s₃, RefExec exec030_c s (.fail 0) s₁ ∧
      xrun exec030_c s₁ (.commit 1 :: exec030_cyc) = some s₂ ∧
      RefExec exec030_c s₂ (.start "u" false) s₃) ∧
    (∃ s s₁ s₂ s₃, s.phase = .pass ∧ RefExec exec030_c s (.fail 0) s₁ ∧
      xrun exec030_c s₁ [] = some s₂ ∧ RefExec exec030_c s₂ (.start "u" false) s₃) ∧
    (∃ s s', RefExec exec030_cR s (.fail 1) s' ∧ s'.fl.map (·.id) = [0, 2] ∧
      (s'.fl.map (·.t.core.name)) = ["t", "u"]) ∧
    (∃ s s₁ s₂ s₃, RefExec exec030_c s (.fail 0) s₁ ∧ xrun exec030_c s₁ exec030_cyc = some s₂ ∧
      RefExec exec030_c s₂ (.start "t" false) s₃) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec030_c)
      (o := exec030_at exec030_c exec030_async) (l := .fail 0)
      (p := fun _ s' => s'.M 0 == [] && s'.fl.map (·.id) == [1] && s'.cq == [1]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s₁, s₂, s₃, -, h₁, h₂, h₃⟩ := exec030_chain (C := exec030_c)
      (o := exec030_at exec030_c exec030_async) (l₁ := .fail 0)
      (mid := .commit 1 :: exec030_cyc) (l₂ := .start "u" false) (by decide)
    exact ⟨s, s₁, s₂, s₃, h₁, h₂, h₃⟩
  · have hc : ((exec030_at exec030_c exec030_sync).bind fun s =>
        (xstep exec030_c s (.fail 0)).bind fun s₁ => (xrun exec030_c s₁ []).bind fun s₂ =>
          (xstep exec030_c s₂ (.start "u" false)).map fun _ => s.phase == .pass) =
        some true := by decide
    obtain ⟨s, s₁, s₂, s₃, ho, h₁, h₂, h₃⟩ := exec030_chain (C := exec030_c)
      (o := exec030_at exec030_c exec030_sync) (l₁ := .fail 0) (mid := [])
      (l₂ := .start "u" false) (by decide)
    have hp : s.phase = .pass := by
      rw [ho] at hc
      simp only [Option.bind_some] at hc
      rw [h₁] at hc
      simp only [Option.bind_some] at hc
      rw [h₂] at hc
      simp only [Option.bind_some] at hc
      rw [h₃] at hc
      simpa using hc
    exact ⟨s, s₁, s₂, s₃, hp, h₁, h₂, h₃⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec030_cR)
      (o := exec030_at exec030_cR exec030_sib) (l := .fail 1)
      (p := fun _ s' => s'.fl.map (·.id) == [0, 2] && s'.fl.map (·.t.core.name) == ["t", "u"])
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s₁, s₂, s₃, -, h₁, h₂, h₃⟩ := exec030_chain (C := exec030_c)
      (o := xrun exec030_c exec030_s2 exec030_again) (l₁ := .fail 0) (mid := exec030_cyc)
      (l₂ := .start "t" false) (by decide)
    exact ⟨s, s₁, s₂, s₃, h₁, h₂, h₃⟩

end Libpetri.Spec
