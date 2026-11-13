import Libpetri.Spec.Req.EXEC_021
import Libpetri.Spec.Req.IO_015
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020
import Libpetri.Spec.Req.TIME_010
import Libpetri.Spec.Req.TIME_012
import Libpetri.Spec.Req.TIME_013
import Libpetri.Spec.Req.TIME_015
import Libpetri.Spec.Req.EXEC_001
import Libpetri.Spec.Req.EXEC_003
import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Req.EXEC_030
import Libpetri.Spec.Req.EXEC_031
import Libpetri.Spec.Req.EXEC_040
import Libpetri.Spec.Req.EXEC_041
import Libpetri.Spec.Req.EXEC_042
import Libpetri.Spec.Req.EXEC_cycle
import Libpetri.Spec.Req.TIME_014
import Libpetri.Spec.Req.TIME_cycle
import Libpetri.Spec.Req.CONC_001
import Libpetri.Spec.Req.CONC_002
import Libpetri.Spec.Req.CONC_003
import Libpetri.Spec.Req.CONC_005_cycle
import Libpetri.Spec.Req.CONC_010
import Libpetri.Spec.Req.ENV_002
import Libpetri.Spec.Req.ENV_003
import Libpetri.Spec.Req.ENV_004
import Libpetri.Spec.Req.ENV_005
import Libpetri.Spec.Req.ENV_006
import Libpetri.Spec.Req.ENV_010
import Libpetri.Spec.Req.ENV_011
import Libpetri.Spec.Req.ENV_013
import Libpetri.Spec.Req.ENV_014
import Libpetri.Spec.Req.ENV_015
import Libpetri.Spec.Req.ENV_016
import Libpetri.Reference.ExecLink

set_option linter.missingDocs true

/-!
# Consistency of the executor requirements

The target of this module is one theorem, `spec_consistent_exec`, that picks one witness for
every variable the execution, concurrency and environment blocks share with the Phase 1 blocks
and shows that every block holds of it: one output validator `V` (shared with IO-015), one queue
firing `Q` (shared with EXEC-010, EXEC-013 and EXEC-020), one timed step `R` (shared with the
TIME blocks) and one executor `E`, tied to them by agreement conjuncts, so that the result is one
model.

`spec_consistent_exec_sketch` is the theorem as wave W5 leaves it. Every executor block of the
wave (EXEC, CONC, ENV, TIME-014 and the cycle companions of EXEC-002, EXEC-010, EXEC-013,
EXEC-020, TIME-010, TIME-012, TIME-013, TIME-015 and CONC-005) holds of the one executor `E`, and
ENV-016 of `E` with its expiry handling `X`. The links:

* `ValidatedBy E V`: `E` settles every admitted completion as `V` decides;
* `QueueAgrees E Q` (`Reference/ExecLink.lean`, L2): a start, steps that leave the marking alone
  and the commit of that firing are one `Q` firing of the order head;
* `AtomicAgrees E R` (L3): a delay, a deadline step and an atomic firing segment of `E` are steps
  of `R` on the timed view.

Coverage keeps the conjunction from holding of an executor that takes no step
(`exec_coverage_excludes_empty`). `ExecCovers` (glossary, wave 0) offers the delay and the
return; `ExecCoversW5` adds the existence halves the W5 blocks leave to this theorem: the fail
step of EXEC-030, the expiry and the timeout deposit of EXEC-022, `finish quiescent` at rest
(EXEC-040), `finish terminal` at once (EXEC-042), the drain, finish and wake of ENV-011, `finish
closed` with nothing in flight (ENV-013), the snapshot answer of ENV-014, the stop of ENV-015 and
the orchestrator going on of CONC-002 (a pass begun from the test, the head of every order started
or passed over), the answers to injection requests (ENV-002, ENV-006, ENV-010), the injection of a
queued event (ENV-003, ENV-010), the way out of the wait (ENV-005, CONC-010, ENV-010), the commit
of an accepted completion at the head of the completion queue (EXEC-020) and, over the expiry
handling `X`, an outcome for every run-budget expiry (ENV-016). The close of ENV-013 is
offered by that ENV-016 clause with ENV-016's close line. Every block keeps its existence halves
out of its statement: blocks state safety, offers are coverage (the convention of
`GlossaryExec.lean`, the user's decision on review finding W5-SR-5). The witnesses are
`ioRefValidate`, `RefExec`, `refExpiry`, `RefQFire` and `RefTStep`.

`EXEC_042_build` is a block over the net builder, not the executor; it joins the net builder of
`joint_core_structure_sketch` (`ConsistencyStructure.lean`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

section Witness

variable {N T : Type} [DecidableEq N]

/-- The reference executor settles every admitted completion as the configured validator
decides: `commit` when it accepts (and the relay check accepts), `fail` when it rejects. -/
theorem refExec_validatedBy (V : OutputValidator N) : ValidatedBy (RefExec (T := T)) V := by
  intro C hC s i f e ⟨hf, he, hc⟩ hr
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h : (commitStep refXPol C s i).isSome = true := by
      unfold commitStep
      rw [hf]
      simp only [he]
      rw [if_pos (by simp [hc, hC, hv, hr, refXPol])]
      rfl
    exact Option.isSome_iff_exists.mp h
  · have h : (failStep refXPol C s i).isSome = true := by
      unfold failStep
      simp [hf, hc, failCause, he, hC, hv, refXPol]
    exact Option.isSome_iff_exists.mp h

/-- The reference executor covers the wave 0 outside steps: the clock always advances, and every
open firing can return either way. -/
theorem refExec_covers : ExecCovers (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s δ => ⟨_, rfl⟩, fun C s i f ok hf ho => ?_⟩
  have h : (retStep s i ok).isSome = true := by
    unfold retStep onOpen
    simp [hf, ho]
  exact Option.isSome_iff_exists.mp h

end Witness

/-! ## The coverage the W5 blocks leave to the consistency theorem -/

section Coverage

variable {N T : Type} [DecidableEq N]

/-- **Fail coverage** ([EXEC-030]): a firing whose outcome is queued and may be settled is failed
when its action failed, or when the join-relay check of [NU-054] rejects its returned emission or
its timeout outcome. A returned emission that output validation rejects is `ValidatedBy`'s. -/
def ExecFailCovers (E : XRel N T) : Prop :=
  ∀ C s i f, s.fl.find? (·.id == i) = some f → canSettle C s i f = true →
    (f.out = some .err ∨ (∃ e, f.out = some (.ok e) ∧ C.relay f.t f.deliv e = false) ∨
      ∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = false) →
    ∃ s', E C s (.fail i) s'

/-- **Finish coverage at rest** ([EXEC-040], the first shall sentence's "shall terminate"):
without environment places, `finish quiescent` is offered at every termination test with no
terminal place marked and at rest. -/
def Exec040Covers (E : XRel N T) : Prop :=
  ∀ C s, C.envs = [] → Live C s → s.phase = .test → Rest C s →
    ∃ s', E C s (.finish .quiescent) s'

/-- **Snapshot coverage** ([ENV-014], AC1 and AC2): a snapshot request is answered in every live
state at entry to the enablement update, in step 2 and in the wait. What the answer says is the
block's lines. -/
def Env014Covers (E : XRel N T) : Prop :=
  ∀ C s, Live C s → (s.phase = .events ∨ s.phase = .update ∨ s.phase = .await) →
    ∃ a s', E C s (.snapshot a) s'

/-- **Timeout coverage** ([EXEC-022]): the budget of an asynchronous firing whose spec has a
`Timeout` node can run out while its action has not reported, with every timeout outcome the
configuration accepts (ruling D18 (b): the expiry is a free outside step); and a recorded timeout
outcome that may be settled and that the join-relay check of [NU-054] accepts is deposited. -/
def Exec022Covers (E : XRel N T) : Prop :=
  (∀ C s i f e, s.fl.find? (·.id == i) = some f → f.out = none → f.sync = false →
    hasTimeoutB f.t = true → C.timeoutOut f.t f.deliv e = true →
    ∃ s', E C s (.expire i e) s') ∧
  (∀ C s i f e, s.fl.find? (·.id == i) = some f → canSettle C s i f = true →
    f.out = some (.timedOut e) → C.relay f.t f.deliv e = true →
    ∃ s', E C s (.tdeposit i) s')

/-- **Finish coverage of a closed run** ([ENV-013], the eighth line's "it terminates at the first
termination test that finds no action in flight"): a closed executor at a live termination test
with nothing in flight can finish. That the close itself is offered is ENV-016's coverage clause `Env016Covers`
with ENV-016's line 2. -/
def Env013Covers (E : XRel N T) : Prop :=
  ∀ C s, Live C s → s.phase = .test → s.mode = .closed → s.fl = [] →
    ∃ s', E C s (.finish .closed) s'

/-- **The W5 coverage conjunct**: the existence halves the executor blocks of wave W5 leave to
the consistency theorem, one clause per block that asked for one (blocks state safety, offers are
coverage: the convention of `GlossaryExec.lean`). Every clause is over the executor `E` except
ENV-016's, which is over its expiry handling `X`. -/
def ExecCoversW5 (E : XRel N T) (X : ExpiryRel N T) : Prop :=
  ExecFailCovers E ∧ Exec022Covers E ∧ Exec040Covers E ∧ Exec042Covers E ∧ Env011Covers E ∧
    Env013Covers E ∧ Env014Covers E ∧ Env015Covers E ∧ conc002Covers E ∧
    Env002Covers E ∧ Env003Covers E ∧ Env005Covers E ∧ Env006Covers E ∧ Env010Covers E ∧
    Conc010Covers E ∧ Exec020Covers E ∧ Env016Covers X

/-- The reference offers `fail` for an error outcome and for an outcome the relay check rejects. -/
theorem refExec_failCovers : ExecFailCovers (RefExec (N := N) (T := T)) := by
  intro C s i f hf hc ho
  have h : (failStep refXPol C s i).isSome = true := by
    unfold failStep
    rw [hf]
    rcases ho with ho | ⟨e, ho, hr⟩ | ⟨e, ho, hr⟩
    · simp [hc, failCause, ho]
    · simp [hc, failCause, ho, hr]
    · simp [hc, failCause, ho, hr]
  exact Option.isSome_iff_exists.mp h

/-- The reference offers the expiry of every open asynchronous firing with a `Timeout` node, and
the deposit of every settleable timeout outcome the relay check accepts. -/
theorem refExec_timeoutCovers : Exec022Covers (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s i f e hf ho hs ht hto => ?_, fun C s i f e hf hc ho hr => ?_⟩
  · have h : (expireStep C s i e).isSome = true := by
      unfold expireStep
      simp [hf, ho, hs, ht, hto]
    exact Option.isSome_iff_exists.mp h
  · have h : (tdepositStep C s i).isSome = true := by
      unfold tdepositStep
      simp [hf, ho, hc, hr]
    exact Option.isSome_iff_exists.mp h

/-- The reference meets the W5 coverage conjunct. -/
theorem refExec_coversW5 : ExecCoversW5 (RefExec (N := N) (T := T)) refExpiry :=
  ⟨refExec_failCovers, refExec_timeoutCovers,
    fun C s hE hL hp hr => exec040_finish_offered C s hE hL hp hr,
    exec042_ref_covers, env011_ref_covers,
    fun C s hL hp hm hfl => env013_finish_offered C s hL hp hm hfl,
    fun C s hL hp => ⟨_, _, env014_snapshot_offered C s hL hp⟩, env015_ref_covers,
    conc002_covers_reference, env002_ref_covers, env003_ref_covers, env005_ref_covers,
    env006_ref_covers, env010_ref_covers, conc010_ref_covers, exec020_ref_covers,
    env016_ref_covers⟩

end Coverage

/-- The empty executor fails the coverage condition: the clock cannot advance. -/
theorem exec_coverage_excludes_empty {N T : Type} :
    ¬ ExecCovers (fun (_ : Cfg N T) (_ : XSt N T) (_ : XLbl N T) (_ : XSt N T) => False) := by
  rintro ⟨h, -⟩
  let C : Cfg N T :=
    { X := { net := { places := [], transitions := [] }, timing := fun _ => .immediate, tol := 0 },
      prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
      validate := fun _ _ => true, relay := fun _ _ _ => true,
      timeoutOut := fun _ _ _ => false, res := 0 }
  let s : XSt N T :=
    { M := fun _ => [], now := 0, cyc := 0, st := fun _ => .off, fl := [], nextId := 0, cq := [],
      pq := [], eq := [], mode := Mode.open, phase := .completions, order := [],
      delta := fun _ => 0, started := false, parked := false }
  obtain ⟨_, h⟩ := h C s 0
  exact h

/-- **CONC-010 gives ENV-005's lines 1 and 3**: the park guard of CONC-010 (no park while work is
queued) restricted to queued injections is ENV-005's line 1, and CONC-010's arrival line read at
an accepted request (an arrival) is ENV-005's line 3. -/
theorem conc010_env005_lines {N T : Type} [DecidableEq N] {R : XRel N T} (h : CONC_010 R)
    (C : Cfg N T) :
    WhileNever (fun s => s.eq ≠ []) (fun s s' => ∃ tmr, R C s (.park tmr) s') ∧
    ∀ p x, StepShall (fun s s' => R C s (.request p x .accepted) s') (fun _ s' => s'.parked = false) :=
  ⟨(h C).1.mono_pre fun _ hs => Or.inr (Or.inr hs),
    fun _ _ s s' hs => (h C).2.2.1 _ s s' ⟨hs, trivial⟩⟩

/-- **One admission signal for ENV-004 and ENV-006**: ENV-004's answering step (an injection of
ticket `k`, or a step that takes `k` off the event queue without injecting it) is ENV-006's
`answersTicket` on every step of every executor; both read the queue, not the label. -/
theorem env004_answers_eq_answersTicket {N T : Type} (k : Nat) (st : XStep N T) :
    env004_answers k st = Env006.answersTicket k st := by
  obtain ⟨s, l, s'⟩ := st
  cases l <;> simp [env004_answers, env004_isDrop, env004_isInject, env004_tickets,
    Env006.answersTicket]
  rename_i j
  cases j == k <;> rfl

/-- ✓ The executor requirements hold together, over one model: the reference validator, the
reference executor with its expiry handling, the reference queue firing and the reference timed
step satisfy every executor block of wave W5 and the Phase 1 blocks they share a variable with;
the executor settles admitted completions as the validator decides, agrees with the queue firing
(L2) and with the timed step (L3), and takes the steps of both coverage conditions. -/
@[evidence consistent EXEC_021 IO_015 EXEC_001 EXEC_003 EXEC_022 EXEC_030 EXEC_031 EXEC_040
  EXEC_041 EXEC_042 TIME_014 CONC_001 CONC_002 CONC_003 CONC_010 ENV_002 ENV_003 ENV_004 ENV_005
  ENV_006 ENV_010 ENV_011 ENV_013 ENV_014 ENV_015 ENV_016 EXEC_002_cycle EXEC_010_cycle
  EXEC_013_cycle EXEC_020_cycle TIME_010_cycle TIME_012_cycle TIME_013_cycle TIME_015_cycle
  CONC_005_cycle EXEC_010 EXEC_013 EXEC_020 TIME_010 TIME_012 TIME_013 TIME_015]
theorem spec_consistent_exec_sketch {N T : Type} [DecidableEq N] :
    ∃ (V : OutputValidator N) (E : XRel N T) (X : ExpiryRel N T) (Q : QFireRel N T) (R : TRel N),
      (EXEC_021 E ∧ IO_015 V ∧ ValidatedBy E V) ∧
      (EXEC_001 E ∧ EXEC_003 E ∧ EXEC_022 E ∧ EXEC_030 E ∧ EXEC_031 E ∧ EXEC_040 E ∧
        EXEC_041 E ∧ EXEC_042 E ∧ TIME_014 E) ∧
      (CONC_001 E ∧ CONC_002 E ∧ CONC_003 E ∧ CONC_010 E) ∧
      (ENV_002 E ∧ ENV_003 E ∧ ENV_004 E ∧ ENV_005 E ∧ ENV_006 E ∧ ENV_010 E ∧ ENV_011 E ∧
        ENV_013 E ∧ ENV_014 E ∧ ENV_015 E ∧ ENV_016 E X) ∧
      (EXEC_002_cycle E ∧ EXEC_010_cycle E ∧ EXEC_013_cycle E ∧ EXEC_020_cycle E ∧
        TIME_010_cycle E ∧ TIME_012_cycle E ∧ TIME_013_cycle E ∧ TIME_015_cycle E ∧
        CONC_005_cycle E) ∧
      (EXEC_010 Q ∧ EXEC_013 Q ∧ EXEC_020 Q ∧ QueueAgrees E Q) ∧
      (TIME_010 R ∧ TIME_012 R ∧ TIME_013 R ∧ TIME_015 R ∧ AtomicAgrees E R) ∧
      ExecCovers E ∧ ExecCoversW5 E X :=
  ⟨ioRefValidate, RefExec, refExpiry, RefQFire, RefTStep,
    ⟨EXEC_021_reference, IO_015_reference, refExec_validatedBy _⟩,
    ⟨EXEC_001_reference, EXEC_003_reference, EXEC_022_reference, EXEC_030_reference,
      EXEC_031_reference, EXEC_040_reference, EXEC_041_reference, EXEC_042_reference,
      TIME_014_reference⟩,
    ⟨CONC_001_reference, CONC_002_reference, CONC_003_reference, CONC_010_reference⟩,
    ⟨ENV_002_reference, ENV_003_reference, ENV_004_reference, ENV_005_reference,
      ENV_006_reference, ENV_010_reference, ENV_011_reference, ENV_013_reference,
      ENV_014_reference, ENV_015_reference, ENV_016_reference⟩,
    ⟨EXEC_002_cycle_reference, EXEC_010_cycle_reference, EXEC_013_cycle_reference,
      EXEC_020_cycle_reference, TIME_010_cycle_reference, TIME_012_cycle_reference,
      TIME_013_cycle_reference, TIME_015_cycle_reference, CONC_005_cycle_reference⟩,
    ⟨EXEC_010_reference, EXEC_013_reference, EXEC_020_reference, queueAgrees_ref⟩,
    ⟨TIME_010_reference, TIME_012_reference, TIME_013_reference, TIME_015_reference,
      atomicAgrees_ref⟩,
    refExec_covers, refExec_coversW5⟩

end Libpetri.Spec
