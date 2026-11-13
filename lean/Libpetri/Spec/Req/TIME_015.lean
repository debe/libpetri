import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010

set_option linter.missingDocs true

/-!
# TIME-015: Injectable clock (`spec/03-timing.md`)

TIME-015 is mostly about the seam a host plugs a clock into, which a step relation does not
see. What it does see are the assumptions the executor makes of its firing clock, and those are
this block: the readings never decrease, a delay moves the clock by exactly its length, and a
completed wait, early or not, never lets a transition fire below its earliest bound or once it
is expired, both measured from the stamps it held before the wait.

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), so `ConsistencyTime` can conjoin it with TIME-010 on `RefTStep`. The
evidence checks it against the timed reference step, against clocks that run backwards, against
executors that trust their wait or ignore expiry, and against waits that rewrite or drop stamps.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-- The state a wait reached, read with the stamps the transitions held when the wait began: the
marking and the reading of the firing clock after the wait, the stamps before it. A wait does not
stamp (TIME-010), so for a relation whose delay keeps the stamps this is the state the wait
reached (`time015_afterWait_self`); for one whose delay rewrites or drops stamps it is what the
executor should have seen. -/
def AfterWait {N : Type} (s₀ s : TSt N) : TSt N := { s with stamp := s₀.stamp }

/-! ## TIME-015: Injectable clock -/

requirement TIME_015
  id "TIME-015"
  title "Injectable Clock"
  kind A
  scope "all executors, on the default or an injected firing clock"
  source verbatim "spec/03-timing.md"
  quote "*While* an executor runs on an injected clock, successive readings of its firing clock *shall* be non-decreasing."
        "*When* the executor's wait completes, the executor *shall* re-check its boundary conditions before it fires any transition, so an armed transition *shall not* fire before its earliest bound because a wait completed early ([TIME-010])."
  reading "For every timed net X:"
          "no step lowers the reading of the firing clock;"
          "a delay of δ advances the reading by exactly δ;"
          "no transition fires from the state a delay of any length reached if, read with the stamps held before the delay, it is armed there and its elapsed time is below its earliest bound;"
          "no transition fires from the state a delay of any length reached if, read with the stamps held before the delay, it is expired there."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock (ClockReading) and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). The relation has one firing clock and does not say where its readings come from, so the block holds of the default clock as of an injected one. The epoch clock (token creation times, [CORE-011]) is not modelled: the Phase 1 marking is token counts. Injected tokens are not steps of the Phase 1 relation."
          "Line 1 of the formula is the first 'shall' sentence, over every step. A host reading that goes backwards cannot be written as a delay, since a delay's length is a natural number: across a wait, the sentence is carried by that type together with line 2, and a clock that rewinds on a delay breaks lines 1 and 2 at once (TIME_015_forbids_rewind). Line 1 on its own constrains firings and reaps: one that lowers the reading breaks it alone (TIME_015_mutant_waitOnly_killed)."
          "Line 2 says a delay moves the clock by its length; it is the only statement of that fact, and TIME-003 to TIME-006 rely on it through ConsistencyTime for the elapsed time of their transitions to grow with the clock (their clock frame keeps the stamp across a delay, GlossaryTime ClockFrame). That a firing and a reap take no time (an atomic step happens at one reading) is a convention of the Phase 1 relation, not a sentence of this section, so it is not a line of this block; its firing half is time012_FramesClock, which ConsistencyTime conjoins, and its reap half is [TIME-013] line 1 (a reap leaves the clock reading as it is). Which reading stamps a transition armed by a firing is fixed by [TIME-010]: the reading the next enablement update that finds it enabled takes, and [TIME-012] stamps a restarted clock the same way. The Phase 1 relation has no enablement update, as a firing is atomic, so it takes the firing step's own reading (refPolicy.fresh) as an abstraction of that rule; the companions TIME_010_cycle and TIME_012_cycle state the rule itself, for a synchronous deposit and for an asynchronous completion alike."
          "Contract 1's other half (the clock is not assumed to advance between two reads) is not a line of this block. A repeated reading is a delay of 0; that one is offered is CoversDelay, and that it changes nothing else is TIME-010's framing of stamps across a delay together with FramesMarking. The reference meets it (time015_stutter)."
          "Lines 3 and 4 are the second 'shall' sentence. A completed wait is a delay step of any length: the executor cannot tell an early or spurious completion from a due one, so both lines quantify over every delay. The boundary conditions are read in AfterWait: the marking and reading after the wait with the stamps held before it, so that a wait that rewrites or drops stamps cannot hide an early firing (TIME_015_mutant_inState_killed, TIME_015_forbids_dropStamps). For a relation that keeps stamps across a delay, as TIME-010 line 2 asks, AfterWait is the state the wait reached."
          "Line 3 is the earliest side, which the sentence names. Line 4 is the latest side of 'its boundary conditions': a transition that is expired (glossary: reapable, armed, elapsed time strictly greater than its latest bound plus the deadline tolerance; rulings D2 and D4) does not fire after a wait that overshot. Exact transitions are not reapable and are never expired [TIME-006]. With TIME-010 and FramesMarking, line 3 holds of every relation (time015_ac4_of_time010, cited for AC4)."
          "AC6: the reap test, that with tolerance 0 a Deadline transition can be reaped exactly when it is armed and its elapsed time is strictly greater than its bound, is the cited theorem time015_ac6_reap_strict (the strict test of TIME-013, ruling D4). That the reap happens on the first such cycle is a property of the executor loop and is deferred to Phase 2."
          "AC10 is read under ruling D12 (a): stuttering invariance only. A clock that returns the same reading across several cycles takes delays of 0 between them, and a delay of 0 is an identity step (refTStepW_delay_zero, ClashesTime.lean, cited for TIME-015), which the reference offers from every state (time015_stutter); so a run that repeats readings reaches the outcome of the same run with each repeated reading taken once. A clock that advances in coarse jumps is not claimed to reach the outcome of a finer one: the reference refutes that (time015_ac10_coarse_jump: a Window(3, 5) transition with tolerance 0 fires under a clock advancing 1 ms per reading, and is reaped, its token stranded, under the readings 0 then 10), and the AC10 text says so."
          "AC1, AC2, AC3, AC9, AC12 and AC15 are properties of the seam, its default path and its documentation (configuration, N kind), not of a step relation. The MUST of AC14 (two executors constructed in one process carry different execution IDs, whatever the clock reads) is the line of EVT_002_executionId (ruling D98 (a)), which cites this requirement; its SHOULD (reproducible IDs) is that block's nonvacuous evidence. AC5, AC7, AC8 and AC11 are properties of the executor loop (abort, the boundary short-circuit, wake-up, reentrant admission) and AC13 of token stamping through the epoch clock; they are deferred to Phase 2."
          "The section's other MUST sentences are not lines of this block, and none is a property of the atomic step. The scope limit on action timeouts ([IO-013]): 'An implementation MUST document this limit rather than let a host infer from the rest of the requirement that all net-declared timing is virtualized' is documentation (N kind), and 'An implementation MUST NOT route the timeout interval through the injected clock while leaving the action's own wait on real time' is a property of the host interface, as an action timeout is a per-action wait the seam does not own (the budget is host time under ruling D18 (b), as EXEC_022's assumes read it; EXEC_022_forbids_clockTimeout rejects a timeout outcome reached on a delay of the firing clock). Contract 2's asynchronous wait ('MUST NOT complete synchronously on first poll, and MUST NOT block the calling thread') and its default ('MUST document that the default suits only a clock that advances, and MUST NOT ship a suspending clock that inherits it') are properties of the host interface and its documentation, with AC15. 'The executor MUST NOT silently re-stamp host-supplied tokens' is the restore of [CORE-073], which keeps every token's created_at (CORE_073); the epoch clock is not modelled here. 'The two are separate values, and an implementation MUST NOT derive either from the other' (the run identifier and the default minting scope of [NU-011]) is the line of NU_011_default (nu011_default_not_runId), with the run identifier of EVT_002_executionId ([EVT-002]). 'A conformance suite running on a virtual clock MUST NOT pin fast-path order for a net that takes the general path, or the reverse' is an obligation of a test suite (Q kind), not of an executor; the two orders are EXEC_002's."
          "Every remaining MUST of the section is tied to an acceptance criterion above or named here, and none is a property of the atomic step. 'Their origins are unrelated and MUST NOT be conflated' (the firing clock and the epoch clock): the Phase 1 relation has the firing clock only and does not model the epoch clock (first paragraph); the epoch stamps are AC13's. 'The seam MUST therefore also own the executor's wait for the next timing boundary' and 'The seam MUST carry both halves' (the wake-up and the interval) are properties of the host interface (kind N), with AC3 and AC8. Contract 2's 'Given a finite interval the wait MUST either suspend until that boundary or advance the clock to it' and, for an infinite interval, 'the wait MUST suspend until woken' are host-interface properties, with AC3 and AC15; 'a test MUST NOT be bounded by patience' is an obligation of a test suite (kind Q). Contract 4's 'On abort the wait MUST complete normally rather than failing, and MUST release whatever it registered to hear the abort' is AC5; 'A host MUST therefore not read abort as teardown' is a host rule (kind N); 'MUST still keep the no-clock path free of the allocation' is AC9. Contract 5's 'A host-visible readiness predicate the wait consults MUST be cheap, repeatable and side-effect free, and MUST NOT itself consult a clock' is a property of the host interface (kind N), and the predicate's visibility and completeness MUSTs are AC8. The admission MUSTs (inject() legal from inside the wait, an injection or a completion from inside the wait only enqueued and admitted in step 2 or step 1 of a following cycle, never at the call; whatever a completion runs inline not awaiting an admission signal and not blocking; the admission signal not awaited there) are AC11, a property of the executor loop deferred to Phase 2; the queueing itself is ENV-003's and EXEC-001's. 'Absent an injected clock an implementation MUST behave exactly as before' and 'every existing timing conformance test MUST pass unchanged' are AC1. The boundary short-circuit ('the executor MUST return and let the next cycle act on it rather than waiting', 'an injected clock MUST NOT make them diverge') is AC7; over the executor, CONC-010's second line (no block while a transition is Ready or Expired at the cycle reading) states it on every clock. 'an implementation MUST therefore offer construction of a token at an explicit timestamp ([CORE-011])' is an API obligation (kind N) of CORE-011's token constructor. 'Such a token is executor-produced and MUST be stamped through the injected epoch clock', with every token the implementation synthesises during a firing, is AC13; 'MUST document that its default token constructor is non-deterministic under a host clock' is AC12. 'Any identifier an implementation derives for a run ... MUST NOT be derived solely from a clock reading' and 'Such an identifier MUST be unique among executors that can be observed together' are AC14's MUST, the line of EVT_002_executionId; 'That scope MUST differ between two processes that did nothing differently' is NU-011's (NU_011_default)."
  signoff "2026-11-13 59da872b35939352 ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ l, on (fun s s' => R X s l s'), shall (fun s s' =>
          ClockReading s ≤ ClockReading s')) ∧
      (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
          ClockReading s' = ClockReading s + δ)) ∧
      (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
          Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
            ∀ d s', ¬ R X s (.fire u d) s')) ∧
      (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
          Expired X (AfterWait s₀ s) u → ∀ d s', ¬ R X s (.fire u d) s'))

/- The pinned readable form of TIME-015: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_015 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (l : TLbl N), on fun s s' => R X s l s', shall fun s s' => ClockReading s ≤ ClockReading s') ∧
      (∀ (δ : ℕ), on fun s s' => R X s (TLbl.delay δ) s', shall fun s s' => ClockReading s' = ClockReading s + δ) ∧
        (∀ (δ : ℕ) (u : Reference.Trans N),
            on fun s₀ s => R X s₀ (TLbl.delay δ) s, shall fun s₀ s =>
              Armed (AfterWait s₀ s) u →
                Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
                  ∀ (d : List N) (s' : TSt N), ¬R X s (TLbl.fire u d) s') ∧
          ∀ (δ : ℕ) (u : Reference.Trans N),
            on fun s₀ s => R X s₀ (TLbl.delay δ) s, shall fun s₀ s =>
              Expired X (AfterWait s₀ s) u → ∀ (d : List N) (s' : TSt N), ¬R X s (TLbl.fire u d) s'
-/
#guard_msgs in #print TIME_015

/-! ### The four lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- A delay of `δ`, under any policy, advances the reading by `δ`. -/
theorem time015_delay {P : Policy N} {X : TimedNet N} {s s' : TSt N} {δ : Nat}
    (h : RefTStepW P X s (.delay δ) s') : ClockReading s' = ClockReading s + δ := by
  cases h; rfl

/-- A firing, under any policy, leaves the reading as it is. -/
theorem time015_fire {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    {d : List N} (h : RefTStepW P X s (.fire t d) s') : ClockReading s' = ClockReading s := by
  cases h; rfl

/-- A reap, under any policy, leaves the reading as it is. -/
theorem time015_reap {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    (h : RefTStepW P X s (.reap t) s') : ClockReading s' = ClockReading s := by
  cases h; rfl

/-- No step, under any policy, lowers the reading. -/
theorem time015_mono {P : Policy N} {X : TimedNet N} {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') : ClockReading s ≤ ClockReading s' := by
  cases h <;> simp [ClockReading]

/-- A delay, under any policy, keeps the stamps, so the state it reached is its own
`AfterWait`. -/
theorem time015_afterWait_self {P : Policy N} {X : TimedNet N} {s₀ s : TSt N} {δ : Nat}
    (h : RefTStepW P X s₀ (.delay δ) s) : AfterWait s₀ s = s := by
  cases h; rfl

/-- A firing under any policy with the spec's expiry test is from a state in which its
transition is not expired. -/
theorem time015_notExpired {P : Policy N} (hx : P.expired = refPolicy.expired) {X : TimedNet N}
    {u : Trans N} {d : List N} {s s' : TSt N} (h : RefTStepW P X s (.fire u d) s') :
    ¬ Expired X s u := by
  obtain ⟨-, -, -, -, hf, -⟩ := refTStepW_fire_inv h
  rw [hx] at hf
  intro he
  have := (expired_iff X s u).1 he
  simp [refPolicy] at hf
  rw [hf] at this
  exact Bool.false_ne_true this

/-- Line 3 for every relation whose firings are firings of a policy with the spec's gate and
whose delays keep the stamps. -/
theorem time015_recheckEarly {R : TRel N} {P : Policy N} (hg : P.gate = refPolicy.gate)
    (hfire : ∀ X s u d s', R X s (.fire u d) s' → ∃ s₁, RefTStepW P X s (.fire u d) s₁)
    (hdel : ∀ X s₀ δ s, R X s₀ (.delay δ) s → AfterWait s₀ s = s) (X : TimedNet N) :
    ∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
      Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
        ∀ d s', ¬ R X s (.fire u d) s') := by
  intro δ u s₀ s hd _ hlt d s' hf
  obtain ⟨_, h1⟩ := hfire X s u d s' hf
  rw [hdel X s₀ δ s hd] at hlt
  have := time010_gate hg h1
  omega

/-- Line 4 for every relation whose firings are firings of a policy with the spec's expiry
test and whose delays keep the stamps. -/
theorem time015_recheckLate {R : TRel N} {P : Policy N} (hx : P.expired = refPolicy.expired)
    (hfire : ∀ X s u d s', R X s (.fire u d) s' → ∃ s₁, RefTStepW P X s (.fire u d) s₁)
    (hdel : ∀ X s₀ δ s, R X s₀ (.delay δ) s → AfterWait s₀ s = s) (X : TimedNet N) :
    ∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
      Expired X (AfterWait s₀ s) u → ∀ d s', ¬ R X s (.fire u d) s') := by
  intro δ u s₀ s hd he d s' hf
  obtain ⟨_, h1⟩ := hfire X s u d s' hf
  rw [hdel X s₀ δ s hd] at he
  exact time015_notExpired hx h1 he

/-- Lines 1 and 2 for any policy. -/
theorem time015_clock (P : Policy N) (X : TimedNet N) :
    (∀ l, on (fun s s' => RefTStepW P X s l s'), shall (fun s s' =>
        ClockReading s ≤ ClockReading s')) ∧
      (∀ δ, on (fun s s' => RefTStepW P X s (.delay δ) s'), shall (fun s s' =>
        ClockReading s' = ClockReading s + δ)) :=
  ⟨fun _ _ _ h => time015_mono h, fun _ _ _ h => time015_delay h⟩

/-- TIME-015 for any policy with the spec's gate and expiry test. -/
theorem time015_of_policy {P : Policy N} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) : TIME_015 (RefTStepW P) := fun X =>
  let hf : ∀ X s u d s', RefTStepW P X s (.fire u d) s' → ∃ s₁, RefTStepW P X s (.fire u d) s₁ :=
    fun _ _ _ _ _ h => ⟨_, h⟩
  let hd : ∀ X s₀ δ s, RefTStepW P X s₀ (.delay δ) s → AfterWait s₀ s = s :=
    fun _ _ _ _ h => time015_afterWait_self h
  ⟨(time015_clock P X).1, (time015_clock P X).2, time015_recheckEarly hg hf hd X,
    time015_recheckLate hx hf hd X⟩

/-- A repeated reading is a delay of `0`, which the timed step, under any policy, takes to the
same state: the clock is not assumed to advance (contract 1). -/
theorem time015_stutter (P : Policy N) (X : TimedNet N) (s : TSt N) :
    RefTStepW P X s (.delay 0) s :=
  RefTStepW.delay X s 0

end Lines

/-- The timed reference step satisfies TIME-015: a delay advances the reading by its length,
a firing and a reap leave it as it is, so no step lowers it (lines 1 and 2); a delay keeps the
stamps, so the state it reaches is its own `AfterWait`, and a firing needs its transition past
`refPolicy`'s earliest-bound gate and not expired in the state it fires from (lines 3 and 4). -/
@[evidence holds TIME_015]
theorem TIME_015_reference {N : Type} [DecidableEq N] : TIME_015 (RefTStep (N := N)) :=
  time015_of_policy rfl rfl

/-! ### Cited corollaries (AC4, AC6) -/

/-- AC4: a wait that completes spuriously does not let an armed transition fire before its
earliest bound. For every relation that meets TIME-010 and changes the marking only by
firing, line 3 of TIME-015 holds: a firing transition is armed (TIME-010 line 5), so it was armed
before the wait and kept its stamp across it (TIME-010 line 2), and its elapsed time is then at
least its earliest bound (TIME-010 line 4). -/
@[evidence cites "TIME-015" "AC4: a wait that completes early or spuriously (a delay of any length) does not let an armed transition fire before its earliest bound; a corollary of TIME-010"]
theorem time015_ac4_of_time010 {N : Type} [DecidableEq N] {R : TRel N} (h : TIME_010 R)
    (hF : FramesMarking R) (X : TimedNet N) (δ : Nat) (u : Trans N) :
    on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
      Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
        ∀ d s', ¬ R X s (.fire u d) s') := by
  intro s₀ s hd ha hlt d s' hf
  have hm : s.m = s₀.m := hF X s₀ (.delay δ) s hd (fun _ _ h => by cases h)
  have hs : Armed s u := by
    by_contra hn
    exact (h X).2.2.2.2 u s s' ⟨d, hf⟩ hn
  have ha0 : Armed s₀ u := by
    obtain ⟨he, hst⟩ := ha
    exact ⟨by simpa [AfterWait, hm] using he, hst⟩
  rcases (h X).2.1 (.delay δ) u s₀ s hd ha0 hs with he | ⟨⟨t, d', hl⟩, _⟩
  · have hw : Elapsed (AfterWait s₀ s) u = Elapsed s u := by
      simp only [Elapsed, ClockReading, AfterWait, he]
    exact (h X).2.2.2.1 u s s' ⟨d, hf⟩ ⟨hs, hw ▸ hlt⟩
  · cases hl

/-- AC6, the reap test: with deadline tolerance `0`, a `Deadline(b)` transition of the net can be
reaped exactly when it is armed and its elapsed time is strictly greater than `b`; at elapsed
time `b` it cannot. -/
@[evidence cites "TIME-015" "AC6: with deadline tolerance 0 a Deadline transition is reaped when its elapsed time is strictly greater than its bound, and not when it is exactly its bound (the reap test of TIME-013)"]
theorem time015_ac6_reap_strict {N : Type} [DecidableEq N] (X : TimedNet N) (s : TSt N)
    (t : Trans N) (b : Nat) (ht : t ∈ X.net.transitions) (htol : Tolerance X = 0)
    (htm : TimingOf X t = .deadline b) :
    (∃ s', RefTStep X s (.reap t) s') ↔ Armed s t ∧ b < Elapsed s t := by
  have hx : Expired X s t ↔ Armed s t ∧ b < Elapsed s t := by
    simp [Expired, Reapable, htm, htol, Timing.reapable, Timing.latest]
  rw [← hx]
  refine ⟨fun ⟨s', h⟩ => ?_, fun h => refTStep_coversReap X s t ht h⟩
  match h with
  | .reap _ _ _ _ hx' => exact (expired_iff X s t).2 hx'

/-! ### Examples -/

/-- A window transition: one input arc on place `0`, no output spec. -/
def time015_w : Trans Nat :=
  { core := { name := "w", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- A deadline transition: one input arc on place `1`, no output spec. -/
def time015_k : Trans Nat :=
  { core := { name := "k", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `w` is `Window(2, 3)`, every other transition `Deadline(3)`. -/
def time015_timing (t : Trans Nat) : Timing :=
  if t.core.name = "w" then .window 2 3 else .deadline 3

/-- The timed net of the examples: `w` and `k`, tolerance 0. -/
def time015_X : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [time015_w, time015_k] },
    timing := time015_timing, tol := 0 }

/-- The state at reading `n`: one token in places `0` and `1`, both transitions armed since
`0`. -/
def time015_at (n : Nat) : TSt Nat :=
  { m := fun p => if p = 0 ∨ p = 1 then 1 else 0, now := n,
    stamp := fun x => if x = "w" ∨ x = "k" then some 0 else none }

/-- The state after `w` fires at reading `n` under policy `P`. -/
def time015_fired (P : Policy Nat) (n : Nat) : TSt Nat :=
  { m := fireNC (time015_at n).m time015_w.core (depProd []), now := n,
    stamp := restampAll P time015_X (time015_at n) time015_w []
      (fireNC (time015_at n).m time015_w.core (depProd [])) }

/-- Every state `time015_at n` is reached from reading `0` by a delay of `n`, under any
policy. -/
theorem time015_reach (P : Policy Nat) (n : Nat) :
    RefTStepW P time015_X (time015_at 0) (.delay n) (time015_at n) := by
  have h := RefTStepW.delay (P := P) time015_X (time015_at 0) n
  simpa [time015_at] using h

/-- `w` fires at reading `n` under a policy whose gate and expiry allow it there. -/
theorem time015_w_fires {P : Policy Nat} {n : Nat}
    (hg : P.gate time015_X (time015_at n) time015_w = true)
    (hx : P.expired time015_X (time015_at n) time015_w = false) :
    RefTStepW P time015_X (time015_at n) (.fire time015_w []) (time015_fired P n) :=
  RefTStepW.fire _ _ _ _ _ (by simp [time015_X]) ⟨rfl, ⟨.action 0, rfl⟩, rfl⟩ rfl hg hx

/-! ### Forbidden: a clock that runs backwards on a wait -/

/-- A relation whose delay takes the host's reading as it comes, here one that goes back by the
delay's length; firings and reaps are the reference's. -/
def time015_rewind : TRel Nat := fun X s l s' =>
  match l with
  | .delay δ => s' = { s with now := s.now - δ }
  | l => RefTStep X s l s'

/-- ✗ A clock that runs backwards on a wait violates TIME-015, lines 1 and 2 at once: a delay of
`1` at reading `5` reads `4`. -/
@[evidence forbids TIME_015]
theorem TIME_015_forbids_rewind : ¬ TIME_015 time015_rewind := by
  intro h
  have := (h time015_X).1 (.delay 1) (time015_at 5) { time015_at 5 with now := 4 } rfl
  revert this
  decide

/-! ### Mutant: the executor takes the host's reading as it comes -/

/-- Mutant reading of TIME-015 that puts no condition on the reading a step produces: the host
supplies a `now` and the executor takes it (lines 1 and 2 dropped). Lines 3 and 4 are as in
TIME-015. -/
def TIME_015_mutant_hostNow {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
          ∀ d s', ¬ R X s (.fire u d) s')) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Expired X (AfterWait s₀ s) u → ∀ d s', ¬ R X s (.fire u d) s'))

/-- The rewinding clock kills the mutant: it satisfies the mutant reading, since its delays keep
the stamps and its firings are the reference's, but not TIME-015. -/
@[evidence mutant TIME_015]
theorem TIME_015_mutant_hostNow_killed :
    TIME_015_mutant_hostNow time015_rewind ∧ ¬ TIME_015 time015_rewind := by
  have hf : ∀ X s u d s', time015_rewind X s (.fire u d) s' →
      ∃ s₁, RefTStepW refPolicy X s (.fire u d) s₁ := fun _ _ _ _ _ h => ⟨_, h⟩
  have hd : ∀ X s₀ δ s, time015_rewind X s₀ (.delay δ) s → AfterWait s₀ s = s := by
    intro X s₀ δ s h
    have h' : s = { s₀ with now := s₀.now - δ } := h
    subst h'
    rfl
  exact ⟨fun X => ⟨time015_recheckEarly rfl hf hd X, time015_recheckLate rfl hf hd X⟩,
    TIME_015_forbids_rewind⟩

/-! ### Mutant: only waits are checked -/

/-- A relation whose firing stamps the clock with a stale reading, one millisecond before the
one it fired at (for example the reading taken when the cycle began, kept after a wait the
executor did not count): a reference firing, then the reading goes back by `1`. Delays and
reaps are the reference's. -/
def time015_staleFire : TRel Nat := fun X s l s' =>
  match l with
  | .fire t d => ∃ s₁, RefTStep X s (.fire t d) s₁ ∧ s' = { s₁ with now := s₁.now - 1 }
  | l => RefTStep X s l s'

/-- Mutant reading of TIME-015 in which the readings need be non-decreasing only across a wait:
line 1 is dropped, which line 2 implies for delays. Lines 2 to 4 are as in TIME-015. -/
def TIME_015_mutant_waitOnly {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
        ClockReading s' = ClockReading s + δ)) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
          ∀ d s', ¬ R X s (.fire u d) s')) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Expired X (AfterWait s₀ s) u → ∀ d s', ¬ R X s (.fire u d) s'))

/-- The stale firing kills the mutant: it satisfies the mutant reading, but not TIME-015 (line 1
alone), since `w`, ready at reading `2`, fires and leaves the clock at `1`. -/
@[evidence mutant TIME_015]
theorem TIME_015_mutant_waitOnly_killed :
    TIME_015_mutant_waitOnly time015_staleFire ∧ ¬ TIME_015 time015_staleFire := by
  have hf : ∀ X s u d s', time015_staleFire X s (.fire u d) s' →
      ∃ s₁, RefTStepW refPolicy X s (.fire u d) s₁ := fun _ _ _ _ _ ⟨s₁, h, _⟩ => ⟨s₁, h⟩
  have hd : ∀ X s₀ δ s, time015_staleFire X s₀ (.delay δ) s → AfterWait s₀ s = s :=
    fun _ _ _ _ h => time015_afterWait_self (P := refPolicy) h
  refine ⟨fun X => ⟨fun δ s s' h => time015_delay (P := refPolicy) h,
    time015_recheckEarly rfl hf hd X, time015_recheckLate rfl hf hd X⟩, fun h => ?_⟩
  have hs : time015_staleFire time015_X (time015_at 2) (.fire time015_w [])
      { time015_fired refPolicy 2 with now := 1 } :=
    ⟨_, time015_w_fires (by decide) (by decide), rfl⟩
  have := (h time015_X).1 (.fire time015_w []) _ _ hs
  revert this
  decide

/-! ### Mutant: the executor trusts its wait -/

/-- The policy of an executor that treats "the wait completed" as "the boundary is reached":
every armed transition that is not expired passes the gate. -/
def time015_trustWaitPolicy : Policy Nat := { refPolicy with gate := fun _ _ _ => true }

/-- Mutant reading of TIME-015 without the earliest-side re-check (line 3 dropped): the wait owns
the earliest boundary. The other lines are as in TIME-015. -/
def TIME_015_mutant_trustWait {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l, on (fun s s' => R X s l s'), shall (fun s s' =>
        ClockReading s ≤ ClockReading s')) ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
        ClockReading s' = ClockReading s + δ)) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Expired X (AfterWait s₀ s) u → ∀ d s', ¬ R X s (.fire u d) s'))

/-- The executor that trusts its wait kills the mutant: it satisfies the mutant reading, but not
TIME-015. A wait that completes early, at reading `1`, wakes it, and `w` fires with elapsed time
`1`, below its earliest bound `2`. -/
@[evidence mutant TIME_015]
theorem TIME_015_mutant_trustWait_killed :
    TIME_015_mutant_trustWait (RefTStepW time015_trustWaitPolicy) ∧
      ¬ TIME_015 (RefTStepW time015_trustWaitPolicy) := by
  refine ⟨fun X => ⟨(time015_clock _ X).1, (time015_clock _ X).2,
    time015_recheckLate (R := RefTStepW time015_trustWaitPolicy) (P := time015_trustWaitPolicy) rfl
      (fun _ _ _ _ _ h => ⟨_, h⟩)
      (fun _ _ _ _ h => time015_afterWait_self h) X⟩, fun h => ?_⟩
  exact (h time015_X).2.2.1 1 time015_w (time015_at 0) (time015_at 1) (time015_reach _ 1)
    (by decide) (by decide) [] _ (time015_w_fires (P := time015_trustWaitPolicy) rfl (by decide))

/-! ### Mutant: the executor re-checks only the earliest bound -/

/-- The policy of an executor whose re-check after a wait looks at the earliest bound only: it
never reaps, and fires a transition past its earliest bound however late. -/
def time015_ignoreExpiryPolicy : Policy Nat := { refPolicy with expired := fun _ _ _ => false }

/-- Mutant reading of TIME-015 that takes 'its boundary conditions' as the earliest bound only
(line 4 dropped). The other lines are as in TIME-015. -/
def TIME_015_mutant_earliestOnly {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l, on (fun s s' => R X s l s'), shall (fun s s' =>
        ClockReading s ≤ ClockReading s')) ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
        ClockReading s' = ClockReading s + δ)) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun s₀ s =>
        Armed (AfterWait s₀ s) u → Elapsed (AfterWait s₀ s) u < (TimingOf X u).earliest →
          ∀ d s', ¬ R X s (.fire u d) s'))

/-- The executor that ignores expiry kills the mutant: it satisfies the mutant reading, but not
TIME-015. A wait of `4` overshoots `w`'s window (`Window(2, 3)`, armed at `0`, tolerance 0): `w`
is expired at reading `4` and still fires there. -/
@[evidence mutant TIME_015]
theorem TIME_015_mutant_earliestOnly_killed :
    TIME_015_mutant_earliestOnly (RefTStepW time015_ignoreExpiryPolicy) ∧
      ¬ TIME_015 (RefTStepW time015_ignoreExpiryPolicy) := by
  refine ⟨fun X => ⟨(time015_clock _ X).1, (time015_clock _ X).2,
    time015_recheckEarly (R := RefTStepW time015_ignoreExpiryPolicy)
      (P := time015_ignoreExpiryPolicy) rfl (fun _ _ _ _ _ h => ⟨_, h⟩)
      (fun _ _ _ _ h => time015_afterWait_self h) X⟩, fun h => ?_⟩
  exact (h time015_X).2.2.2 4 time015_w (time015_at 0) (time015_at 4) (time015_reach _ 4)
    (by decide) [] _ (time015_w_fires (P := time015_ignoreExpiryPolicy) (by decide) rfl)

/-! ### Mutant: the boundary read in the state the wait reached -/

/-- A wait that counts its own length twice: a delay of `δ` advances the reading by `δ` and also
moves every stamp back by `δ`, so elapsed time grows by `2δ` across the wait. Firings and reaps
are the reference's. -/
def time015_shiftStamps : TRel Nat := fun X s l s' =>
  match l with
  | .delay δ => s' = { s with now := s.now + δ, stamp := fun n => (s.stamp n).map (· - δ) }
  | l => RefTStep X s l s'

/-- The stamp-shifting wait is otherwise a plausible executor: it fires as the reference
semantics says, changes the marking only by firing, and has every firing, reap and delay the
coverage conditions ask for. TIME-010 line 2 rejects it as well (not proved here). -/
theorem time015_shiftStamps_plausible :
    ProjectsTo time015_shiftStamps RefFire ∧ FramesMarking time015_shiftStamps ∧
      Covers time015_shiftStamps ∧ CoversReap time015_shiftStamps ∧
      CoversDelay time015_shiftStamps := by
  refine ⟨fun _ _ _ _ _ h => refTStep_projects h, ?_, fun X s t d m' ht hr hf =>
    refTStep_covers X s t d m' ht hr hf, fun X s t ht hx => refTStep_coversReap X s t ht hx,
    fun _ _ _ => ⟨_, rfl, rfl⟩⟩
  intro X s l s' h hl
  cases l with
  | delay δ => subst h; rfl
  | fire t d => exact absurd rfl (hl t d)
  | reap t => exact refTStepW_marking (P := refPolicy) h hl

/-- Mutant reading of TIME-015 that reads the boundary conditions in the state the wait reached,
with whatever stamps the delay left there (lines 3 and 4 measured without `AfterWait`). Lines 1
and 2 are as in TIME-015. -/
def TIME_015_mutant_inState {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l, on (fun s s' => R X s l s'), shall (fun s s' =>
        ClockReading s ≤ ClockReading s')) ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
        ClockReading s' = ClockReading s + δ)) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun _ s =>
        Armed s u → Elapsed s u < (TimingOf X u).earliest → ∀ d s', ¬ R X s (.fire u d) s')) ∧
    (∀ δ u, on (fun s₀ s => R X s₀ (.delay δ) s), shall (fun _ s =>
        Expired X s u → ∀ d s', ¬ R X s (.fire u d) s'))

/-- The state at reading `1`, `w` and `k` armed since `1`. -/
def time015_at1 : TSt Nat :=
  { m := fun p => if p = 0 ∨ p = 1 then 1 else 0, now := 1,
    stamp := fun x => if x = "w" ∨ x = "k" then some 1 else none }

/-- The stamp-shifting wait kills the mutant: it satisfies the mutant reading, but not TIME-015.
`w` (`Window(2, 3)`) is armed at reading `1` with stamp `1`; a wait of `1` reaches reading `2`
and moves the stamp to `0`, so `w` fires there, `1` ms after its stamp, below its earliest bound
`2`. -/
@[evidence mutant TIME_015]
theorem TIME_015_mutant_inState_killed :
    TIME_015_mutant_inState time015_shiftStamps ∧ ¬ TIME_015 time015_shiftStamps := by
  refine ⟨fun X => ⟨fun l s s' h => ?_, fun δ s s' h => by subst h; rfl,
    fun δ u s₀ s _ _ hlt d s' hf => absurd (time010_gate (P := refPolicy) rfl hf) (by omega),
    fun δ u s₀ s _ he d s' hf => time015_notExpired (P := refPolicy) rfl hf he⟩, fun h => ?_⟩
  · cases l with
    | delay δ => subst h; simp [ClockReading]
    | fire t d => exact time015_mono (P := refPolicy) h
    | reap t => exact time015_mono (P := refPolicy) h
  · have hd : time015_shiftStamps time015_X time015_at1 (.delay 1) (time015_at 2) := by
      show time015_at 2 = _
      simp only [time015_at, time015_at1, TSt.mk.injEq, true_and]
      funext x; split <;> rfl
    exact (h time015_X).2.2.1 1 time015_w _ _ hd (by decide) (by decide) [] _
      (time015_w_fires (P := refPolicy) (by decide) (by decide))

/-! ### Forbidden: a wait that forgets every clock -/

/-- A wait that forgets every clock, and a firing that does not look at the clock: a delay drops
every stamp, and a firing fires any enabled, non-expired transition of the net with the
reference marking effect and stamps. Reaps are the reference's. -/
def time015_dropStamps : TRel Nat := fun X s l s' =>
  match l with
  | .delay δ => s' = { s with now := s.now + δ, stamp := fun _ => none }
  | .fire t d => t ∈ X.net.transitions ∧ RefFire t s.m d s'.m ∧
      (refPolicy (N := Nat)).expired X s t = false ∧
      s' = { m := s'.m, now := s.now, stamp := restampAll refPolicy X s t d s'.m }
  | l => RefTStep X s l s'

/-- The stamp-dropping wait is otherwise a plausible executor: it fires as the reference
semantics says, changes the marking only by firing, and has every firing, reap and delay the
coverage conditions ask for. TIME-010 line 5 rejects it as well (not proved here). -/
theorem time015_dropStamps_plausible :
    ProjectsTo time015_dropStamps RefFire ∧ FramesMarking time015_dropStamps ∧
      Covers time015_dropStamps ∧ CoversReap time015_dropStamps ∧
      CoversDelay time015_dropStamps := by
  refine ⟨fun _ _ _ _ _ h => h.2.1, ?_, ?_, fun X s t ht hx => refTStep_coversReap X s t ht hx,
    fun _ _ _ => ⟨_, rfl, rfl⟩⟩
  · intro X s l s' h hl
    cases l with
    | delay δ => subst h; rfl
    | fire t d => exact absurd rfl (hl t d)
    | reap t => exact refTStepW_marking (P := refPolicy) h hl
  · intro X s t d m' ht hr hf
    obtain ⟨_, _, hx⟩ := (ready_iff X s t).1 hr
    exact ⟨{ m := m', now := s.now, stamp := restampAll refPolicy X s t d m' },
      ⟨ht, hf, hx, rfl⟩, rfl⟩

/-- ✗ A wait that forgets every clock violates TIME-015 (line 3). Read in the state the wait
reached, nothing is armed, so the boundary check there passes vacuously; read with the stamps
held before the wait, `w` (`Window(2, 3)`, armed at `0`) has elapsed time `1` after a wait of
`1`, below its earliest bound `2`, and it fires. -/
@[evidence forbids TIME_015]
theorem TIME_015_forbids_dropStamps : ¬ TIME_015 time015_dropStamps := by
  intro h
  exact (h time015_X).2.2.1 1 time015_w (time015_at 0)
    { time015_at 0 with now := 1, stamp := fun _ => none } rfl (by decide) (by decide) []
    { m := fireNC (time015_at 0).m time015_w.core (depProd []), now := 1,
      stamp := restampAll refPolicy time015_X
        { time015_at 0 with now := 1, stamp := fun _ => none } time015_w []
        (fireNC (time015_at 0).m time015_w.core (depProd [])) }
    ⟨by simp [time015_X], ⟨rfl, ⟨.action 0, rfl⟩, rfl⟩, by decide, rfl⟩

/-! ### Every line exercised -/

/-- Every line of TIME-015 is exercised by the reference step, in the net of `w`
(`Window(2, 3)`) and `k` (`Deadline(3)`), both armed at reading `0`, tolerance 0. A delay of `1`
reads `1` (lines 1 and 2); a wait that completes there finds `w` armed with elapsed time `1`,
below its earliest bound `2`, and `w` does not fire (line 3). A delay of `2` reads `2`, where
`w` fires and the reading stays `2` (line 1 for a firing). A delay of `4` overshoots `w`'s
window: `w` is expired at reading `4` and does not fire (line 4), and `k`, expired too, is reaped
and the reading stays `4` (line 1 for a reap). A delay of `0` stays where it is, since readings
may repeat. -/
@[evidence nonvacuous TIME_015]
theorem TIME_015_nonvacuous :
    RefTStep time015_X (time015_at 0) (.delay 1) (time015_at 1) ∧
      ClockReading (time015_at 1) = ClockReading (time015_at 0) + 1 ∧
      Armed (AfterWait (time015_at 0) (time015_at 1)) time015_w ∧
      Elapsed (AfterWait (time015_at 0) (time015_at 1)) time015_w <
        (TimingOf time015_X time015_w).earliest ∧
      (∀ d s', ¬ RefTStep time015_X (time015_at 1) (.fire time015_w d) s') ∧
      RefTStep time015_X (time015_at 0) (.delay 2) (time015_at 2) ∧
      RefTStep time015_X (time015_at 2) (.fire time015_w []) (time015_fired refPolicy 2) ∧
      ClockReading (time015_fired refPolicy 2) = ClockReading (time015_at 2) ∧
      RefTStep time015_X (time015_at 0) (.delay 4) (time015_at 4) ∧
      Expired time015_X (AfterWait (time015_at 0) (time015_at 4)) time015_w ∧
      (∀ d s', ¬ RefTStep time015_X (time015_at 4) (.fire time015_w d) s') ∧
      RefTStep time015_X (time015_at 4) (.reap time015_k)
        { time015_at 4 with stamp := fun n => if n = "k" then none else (time015_at 4).stamp n } ∧
      RefTStep time015_X (time015_at 4) (.delay 0) (time015_at 4) := by
  refine ⟨time015_reach _ 1, rfl, by decide, by decide, fun d s' h => ?_, time015_reach _ 2,
    time015_w_fires (by decide) (by decide), rfl, time015_reach _ 4, by decide,
    fun d s' h => ?_, RefTStepW.reap _ _ _ (by simp [time015_X]) (by decide),
    time015_stutter _ _ _⟩
  · have := time010_gate rfl h
    revert this
    decide
  · exact time015_notExpired (P := refPolicy) rfl h (by decide)

end Libpetri.Spec
