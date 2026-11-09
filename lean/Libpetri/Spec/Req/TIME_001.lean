import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime

set_option linter.missingDocs true

/-!
# TIME-001: Timing specification (`spec/03-timing.md`)

TIME-001 is a pure-function requirement (kind F): it fixes the three accessors every timing
exposes (`earliest()`, `latest()`, `hasDeadline()`), the validity table, the message a factory
fails with when the bounds break a rule of the table, and the check the transition builder runs
again on a timing written out without a factory. The statement is a predicate over a *timing
contract*: those three accessors, the factory and the builder of one implementation, over the
five variants of `Novel.TimedScg.Timing` (milliseconds). The witness is the reference contract,
built from `Timing.earliest`, `Timing.latest`, `Timing.hasDeadline` and `Timing.Valid`, the
functions the timed step (`RefTStep`) and the state-class graph (`Novel.TimedScg`) read.

The two body bullets (no firing before `earliest`, reaping past `latest` plus the tolerance) are
the rules of TIME-010 and TIME-013; this file does not encode them again, it cites them on the
reference step with the reference contract's accessors (`time001_fire_after_earliest`,
`time001_reap_past_latest`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## The model: a timing contract -/

/-- A timing contract: the accessors of [TIME-001] and the two places a timing is checked, for
every timing written out as a variant with its bounds (milliseconds). A call that fails (a
panic, an exception) is read as `.error msg`, with `msg` its message. -/
structure TimingContract where
  /-- `earliest()` of each timing. -/
  earliest    : Timing → Nat
  /-- `latest()` of each timing. -/
  latest      : Timing → Nat
  /-- `hasDeadline()` of each timing. -/
  hasDeadline : Timing → Bool
  /-- The factory of the variant called with the bounds of the timing: `.ok v` returns the
  timing `v`, `.error msg` fails with `msg`. -/
  factory     : Timing → Except String Timing
  /-- Building a transition with the timing written out without a factory: `.ok v` builds a
  transition whose timing is `v`, `.error msg` fails with `msg`. -/
  build       : Timing → Except String Timing
  /-- The timing of a transition built without one ([TIME-001] AC1, the builder's default). -/
  defaultTiming : Timing

namespace Time001

/-- `Timing.Valid` is decidable (it is a conjunction of `≤` and `<` per variant). -/
instance decValid : DecidablePred Timing.Valid := fun tm => by
  cases tm <;> unfold Timing.Valid <;> infer_instance

/-- `Timing.ValidPre` is decidable. -/
instance decValidPre : DecidablePred Timing.ValidPre := fun tm => by
  cases tm <;> unfold Timing.ValidPre <;> infer_instance

end Time001

open Time001 in
/-- The message the Rust factories (`timing.rs`, `deadline`, `delayed`, `window`, `exact`) panic
with, for a timing that is not `Timing.Valid`: the first check the bounds break, in the order the
factories run them. `Immediate` has no check; its entry is never raised. -/
def refTimingMsg : Timing → String
  | .deadline b =>
    if b = 0 then "Deadline must be positive: " ++ toString b
    else "Deadline must be at most MAX_DURATION_MS (3153600000000): " ++ toString b
  | .delayed a => "Delay must be at most MAX_DURATION_MS (3153600000000): " ++ toString a
  | .window e l =>
    if maxDurationMs < e then
      "Earliest must be at most MAX_DURATION_MS (3153600000000): " ++ toString e
    else if l < e then "Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")"
    else "Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l
  | .exact a => "Exact time must be at most MAX_DURATION_MS (3153600000000): " ++ toString a
  | .immediate => ""

open Time001 in
/-- The reference factory: accept a timing the shipped constructors accept (`Timing.Valid`) as
written, and fail with `refTimingMsg` otherwise. -/
def refTimingFactory (tm : Timing) : Except String Timing :=
  if tm.Valid then .ok tm else .error (refTimingMsg tm)

/-- The reference contract: the accessors of `Novel.TimedScg.Timing` (`timing.rs:108-138`), the
reference factory, and a builder that runs the factory's check again (`transition.rs::build`,
[TIME-001] AC5), so it builds a valid timing unchanged and fails on an invalid one with the
factory's message; a transition built without a timing is `Immediate` (`transition.rs`, AC1). -/
def refTimingQ : TimingContract where
  earliest    := Timing.earliest
  latest      := Timing.latest
  hasDeadline := Timing.hasDeadline
  factory     := refTimingFactory
  build       := refTimingFactory
  defaultTiming := .immediate

/- The reference contract is the witness model of TIME-001's `holds` theorem. -/
#spec_witness refTimingQ

/-! ## TIME-001: Timing Specification -/

requirement TIME_001
  id "TIME-001"
  title "Timing Specification"
  kind F
  scope "all timing variants, all implementations"
  source verbatim "spec/03-timing.md"
  quote "`earliest()` *shall* return 0 for `Immediate` and `Deadline`, `after` for `Delayed(after)`, `earliest` for `Window(earliest, latest)` and `at` for `Exact(at)`."
        "`latest()` *shall* return the maximum duration for `Immediate` and `Delayed`, `by` for `Deadline(by)`, `latest` for `Window(earliest, latest)` and `at` for `Exact(at)`."
        "`hasDeadline()` *shall* return true for `Deadline`, `Window` and `Exact`, and false for `Immediate` and `Delayed`."
        "A timing is **valid** exactly when its bounds satisfy these rules, which are canonical for every variant ([TIME-002]–[TIME-006] restate them):"
        "*If* a factory is called with bounds that make the timing invalid, *then* the factory *shall* fail with the message the table below gives for the first rule the bounds break (Rust panics; Python raises `ValueError` with the Rust message; Java throws `IllegalArgumentException`; TypeScript throws `Error`)."
        "The checks run in the order of the table."
        "*If* a transition is built with a timing written out without a factory and that timing is invalid, *then* building the transition *shall* fail with the factory's message."
        "Each transition has a timing specification (defaults to Immediate)."
  reading "For every timing contract K:"
          "earliest() is 0 for Immediate and Deadline(by), after for Delayed(after), earliest for Window(earliest, latest) and at for Exact(at);"
          "latest() is the maximum duration (3153600000000 ms) for Immediate and Delayed(after), by for Deadline(by), latest for Window(earliest, latest) and at for Exact(at);"
          "hasDeadline() is true for every Deadline, Window and Exact and false for every Immediate and Delayed, whatever the bounds;"
          "a factory called with bounds that satisfy the validity table (Immediate always, 0 < by <= maximum, after <= maximum, earliest <= latest <= maximum, at <= maximum) returns the timing as written;"
          "deadline(0) fails with 'Deadline must be positive: 0';"
          "deadline(by) with by above the maximum (so by is positive) fails with 'Deadline must be at most MAX_DURATION_MS (3153600000000): {by}';"
          "delayed(after) with after above the maximum fails with 'Delay must be at most MAX_DURATION_MS (3153600000000): {after}';"
          "window(earliest, latest) with earliest above the maximum fails with 'Earliest must be at most MAX_DURATION_MS (3153600000000): {earliest}', whatever latest is;"
          "window(earliest, latest) with earliest at most the maximum and latest below earliest fails with 'Latest ({latest}) must be >= earliest ({earliest})';"
          "window(earliest, latest) with earliest at most the maximum, latest at least earliest and latest above the maximum fails with 'Latest must be at most MAX_DURATION_MS (3153600000000): {latest}';"
          "exact(at) with at above the maximum fails with 'Exact time must be at most MAX_DURATION_MS (3153600000000): {at}';"
          "building a transition with a timing written out without a factory gives what the factory gives for its bounds: the same message for an invalid timing, the timing unchanged for a valid one;"
          "a transition built without a timing has the timing Immediate ({x} above is the argument in decimal milliseconds)."
  assumes "A contract is the accessors, the factories and the transition builder of one implementation over the five variants of the Rust enum (Novel.TimedScg.Timing), with bounds in milliseconds; a call that fails is read as `.error msg` with its message, a call that returns as `.ok`. `factory tm` is the factory of tm's variant called with tm's bounds; `build tm` builds a transition with tm written out directly (a Rust enum variant, a TypeScript object literal, a Java record constructor)."
          "Bounds are naturals, as Rust's `u64` arguments are, so the rows of the message table that check for a negative bound (TypeScript and Java only) and the `0 <=` halves of the validity table are not encoded. The messages are the Rust, TypeScript and Python form, with the argument printed in decimal milliseconds; Java's form (`MAX_DURATION (PT876000H)`, `Duration.toString()`) is the same table in another notation and is not encoded."
          "'The first rule the bounds break' together with 'The checks run in the order of the table' is encoded by the premises of lines 5 to 11: each line assumes the bounds pass every earlier rule of the variant (only `window` has rules the same bounds can break together; `deadline(0)` and `deadline(by > maximum)` exclude each other). Lines 4 to 11 fix the factory on every timing: a valid one is returned as written, an invalid one fails with exactly one message."
          "AC1 (each transition has a timing, Immediate by default) is line 13: `defaultTiming` is the timing the builder gives a transition built without one. The default Delayed(0), which has the same interval [0, maximum] as Immediate, is killed as TIME_001_mutant_sameInterval."
          "AC2 (earliest() and latest() are queryable) is lines 1 and 2; the value table of the accessors is the first two shall sentences."
          "AC3 (hasDeadline() by variant whatever the bounds, so a Window whose latest bound equals the maximum still has a deadline) is line 3 (ruling D2). The older literal reading 'hasDeadline() is latest below the maximum' is killed as TIME_001_mutant_latestBelowMax, on window(0, maximum). That a transition SHOULD be disabled after its latest bound is keyed on Reapable (Deadline, Window), not on hasDeadline: Exact has a deadline but is enforced softly (TIME-006, TIME-013)."
          "The validity table of line 4 is Timing.Valid, the predicate the timed step, the state-class graph and the TIME-002 to TIME-006 blocks read (time001_valid_iff, cited)."
          "AC4 (the validity table is canonical; the boundary at the maximum duration for every bound, including deadline's by and window's latest, with the table's messages) is lines 4 to 11 (ruling D11). The nonvacuous example TIME_001_nonvacuous checks each boundary named in AC4 and in the test derivation, window(maximum + 1, maximum + 2) included. The old checks (Timing.ValidPre: deadline only 0 < by, window only earliest <= latest, delayed and exact nothing) are killed as TIME_001_mutant_validPre."
          "AC5 (a timing written out without a factory is held to AC4 and to the factories' other checks, and a valid one builds unchanged) is line 12; TIME_001_forbids_uncheckedBuild is the builder that skips the check and passes delayed(maximum + 1) on to the verifier. Java's records check in their constructors, which the contract reads as a factory and a builder that agree."
          "A factory returns the timing as written (line 4): a valid window(earliest, maximum) stays a Window and keeps its deadline (AC3); it is not normalised to delayed(earliest)."
          "The two body bullets are the rules of other blocks and are not encoded again: no firing before the earliest bound since the transition was armed is TIME-010 (cited by time001_fire_after_earliest), and reaping a reapable transition once its elapsed time exceeds latest plus the deadline tolerance is TIME-013 (cited by time001_reap_past_latest). That Immediate and Delayed have no finite latest bound and their latest() reports the maximum duration is line 2; reading the maximum as no bound at all is not proven (Novel.TimedScg.Timing, module docstring)."
          "The maximum-duration constant is maxDurationMs = 3153600000000 (time001_maxDuration); Java's MAX_DURATION is Duration.ofDays(36500), the same duration. Java's sixth variant `Unconstrained` is not in the spec and not modelled."
  signoff "pending"
  statement : TimingContract → Prop :=
    fun K =>
      (∀ tm, K.earliest tm =
        match tm with
        | .immediate => 0
        | .deadline _ => 0
        | .delayed a => a
        | .window e _ => e
        | .exact a => a) ∧
      (∀ tm, K.latest tm =
        match tm with
        | .immediate => 3153600000000
        | .deadline b => b
        | .delayed _ => 3153600000000
        | .window _ l => l
        | .exact a => a) ∧
      (∀ tm, K.hasDeadline tm =
        match tm with
        | .immediate => false
        | .deadline _ => true
        | .delayed _ => false
        | .window _ _ => true
        | .exact _ => true) ∧
      (∀ tm, (match tm with
        | .immediate => True
        | .deadline b => 0 < b ∧ b ≤ 3153600000000
        | .delayed a => a ≤ 3153600000000
        | .window e l => e ≤ l ∧ l ≤ 3153600000000
        | .exact a => a ≤ 3153600000000) → K.factory tm = .ok tm) ∧
      (∀ b, b = 0 → K.factory (.deadline b) = .error ("Deadline must be positive: " ++ toString b)) ∧
      (∀ b, 3153600000000 < b → K.factory (.deadline b) =
        .error ("Deadline must be at most MAX_DURATION_MS (3153600000000): " ++ toString b)) ∧
      (∀ a, 3153600000000 < a → K.factory (.delayed a) =
        .error ("Delay must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
      (∀ e l, 3153600000000 < e → K.factory (.window e l) =
        .error ("Earliest must be at most MAX_DURATION_MS (3153600000000): " ++ toString e)) ∧
      (∀ e l, e ≤ 3153600000000 → l < e → K.factory (.window e l) =
        .error ("Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")")) ∧
      (∀ e l, e ≤ 3153600000000 → e ≤ l → 3153600000000 < l → K.factory (.window e l) =
        .error ("Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l)) ∧
      (∀ a, 3153600000000 < a → K.factory (.exact a) =
        .error ("Exact time must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
      (∀ tm, K.build tm = K.factory tm) ∧
      K.defaultTiming = .immediate


/- The pinned readable form of TIME-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_001 : TimingContract → Prop :=
fun K =>
  (∀ (tm : Timing),
      K.earliest tm =
        match tm with
        | Timing.immediate => 0
        | Timing.deadline byMs => 0
        | Timing.delayed a => a
        | Timing.window e latestMs => e
        | Timing.exact a => a) ∧
    (∀ (tm : Timing),
        K.latest tm =
          match tm with
          | Timing.immediate => 3153600000000
          | Timing.deadline b => b
          | Timing.delayed afterMs => 3153600000000
          | Timing.window earliestMs l => l
          | Timing.exact a => a) ∧
      (∀ (tm : Timing),
          K.hasDeadline tm =
            match tm with
            | Timing.immediate => false
            | Timing.deadline byMs => true
            | Timing.delayed afterMs => false
            | Timing.window earliestMs latestMs => true
            | Timing.exact atMs => true) ∧
        (∀ (tm : Timing),
            (match tm with
              | Timing.immediate => True
              | Timing.deadline b => 0 < b ∧ b ≤ 3153600000000
              | Timing.delayed a => a ≤ 3153600000000
              | Timing.window e l => e ≤ l ∧ l ≤ 3153600000000
              | Timing.exact a => a ≤ 3153600000000) →
              K.factory tm = Except.ok tm) ∧
          (∀ (b : ℕ),
              b = 0 → K.factory (Timing.deadline b) = Except.error ("Deadline must be positive: " ++ toString b)) ∧
            (∀ (b : ℕ),
                3153600000000 < b →
                  K.factory (Timing.deadline b) =
                    Except.error ("Deadline must be at most MAX_DURATION_MS (3153600000000): " ++ toString b)) ∧
              (∀ (a : ℕ),
                  3153600000000 < a →
                    K.factory (Timing.delayed a) =
                      Except.error ("Delay must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
                (∀ (e l : ℕ),
                    3153600000000 < e →
                      K.factory (Timing.window e l) =
                        Except.error ("Earliest must be at most MAX_DURATION_MS (3153600000000): " ++ toString e)) ∧
                  (∀ (e l : ℕ),
                      e ≤ 3153600000000 →
                        l < e →
                          K.factory (Timing.window e l) =
                            Except.error ("Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")")) ∧
                    (∀ (e l : ℕ),
                        e ≤ 3153600000000 →
                          e ≤ l →
                            3153600000000 < l →
                              K.factory (Timing.window e l) =
                                Except.error
                                  ("Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l)) ∧
                      (∀ (a : ℕ),
                          3153600000000 < a →
                            K.factory (Timing.exact a) =
                              Except.error
                                ("Exact time must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
                        (∀ (tm : Timing), K.build tm = K.factory tm) ∧ K.defaultTiming = Timing.immediate
-/
#guard_msgs in #print TIME_001

/-- The maximum duration of the spec, `MAX_DURATION_MS` = 3153600000000 ms, is the constant the
reference timings use (`Novel.TimedScg.maxDurationMs`, 100 years of 365 days). -/
theorem time001_maxDuration : maxDurationMs = 3153600000000 := rfl

/-- The validity table of TIME-001 (line 4) is `Timing.Valid`, what the shipped constructors
assert, on every timing. -/
@[evidence cites "TIME-001" "the validity table (line 4 of the TIME-001 block) is Timing.Valid, the predicate the timed reference step, the state-class graph and the TIME-002 to TIME-006 restatements read"]
theorem time001_valid_iff (tm : Timing) :
    tm.Valid ↔ (match tm with
      | .immediate => True
      | .deadline b => 0 < b ∧ b ≤ 3153600000000
      | .delayed a => a ≤ 3153600000000
      | .window e l => e ≤ l ∧ l ≤ 3153600000000
      | .exact a => a ≤ 3153600000000) := by
  cases tm <;> simp only [Timing.Valid, time001_maxDuration]
  omega

/-- The reference factory on an invalid timing fails with `refTimingMsg`. -/
theorem refTimingFactory_of_not_valid {tm : Timing} (h : ¬ tm.Valid) :
    refTimingFactory tm = .error (refTimingMsg tm) := by
  unfold refTimingFactory; rw [if_neg h]

/-- The reference contract satisfies TIME-001: the accessors are `Timing.earliest`,
`Timing.latest` and `Timing.hasDeadline`, whose tables are the spec's; the factory accepts
exactly `Timing.Valid`, which is the validity table (`time001_valid_iff`), and otherwise fails
with the message of the first check `timing.rs` runs; and the builder runs the same check. -/
@[evidence holds TIME_001]
theorem TIME_001_reference : TIME_001 refTimingQ := by
  refine ⟨fun tm => by cases tm <;> rfl, fun tm => by cases tm <;> rfl,
    fun tm => by cases tm <;> rfl, fun tm h => ?_, fun b hb => ?_, fun b hb => ?_,
    fun a ha => ?_, fun e l he => ?_, fun e l he hl => ?_, fun e l he hel hl => ?_,
    fun a ha => ?_, fun _ => rfl, rfl⟩
  · show refTimingFactory tm = _
    unfold refTimingFactory; rw [if_pos ((time001_valid_iff tm).2 h)]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, hb])]
    simp [refTimingMsg, hb]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    simp [refTimingMsg, show b ≠ 0 by omega]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    rfl
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    simp [refTimingMsg, time001_maxDuration, he]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    simp [refTimingMsg, time001_maxDuration, hl, show ¬ 3153600000000 < e by omega]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    simp [refTimingMsg, time001_maxDuration, show ¬ 3153600000000 < e by omega,
      show ¬ l < e by omega]
  · show refTimingFactory _ = _
    rw [refTimingFactory_of_not_valid (by simp [Timing.Valid, time001_maxDuration]; omega)]
    rfl

/-! ### TIME-001 fixes the contract -/

/-- Any two contracts that satisfy TIME-001 have the same factory: lines 4 to 11 decide every
timing, a valid one as written and an invalid one with exactly one message. -/
theorem time001_factory_det {K J : TimingContract} (hK : TIME_001 K) (hJ : TIME_001 J) :
    K.factory = J.factory := by
  obtain ⟨-, -, -, k4, k5, k6, k7, k8, k9, k10, k11, -, -⟩ := hK
  obtain ⟨-, -, -, j4, j5, j6, j7, j8, j9, j10, j11, -, -⟩ := hJ
  funext tm
  cases tm with
  | immediate => rw [k4 .immediate trivial, j4 .immediate trivial]
  | deadline b =>
    by_cases h0 : b = 0
    · rw [k5 b h0, j5 b h0]
    · by_cases hm : b ≤ 3153600000000
      · rw [k4 (.deadline b) ⟨by omega, hm⟩, j4 (.deadline b) ⟨by omega, hm⟩]
      · rw [k6 b (by omega), j6 b (by omega)]
  | delayed a =>
    by_cases hm : a ≤ 3153600000000
    · rw [k4 (.delayed a) hm, j4 (.delayed a) hm]
    · rw [k7 a (by omega), j7 a (by omega)]
  | window e l =>
    by_cases he : 3153600000000 < e
    · rw [k8 e l he, j8 e l he]
    · by_cases hle : l < e
      · rw [k9 e l (by omega) hle, j9 e l (by omega) hle]
      · by_cases hl : l ≤ 3153600000000
        · rw [k4 (.window e l) ⟨by omega, hl⟩, j4 (.window e l) ⟨by omega, hl⟩]
        · rw [k10 e l (by omega) (by omega) (by omega), j10 e l (by omega) (by omega) (by omega)]
  | exact a =>
    by_cases hm : a ≤ 3153600000000
    · rw [k4 (.exact a) hm, j4 (.exact a) hm]
    · rw [k11 a (by omega), j11 a (by omega)]

/-- **TIME-001 has exactly one model, the reference contract.** Every accessor is fixed by its
table, the factory by lines 4 to 11 and the builder by line 12, so no wrong contract (one that
skips a check, reorders the checks, normalises a timing or reads `hasDeadline()` off the bounds)
satisfies the statement. -/
theorem time001_unique (K : TimingContract) : TIME_001 K ↔ K = refTimingQ := by
  refine ⟨fun hK => ?_, fun e => e ▸ TIME_001_reference⟩
  have hf := time001_factory_det hK TIME_001_reference
  obtain ⟨k1, k2, k3, -, -, -, -, -, -, -, -, k12, k13⟩ := hK
  obtain ⟨r1, r2, r3, -, -, -, -, -, -, -, -, r12, -⟩ := TIME_001_reference
  cases K with
  | mk ea la ha fa ba da =>
    have e1 : ea = refTimingQ.earliest := funext fun tm => (k1 tm).trans (r1 tm).symm
    have e2 : la = refTimingQ.latest := funext fun tm => (k2 tm).trans (r2 tm).symm
    have e3 : ha = refTimingQ.hasDeadline := funext fun tm => (k3 tm).trans (r3 tm).symm
    have e5 : ba = refTimingQ.build :=
      funext fun tm => ((k12 tm).trans (congrFun hf tm)).trans (r12 tm).symm
    simp only at hf k13
    rw [e1, e2, e3, hf, e5, k13]
    rfl

/-! ### Examples: wrong contracts -/

/-- A builder that does not run the factory's check again: it builds every timing written out
directly, valid or not (the Rust builder before AC5). -/
def time001_uncheckedBuildQ : TimingContract := { refTimingQ with build := .ok }

/-- ✗ A builder that skips the check violates TIME-001 (line 12, AC5): it builds a transition
with `delayed(maximum + 1)` written out directly, which the factory rejects, and hands the
verifier an empty interval. -/
@[evidence forbids TIME_001]
theorem TIME_001_forbids_uncheckedBuild : ¬ TIME_001 time001_uncheckedBuildQ := by
  intro h
  exact absurd (h.2.2.2.2.2.2.2.2.2.2.2.1 (.delayed 3153600000001)) (by decide)

/-- A factory that normalises a window without a finite deadline: `window(earliest, maximum)` is
returned as `delayed(earliest)`, which has the same interval in the state-class graph but no
deadline. -/
def time001_normaliseQ : TimingContract :=
  let f : Timing → Except String Timing := fun tm => match tm with
    | .window e l => if l = 3153600000000 then .ok (.delayed e) else refTimingFactory (.window e l)
    | tm => refTimingFactory tm
  { refTimingQ with factory := f, build := f }

/-- ✗ Normalising `window(0, maximum)` to `delayed(0)` violates TIME-001 (line 4): a valid
timing is returned as written, so the window keeps its deadline (AC3). -/
@[evidence forbids TIME_001]
theorem TIME_001_forbids_normalise : ¬ TIME_001 time001_normaliseQ := by
  intro h
  exact absurd (h.2.2.2.1 (.window 0 3153600000000) (by decide)) (by decide)

/-! ### Mutant: the old checks (`Timing.ValidPre`) -/

open Time001 in
/-- The message of the old checks: `deadline` checked only `0 < by`, `window` only
`earliest <= latest`; the other variants checked nothing and never failed. -/
def time001PreMsg : Timing → String
  | .deadline b => "Deadline must be positive: " ++ toString b
  | .window e l => "Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")"
  | _ => ""

open Time001 in
/-- The factory of the old checks: accept `Timing.ValidPre`, fail with the old message
otherwise. -/
def time001PreFactory (tm : Timing) : Except String Timing :=
  if tm.ValidPre then .ok tm else .error (time001PreMsg tm)

/-- The contract of the old checks: the reference accessors, the old factory, and a builder
that runs it again. -/
def time001_preQ : TimingContract :=
  { refTimingQ with factory := time001PreFactory, build := time001PreFactory }

/-- Mutant reading of TIME-001 with the old validity table (`Timing.ValidPre`): `deadline` needs
only `0 < by`, `window` only `earliest <= latest`, `delayed` and `exact` are always valid, and
the only failures are the two old ones. The accessors and the builder are as in TIME-001. -/
def TIME_001_mutant_validPre (K : TimingContract) : Prop :=
  (∀ tm, K.earliest tm =
    match tm with
    | .immediate => 0
    | .deadline _ => 0
    | .delayed a => a
    | .window e _ => e
    | .exact a => a) ∧
  (∀ tm, K.latest tm =
    match tm with
    | .immediate => 3153600000000
    | .deadline b => b
    | .delayed _ => 3153600000000
    | .window _ l => l
    | .exact a => a) ∧
  (∀ tm, K.hasDeadline tm =
    match tm with
    | .immediate => false
    | .deadline _ => true
    | .delayed _ => false
    | .window _ _ => true
    | .exact _ => true) ∧
  (∀ tm, (match tm with
    | .deadline b => 0 < b
    | .window e l => e ≤ l
    | _ => True) → K.factory tm = .ok tm) ∧
  (∀ b, b = 0 → K.factory (.deadline b) = .error ("Deadline must be positive: " ++ toString b)) ∧
  (∀ e l, l < e → K.factory (.window e l) =
    .error ("Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")")) ∧
  (∀ tm, K.build tm = K.factory tm) ∧
  K.defaultTiming = .immediate

/-- The contract of the old checks kills the mutant: it meets the old table, but not TIME-001,
since it accepts `deadline(maximum + 1)`, a deadline no run reaches (AC4). -/
@[evidence mutant TIME_001]
theorem TIME_001_mutant_validPre_killed :
    TIME_001_mutant_validPre time001_preQ ∧ ¬ TIME_001 time001_preQ := by
  obtain ⟨h1, h2, h3, -⟩ := TIME_001_reference
  refine ⟨⟨h1, h2, h3, fun tm h => ?_, fun b hb => ?_, fun e l hl => ?_, fun _ => rfl, rfl⟩,
    fun h => ?_⟩
  · show time001PreFactory tm = _
    unfold time001PreFactory
    rw [if_pos (by revert h; cases tm <;> simp [Timing.ValidPre])]
  · show time001PreFactory _ = _
    unfold time001PreFactory
    rw [if_neg (by simp [Timing.ValidPre, hb])]
    rfl
  · show time001PreFactory _ = _
    unfold time001PreFactory
    rw [if_neg (by simp [Timing.ValidPre]; omega)]
    rfl
  · exact absurd (h.2.2.2.2.2.1 3153600000001 (by decide)) (by decide)

/-! ### Mutant: `hasDeadline()` as "latest below the maximum" -/

/-- The contract that reads `hasDeadline()` literally as "the latest bound is below the maximum
duration", and is the reference otherwise. -/
def time001_latestBelowMaxQ : TimingContract :=
  { refTimingQ with hasDeadline := fun tm => decide (tm.latest < 3153600000000) }

/-- Mutant reading of TIME-001 with the literal older AC3: `hasDeadline()` is true exactly when
`latest()` is below the maximum duration. The other lines are as in TIME-001. -/
def TIME_001_mutant_latestBelowMax (K : TimingContract) : Prop :=
  (∀ tm, K.earliest tm =
    match tm with
    | .immediate => 0
    | .deadline _ => 0
    | .delayed a => a
    | .window e _ => e
    | .exact a => a) ∧
  (∀ tm, K.latest tm =
    match tm with
    | .immediate => 3153600000000
    | .deadline b => b
    | .delayed _ => 3153600000000
    | .window _ l => l
    | .exact a => a) ∧
  (∀ tm, K.hasDeadline tm = decide (K.latest tm < 3153600000000)) ∧
  (∀ tm, (match tm with
    | .immediate => True
    | .deadline b => 0 < b ∧ b ≤ 3153600000000
    | .delayed a => a ≤ 3153600000000
    | .window e l => e ≤ l ∧ l ≤ 3153600000000
    | .exact a => a ≤ 3153600000000) → K.factory tm = .ok tm) ∧
  (∀ b, b = 0 → K.factory (.deadline b) = .error ("Deadline must be positive: " ++ toString b)) ∧
  (∀ b, 3153600000000 < b → K.factory (.deadline b) =
    .error ("Deadline must be at most MAX_DURATION_MS (3153600000000): " ++ toString b)) ∧
  (∀ a, 3153600000000 < a → K.factory (.delayed a) =
    .error ("Delay must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
  (∀ e l, 3153600000000 < e → K.factory (.window e l) =
    .error ("Earliest must be at most MAX_DURATION_MS (3153600000000): " ++ toString e)) ∧
  (∀ e l, e ≤ 3153600000000 → l < e → K.factory (.window e l) =
    .error ("Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")")) ∧
  (∀ e l, e ≤ 3153600000000 → e ≤ l → 3153600000000 < l → K.factory (.window e l) =
    .error ("Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l)) ∧
  (∀ a, 3153600000000 < a → K.factory (.exact a) =
    .error ("Exact time must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
  (∀ tm, K.build tm = K.factory tm) ∧
  K.defaultTiming = .immediate

/-- The literal contract kills the mutant: it meets the mutant, but not TIME-001, since
`window(0, maximum)` has a deadline by its variant and none by the literal reading (AC3). -/
@[evidence mutant TIME_001]
theorem TIME_001_mutant_latestBelowMax_killed :
    TIME_001_mutant_latestBelowMax time001_latestBelowMaxQ ∧ ¬ TIME_001 time001_latestBelowMaxQ := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := TIME_001_reference
  refine ⟨⟨h1, h2, fun _ => rfl, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, fun h => ?_⟩
  exact absurd (h.2.2.1 (.window 0 3153600000000)) (by decide)

/-! ### Mutant: any broken rule instead of the first -/

/-- The factory that runs `window`'s checks with the latest bound's upper limit first, and is the
reference otherwise. -/
def time001LatestFirstFactory : Timing → Except String Timing
  | .window e l =>
    if 3153600000000 < l then
      .error ("Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l)
    else refTimingFactory (.window e l)
  | tm => refTimingFactory tm

/-- The contract whose factory and builder run `window`'s checks in another order. -/
def time001_latestFirstQ : TimingContract :=
  { refTimingQ with factory := time001LatestFirstFactory, build := time001LatestFirstFactory }

/-- Mutant reading of TIME-001 that drops "the first rule": an invalid `window` fails with the
message of some rule its bounds break, not necessarily the first in the table's order. The other
lines are as in TIME-001. -/
def TIME_001_mutant_anyRule (K : TimingContract) : Prop :=
  (∀ tm, K.earliest tm =
    match tm with
    | .immediate => 0
    | .deadline _ => 0
    | .delayed a => a
    | .window e _ => e
    | .exact a => a) ∧
  (∀ tm, K.latest tm =
    match tm with
    | .immediate => 3153600000000
    | .deadline b => b
    | .delayed _ => 3153600000000
    | .window _ l => l
    | .exact a => a) ∧
  (∀ tm, K.hasDeadline tm =
    match tm with
    | .immediate => false
    | .deadline _ => true
    | .delayed _ => false
    | .window _ _ => true
    | .exact _ => true) ∧
  (∀ tm, (match tm with
    | .immediate => True
    | .deadline b => 0 < b ∧ b ≤ 3153600000000
    | .delayed a => a ≤ 3153600000000
    | .window e l => e ≤ l ∧ l ≤ 3153600000000
    | .exact a => a ≤ 3153600000000) → K.factory tm = .ok tm) ∧
  (∀ b, b = 0 → K.factory (.deadline b) = .error ("Deadline must be positive: " ++ toString b)) ∧
  (∀ b, 3153600000000 < b → K.factory (.deadline b) =
    .error ("Deadline must be at most MAX_DURATION_MS (3153600000000): " ++ toString b)) ∧
  (∀ a, 3153600000000 < a → K.factory (.delayed a) =
    .error ("Delay must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
  (∀ e l, ¬ (e ≤ l ∧ l ≤ 3153600000000) →
    (3153600000000 < e ∧ K.factory (.window e l) =
      .error ("Earliest must be at most MAX_DURATION_MS (3153600000000): " ++ toString e)) ∨
    (l < e ∧ K.factory (.window e l) =
      .error ("Latest (" ++ toString l ++ ") must be >= earliest (" ++ toString e ++ ")")) ∨
    (3153600000000 < l ∧ K.factory (.window e l) =
      .error ("Latest must be at most MAX_DURATION_MS (3153600000000): " ++ toString l))) ∧
  (∀ a, 3153600000000 < a → K.factory (.exact a) =
    .error ("Exact time must be at most MAX_DURATION_MS (3153600000000): " ++ toString a)) ∧
  (∀ tm, K.build tm = K.factory tm) ∧
  K.defaultTiming = .immediate

/-- The latest-first factory kills the mutant: it fails every invalid `window` with the message
of a rule the bounds break, but not TIME-001, since `window(maximum + 1, maximum + 2)` breaks the
earliest bound's rule first and gets the latest bound's message (the test derivation of AC4). -/
@[evidence mutant TIME_001]
theorem TIME_001_mutant_anyRule_killed :
    TIME_001_mutant_anyRule time001_latestFirstQ ∧ ¬ TIME_001 time001_latestFirstQ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h13⟩ := TIME_001_reference
  refine ⟨⟨h1, h2, h3, fun tm h => ?_, h5, h6, h7, fun e l hv => ?_, h11, fun _ => rfl, h13⟩,
    fun h => ?_⟩
  · cases tm with
    | window e l =>
      show time001LatestFirstFactory (.window e l) = _
      simp only [time001LatestFirstFactory, if_neg (show ¬ 3153600000000 < l by
        simp at h; omega)]
      exact h4 (.window e l) h
    | _ => exact h4 _ h
  · have hf : time001_latestFirstQ.factory (.window e l) =
        time001LatestFirstFactory (.window e l) := rfl
    rw [hf]
    by_cases hl : 3153600000000 < l
    · exact .inr (.inr ⟨hl, by simp only [time001LatestFirstFactory, if_pos hl]⟩)
    · simp only [time001LatestFirstFactory, if_neg hl]
      by_cases he : 3153600000000 < e
      · exact .inl ⟨he, h8 e l he⟩
      · exact .inr (.inl ⟨by omega, h9 e l (by omega) (by omega)⟩)
  · exact absurd (h.2.2.2.2.2.2.2.1 3153600000001 3153600000002 (by decide)) (by decide)

/-! ### Mutant: the default as "a timing with Immediate's interval" -/

/-- The contract whose builder gives a transition built without a timing `delayed(0)`, and is the
reference otherwise. -/
def time001_defaultDelayedQ : TimingContract := { refTimingQ with defaultTiming := .delayed 0 }

/-- Mutant reading of AC1: the default timing only has to look like `Immediate` through the
accessors (earliest 0, latest the maximum, no deadline). Lines 1 to 12 are as in TIME-001 (stated
on the contract with its default replaced, which those lines do not read). -/
def TIME_001_mutant_sameInterval (K : TimingContract) : Prop :=
  TIME_001 { K with defaultTiming := .immediate } ∧
  K.earliest K.defaultTiming = 0 ∧ K.latest K.defaultTiming = 3153600000000 ∧
  K.hasDeadline K.defaultTiming = false

/-- The `delayed(0)` default kills the mutant: `delayed(0)` has the interval `[0, maximum]` and no
deadline, as `Immediate` has, so it meets the mutant, but TIME-001 fixes the default to
`Immediate` itself (AC1, line 13). The two differ wherever the variant is read, for example by
the TIME-003 factory checks and by a state-class graph keyed on the variant. -/
@[evidence mutant TIME_001]
theorem TIME_001_mutant_sameInterval_killed :
    TIME_001_mutant_sameInterval time001_defaultDelayedQ ∧ ¬ TIME_001 time001_defaultDelayedQ := by
  refine ⟨⟨TIME_001_reference, rfl, rfl, rfl⟩, fun h => ?_⟩
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2 (by decide)

/-! ### Non-vacuity: the boundary of AC4 and the tables of AC2 and AC3 -/

/-- Every line of TIME-001 is exercised by the reference contract. AC2: `window(2, 5)` reports
`[2, 5]`, `delayed(7)` and `immediate` report the maximum as their latest bound, `exact(4)`
reports `[4, 4]`. AC3: `window(0, maximum)` and `exact(maximum)` have a deadline, `delayed(3)`
has none. AC4: `deadline`, `delayed`, `exact` at the maximum and `window(maximum, maximum)`,
`window(0, maximum)` are returned as written; one millisecond above, each fails with the table's
message, `window(maximum + 1, maximum + 2)` with the earliest bound's; `deadline(0)` and
`window(5, 3)` fail with theirs. AC5: written out directly, `delayed(maximum + 1)` fails to build
with the factory's message, as do `deadline(0)`, `window(5, 3)` and `window(maximum + 1,
maximum + 2)` (the window the verifier would panic on), and `window(2, 5)` builds unchanged. AC1:
the default timing is `Immediate`. -/
@[evidence nonvacuous TIME_001]
theorem TIME_001_nonvacuous :
    refTimingQ.earliest (.window 2 5) = 2 ∧ refTimingQ.latest (.window 2 5) = 5 ∧
      refTimingQ.latest .immediate = 3153600000000 ∧
      refTimingQ.latest (.delayed 7) = 3153600000000 ∧
      refTimingQ.earliest (.exact 4) = 4 ∧ refTimingQ.latest (.exact 4) = 4 ∧
      refTimingQ.hasDeadline (.window 0 3153600000000) = true ∧
      refTimingQ.hasDeadline (.exact 3153600000000) = true ∧
      refTimingQ.hasDeadline (.delayed 3) = false ∧
      refTimingQ.factory (.deadline 3153600000000) = .ok (.deadline 3153600000000) ∧
      refTimingQ.factory (.delayed 3153600000000) = .ok (.delayed 3153600000000) ∧
      refTimingQ.factory (.exact 3153600000000) = .ok (.exact 3153600000000) ∧
      refTimingQ.factory (.window 3153600000000 3153600000000) =
        .ok (.window 3153600000000 3153600000000) ∧
      refTimingQ.factory (.window 0 3153600000000) = .ok (.window 0 3153600000000) ∧
      refTimingQ.factory .immediate = .ok .immediate ∧
      refTimingQ.factory (.deadline 0) = .error "Deadline must be positive: 0" ∧
      refTimingQ.factory (.deadline 3153600000001) =
        .error "Deadline must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.factory (.delayed 3153600000001) =
        .error "Delay must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.factory (.exact 3153600000001) =
        .error "Exact time must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.factory (.window 3153600000001 3153600000002) =
        .error "Earliest must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.factory (.window 5 3) = .error "Latest (3) must be >= earliest (5)" ∧
      refTimingQ.factory (.window 3153600000000 3153600000001) =
        .error "Latest must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.factory (.window 0 3153600000001) =
        .error "Latest must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.build (.delayed 3153600000001) =
        .error "Delay must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.build (.window 2 5) = .ok (.window 2 5) ∧
      refTimingQ.build (.deadline 0) = .error "Deadline must be positive: 0" ∧
      refTimingQ.build (.window 5 3) = .error "Latest (3) must be >= earliest (5)" ∧
      refTimingQ.build (.window 3153600000001 3153600000002) =
        .error "Earliest must be at most MAX_DURATION_MS (3153600000000): 3153600000001" ∧
      refTimingQ.defaultTiming = .immediate := by
  decide

/-! ### The body bullets, on the reference step (cited, not re-encoded) -/

/-- Body bullet 1 on the timed reference step: a transition fires only when armed and with its
elapsed time at least `earliest()` of its timing. -/
@[evidence cites "TIME-001" "body bullet 1 (no firing before earliest() has elapsed since the transition was armed), on the timed reference step RefTStep with the reference contract's earliest(); the rule itself is the TIME-010 block", evidence cites "TIME-010" "the earliest-bound gate of the timed reference step reads earliest() of the TIME-001 reference contract (Timing.earliest)"]
theorem time001_fire_after_earliest {N : Type} [DecidableEq N] {X : TimedNet N}
    {s s' : TSt N} {u : Trans N} {d : List N} (h : RefTStep X s (.fire u d) s') :
    Armed s u ∧ refTimingQ.earliest (TimingOf X u) ≤ Elapsed s u := by
  obtain ⟨-, -, hr, -⟩ := refTStep_fire_inv h
  exact ⟨hr.1, hr.2.1⟩

/-- Body bullet 2 on the timed reference step: a reaped transition has a `Deadline` or `Window`
timing (so it has a deadline, and `Exact`, `Immediate` and `Delayed` are never reaped), and its
elapsed time exceeds `latest()` of its timing plus the deadline tolerance. -/
@[evidence cites "TIME-001" "body bullet 2 (a reapable Deadline or Window is reaped only once its elapsed time exceeds latest() plus the deadline tolerance; Exact, Immediate and Delayed are never reaped), on the timed reference step RefTStep with the reference contract's latest() and hasDeadline(); the rule itself is the TIME-013 block", evidence cites "TIME-013" "the reap step of the timed reference step reads latest() of the TIME-001 reference contract (Timing.latest), strictly past latest plus the tolerance, and only for Deadline and Window"]
theorem time001_reap_past_latest {N : Type} [DecidableEq N] {X : TimedNet N}
    {s s' : TSt N} {t : Trans N} (h : RefTStep X s (.reap t) s') :
    ((∃ b, TimingOf X t = .deadline b) ∨ ∃ e l, TimingOf X t = .window e l) ∧
      refTimingQ.hasDeadline (TimingOf X t) = true ∧
      refTimingQ.latest (TimingOf X t) + Tolerance X < Elapsed s t := by
  have hx : refPolicy.expired X s t = true := by
    unfold RefTStep at h
    match h with
    | .reap _ _ _ _ hx => exact hx
  simp only [refPolicy, tExpired, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨hr, -⟩, hl⟩ := hx
  refine ⟨?_, Timing.reapable_hasDeadline hr, hl⟩
  revert hr
  change (X.timing t).reapable = true →
    (∃ b, X.timing t = .deadline b) ∨ ∃ e l, X.timing t = .window e l
  cases X.timing t <;> simp [Timing.reapable]

end Libpetri.Spec
