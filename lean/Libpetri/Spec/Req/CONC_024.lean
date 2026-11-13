import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_001
import Libpetri.Spec.Req.EXEC_002
import Libpetri.Spec.Text.CONC_024

set_option linter.missingDocs true

/-!
# CONC-024: Precomputed timing arrays (`spec/05-concurrency.md`)

CONC-024 is a pure-function requirement (kind F): when a net is precompiled, a table is filled
from the timings of its transitions, and the executor reads the table instead of the timings.
The requirement is a predicate over an abstract *timing compiler* `C : TimingCompile` (from the
number of transitions and the timing of each, by declaration index, to a `TimingTable`) and a
timing contract `K` of [TIME-001] whose accessors the table caches. TIME-001 says what the
accessors return; this block says the table holds what they return, so a joint model satisfies
`TIME_001 K` and `CONC_024 K C` with the same `K`.

The witness is `refTimingCompile`, the compiler over the reference contract `refTimingQ`. Wrong
compilers (a flag read off the earliest bounds, a flag read as "no deadlines", a deadline flag read
off the bounds, an earliest entry kept only for `Delayed`, a `Window` latest entry dropped, a
deadline count that ignores `Exact`, flags stuck at their conservative values) are killed by
`forbids` and `mutant` evidence. Two derived theorems give the purpose of the flags (AC2, AC3):
with `allImmediate` set, Ready is Armed (`conc024_skipTiming`); with `anyDeadlines` clear, no
transition is reapable or expired (`conc024_skipDeadlines`). `conc024_fastPath` links the flag to
EXEC-002's fast-path condition. `conc024_deadlineAt` shows that a reader who looks at the latest
entry only where the deadline flag is set sees the same deadlines under every compiler that
satisfies CONC-024, which is why the latest entry of a transition without a deadline is left free.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## The model: a timing compiler -/

/-- The timing table of a precompiled net: one entry per transition id, and two global flags.
Bounds are in milliseconds, the unit of [TIME-001]'s contract. -/
structure TimingTable where
  /-- The earliest entry of each transition id (`earliestMillis[]`, `earliest_ms`). -/
  earliest     : Nat → Nat
  /-- The latest entry of each transition id (`latestMillis[]`, `latest_ms`). -/
  latest       : Nat → Nat
  /-- The deadline flag of each transition id (`hasDeadline[]`). -/
  hasDeadline  : Nat → Bool
  /-- The global flag `allImmediate`. -/
  allImmediate : Bool
  /-- The global flag `anyDeadlines`. -/
  anyDeadlines : Bool

/-- A timing compiler: from the number `n` of a net's transitions and the timing of each
transition, by declaration index (the transition id), to the timing table. -/
abbrev TimingCompile := (n : Nat) → (Nat → Timing) → TimingTable

/-- The compiler that caches the accessors of a timing contract `K`: every entry is what `K`
returns for the transition's timing, `allImmediate` checks every transition's variant and
`anyDeadlines` looks for a transition with a deadline (`precompiled_net.rs`, "Precompute timing";
the latest entry is stored for every transition, TypeScript's form). -/
def timingCompileOf (K : TimingContract) : TimingCompile := fun n tm =>
  { earliest     := fun i => K.earliest (tm i)
    latest       := fun i => K.latest (tm i)
    hasDeadline  := fun i => K.hasDeadline (tm i)
    allImmediate := decide (∀ i, i < n → tm i = .immediate)
    anyDeadlines := decide (∃ i, i < n ∧ K.hasDeadline (tm i) = true) }

/-- The reference compiler: the compiler over the reference timing contract `refTimingQ`. -/
def refTimingCompile : TimingCompile := timingCompileOf refTimingQ

/- The reference compiler is the witness model of CONC-024's `holds` theorem. -/
#spec_witness refTimingCompile

/-! ## CONC-024: Precomputed Timing Arrays -/

requirement CONC_024
  id "CONC-024"
  title "Precomputed Timing Arrays"
  kind F
  scope "the precompiled net of every implementation"
  source verbatim "spec/05-concurrency.md"
  covers CONC_024.s1, CONC_024.s2, CONC_024.s3, CONC_024.s4
  reading "For every timing contract K (the accessors of TIME-001) and every net of n transitions whose timings, by transition id, are tm:"
          "for every transition id i below n, the earliest entry is K's earliest() of tm i (in K's unit, milliseconds) and the deadline flag is K's hasDeadline() of tm i;"
          "for every transition id i below n with K's hasDeadline() of tm i true, the latest entry is K's latest() of tm i (in K's unit);"
          "allImmediate is true exactly when tm i is Immediate for every i below n;"
          "anyDeadlines is true exactly when K's hasDeadline() of tm i is true for some i below n."
  assumes "A timing compiler maps the number n of a net's transitions and the timing of each transition, by declaration index (the transition id of the precompiled net), to a timing table: an earliest entry, a latest entry and a deadline flag per transition id, and the two global flags. Entries at an id of n or more are not read and no line constrains them. Timing, enablement and the marking at run time play no part: the table is a function of the timings alone."
          "The entries are stated through the accessors of a timing contract K of TIME-001, not through Timing.earliest directly: this block says the table holds what the accessors return, TIME-001 says what they return. A joint model satisfies TIME_001 K and CONC_024 K C with the same K, and conc024_skipDeadlines needs both. Bounds are naturals in milliseconds, as in TIME-001."
          "The bullet list names a nanosecond and a millisecond array for each bound, and the body sentence 'Millisecond arrays are precomputed to avoid nanosecond-to-millisecond division on the hot path.' and AC4 (the millisecond values match the nanosecond values within rounding) concern that pair. Only Java keeps both units; Rust and TypeScript keep milliseconds only (clash conc-b#7). The block states one entry per bound in the contract's unit (milliseconds), which is what the quoted sentences mean by 'in the array's unit': Java's earliestNanos[] holds earliest() converted to nanoseconds, its earliestMillis[] the same bound in milliseconds. The unit pair and AC4 are a layout property of the Java runtime (Q) and no line encodes them; the wording that makes the bullet list unit-neutral waits for ruling D20, and until then those bullets, the body sentence and AC4 stay normative prose that only Java meets."
          "'MAX_VALUE if no deadline' is not encoded: no line constrains the latest entry of a transition whose deadline flag is clear, and conc024_noDeadlineLatest_free shows the block accepts any value there, 0 included (a compiler that zero-fills the array and writes only flagged entries, so delayed(5) gets the entries 5 and 0). The runtimes store three different values there (Java Long.MAX_VALUE, Rust f64::MAX, TypeScript the maximum duration, which is latest() of Immediate and Delayed). Each reads the entry only behind the flag: Rust enforce_deadlines and millis_until_next_timed_transition (precompiled_backend.rs), Java enforceDeadlines and nanosUntilNextTimedTransition (PrecompiledNetExecutor.java), TypeScript enforceDeadlines and millisUntilNextTimedTransition (precompiled-net-executor.ts). conc024_deadlineAt proves that such a flag-guarded read is the same under every compiler that satisfies CONC-024, so the free entry changes nothing a guarded reader sees. A fifth line 'the latest entry without the flag is no smaller than latest()' would hold of the three runtimes, but it would settle the D20 item (clash conc-b#7, whose recommendation is that the entry is meaningful only where the flag is set) ahead of the ruling, so it stays out; if D20 keeps a fixed value, that line is added and conc024_maxValueCompile 0 becomes its forbids evidence."
          "The deadline flag is hasDeadline() by variant (ruling D2, TIME-001 line 3): Exact has the flag although it is enforced softly and never reaped (TIME-006, TIME-013). A flag read off the bounds (latest below the maximum duration) is killed as CONC_024_forbids_latestBelowMax on window(0, maximum). The separate Exact flag every runtime keeps is not in the spec's list and is not encoded."
          "AC1 (populated at compile time, not computed per cycle) and the purpose 'to avoid virtual dispatch on timing types during execution' are cost and layout (Q), and no line encodes them. That a compiler is a function of n and the timings alone is the model's typing, not a checked property: it cannot tell a runtime that fills the table once from one that refills it every cycle."
          "Line 3 tests the variant (tm i is Immediate) while lines 1, 2 and 4 go through K, because the quoted sentence names the variant `Immediate` and the contract has no accessor for it. The two bases agree in a joint model: conc024_flags_exclusive proves that under TIME_001 K the flags allImmediate and anyDeadlines are never both set."
          "The bullets 'true if all transitions are immediate' and 'true if any transition has a deadline' state only the direction that makes the flag set; the quoted 'exactly when' sentences add the converse and fix the reading of 'immediate' as the variant (so delayed(0) does not count). The bullets themselves are left as written: rewording them is a D20 item. Both directions are killed when violated: the unsafe one by CONC_024_forbids_earliestZero, CONC_024_forbids_noDeadlineImmediate and CONC_024_mutant_reapable, the conservative one (allImmediate stuck false, anyDeadlines stuck true) by CONC_024_forbids_neverImmediate, CONC_024_forbids_alwaysDeadlines and CONC_024_mutant_safeDirection."
          "AC2 (allImmediate allows skipping timing checks entirely for immediate-only nets) is line 3, and conc024_skipTiming shows why the skip is sound: when the flag is set, every transition of the net is Ready exactly when it is Armed, so the checks of the earliest and the latest bound decide nothing. The flag read off the earliest bounds (a Deadline net then skips its deadline) is killed as CONC_024_mutant_earliestZero; the flag read as 'no deadlines' (a Delayed net then fires before its earliest bound) as CONC_024_forbids_noDeadlineImmediate."
          "AC3 (anyDeadlines allows skipping deadline enforcement when no deadlines exist) is line 4, and conc024_skipDeadlines shows why the skip is sound: with TIME-001's accessors, when the flag is clear no transition of the net is reapable, so none is ever Expired and enforcement reaps nothing. The flag read as 'some transition is reapable', which ignores Exact, is killed as CONC_024_mutant_reapable: it would reap the same transitions, but the text (hasDeadline() is true for Exact, D2) and the three runtimes count Exact."
          "Where a runtime takes the all-immediate fast path, it tests allImmediate together with a single priority level, which is EXEC-002's fast-path condition ReadyIn.FastPath (conc024_fastPath). The link states the condition only; what the fast path does is EXEC-002's subject (its fourth line: declaration order, ruling D14 (a)), and the link does not depend on it."
          "The test derivation (compile nets with various timing configurations, verify array values and global flags) is CONC_024_nonvacuous: a net with one transition of each variant, a net of Exact transitions only, an all-Immediate net and the empty net."
          "The scope is the five variants of the spec (Novel.TimedScg.Timing). Java's deprecated sixth variant Unconstrained, which Java's allImmediate counts as immediate, is not in the spec and not modelled."
  signoff "2026-11-13 1f7ebd6d8d6d2983 ai"
  statement : TimingContract → TimingCompile → Prop :=
    fun K C => ∀ n tm,
      (∀ i, i < n → (C n tm).earliest i = K.earliest (tm i) ∧
        (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
      (∀ i, i < n → K.hasDeadline (tm i) = true → (C n tm).latest i = K.latest (tm i)) ∧
      ((C n tm).allImmediate = true ↔ ∀ i, i < n → tm i = .immediate) ∧
      ((C n tm).anyDeadlines = true ↔ ∃ i, i < n ∧ K.hasDeadline (tm i) = true)

/- The pinned readable form of CONC-024: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_024 : TimingContract → TimingCompile → Prop :=
fun K C =>
  ∀ (n : ℕ) (tm : ℕ → Timing),
    (∀ i < n, (C n tm).earliest i = K.earliest (tm i) ∧ (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
      (∀ i < n, K.hasDeadline (tm i) = true → (C n tm).latest i = K.latest (tm i)) ∧
        ((C n tm).allImmediate = true ↔ ∀ i < n, tm i = Timing.immediate) ∧
          ((C n tm).anyDeadlines = true ↔ ∃ i < n, K.hasDeadline (tm i) = true)
-/
#guard_msgs in #print CONC_024

/-- Every contract's caching compiler satisfies CONC-024: its entries are the contract's
accessors and its flags are decided over exactly the transitions below `n`. -/
theorem conc024_timingCompileOf (K : TimingContract) : CONC_024 K (timingCompileOf K) := by
  intro n tm
  refine ⟨fun i _ => ⟨rfl, rfl⟩, fun i _ _ => rfl, ?_, ?_⟩ <;> simp [timingCompileOf]

/-- The reference compiler satisfies CONC-024 over the reference timing contract: the entries
are `Timing.earliest`, `Timing.latest` and `Timing.hasDeadline` of each transition's timing,
`allImmediate` checks every variant and `anyDeadlines` looks for a deadline by variant
(`precompiled_net.rs`, "Precompute timing"). -/
@[evidence holds CONC_024]
theorem CONC_024_reference : CONC_024 refTimingQ refTimingCompile :=
  conc024_timingCompileOf refTimingQ

/-- The compiler that stores `big` as the latest entry of every transition without a deadline
(Rust `f64::MAX`, Java `Long.MAX_VALUE`) and is the reference otherwise. -/
def conc024_maxValueCompile (big : Nat) : TimingCompile := fun n tm =>
  { refTimingCompile n tm with
    latest := fun i => if (tm i).hasDeadline then (tm i).latest else big }

/-- No line constrains the latest entry of a transition without a deadline: the compiler that
stores any value there satisfies CONC-024, so the three runtimes' values (Java `Long.MAX_VALUE`,
Rust `f64::MAX`, TypeScript the maximum duration) all do. -/
theorem conc024_noDeadlineLatest_free (big : Nat) :
    CONC_024 refTimingQ (conc024_maxValueCompile big) := by
  intro n tm
  obtain ⟨h1, -, h3, h4⟩ := CONC_024_reference n tm
  refine ⟨h1, fun i _ hd => ?_, h3, h4⟩
  show (if (tm i).hasDeadline then (tm i).latest else big) = (tm i).latest
  rw [if_pos (show (tm i).hasDeadline = true from hd)]

/-- The deadline of transition id `i` as a flag-guarded reader sees it: the latest entry where
the deadline flag is set, nothing where it is clear (every runtime's reaping loop and its
next-wake computation read the latest entry only behind the flag). -/
def TimingTable.deadlineAt (T : TimingTable) (i : Nat) : Option Nat :=
  if T.hasDeadline i then some (T.latest i) else none

/-- Under any compiler that satisfies CONC-024, the flag-guarded read of each transition's
deadline is fixed by the contract: `K.latest` where `K.hasDeadline` holds, nothing otherwise. -/
theorem conc024_deadlineAt {K : TimingContract} {C : TimingCompile} (h : CONC_024 K C)
    (n : Nat) (tm : Nat → Timing) (i : Nat) (hi : i < n) :
    (C n tm).deadlineAt i =
      if K.hasDeadline (tm i) then some (K.latest (tm i)) else none := by
  obtain ⟨h1, h2, -, -⟩ := h n tm
  unfold TimingTable.deadlineAt
  rw [(h1 i hi).2]
  cases hk : K.hasDeadline (tm i) with
  | false => rfl
  | true => simp [h2 i hi hk]

/-- The latest entry of a transition without a deadline is invisible to a flag-guarded reader:
two compilers that satisfy CONC-024 over the same contract give every transition the same
guarded deadline, whatever they store in the free entries. -/
theorem conc024_deadlineAt_agree {K : TimingContract} {C C' : TimingCompile}
    (h : CONC_024 K C) (h' : CONC_024 K C') (n : Nat) (tm : Nat → Timing) (i : Nat)
    (hi : i < n) : (C n tm).deadlineAt i = (C' n tm).deadlineAt i := by
  rw [conc024_deadlineAt h n tm i hi, conc024_deadlineAt h' n tm i hi]

/-- The zero-filling compiler (`conc024_maxValueCompile 0`) stores the interval `[5, 0]` for
`delayed(5)`, below its earliest entry, yet a guarded reader sees no deadline, as under the
reference. -/
theorem conc024_zeroFill_guarded :
    (conc024_maxValueCompile 0 1 (fun _ => .delayed 5)).latest 0 = 0 ∧
    (conc024_maxValueCompile 0 1 (fun _ => .delayed 5)).earliest 0 = 5 ∧
    (conc024_maxValueCompile 0 1 (fun _ => .delayed 5)).deadlineAt 0 =
      (refTimingCompile 1 (fun _ => .delayed 5)).deadlineAt 0 :=
  ⟨by decide, by decide,
    conc024_deadlineAt_agree (conc024_noDeadlineLatest_free 0) CONC_024_reference 1 _ 0
      (by decide)⟩

/-! ### What the flags allow (AC2, AC3) -/

/-- The timings of a timed net's transitions by declaration index, as a compiler reads them
(the same function as `(ReadyIn.ofTSt X prio s X.net.transitions).timing`). -/
def conc024_timings {N : Type} (X : TimedNet N) : Nat → Timing :=
  fun i => (X.net.transitions[i]?.map (TimingOf X)).getD .immediate

/-- The timing of a transition of the net, by its declaration index. -/
theorem conc024_timings_get {N : Type} (X : TimedNet N) (i : Nat)
    (hi : i < X.net.transitions.length) :
    conc024_timings X i = TimingOf X X.net.transitions[i] := by
  simp [conc024_timings, List.getElem?_eq_getElem hi]

/-- **AC2.** Under any compiler that satisfies CONC-024, when `allImmediate` is set for a net,
every transition of the net is Ready exactly when it is Armed: its earliest bound is `0` and it
is not reapable, so skipping the timing checks changes nothing. -/
theorem conc024_skipTiming {N : Type} {K : TimingContract} {C : TimingCompile}
    (h : CONC_024 K C) (X : TimedNet N)
    (hall : (C X.net.transitions.length (conc024_timings X)).allImmediate = true)
    (s : TSt N) (t : Trans N) (ht : t ∈ X.net.transitions) : Ready X s t ↔ Armed s t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have himm := (h _ _).2.2.1.1 hall i hi
  rw [conc024_timings_get X i hi] at himm
  simp [Ready, Expired, Reapable, himm, Timing.earliest, Timing.reapable]

/-- **AC3.** Under a contract that satisfies TIME-001 and any compiler that satisfies CONC-024
over it, when `anyDeadlines` is clear for a net, no transition of the net is reapable, so none is
ever Expired and skipping deadline enforcement reaps nothing. -/
theorem conc024_skipDeadlines {N : Type} {K : TimingContract} {C : TimingCompile}
    (hK : TIME_001 K) (h : CONC_024 K C) (X : TimedNet N)
    (hno : (C X.net.transitions.length (conc024_timings X)).anyDeadlines = false)
    (s : TSt N) (t : Trans N) (ht : t ∈ X.net.transitions) :
    ¬ Reapable X t ∧ ¬ Expired X s t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hd : K.hasDeadline (conc024_timings X i) = false := by
    cases hk : K.hasDeadline (conc024_timings X i) with
    | false => rfl
    | true =>
      have := (h _ _).2.2.2.2 ⟨i, hi, hk⟩
      rw [hno] at this; exact absurd this (by decide)
  rw [hK.2.2.1, conc024_timings_get X i hi] at hd
  have hr : ¬ Reapable X X.net.transitions[i] := by
    simp only [Reapable]
    revert hd
    cases TimingOf X X.net.transitions[i] <;> simp [Timing.reapable]
  exact ⟨hr, fun he => hr he.1⟩

/-- **The two bases of the flags agree.** Line 3 tests the variant and line 4 goes through the
contract; under a contract that satisfies TIME-001 (`Immediate` has no deadline) the two flags
are never both set. -/
theorem conc024_flags_exclusive {K : TimingContract} {C : TimingCompile}
    (hK : TIME_001 K) (h : CONC_024 K C) (n : Nat) (tm : Nat → Timing) :
    ¬ ((C n tm).allImmediate = true ∧ (C n tm).anyDeadlines = true) := by
  rintro ⟨ha, hd⟩
  obtain ⟨i, hi, hk⟩ := (h n tm).2.2.2.1 hd
  rw [(h n tm).2.2.1.1 ha i hi, hK.2.2.1] at hk
  exact absurd hk (by decide)

/-- **The link to EXEC-002.** Under any compiler that satisfies CONC-024, the fast-path
condition of EXEC-002 (every transition `Immediate`, one priority level) is the flag
`allImmediate` together with one priority level. -/
theorem conc024_fastPath {K : TimingContract} {C : TimingCompile} (h : CONC_024 K C)
    (I : ReadyIn) :
    I.FastPath ↔ ((C I.n I.timing).allImmediate = true ∧
      ∀ a, a < I.n → ∀ b, b < I.n → I.prio a = I.prio b) := by
  rw [(h I.n I.timing).2.2.1]
  constructor
  · intro hf
    exact ⟨fun a ha => (hf a ha a ha).1, fun a ha b hb => (hf a ha b hb).2⟩
  · rintro ⟨hi, hp⟩ a ha b hb
    exact ⟨hi a ha, hp a ha b hb⟩

/-! ### Examples: wrong compilers -/

/-- A compiler that reads "immediate" off the earliest bounds: `allImmediate` is set when every
earliest bound is `0`, so a net of `Deadline` transitions counts as immediate. -/
def conc024_earliestZeroCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with allImmediate := decide (∀ i, i < n → (tm i).earliest = 0) }

/-- ✗ A flag read off the earliest bounds violates CONC-024 (line 3), under every contract: the
net of one `deadline(5)` transition gets `allImmediate`, and an executor would skip its
deadline. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_earliestZero (K : TimingContract) :
    ¬ CONC_024 K conc024_earliestZeroCompile := by
  intro h
  have := (h 1 (fun _ => .deadline 5)).2.2.1.1 (by decide) 0 (by decide)
  exact absurd this (by decide)

/-- A compiler that reads "immediate" as "no deadlines": `allImmediate` is the negation of
`anyDeadlines`, so a net of `Delayed` transitions counts as immediate. -/
def conc024_noDeadlineImmediateCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with allImmediate := !(refTimingCompile n tm).anyDeadlines }

/-- ✗ A flag read as "no deadlines" violates CONC-024 (line 3), under every contract: the net of
one `delayed(5)` transition gets `allImmediate`, and an executor would fire it before its earliest
bound. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_noDeadlineImmediate (K : TimingContract) :
    ¬ CONC_024 K conc024_noDeadlineImmediateCompile := by
  intro h
  have := (h 1 (fun _ => .delayed 5)).2.2.1.1 (by decide) 0 (by decide)
  exact absurd this (by decide)

/-- A compiler that reads the deadline flag off the bounds: a transition has the flag when its
latest bound is below the maximum duration (the literal older reading of TIME-001 AC3), and
`anyDeadlines` is decided over those flags. -/
def conc024_latestBelowMaxCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with
    hasDeadline := fun i => decide ((tm i).latest < maxDurationMs)
    anyDeadlines := decide (∃ i, i < n ∧ (tm i).latest < maxDurationMs) }

/-- ✗ A deadline flag read off the bounds violates CONC-024 (line 1, ruling D2): `window(0,
maximum)` has a deadline by its variant, but no flag, and would never be reaped. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_latestBelowMax : ¬ CONC_024 refTimingQ conc024_latestBelowMaxCompile := by
  intro h
  have := ((h 1 (fun _ => .window 0 3153600000000)).1 0 (by decide)).2
  exact absurd this (by decide)

/-- A compiler that keeps the earliest bound only for `Delayed` and stores `0` for every other
variant, so a `Window` or an `Exact` transition loses its earliest bound. -/
def conc024_earliestDelayedOnlyCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with
    earliest := fun i => match tm i with
      | .delayed a => a
      | _ => 0 }

/-- ✗ An earliest entry kept only for `Delayed` violates CONC-024 (line 1): the earliest entry of
`window(5, 10)` is `0`, and an executor would fire it before its earliest bound. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_earliestDelayedOnly :
    ¬ CONC_024 refTimingQ conc024_earliestDelayedOnlyCompile := by
  intro h
  have := ((h 1 (fun _ => .window 5 10)).1 0 (by decide)).1
  exact absurd this (by decide)

/-- A compiler that stores the maximum duration as the latest entry of every `Window`, as if a
window were a delay. -/
def conc024_windowNoLatestCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with
    latest := fun i => match tm i with
      | .window _ _ => maxDurationMs
      | t => t.latest }

/-- ✗ A `Window` whose latest entry is the maximum duration violates CONC-024 (line 2):
`window(0, 10)` has a deadline, and its latest entry must be `10`. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_windowNoLatest :
    ¬ CONC_024 refTimingQ conc024_windowNoLatestCompile := by
  intro h
  have := (h 1 (fun _ => .window 0 10)).2.1 0 (by decide) (by decide)
  exact absurd this (by decide)

/-- A compiler whose `allImmediate` is stuck at `false`: safe, but it never takes the skip of AC2. -/
def conc024_neverImmediateCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with allImmediate := false }

/-- ✗ An `allImmediate` stuck at `false` violates CONC-024 (line 3, the "if" direction of the
bullet), under every contract: a net of one `Immediate` transition must get the flag. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_neverImmediate (K : TimingContract) :
    ¬ CONC_024 K conc024_neverImmediateCompile := by
  intro h
  have := (h 1 (fun _ => .immediate)).2.2.1.2 (fun _ _ => rfl)
  exact absurd this (by decide)

/-- A compiler whose `anyDeadlines` is stuck at `true`: safe, but it never takes the skip of
AC3. -/
def conc024_alwaysDeadlinesCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with anyDeadlines := true }

/-- ✗ An `anyDeadlines` stuck at `true` violates CONC-024 (line 4, the converse added by the
"exactly when" sentence): a net of one `Immediate` transition has no deadline, and so does the
empty net. -/
@[evidence forbids CONC_024]
theorem CONC_024_forbids_alwaysDeadlines :
    ¬ CONC_024 refTimingQ conc024_alwaysDeadlinesCompile := by
  intro h
  obtain ⟨i, hi, hk⟩ := (h 1 (fun _ => .immediate)).2.2.2.1 rfl
  exact absurd hk (by decide)

/-- A compiler whose `anyDeadlines` looks for a reapable transition (`Deadline`, `Window`) and so
ignores `Exact`. -/
def conc024_reapableCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with anyDeadlines := decide (∃ i, i < n ∧ (tm i).reapable = true) }

/-! ### Mutant readings -/

/-- Mutant reading of CONC-024 whose third line reads `allImmediate` off the earliest bounds:
the flag is set exactly when every transition's earliest bound is `0`. The other lines are as in
CONC-024. -/
def CONC_024_mutant_earliestZeroReading (K : TimingContract) (C : TimingCompile) : Prop :=
  ∀ n tm,
    (∀ i, i < n → (C n tm).earliest i = K.earliest (tm i) ∧
      (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
    (∀ i, i < n → K.hasDeadline (tm i) = true → (C n tm).latest i = K.latest (tm i)) ∧
    ((C n tm).allImmediate = true ↔ ∀ i, i < n → K.earliest (tm i) = 0) ∧
    ((C n tm).anyDeadlines = true ↔ ∃ i, i < n ∧ K.hasDeadline (tm i) = true)

/-- The earliest-zero compiler kills the mutant: it meets the mutant reading, but not CONC-024,
since a `deadline(5)` transition has earliest bound `0` and is not `Immediate` (AC2). -/
@[evidence mutant CONC_024]
theorem CONC_024_mutant_earliestZero :
    CONC_024_mutant_earliestZeroReading refTimingQ conc024_earliestZeroCompile ∧
      ¬ CONC_024 refTimingQ conc024_earliestZeroCompile := by
  refine ⟨fun n tm => ?_, CONC_024_forbids_earliestZero refTimingQ⟩
  obtain ⟨h1, h2, -, h4⟩ := CONC_024_reference n tm
  refine ⟨h1, h2, ?_, h4⟩
  show decide _ = true ↔ _
  simp only [decide_eq_true_iff]
  rfl

/-- Mutant reading of CONC-024 whose fourth line counts reapable transitions only:
`anyDeadlines` is set exactly when some transition is `Deadline` or `Window`. The other lines are
as in CONC-024. -/
def CONC_024_mutant_reapableReading (K : TimingContract) (C : TimingCompile) : Prop :=
  ∀ n tm,
    (∀ i, i < n → (C n tm).earliest i = K.earliest (tm i) ∧
      (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
    (∀ i, i < n → K.hasDeadline (tm i) = true → (C n tm).latest i = K.latest (tm i)) ∧
    ((C n tm).allImmediate = true ↔ ∀ i, i < n → tm i = .immediate) ∧
    ((C n tm).anyDeadlines = true ↔ ∃ i, i < n ∧ (tm i).reapable = true)

/-- The reapable compiler kills the mutant: it meets the mutant reading, but not CONC-024, since
a net of one `exact(5)` transition has a deadline (`hasDeadline()` is true for `Exact`, ruling
D2) and gets no `anyDeadlines`. -/
@[evidence mutant CONC_024]
theorem CONC_024_mutant_reapable :
    CONC_024_mutant_reapableReading refTimingQ conc024_reapableCompile ∧
      ¬ CONC_024 refTimingQ conc024_reapableCompile := by
  refine ⟨fun n tm => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := CONC_024_reference n tm
    refine ⟨h1, h2, h3, ?_⟩
    show decide _ = true ↔ _
    simp only [decide_eq_true_iff]
  · have := (h 1 (fun _ => .exact 5)).2.2.2.2 ⟨0, by decide, by decide⟩
    exact absurd this (by decide)

/-- Mutant reading of CONC-024 that drops the second line: the latest entry is unconstrained.
The other lines are as in CONC-024. -/
def CONC_024_mutant_dropLatestReading (K : TimingContract) (C : TimingCompile) : Prop :=
  ∀ n tm,
    (∀ i, i < n → (C n tm).earliest i = K.earliest (tm i) ∧
      (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
    ((C n tm).allImmediate = true ↔ ∀ i, i < n → tm i = .immediate) ∧
    ((C n tm).anyDeadlines = true ↔ ∃ i, i < n ∧ K.hasDeadline (tm i) = true)

/-- The window-as-delay compiler kills the mutant: its flags and earliest entries are the
reference's, but `window(0, 10)` gets the latest entry of a delay, so its deadline would never
be enforced (CONC-024 fails, line 2). -/
@[evidence mutant CONC_024]
theorem CONC_024_mutant_dropLatest :
    CONC_024_mutant_dropLatestReading refTimingQ conc024_windowNoLatestCompile ∧
      ¬ CONC_024 refTimingQ conc024_windowNoLatestCompile := by
  refine ⟨fun n tm => ?_, CONC_024_forbids_windowNoLatest⟩
  obtain ⟨h1, -, h3, h4⟩ := CONC_024_reference n tm
  exact ⟨h1, h3, h4⟩

/-- Mutant reading of CONC-024 that keeps only the safe direction of the two flag lines: a set
`allImmediate` implies every transition is `Immediate`, and a transition with a deadline implies
`anyDeadlines`. The flags may then be stuck at their conservative values. The other lines are as
in CONC-024. -/
def CONC_024_mutant_safeDirectionReading (K : TimingContract) (C : TimingCompile) : Prop :=
  ∀ n tm,
    (∀ i, i < n → (C n tm).earliest i = K.earliest (tm i) ∧
      (C n tm).hasDeadline i = K.hasDeadline (tm i)) ∧
    (∀ i, i < n → K.hasDeadline (tm i) = true → (C n tm).latest i = K.latest (tm i)) ∧
    ((C n tm).allImmediate = true → ∀ i, i < n → tm i = .immediate) ∧
    ((∃ i, i < n ∧ K.hasDeadline (tm i) = true) → (C n tm).anyDeadlines = true)

/-- A compiler with both flags stuck at their conservative values: `allImmediate` false and
`anyDeadlines` true. -/
def conc024_conservativeCompile : TimingCompile := fun n tm =>
  { refTimingCompile n tm with allImmediate := false, anyDeadlines := true }

/-- The conservative compiler kills the mutant: it meets the safe-direction reading, but not
CONC-024, since an all-`Immediate` net must get `allImmediate` (the bullet's "true if all
transitions are immediate", AC2). -/
@[evidence mutant CONC_024]
theorem CONC_024_mutant_safeDirection :
    CONC_024_mutant_safeDirectionReading refTimingQ conc024_conservativeCompile ∧
      ¬ CONC_024 refTimingQ conc024_conservativeCompile := by
  refine ⟨fun n tm => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := CONC_024_reference n tm
    exact ⟨h1, h2, fun hf => absurd hf Bool.false_ne_true, fun _ => rfl⟩
  · have := (h 1 (fun _ => .immediate)).2.2.1.2 (fun _ _ => rfl)
    exact absurd this (by decide)

/-! ### Nonvacuous: the test derivation -/

/-- A net of five transitions, one of each variant: `Immediate`, `Deadline(10)`, `Delayed(5)`,
`Window(5, 10)` and `Exact(7)`. -/
def conc024_five : Nat → Timing
  | 0 => .immediate
  | 1 => .deadline 10
  | 2 => .delayed 5
  | 3 => .window 5 10
  | _ => .exact 7

/-- Every line of CONC-024 bites on the reference compiler (the test derivation): on the net of
one transition of each variant, the earliest entries are `0, 0, 5, 5, 7`, the deadline flags are
set for `Deadline`, `Window` and `Exact` only, the latest entries of the flagged transitions are
`10, 10, 7`, `allImmediate` is clear and `anyDeadlines` set; a net of `Exact` transitions only
has `anyDeadlines` set; an all-`Immediate` net has `allImmediate` set and `anyDeadlines` clear,
and so has the empty net. -/
@[evidence nonvacuous CONC_024]
theorem CONC_024_nonvacuous :
    (refTimingCompile 5 conc024_five).earliest 0 = 0 ∧
    (refTimingCompile 5 conc024_five).earliest 1 = 0 ∧
    (refTimingCompile 5 conc024_five).earliest 2 = 5 ∧
    (refTimingCompile 5 conc024_five).earliest 3 = 5 ∧
    (refTimingCompile 5 conc024_five).earliest 4 = 7 ∧
    (refTimingCompile 5 conc024_five).hasDeadline 0 = false ∧
    (refTimingCompile 5 conc024_five).hasDeadline 1 = true ∧
    (refTimingCompile 5 conc024_five).hasDeadline 2 = false ∧
    (refTimingCompile 5 conc024_five).hasDeadline 3 = true ∧
    (refTimingCompile 5 conc024_five).hasDeadline 4 = true ∧
    (refTimingCompile 5 conc024_five).latest 1 = 10 ∧
    (refTimingCompile 5 conc024_five).latest 3 = 10 ∧
    (refTimingCompile 5 conc024_five).latest 4 = 7 ∧
    (refTimingCompile 5 conc024_five).allImmediate = false ∧
    (refTimingCompile 5 conc024_five).anyDeadlines = true ∧
    (refTimingCompile 2 (fun _ => .exact 3)).anyDeadlines = true ∧
    (refTimingCompile 2 (fun _ => .exact 3)).allImmediate = false ∧
    (refTimingCompile 3 (fun _ => .immediate)).allImmediate = true ∧
    (refTimingCompile 3 (fun _ => .immediate)).anyDeadlines = false ∧
    (refTimingCompile 0 conc024_five).allImmediate = true ∧
    (refTimingCompile 0 conc024_five).anyDeadlines = false := by
  decide

end Libpetri.Spec
