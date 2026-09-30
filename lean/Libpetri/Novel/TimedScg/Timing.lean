import Libpetri.Novel.TimedScg.Succ

/-!
# The intervals the Rust graph gives a transition ([TIME-001] – [TIME-006], [VER-010])

`Succ.lean` takes a transition's static interval `[eft, lft]` as data (`TTrans.eft`,
`TTrans.lft : Bound`). This file says which intervals the Rust graph actually produces, from
`libpetri-core/src/timing.rs`:

* `Timing` is the Rust enum, with `earliest` / `latest` / `has_deadline` as in `timing.rs:95-125`.
  `latest()` returns the **finite** `MAX_DURATION_MS` (100 years of 365 days) for `Immediate` and
  `Delayed`; it never returns `f64::INFINITY`. `timing_earliest` / `timing_latest`
  (`state_class_graph.rs`) divide by `1000`, so the faithful interval of a transition is
  `[eftT tm, lftT tm]`, and `lftT tm` is never `⊤` (`lftT_ne_top`). `⊤` enters the model only
  through `Late.relax`, which is not what the shipped graph builds.
* `Timing.Valid` is what the constructors assert: `deadline(by)` panics on `by = 0`,
  `window(e, l)` on `l < e` or `e > MAX_DURATION_MS`, and `delayed(after)` and `exact(at)` on an
  earliest bound above `MAX_DURATION_MS`. `Timing.ValidPre` is what they asserted before the
  R6 fix: `delayed` and `exact` checked nothing, `window` only `l < e`.
* `timingWF_iff`: a timing valid in the old sense gives `0 ≤ eft ≤ lft` (`Succ.TimingWF`,
  premise 6) **iff** it is not a `delayed(after)` with `after > MAX_DURATION_MS`. The old
  constructor accepted `delayed(MAX_DURATION_MS + 1)`, which breaks premise 6
  (`Retrodict.delayed_past_max_*`). `timingWF_of_valid`: every timing the shipped constructors
  accept meets premise 6, so that case is gone (`timingWF_of_valid_timings`).
  The Rust variants are public, so a caller can write a `Timing` out without a constructor.
  `transition.rs::build` (`TransitionBuilder::build`) therefore calls the constructor of the
  variant again and panics with its message ([TIME-001] AC5), so the timing of every built
  transition is `Valid`, however it was written. Before that check a directly written
  `Timing::Delayed { after_ms: MAX_DURATION_MS + 1 }` reached the graph and broke premise 6 as
  the old constructor did, and a directly written `Window` with `e > MAX_DURATION_MS` made
  `reaping::relax_late` panic when it rebuilt it as `delayed(e)`.
* `netGrid_of_timings`: every faithful bound is on the millisecond grid `1/1000 · ℤ`, the
  premise of `Progress.reachable_quiescent_iff_dead_grid` that lets the Rust `EPSILON = 1e-9`
  stand in for the exact emptiness check.
* `Timing.reapable`: the timings `enforce_deadlines` reaps (`has_deadline` and not `Exact`,
  [TIME-006], [TIME-013]); used by `Late.lean`.

Two readings of the unbounded timings are in play and the model keeps them apart:

* the **graph** reads `Immediate` / `Delayed` as `[·, MAX_DURATION_MS]` (`lftT`);
* the **executor** never forces or reaps them (`has_deadline` is false): as far as it is
  concerned their upper bound is `⊤`.

That `MAX_DURATION_MS` may be read as `⊤` is **not proven**. It failed outright for
`delayed(after > MAX_DURATION_MS)` before the constructors rejected it (premise 6 broke, and the
executor fired what the graph could not, `Retrodict.delayed_past_max_escapes`), and in general
it needs the executor to fire a
ready `Immediate` / `Delayed` transition within 100 years of its clock start, which the eager
executor does on time and a late one need not (`Late.lean` drops every upper bound instead).
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

/-- `MAX_DURATION_MS` (`timing.rs:2`): 100 years of 365 days, in milliseconds. -/
def maxDurationMs : Nat := 365 * 100 * 24 * 60 * 60 * 1000

/-- The Rust `Timing` enum (`timing.rs:12-23`), durations in milliseconds. -/
inductive Timing where
  | immediate
  | deadline (byMs : Nat)
  | delayed (afterMs : Nat)
  | window (earliestMs latestMs : Nat)
  | exact (atMs : Nat)
  deriving DecidableEq

namespace Timing

/-- `Timing::earliest` (`timing.rs:97-105`). -/
def earliest : Timing → Nat
  | immediate => 0
  | deadline _ => 0
  | delayed a => a
  | window e _ => e
  | exact a => a

/-- `Timing::latest` (`timing.rs:108-116`): finite for every variant. -/
def latest : Timing → Nat
  | immediate => maxDurationMs
  | deadline b => b
  | delayed _ => maxDurationMs
  | window _ l => l
  | exact a => a

/-- `Timing::has_deadline` (`timing.rs:119-124`). -/
def hasDeadline : Timing → Bool
  | deadline _ => true
  | window _ _ => true
  | exact _ => true
  | _ => false

/-- The timings `enforce_deadlines` reaps: a deadline, and not `exact` (soft, [TIME-006]). -/
def reapable : Timing → Bool
  | deadline _ => true
  | window _ _ => true
  | _ => false

/-- What the constructors assert: `deadline(by)` a positive bound, `window(e, l)` an earliest
bound at most `MAX_DURATION_MS` and `e ≤ l`, `delayed(after)` and `exact(at)` an earliest bound
at most `MAX_DURATION_MS` (`timing.rs`, `deadline`, `delayed`, `window`, `exact`). -/
def Valid : Timing → Prop
  | deadline b => 0 < b
  | window e l => e ≤ maxDurationMs ∧ e ≤ l
  | delayed a => a ≤ maxDurationMs
  | exact a => a ≤ maxDurationMs
  | immediate => True

/-- What the constructors asserted before the R6 fix: `deadline` and `window` as now without the
`MAX_DURATION_MS` check, `delayed` and `exact` nothing. -/
def ValidPre : Timing → Prop
  | deadline b => 0 < b
  | window e l => e ≤ l
  | _ => True

/-- The shipped checks include the old ones. -/
theorem Valid.pre {tm : Timing} (h : tm.Valid) : tm.ValidPre := by
  cases tm <;> simp_all [Valid, ValidPre]

/-- The earliest bound of a timing the shipped constructors accept is at most
`MAX_DURATION_MS`, the graph's reading of every unbounded latest bound. -/
theorem Valid.earliest_le {tm : Timing} (h : tm.Valid) : tm.earliest ≤ maxDurationMs := by
  cases tm <;> simp_all [Valid, earliest]

theorem reapable_hasDeadline {tm : Timing} (h : tm.reapable = true) : tm.hasDeadline = true := by
  cases tm <;> simp_all [reapable, hasDeadline]

end Timing

/-- The earliest firing time the graph uses, in seconds (`timing_earliest`). -/
def eftT (tm : Timing) : ℚ := (tm.earliest : ℚ) / 1000

/-- The latest firing time the graph uses, in seconds (`timing_latest`): always finite. -/
def lftT (tm : Timing) : Bound := (((tm.latest : ℚ) / 1000 : ℚ) : Bound)

theorem lftT_ne_top (tm : Timing) : lftT tm ≠ ⊤ := WithTop.coe_ne_top

/-- A transition whose interval is the graph's reading of `tm`. -/
def mkT (tr : Transition) (rows : List Deposit) (tm : Timing) : TTrans :=
  ⟨tr, rows, eftT tm, lftT tm⟩

/-- The net's intervals are the graph's reading of the timings `tms`. -/
def FromTimings (N : TNet) (tms : Nat → Timing) : Prop :=
  ∀ i, i < N.length → eftOf N i = eftT (tms i) ∧ lftOf N i = lftT (tms i)

/-- **Premise 6 for one transition, before the R6 fix.** A timing the old constructors accepted
has `0 ≤ eft ≤ lft` in the graph's reading iff it is not a `delayed(after)` past
`MAX_DURATION_MS`. -/
theorem timingWF_iff (tm : Timing) (hv : tm.ValidPre) :
    (0 ≤ eftT tm ∧ ((eftT tm : ℚ) : Bound) ≤ lftT tm) ↔ ∀ a, tm = .delayed a → a ≤ maxDurationMs := by
  have key : ((eftT tm : ℚ) : Bound) ≤ lftT tm ↔ tm.earliest ≤ tm.latest := by
    unfold eftT lftT
    rw [WithTop.coe_le_coe, div_le_div_iff_of_pos_right (by norm_num), Nat.cast_le]
  rw [key]
  have h0 : 0 ≤ eftT tm := by unfold eftT; exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  simp only [h0, true_and]
  cases tm with
  | immediate => simp [Timing.earliest, Timing.latest]
  | deadline b => simp [Timing.earliest, Timing.latest]
  | delayed a => simp [Timing.earliest, Timing.latest]
  | window e l => simpa [Timing.earliest, Timing.latest, Timing.ValidPre] using hv
  | exact a => simp [Timing.earliest, Timing.latest]

/-- **A faithful net meets premise 6** when every timing is valid and no `delayed` exceeds
`MAX_DURATION_MS`. -/
theorem timingWF_of_timings {N : TNet} {tms : Nat → Timing} (hN : FromTimings N tms)
    (hv : ∀ i, i < N.length → (tms i).ValidPre)
    (hmax : ∀ i, i < N.length → ∀ a, tms i = .delayed a → a ≤ maxDurationMs) : TimingWF N := by
  intro i
  by_cases hi : i < N.length
  · rw [(hN i hi).1, (hN i hi).2]
    exact (timingWF_iff _ (hv i hi)).mpr (hmax i hi)
  · have e1 : eftOf N i = 0 := by simp [eftOf, List.getElem?_eq_none (by omega : N.length ≤ i)]
    have e2 : lftOf N i = ⊤ := by simp [lftOf, List.getElem?_eq_none (by omega : N.length ≤ i)]
    rw [e1, e2]
    exact ⟨le_refl _, le_top⟩

/-- **Premise 6 holds for every timing the shipped constructors accept** (the R6 fix:
`delayed`, `window` and `exact` reject an earliest bound above `MAX_DURATION_MS`). -/
theorem timingWF_of_valid {tm : Timing} (hv : tm.Valid) :
    0 ≤ eftT tm ∧ ((eftT tm : ℚ) : Bound) ≤ lftT tm := by
  refine (timingWF_iff tm hv.pre).mpr fun a ha => ?_
  subst ha
  exact hv

/-- **A faithful net of shipped timings meets premise 6**, with no side condition. -/
theorem timingWF_of_valid_timings {N : TNet} {tms : Nat → Timing} (hN : FromTimings N tms)
    (hv : ∀ i, i < N.length → (tms i).Valid) : TimingWF N :=
  timingWF_of_timings hN (fun i hi => (hv i hi).pre) fun i hi a ha => by
    have := hv i hi
    rw [ha] at this
    exact this

/-! ## The millisecond grid -/

/-- `x` is a multiple of `g`. -/
def GridQ (g x : ℚ) : Prop := ∃ z : ℤ, x = z * g

/-- A bound that is `⊤` or a multiple of `g`. -/
def GridB (g : ℚ) (x : Bound) : Prop := x = ⊤ ∨ ∃ z : ℤ, x = ((z * g : ℚ) : Bound)

/-- Every static bound of the net is on the grid `g · ℤ`. -/
def NetGrid (g : ℚ) (N : TNet) : Prop := ∀ i, GridQ g (eftOf N i) ∧ GridB g (lftOf N i)

theorem gridQ_ms (n : Nat) : GridQ (1 / 1000) ((n : ℚ) / 1000) := ⟨n, by push_cast; ring⟩

/-- **Faithful bounds are on the millisecond grid.** -/
theorem netGrid_of_timings {N : TNet} {tms : Nat → Timing} (hN : FromTimings N tms) :
    NetGrid (1 / 1000) N := by
  intro i
  by_cases hi : i < N.length
  · rw [(hN i hi).1, (hN i hi).2]
    obtain ⟨z, hz⟩ := gridQ_ms (tms i).latest
    exact ⟨gridQ_ms _, Or.inr ⟨z, by unfold lftT; rw [hz]⟩⟩
  · have e1 : eftOf N i = 0 := by simp [eftOf, List.getElem?_eq_none (by omega : N.length ≤ i)]
    have e2 : lftOf N i = ⊤ := by simp [lftOf, List.getElem?_eq_none (by omega : N.length ≤ i)]
    rw [e1, e2]
    exact ⟨⟨0, by simp⟩, Or.inl rfl⟩

end Libpetri.Novel.TimedScg
