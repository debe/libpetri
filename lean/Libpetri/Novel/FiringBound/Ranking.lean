import Libpetri.Novel.LinearBound

/-!
# The firing bound: `can_fire` and the ranking ([VER-019])

`bounded_run.rs`'s `can_fire` and `check_ranking_exact`, and the run-length bound a ranking gives.
Runs are index sequences replayed as `replay_run` replays them (`replay`). See
`Libpetri/Novel/FiringBound.lean` for the module overview and the premises P1–P7.
-/

namespace Libpetri.Novel.FiringBound

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound


/-- A flat transition: the transition's arcs and the deposit its outcome writes (`post`). -/
abbrev Row := Transition × Deposit

/-! ## `can_fire` -/

/-- `can_fire`: every inhibited place is neither an input with a positive requirement nor read.
Rust reads `pre[p] ≤ 0` off the flat vector; `pre t p` is that vector under P1. -/
def canFire (t : Transition) : Bool :=
  t.inhibitors.all fun p => pre t p == 0 && !t.reads.contains p

/-- An enabled transition passes the filter. -/
theorem canFire_of_enabled {a : AMarking} {t : Transition} (h : enabledA a t = true) :
    canFire t = true := by
  unfold canFire
  rw [List.all_eq_true]
  intro p hp
  have hEn := h
  unfold enabledA at hEn
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hEn
  obtain ⟨⟨_, hInh⟩, hRd⟩ := hEn
  have h0 : a p = 0 := hInh p hp
  have hpre : pre t p ≤ a p := pre_le_of_enabledA h p
  have hr : ¬ p ∈ t.reads := fun hm => by have := hRd p hm; omega
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨by omega, ?_⟩
  simpa using hr

/-- **A filtered transition is enabled at no marking at all.** -/
theorem not_canFire_never_enabled {t : Transition} (h : canFire t = false) (a : AMarking) :
    enabledA a t = false := by
  cases hEn : enabledA a t with
  | false => rfl
  | true => rw [canFire_of_enabled hEn] at h; exact absurd h (by decide)

/-- **`canFire_filter_sound`**: a row that `can_fire` filters out never fires on a reachable
marking. -/
theorem canFire_filter_sound {rows : List Row} {a0 a : AMarking} (_h : ReachAD rows a0 a)
    {tr : Row} (hf : canFire tr.1 = false) : enabledA a tr.1 = false :=
  not_canFire_never_enabled hf a

/-- Dropping the filtered rows changes no reachable set. -/
theorem reachAD_filter_canFire (rows : List Row) (a0 a : AMarking) :
    ReachAD rows a0 a ↔ ReachAD (rows.filter fun tr => canFire tr.1) a0 a := by
  have : StepAD rows = StepAD (rows.filter fun tr => canFire tr.1) := by
    funext x y
    apply propext
    constructor
    · rintro ⟨tr, hmem, hen, rfl⟩
      exact ⟨tr, List.mem_filter.mpr ⟨hmem, canFire_of_enabled hen⟩, hen, rfl⟩
    · rintro ⟨tr, hmem, hen, rfl⟩
      exact ⟨tr, (List.mem_filter.mp hmem).1, hen, rfl⟩
  unfold ReachAD
  rw [this]

/-! ## Runs as the Rust replays them -/

/-- `replay_run` without the final property check: fire the rows named by index in order,
each enabled (`enabled_a`) at the marking it fires from (`fire_a`); `none` on a disabled firing
or an index the net does not have. -/
def replay (rows : List Row) : AMarking → List Nat → Option AMarking
  | a, [] => some a
  | a, t :: ts =>
    match rows[t]? with
    | none => none
    | some tr => if enabledA a tr.1 = true then replay rows (fireAD a tr.1 tr.2) ts else none

theorem replay_append (rows : List Row) :
    ∀ (a : AMarking) (xs ys : List Nat),
      replay rows a (xs ++ ys) = (replay rows a xs).bind fun b => replay rows b ys
  | a, [], ys => rfl
  | a, t :: xs, ys => by
    simp only [List.cons_append, replay]
    cases rows[t]? with
    | none => rfl
    | some tr =>
      simp only
      split
      · exact replay_append rows _ xs ys
      · rfl

/-- One firing at the end of a replay. -/
theorem replay_snoc {rows : List Row} {a b : AMarking} {ts : List Nat} {t : Nat} {tr : Row}
    (h : replay rows a ts = some b) (ht : rows[t]? = some tr) (hen : enabledA b tr.1 = true) :
    replay rows a (ts ++ [t]) = some (fireAD b tr.1 tr.2) := by
  rw [replay_append, h]
  simp [replay, ht, hen]

/-- A replayed run is a run: its end is `ReachAD`-reachable. -/
theorem replay_sound {rows : List Row} :
    ∀ {a b : AMarking} {ts : List Nat}, replay rows a ts = some b → ReachAD rows a b
  | a, b, [], h => by
    simp only [replay, Option.some.injEq] at h
    subst h; exact Relation.ReflTransGen.refl
  | a, b, t :: ts, h => by
    simp only [replay] at h
    cases ht : rows[t]? with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some tr =>
      rw [ht] at h
      simp only at h
      split at h
      · rename_i hen
        have hmem : tr ∈ rows := List.mem_of_getElem? ht
        exact Relation.ReflTransGen.head ⟨tr, hmem, hen, rfl⟩ (replay_sound h)
      · exact absurd h (by simp)

/-- Every index a successful replay fires names a row. -/
theorem replay_lt {rows : List Row} :
    ∀ {a b : AMarking} {ts : List Nat}, replay rows a ts = some b → ∀ t ∈ ts, t < rows.length
  | _, _, [], _ => by simp
  | a, b, t :: ts, h => by
    simp only [replay] at h
    cases ht : rows[t]? with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some tr =>
      rw [ht] at h
      simp only at h
      split at h
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (List.getElem?_eq_some_iff.mp ht).1
        · exact replay_lt h u hu
      · exact absurd h (by simp)

/-- `n` steps of a relation. -/
def NRel {α : Type} (R : α → α → Prop) : Nat → α → α → Prop
  | 0, a, b => a = b
  | k + 1, a, c => ∃ b, NRel R k a b ∧ R b c

/-- Every counted run of the rows is a replay of the same length. -/
theorem nrel_replay {rows : List Row} :
    ∀ {k : Nat} {a b : AMarking}, NRel (StepAD rows) k a b →
      ∃ ts : List Nat, ts.length = k ∧ replay rows a ts = some b
  | 0, a, b, h => ⟨[], rfl, by simp [NRel] at h; simp [replay, h]⟩
  | k + 1, a, c, ⟨b, hab, tr, hmem, hen, hc⟩ => by
    obtain ⟨ts, hlen, hts⟩ := nrel_replay hab
    obtain ⟨t, ht, htr⟩ := List.getElem_of_mem hmem
    refine ⟨ts ++ [t], by simp [hlen], ?_⟩
    rw [hc]
    exact replay_snoc hts (by simp [ht, htr]) hen

/-- Reachability is a replay. -/
theorem reachAD_replay {rows : List Row} {a0 a : AMarking} (h : ReachAD rows a0 a) :
    ∃ ts : List Nat, replay rows a0 ts = some a := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hs ih =>
    obtain ⟨ts, hts⟩ := ih
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    obtain ⟨t, ht, htr⟩ := List.getElem_of_mem hmem
    exact ⟨ts ++ [t], replay_snoc hts (by simp [ht, htr]) hen⟩

theorem reachAD_iff_replay {rows : List Row} {a0 a : AMarking} :
    ReachAD rows a0 a ↔ ∃ ts : List Nat, replay rows a0 ts = some a :=
  ⟨reachAD_replay, fun ⟨_, h⟩ => replay_sound h⟩

/-! ## The ranking -/

/-- A ranking over the first `n` places: non-negative, and every row `can_fire` keeps lowers
`r·M` by at least one in its column. `dotIncD r tr n` is `check_ranking_exact`'s `delta`, the sum
over `p < place_count` of `w[p] * column(ft, p)`, where the Rust `column(ft, p)` is
`post[p] − pre[p]` widened to `i128` and the row's `post[p]` is `tr.2.count p` (`Bmc.lean`'s
`column` is the same function, per place). -/
def IsRanking (n : Nat) (rows : List Row) (r : Weight) : Prop :=
  (∀ p, p < n → 0 ≤ r p) ∧ ∀ tr ∈ rows, canFire tr.1 = true → dotIncD r tr n ≤ -1

/-- `check_ranking_exact` in exact arithmetic: `some K` with `K = r·M0` when every weight below
`n` is non-negative and every row `can_fire` keeps has column sum `≤ −1`; `none` otherwise. -/
def checkRankingExact (n : Nat) (rows : List Row) (a0 : AMarking) (r : Weight) : Option Int :=
  if ((List.range n).all fun p => decide (0 ≤ r p))
      && (rows.all fun tr => !canFire tr.1 || decide (dotIncD r tr n ≤ -1)) then
    some (dot r a0 n)
  else none

/-- The exact check accepts only rankings, and its bound is `r·M0`. -/
theorem checkRankingExact_sound {n : Nat} {rows : List Row} {a0 : AMarking} {r : Weight}
    {K : Int} (h : checkRankingExact n rows a0 r = some K) :
    IsRanking n rows r ∧ K = dot r a0 n := by
  unfold checkRankingExact at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
      Bool.or_eq_true, Bool.not_eq_true'] at hc
    refine ⟨⟨hc.1, fun tr hmem hcf => ?_⟩, (Option.some.inj h).symm⟩
    rcases hc.2 tr hmem with h1 | h1
    · rw [hcf] at h1; exact absurd h1 (by decide)
    · exact h1
  · exact absurd h (by simp)

/-- A marking weighs at least zero under a non-negative weighting. -/
theorem dot_nonneg {r : Weight} {n : Nat} (hpos : ∀ p, p < n → 0 ≤ r p) (a : AMarking) :
    0 ≤ dot r a n := by
  rw [dot_eq_isum]
  unfold isum
  exact Finset.sum_nonneg fun p hp =>
    Int.mul_nonneg (hpos p (Finset.mem_range.mp hp)) (Int.natCast_nonneg _)

/-- One enabled firing lowers `r·M` by at least one. -/
theorem ranking_step {n : Nat} {rows : List Row} {r : Weight} (hr : IsRanking n rows r)
    {a : AMarking} {tr : Row} (hmem : tr ∈ rows) (hen : enabledA a tr.1 = true) :
    dot r (fireAD a tr.1 tr.2) n + 1 ≤ dot r a n := by
  have h1 : dot r (fireAD a tr.1 tr.2) n ≤ dot r a n + dotIncD r tr n :=
    dot_fireAD_le r (d := tr.2) hr.1 hen
  have h2 := hr.2 tr hmem (canFire_of_enabled hen)
  omega

/-- **`ranking_bounds_runs`**: every replayable run from `a0` has at most `r·a0` firings —
`|run| + r·M ≤ r·M0`, and `r·M ≥ 0`. -/
theorem ranking_bounds_runs {n : Nat} {rows : List Row} {r : Weight} (hr : IsRanking n rows r) :
    ∀ {a0 a : AMarking} {ts : List Nat}, replay rows a0 ts = some a →
      (ts.length : Int) + dot r a n ≤ dot r a0 n
  | a0, a, [], h => by
    simp only [replay, Option.some.injEq] at h
    subst h; simp
  | a0, a, t :: ts, h => by
    simp only [replay] at h
    cases ht : rows[t]? with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some tr =>
      rw [ht] at h
      simp only at h
      split at h
      · rename_i hen
        have hstep := ranking_step hr (List.mem_of_getElem? ht) hen
        have ih := ranking_bounds_runs hr h
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      · exact absurd h (by simp)

/-- The run-length form: at most `K` firings. -/
theorem ranking_bounds_length {n : Nat} {rows : List Row} {r : Weight}
    (hr : IsRanking n rows r) {a0 a : AMarking} {ts : List Nat}
    (h : replay rows a0 ts = some a) : (ts.length : Int) ≤ dot r a0 n := by
  have h1 := ranking_bounds_runs hr h
  have h2 := dot_nonneg hr.1 a
  omega

/-- The same over counted steps of `StepAD`. -/
theorem ranking_bounds_steps {n : Nat} {rows : List Row} {r : Weight}
    (hr : IsRanking n rows r) {k : Nat} {a0 a : AMarking} (h : NRel (StepAD rows) k a0 a) :
    (k : Int) ≤ dot r a0 n := by
  obtain ⟨ts, hlen, hts⟩ := nrel_replay h
  rw [← hlen]
  exact ranking_bounds_length hr hts

/-- Counted steps lift along a step map. -/
theorem nrel_lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → S (f x) (f y)) :
    ∀ {k : Nat} {x y : α}, NRel R k x y → NRel S k (f x) (f y)
  | 0, x, y, h => by simp only [NRel] at h ⊢; rw [h]
  | k + 1, x, z, ⟨y, hxy, hyz⟩ => ⟨f y, nrel_lift f hf hxy, hf y z hyz⟩

/-- **The bound holds for the executor.** A concrete run of `k` steps, each depositing a row's
counts (`StepCR`), has `k ≤ r·α(M0)` when every consume-all arc is unguarded. -/
theorem ranking_bounds_concrete {n : Nat} {rows : List Row} {r : Weight}
    (hr : IsRanking n rows r) (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1)
    {k : Nat} {m0 m : CMarking} (h : NRel (StepCR rows) k m0 m) :
    (k : Int) ≤ dot r (alpha m0) n :=
  ranking_bounds_steps hr (nrel_lift alpha (fun _ _ hs => stepCR_simulated hG hs) h)

end Libpetri.Novel.FiringBound
