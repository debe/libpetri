import Libpetri.Novel.LinearBound

/-!
# Route A: the checked colour-slot bound ([NU-053])

The name-coloured encoding gives every coloured place `k` colour columns. `k` has to bound the
number of names that are live at the same time: a mint takes a colour that no coloured place
holds, and with too few colours a mint the executor can fire finds no free colour, so the
encoding misses that run. This module models how the shipped verifier obtains `k` and proves
that every `k` it accepts is such a bound.

## How `k` is obtained

`k = ⌊opt⌋`, where `opt` is the optimum of the linear program over the flat net

* minimise `y·M₀`
* subject to `y ≥ 0`, `y_p ≥ 1` on every coloured place `p`, and `y·C_r ≤ 0` for every flat
  row `r`,

with `C_r` the row's column `post − pre`, read as `dotIncD` reads it: deposit counts minus
required counts. Every implementation solves the program with its own exact rational simplex
(`solve`, `slot_bound_lp.rs`). The simplex is neither modelled nor trusted. Its answer is a
weighting scaled to integers, a vector `Y` and a denominator `D` that stand for `y = Y / D`.

## The checker

`check_cover` (`slot_bound_lp.rs`) re-checks the answer in exact integer arithmetic before the
plan uses it, and computes `k` itself as `⌊Y·M₀ / D⌋`. It accepts when `D ≥ 1`, `Y_p ≥ 0` on
every place, `Y_p ≥ D` on every coloured place, `Y·C_r ≤ 0` on every flat row (the rows the
simplex's presolve dropped included), and `k ≤ slotCap`. `checked` (`slot_bound_lp.rs`) passes
an optimal answer through `check_cover` and turns every other answer (infeasible, over a size or
pivot limit, stopped) into no bound. `checkCover` and `colourSlotBoundLP` model the two
functions. The model reads `Y` as a total `Weight` and `D` as a `Nat`. The Rust's length check
on `Y` and its refusal of a negative `D` have no counterpart in the model, and both only refuse
more.

## What is proved

* `checkCover_sound`, `colourSlotBoundLP_sound`: an accepted answer gives a `ScaledCover`,
  that is some `D > 0` and `y` with `y ≥ 0`, `y ≥ D` on every coloured place, `y·C_r ≤ 0` on
  every row and `y·M₀ < D·(k + 1)`. Nothing is assumed about the simplex.
* `coloured_tokens_le`: under a scaled cover, every marking the flat rows reach holds at most
  `k` tokens on the coloured places. Along a run `y·M` never grows (`dot_le_initial_rows`),
  and `D·Σ_C M ≤ y·M` (`sum_le_dot_scaled`), so `D·Σ_C M < D·(k + 1)`.
* `vacuous_colour_layer_lp` ([NU-053] AC6): with `k = 0` no coloured place ever holds a
  token, so no row that consumes from or deposits into one is ever enabled, and dropping those
  rows changes no reachable marking. The zero-slot plan is exact.
* `scaledCover_of_cover`: the unscaled cover of the old semiflow bound is the case `D = 1`.

`Simulate.lean` takes the scaled cover as the `cover` premise of `coloured_simulates`
(`colour_slots_suffice`), and `Plan.lean` computes it as `colourSlotBoundLP` of an arbitrary
simplex answer, so `buildPlan_premisesS` carries no hypothesis about the simplex.

## No H1

A reset place or a consume-all place may carry weight. At an enabled firing such a place ends
at `post[p]`, which is at most `m_p − pre[p] + post[p]` because enablement gives
`pre[p] ≤ m_p` (`fireAD_le_linear`), and a non-negative weight keeps the inequality
(`dot_fireAD_le`). The [VER-015] check `check_linear_bound_exact` still pins such places to
weight zero (H1), although its proof does not use that (`linear_bound_sound_noH1`). The slot
bound follows the proof. The difference is deliberate.

## Why the cover is scaled

`Weight` is integer valued and the optimum is rational. A fork that consumes `exactly(3)`
budget tokens into two coloured places, with a join that refunds one, from a budget of 7, has
the optimum `14/3`, and at most 4 coloured tokens are ever present. Every integer cover weights
the budget at least 1 and so has `y·M₀ ≥ 7`. The scaled cover `Y = (2, 3, 3)` on budget and
the two keys, `D = 3`, gives `k = 4`. `Frac` at the end of this file checks all three claims on
that net (`Frac.checked_fractional`, `Frac.keys_le_four`, `Frac.integer_cover_ge_seven`).
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## The checker -/

/-- The largest colour-slot bound a plan may carry. It is the limit of Java's `int`, applied by
every implementation so that all three refuse the same nets. -/
def slotCap : Nat := 2147483647

/-- A scaled cover of the flat rows: some denominator `D > 0` and weighting `y` with `y ≥ 0`
below `n`, `y ≥ D` on every coloured place, `y` not increasing along any row, and
`y·M₀ < D·(k + 1)`, that is `⌊y·M₀ / D⌋ ≤ k`. With `D = 1` it is the cover of the semiflow
bound (`scaledCover_of_cover`). -/
def ScaledCover (n : Nat) (C : List PlaceId) (rows : List (Transition × Deposit))
    (a0 : AMarking) (k : Nat) : Prop :=
  ∃ (D : Nat) (y : Weight), 0 < D ∧ (∀ p, p < n → 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
    (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ dot y a0 n < (D : Int) * ((k : Int) + 1)

/-- `check_cover` (`slot_bound_lp.rs`): accept the scaled weighting `y / D` and return
`k = ⌊y·M₀ / D⌋`, or refuse. The checks are the Rust's, in its order: `D` positive, every
weight non-negative, every coloured weight at least `D`, no flat row increasing the weighted
sum, `k` within `slotCap`. The Rust also checks that the weighting has one entry per place;
`Weight` is total, so that shape guard only refuses more. `y·M₀ ≥ 0` once the weights are
non-negative, so `Int.toNat` truncates nothing there. `rows` is every flat row
(`flat.transitions`; `buildPlan` passes `src.map SrcRow.flat`), never the rows the simplex's
presolve kept. -/
def checkCover (n : Nat) (C : List PlaceId) (rows : List (Transition × Deposit))
    (a0 : AMarking) (D : Nat) (y : Weight) : Option Nat :=
  if 0 < D ∧ (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
      (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ (dot y a0 n).toNat / D ≤ slotCap
  then some ((dot y a0 n).toNat / D) else none

/-- `checked` (`slot_bound_lp.rs`): the bound of whatever the simplex answered. `some (D, y)`
is an optimal answer with its scaled weighting, and `none` stands for every answer without one
(infeasible, over a limit, stopped). The simplex itself (`solve`) is not modelled: `ans` is
arbitrary. -/
def colourSlotBoundLP (n : Nat) (C : List PlaceId) (rows : List (Transition × Deposit))
    (a0 : AMarking) (ans : Option (Nat × Weight)) : Option Nat :=
  ans.bind fun a => checkCover n C rows a0 a.1 a.2

/-! ## Soundness of the checker -/

/-- A weighting that is non-negative below `n` has a non-negative weighted sum. -/
theorem dot_nonneg_of {y : Weight} {a : AMarking} {n : Nat} (hy : ∀ p, p < n → 0 ≤ y p) :
    0 ≤ dot y a n := by
  rw [dot_eq_isum]
  exact Finset.sum_nonneg fun p hp =>
    Int.mul_nonneg (hy p (Finset.mem_range.mp hp)) (Int.natCast_nonneg _)

/-- **`check_cover` is sound.** Whatever `k` it accepts comes with a scaled cover. -/
theorem checkCover_sound {n : Nat} {C : List PlaceId} {rows : List (Transition × Deposit)}
    {a0 : AMarking} {D : Nat} {y : Weight} {k : Nat}
    (h : checkCover n C rows a0 D y = some k) : ScaledCover n C rows a0 k := by
  unfold checkCover at h
  split at h
  · rename_i hc
    obtain ⟨hD, hpos, hcov, hdec, -⟩ := hc
    obtain rfl := Option.some.inj h
    have hpos' : ∀ p, p < n → 0 ≤ y p := fun p hp => hpos p (List.mem_range.mpr hp)
    have hv : ((dot y a0 n).toNat : Int) = dot y a0 n := Int.toNat_of_nonneg (dot_nonneg_of hpos')
    refine ⟨D, y, hD, hpos', hcov, hdec, ?_⟩
    have hlt := Nat.lt_mul_div_succ (dot y a0 n).toNat hD
    generalize (dot y a0 n).toNat / D = q at hlt ⊢
    generalize (dot y a0 n).toNat = v at hlt hv
    rw [← hv]
    exact_mod_cast hlt
  · exact absurd h (by simp)

/-- **`checked` is sound**, for any simplex answer. -/
theorem colourSlotBoundLP_sound {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {ans : Option (Nat × Weight)}
    {k : Nat} (h : colourSlotBoundLP n C rows a0 ans = some k) : ScaledCover n C rows a0 k := by
  cases ans with
  | none => exact absurd h (by simp [colourSlotBoundLP])
  | some a => exact checkCover_sound h

/-- The unscaled cover is the `D = 1` case (the semiflow bound of the historical
`buildPlanBudget`, `Plan.lean`). -/
theorem scaledCover_of_cover {n : Nat} {C : List PlaceId} {rows : List (Transition × Deposit)}
    {a0 : AMarking} {k : Nat} {y : Weight} (hpos : ∀ p, p < n → 0 ≤ y p)
    (hcov : ∀ p ∈ C, 1 ≤ y p) (hdec : ∀ tr ∈ rows, dotIncD y tr n ≤ 0)
    (hk : dot y a0 n ≤ k) : ScaledCover n C rows a0 k :=
  ⟨1, y, Nat.one_pos, hpos, fun p hp => by rw [Nat.cast_one]; exact hcov p hp, hdec,
    by rw [Nat.cast_one, Int.one_mul]; omega⟩

/-! ## The token-sum bound -/

/-- With `y ≥ 0` and `y ≥ D` on the (duplicate-free, dense) coloured places, `D` times their
token total is at most `y·M`. -/
theorem sum_le_dot_scaled {C : List PlaceId} {y : Weight} {a : AMarking} {n D : Nat}
    (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n) (hpos : ∀ p, p < n → 0 ≤ y p)
    (hcov : ∀ p ∈ C, (D : Int) ≤ y p) :
    (D : Int) * (((C.map a).sum : Nat) : Int) ≤ dot y a n := by
  rw [← List.sum_toFinset _ hnd, dot_eq_isum, isum]
  push_cast
  rw [Finset.mul_sum]
  calc ∑ p ∈ C.toFinset, (D : Int) * (a p : Int) ≤ ∑ p ∈ C.toFinset, y p * (a p : Int) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Int.mul_le_mul_of_nonneg_right (hcov p (List.mem_toFinset.mp hp))
          (Int.natCast_nonneg _)
    _ ≤ ∑ p ∈ Finset.range n, y p * (a p : Int) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_range.mpr (hCn p (List.mem_toFinset.mp hp))
        · intro p hp _
          exact Int.mul_nonneg (hpos p (Finset.mem_range.mp hp)) (Int.natCast_nonneg _)

/-- **The token-sum bound.** Under a scaled cover, every marking the rows reach holds at most
`k` tokens on the coloured places. -/
theorem coloured_tokens_le {rows : List (Transition × Deposit)} {C : List PlaceId}
    {a0 a : AMarking} {n k : Nat} (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n)
    (hcov : ScaledCover n C rows a0 k) (h : ReachAD rows a0 a) : (C.map a).sum ≤ k := by
  obtain ⟨D, y, hD, hpos, hcovD, hdec, hk⟩ := hcov
  have hle : dot y a n ≤ dot y a0 n :=
    dot_le_initial_rows (envs := []) hpos hdec (by simp) (reachAD_sub_inj h)
  have hsum := sum_le_dot_scaled (a := a) hnd hCn hpos hcovD
  have hlt : (D : Int) * (((C.map a).sum : Nat) : Int) < (D : Int) * ((k : Int) + 1) :=
    lt_of_le_of_lt (le_trans hsum hle) hk
  have hs := Int.lt_of_mul_lt_mul_left hlt (Int.natCast_nonneg D)
  omega

/-! ## `k = 0` is exact -/

/-- Every arm of `fireAD` leaves at least the row's deposit on a place. -/
theorem count_le_fireAD (a : AMarking) (t : Transition) (d : Deposit) (p : PlaceId) :
    d.count p ≤ fireAD a t d p := by
  unfold fireAD
  by_cases hR : t.resets.contains p = true
  · rw [if_pos hR]
  · rw [if_neg hR]
    by_cases hCA : consumeAllAt t p = true
    · rw [if_pos hCA]
    · rw [if_neg hCA]; omega

/-- **The zero-slot plan of the LP bound is exact** ([NU-053] AC6). With a scaled cover at
`k = 0`, every coloured place is empty on every reachable marking. A row that consumes from a
coloured place is therefore never enabled, and neither is a row that deposits into one, since
firing it would reach a marking with a coloured token. Any sub-net that keeps the rows touching
no coloured place, the only rows the zero-slot encoding emits a rule for, reaches exactly the
markings the full net reaches. This is the twin of the locked `vacuous_colour_layer`
(`Semiflow.lean`) for a non-increasing weighting with no H1. -/
theorem vacuous_colour_layer_lp {rows rows' : List (Transition × Deposit)} {C : List PlaceId}
    {a0 : AMarking} {n : Nat} (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n)
    (hcov : ScaledCover n C rows a0 0)
    (hsub : ∀ tr ∈ rows', tr ∈ rows)
    (hkeep : ∀ tr ∈ rows, (∀ p ∈ C, pre tr.1 p = 0 ∧ tr.2.count p = 0) → tr ∈ rows') :
    ∀ a, ReachAD rows a0 a ↔ ReachAD rows' a0 a := by
  have hempty : ∀ a, ReachAD rows a0 a → ∀ p ∈ C, a p = 0 := by
    intro a h p hp
    have h0 := coloured_tokens_le hnd hCn hcov h
    have hle : a p ≤ (C.map a).sum :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    omega
  intro a
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a1 a2 hr hs ih =>
      obtain ⟨tr, hmem, hen, rfl⟩ := hs
      have hkept : tr ∈ rows' := hkeep tr hmem fun p hp => by
        have h1 := hempty a1 hr p hp
        have hpre := pre_le_of_enabledA hen p
        have hsucc : ReachAD rows a0 (fireAD a1 tr.1 tr.2) :=
          Relation.ReflTransGen.tail hr ⟨tr, hmem, hen, rfl⟩
        have h2 := hempty _ hsucc p hp
        have hge := count_le_fireAD a1 tr.1 tr.2 p
        omega
      exact Relation.ReflTransGen.tail ih ⟨tr, hkept, hen, rfl⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨tr, hmem, hen, rfl⟩ := hs
      exact Relation.ReflTransGen.tail ih ⟨tr, hsub tr hmem, hen, rfl⟩

/-! ## A fractional optimum

The net of the module header, on which the scaled cover is strictly better than any integer
one. Places: `0 = budget`, `1 = a`, `2 = b` (the two coloured keys). -/

namespace Frac

/-- `fork : exactly(3) budget → a, b`. -/
def tFork : Transition :=
  { name := "fork", inputs := [⟨0, .exactly 3, none⟩], inhibitors := [], reads := [],
    resets := [] }

/-- `join : a, b → budget`, refunding one budget token. -/
def tJoin : Transition :=
  { name := "join", inputs := [⟨1, .one, none⟩, ⟨2, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }

/-- The two flat rows. -/
def rowsFrac : List (Transition × Deposit) := [(tFork, [1, 2]), (tJoin, [0])]

/-- A budget of 7. -/
def a0Frac : AMarking := fun p => if p = 0 then 7 else 0

/-- The simplex's weighting, scaled: `Y = (2, 3, 3)` over `D = 3`, that is `y = (2/3, 1, 1)`
and `y·M₀ = 14/3`, the optimum. -/
def yFrac : Weight := fun p => if p = 0 then 2 else if p = 1 ∨ p = 2 then 3 else 0

/-- The checker accepts the scaled weighting and returns `k = ⌊14/3⌋ = 4`. -/
theorem checked_fractional : checkCover 3 [1, 2] rowsFrac a0Frac 3 yFrac = some 4 := by
  decide

/-- Hence no marking the rows reach holds more than 4 tokens on the keys. -/
theorem keys_le_four : ∀ a, ReachAD rowsFrac a0Frac a → a 1 + a 2 ≤ 4 := by
  intro a h
  have := coloured_tokens_le (C := [1, 2]) (n := 3) (by decide) (by decide)
    (checkCover_sound checked_fractional) h
  simpa using this

/-- Every integer cover (the case `D = 1`) has `y·M₀ ≥ 7`: the fork forces
`3·y_budget ≥ y_a + y_b ≥ 2`, so `y_budget ≥ 1`. -/
theorem integer_cover_ge_seven {y : Weight} (hcov : ∀ p ∈ [1, 2], 1 ≤ y p)
    (hdec : ∀ tr ∈ rowsFrac, dotIncD y tr 3 ≤ 0) : 7 ≤ dot y a0Frac 3 := by
  have hf := hdec (tFork, [1, 2]) (by simp [rowsFrac])
  have h1 := hcov 1 (by simp)
  have h2 := hcov 2 (by simp)
  have hp0 : pre tFork 0 = 3 := rfl
  have hp1 : pre tFork 1 = 0 := rfl
  have hp2 : pre tFork 2 = 0 := rfl
  simp [dotIncD, isum, Finset.sum_range_succ, hp0, hp1, hp2] at hf
  simp [dot_eq_isum, isum, a0Frac]
  omega

end Frac

end Libpetri.Novel.RouteA
