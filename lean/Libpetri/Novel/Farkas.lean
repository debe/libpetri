import Libpetri.StateEquation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Farkas / Colom–Silva semiflow enumeration is sound

Model of `compute_p_semiflows` (`rust/libpetri-verification/src/p_invariant.rs:141-219`), the
P-semiflow source of [VER-007], against the incidence matrix and abstract reachability of
`StateEquation.lean` / `Strengthening.lean`.

**The algorithm.** A generator row is a pair (signature over transitions, weight over places)
(`GenRow`). Row `p` starts as (column `p` of `C`, unit vector `e_p`)
(`p_invariant.rs:156-163`, `initRows`). Transition columns are eliminated in index order
(`p_invariant.rs:165-199`, `farkasRound`): rows with a zero entry at `t` survive, every
(positive, negative) pair is combined as `(-rn[t])·rp + rp[t]·rn` (`combine`, the checked
`combine_row`), and each combination is divided by the gcd of all its entries when that gcd
exceeds `1` (`reduceGcd`, `reduce_gcd`). Rows with an all-zero weight are dropped at the end
(`farkas`, `p_invariant.rs:201-202`).

**What is abstracted.** Everything the Rust round does after building the candidates only
*removes* rows: the i64 overflow drop in `combine_row`, the candidate ceiling
`MAX_SEMIFLOW_CANDIDATES`, `keep_support_minimal` and the `MAX_SEMIFLOW_ROWS` truncation. The
model takes the round's post-processing as an arbitrary `prune` that returns a sub-selection of
its input (`hprune`); `shippedPrune` is the minimality filter plus truncation as one instance.
`good_candidates` is stated for any sub-selection, so the i64 overflow drop is covered too even
though `prune` sees only the combined rows. Arithmetic is unbounded `Int`. The weight vector
the Rust code returns is `GenRow.w` restricted to `[0, np)`; `constant = y·M0` is `dot y a0 np`.
The matrix is `incAt net`, the flat transitions only: env-injector columns
(`IncidenceMatrix::from_flat_net` with a non-empty env list) are not modelled.

**Results.**
* `good_candidates`: one elimination round keeps every row a non-negative combination whose
  signature is `yᵀC` and is zero on every eliminated column. This is the invariant of the whole
  algorithm.
* `farkas_output_semiflow`: every vector the algorithm returns is semi-positive, supported
  below `np`, nonzero, and annihilates every column of `C` (`y ≥ 0`, `yᵀC = 0`).
* `certificate_sound`: a certificate passing the `yᵀC = 0` check (column by column, as
  `validate_invariants_exact` does), together with the H1 linearity guard, keeps `y·M`
  constant on every reachable marking. H1 cannot be dropped: `semiflow_gate_is_necessary`
  (`Semiflow.lean`) is a Farkas row that is false on the real net without it.
* `farkas_output_is_semiflow` / `farkas_output_sound`: the two combined. Every Farkas output
  that passes H1 is a `Semiflow` in the sense of `Semiflow.lean`, and `y·M = y·M0` on every
  reachable marking.

Not proved: completeness (that the rows form a generating set of the minimal semiflows). The
Rust caps make it false in general anyway ([VER-007]).
-/

namespace Libpetri.Novel.Farkas

open Libpetri Finset

/-! ## Linear algebra over the first `np` places -/

/-- Entry `k` of `yᵀC` over the first `np` places: `Σ_{p < np} y p · C[k][p]`. -/
def lin (c : Nat → PlaceId → Int) (np : Nat) (y : Weight) (k : Nat) : Int :=
  ∑ p ∈ range np, y p * c k p

theorem lin_combine (c : Nat → PlaceId → Int) (np : Nat) (a b : Int) (w1 w2 : Weight)
    (k : Nat) :
    lin c np (fun q => a * w1 q + b * w2 q) k = a * lin c np w1 k + b * lin c np w2 k := by
  unfold lin
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- The one bridge to `isum` of `InvariantSum.lean`, through its `isum_succ` lemma. -/
theorem isum_eq_sum (f : PlaceId → Int) : ∀ n, isum f n = ∑ p ∈ range n, f p
  | 0 => by rw [sum_range_zero]; rfl
  | n + 1 => by rw [sum_range_succ, isum_succ, isum_eq_sum f n]

/-- `dotInc` of flat transition `k` is entry `k` of `yᵀC` for `C = incAt net`. -/
theorem dotInc_eq_lin {net : FlatNet} {k : Nat} {ft : FlatTransition}
    (hk : net[k]? = some ft) (y : Weight) (np : Nat) :
    dotInc y ft np = lin (incAt net) np y k := by
  unfold dotInc lin
  rw [isum_eq_sum]
  refine sum_congr rfl fun p _ => ?_
  simp only [incAt, hk]

/-! ## The algorithm -/

/-- A generator row: `sig` over transition indices, `w` over places
(`(Vec<i64>, Vec<i64>)` in `compute_p_semiflows`). -/
structure GenRow where
  sig : Nat → Int
  w : Weight

/-- Initial row of place `p`: signature = column `p` of `C`, weight = `e_p`. -/
def initRow (c : Nat → PlaceId → Int) (p : PlaceId) : GenRow :=
  ⟨fun k => c k p, fun q => if q = p then 1 else 0⟩

def initRows (c : Nat → PlaceId → Int) (np : Nat) : List GenRow :=
  (List.range np).map (initRow c)

/-- `cp·rp + cn·rn` with `cp = -rn[t]`, `cn = rp[t]` (`combine_row`, both halves). -/
def combine (t : Nat) (rp rn : GenRow) : GenRow :=
  ⟨fun k => -rn.sig t * rp.sig k + rp.sig t * rn.sig k,
   fun q => -rn.sig t * rp.w q + rp.sig t * rn.w q⟩

/-- `gcd` of the absolute values of a list of integers (`0` for the empty list). -/
def gcdAll (l : List Int) : Nat :=
  l.foldr (fun v g => Nat.gcd v.natAbs g) 0

theorem gcdAll_dvd : ∀ {l : List Int} {v : Int}, v ∈ l → ((gcdAll l : Nat) : Int) ∣ v
  | a :: l, v, h => by
    show ((Nat.gcd a.natAbs (gcdAll l) : Nat) : Int) ∣ v
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) (gcdAll_dvd h)

/-- The gcd `reduce_gcd` computes: over the `nt` signature and `np` weight entries. -/
def rowGcd (nt np : Nat) (r : GenRow) : Nat :=
  gcdAll ((List.range nt).map r.sig ++ (List.range np).map r.w)

/-- `reduce_gcd`: divide every entry by the row gcd when it exceeds `1`. -/
def reduceGcd (nt np : Nat) (r : GenRow) : GenRow :=
  if 1 < rowGcd nt np r then
    ⟨fun k => r.sig k / (rowGcd nt np r : Int), fun q => r.w q / (rowGcd nt np r : Int)⟩
  else r

/-- The rows one elimination round builds before any pruning: the rows with a zero entry at
`t`, then every (positive, negative) pair, combined and gcd-reduced, in the Rust loop order. -/
def candidates (nt np t : Nat) (rows : List GenRow) : List GenRow :=
  rows.filter (fun r => decide (r.sig t = 0)) ++
    (rows.filter fun r => decide (0 < r.sig t)).flatMap fun rp =>
      (rows.filter fun r => decide (r.sig t < 0)).map fun rn =>
        reduceGcd nt np (combine t rp rn)

/-- One round: `prune` stands for everything after candidate construction. -/
def farkasRound (prune : Nat → List GenRow → List GenRow) (nt np t : Nat)
    (rows : List GenRow) : List GenRow :=
  prune t (candidates nt np t rows)

/-- The rows after eliminating the columns `0, …, nt - 1` in order. -/
def farkasRows (prune : Nat → List GenRow → List GenRow) (c : Nat → PlaceId → Int)
    (nt np : Nat) : List GenRow :=
  (List.range nt).foldl (fun rows t => farkasRound prune nt np t rows) (initRows c np)

/-- The returned weight vectors: rows whose weight is nonzero somewhere below `np`. -/
def farkas (prune : Nat → List GenRow → List GenRow) (c : Nat → PlaceId → Int)
    (nt np : Nat) : List Weight :=
  ((farkasRows prune c nt np).filter fun r =>
    (List.range np).any fun q => decide (r.w q ≠ 0)).map GenRow.w

/-- `compute_p_semiflows` on a flat net: `C = incAt net`, one column per flat transition. -/
def netFarkas (prune : Nat → List GenRow → List GenRow) (net : FlatNet) (np : Nat) :
    List Weight :=
  farkas prune (incAt net) net.length np

/-! ### The shipped pruning, as one instance -/

/-- The weight support below `np`, ascending. -/
def supp (np : Nat) (r : GenRow) : List Nat :=
  (List.range np).filter fun q => decide (r.w q ≠ 0)

/-- `keep_support_minimal`: drop a row when some row has a strictly smaller support that is
contained in its own (`p_invariant.rs:455-512`, the order-free definition stated there). -/
def keepSupportMinimal (np : Nat) (rows : List GenRow) : List GenRow :=
  rows.filter fun r => !rows.any fun r' =>
    decide ((supp np r').length < (supp np r).length) &&
      (supp np r').all fun q => decide (q ∈ supp np r)

/-- `keep_support_minimal` followed by `truncate(cap)`. -/
def shippedPrune (np cap : Nat) (_t : Nat) (rows : List GenRow) : List GenRow :=
  (keepSupportMinimal np rows).take cap

theorem shippedPrune_sub (np cap : Nat) :
    ∀ t l, ∀ r ∈ shippedPrune np cap t l, r ∈ l := by
  intro t l r h
  exact (List.mem_filter.mp (List.mem_of_mem_take h)).1

/-! ## The invariant of the elimination -/

/-- What every row satisfies after eliminating columns `0, …, t - 1`: a non-negative weight
supported below `np`, the signature is `yᵀC`, and it is zero on the eliminated columns. -/
structure Good (c : Nat → PlaceId → Int) (nt np t : Nat) (r : GenRow) : Prop where
  nonneg : ∀ q, 0 ≤ r.w q
  below : SupportBelow np r.w
  sigEq : ∀ k, k < nt → r.sig k = lin c np r.w k
  elim : ∀ k, k < t → r.sig k = 0

theorem good_init (c : Nat → PlaceId → Int) (nt : Nat) {np p : Nat} (hp : p < np) :
    Good c nt np 0 (initRow c p) where
  nonneg q := by
    show 0 ≤ (if q = p then (1 : Int) else 0)
    split <;> omega
  below q hq := by
    show (if q = p then (1 : Int) else 0) = 0
    rw [if_neg (by omega)]
  sigEq k _ := by
    simp [initRow, lin, hp]
  elim k hk := absurd hk (Nat.not_lt_zero k)

theorem good_combine {c : Nat → PlaceId → Int} {nt np t : Nat} {rp rn : GenRow}
    (hp : Good c nt np t rp) (hn : Good c nt np t rn)
    (hpos : 0 < rp.sig t) (hneg : rn.sig t < 0) :
    Good c nt np (t + 1) (combine t rp rn) where
  nonneg q := by
    show 0 ≤ -rn.sig t * rp.w q + rp.sig t * rn.w q
    exact Int.add_nonneg (Int.mul_nonneg (by omega) (hp.nonneg q))
      (Int.mul_nonneg (by omega) (hn.nonneg q))
  below q hq := by
    show -rn.sig t * rp.w q + rp.sig t * rn.w q = 0
    rw [hp.below q hq, hn.below q hq]
    ring
  sigEq k hk := by
    show -rn.sig t * rp.sig k + rp.sig t * rn.sig k
      = lin c np (fun q => -rn.sig t * rp.w q + rp.sig t * rn.w q) k
    rw [lin_combine, ← hp.sigEq k hk, ← hn.sigEq k hk]
  elim k hk := by
    show -rn.sig t * rp.sig k + rp.sig t * rn.sig k = 0
    rcases Nat.lt_or_ge k t with hlt | hge
    · rw [hp.elim k hlt, hn.elim k hlt]
      ring
    · have hkt : k = t := by omega
      subst hkt
      ring

theorem good_reduce {c : Nat → PlaceId → Int} {nt np t : Nat} {r : GenRow}
    (h : Good c nt np t r) : Good c nt np t (reduceGcd nt np r) := by
  unfold reduceGcd
  split_ifs with hg
  swap
  · exact h
  have hgpos : (0 : Int) < (rowGcd nt np r : Int) := by omega
  have hdw : ∀ q, q < np → (rowGcd nt np r : Int) ∣ r.w q := fun q hq =>
    gcdAll_dvd (List.mem_append_right _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩))
  refine
    { nonneg := fun q => Int.ediv_nonneg (h.nonneg q) (le_of_lt hgpos)
      below := fun q hq => by
        show r.w q / (rowGcd nt np r : Int) = 0
        rw [h.below q hq, Int.zero_ediv]
      sigEq := fun k hk => ?_
      elim := fun k hk => by
        show r.sig k / (rowGcd nt np r : Int) = 0
        rw [h.elim k hk, Int.zero_ediv] }
  show r.sig k / (rowGcd nt np r : Int) = lin c np (fun q => r.w q / (rowGcd nt np r : Int)) k
  have hscale : lin c np r.w k
      = (rowGcd nt np r : Int) * lin c np (fun q => r.w q / (rowGcd nt np r : Int)) k := by
    unfold lin
    rw [mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdw p (mem_range.mp hp))]
  rw [h.sigEq k hk, hscale, Int.mul_ediv_cancel_left _ (ne_of_gt hgpos)]

/-- **One elimination round preserves the invariant** — for every row the round builds,
hence for any sub-selection of them (overflow drop, candidate cap, minimality, truncation). -/
theorem good_candidates {c : Nat → PlaceId → Int} {nt np t : Nat} {rows : List GenRow}
    (h : ∀ r ∈ rows, Good c nt np t r) :
    ∀ r ∈ candidates nt np t rows, Good c nt np (t + 1) r := by
  intro r hr
  simp only [candidates, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map,
    decide_eq_true_eq] at hr
  rcases hr with ⟨hr, h0⟩ | ⟨rp, ⟨hrp, hpos⟩, rn, ⟨hrn, hneg⟩, rfl⟩
  · have g := h r hr
    exact
      { nonneg := g.nonneg
        below := g.below
        sigEq := g.sigEq
        elim := fun k hk => by
          rcases Nat.lt_or_ge k t with hlt | hge
          · exact g.elim k hlt
          · have hkt : k = t := by omega
            exact hkt ▸ h0 }
  · exact good_reduce (good_combine (h rp hrp) (h rn hrn) hpos hneg)

theorem good_farkasRows_aux {prune : Nat → List GenRow → List GenRow}
    (hprune : ∀ t l, ∀ r ∈ prune t l, r ∈ l) (c : Nat → PlaceId → Int) (nt np : Nat) :
    ∀ m, ∀ r ∈ (List.range m).foldl (fun rows t => farkasRound prune nt np t rows)
      (initRows c np), Good c nt np m r
  | 0, r, hr => by
    simp only [List.range_zero, List.foldl_nil, initRows, List.mem_map, List.mem_range] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact good_init c nt hp
  | m + 1, r, hr => by
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      farkasRound] at hr
    exact good_candidates (good_farkasRows_aux hprune c nt np m) r (hprune _ _ r hr)

theorem good_farkasRows {prune : Nat → List GenRow → List GenRow}
    (hprune : ∀ t l, ∀ r ∈ prune t l, r ∈ l) (c : Nat → PlaceId → Int) (nt np : Nat) :
    ∀ r ∈ farkasRows prune c nt np, Good c nt np nt r :=
  good_farkasRows_aux hprune c nt np nt

/-! ## Every output is a semiflow -/

/-- **Every vector the elimination returns is a P-semiflow of `C`**: non-negative, supported
below `np`, nonzero, and `yᵀC = 0` on every one of the `nt` columns. -/
theorem farkas_output_semiflow {prune : Nat → List GenRow → List GenRow}
    (hprune : ∀ t l, ∀ r ∈ prune t l, r ∈ l) {c : Nat → PlaceId → Int} {nt np : Nat}
    {y : Weight} (hy : y ∈ farkas prune c nt np) :
    (∀ q, 0 ≤ y q) ∧ SupportBelow np y ∧ (∃ q, q < np ∧ y q ≠ 0) ∧
      ∀ k, k < nt → lin c np y k = 0 := by
  simp only [farkas, List.mem_map, List.mem_filter, List.any_eq_true, List.mem_range,
    decide_eq_true_eq] at hy
  obtain ⟨r, ⟨hr, q, hq, hq0⟩, rfl⟩ := hy
  have g := good_farkasRows hprune c nt np r hr
  exact ⟨g.nonneg, g.below, ⟨q, hq, hq0⟩, fun k hk => (g.sigEq k hk).symm.trans (g.elim k hk)⟩

/-- The column-wise `yᵀC = 0` over `C = incAt net` is `dotInc y ft np = 0` for every flat
transition of the net, the H2 of `Strengthening.lean`. -/
theorem dotInc_zero_of_lin {net : FlatNet} {np : Nat} {y : Weight}
    (h : ∀ k, k < net.length → lin (incAt net) np y k = 0) :
    ∀ ft ∈ net, dotInc y ft np = 0 := by
  intro ft hft
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hft
  obtain ⟨hkl, _⟩ := List.getElem?_eq_some_iff.mp hk
  rw [dotInc_eq_lin hk]
  exact h k hkl

/-! ## Soundness of the certificate -/

/-- **Certificate soundness.** If `y` passes the check `validate_invariants_exact` performs,
`yᵀC = 0` on every flat-transition column (`p_invariant.rs:336-354`), and the H1 guard
(no weight on a consume-all or reset place, `p_invariant.rs:324-334`), then `y·M` is constant
on every reachable marking. -/
theorem certificate_sound {net : FlatNet} {np : Nat} {y : Weight} {a0 a : AMarking}
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 np)
    (hC : ∀ k, k < net.length → lin (incAt net) np y k = 0)
    (hr : ReachA net a0 a) : dot y a np = dot y a0 np :=
  invariant_strengthening_sound h1 (dotInc_zero_of_lin hC) hr

/-- **Every Farkas output that passes H1 is a `Semiflow`** in the sense of `Semiflow.lean`:
exactly the hypothesis `semiflow_union_sound` needs of the rows [VER-007] unions in. -/
theorem farkas_output_is_semiflow {prune : Nat → List GenRow → List GenRow}
    (hprune : ∀ t l, ∀ r ∈ prune t l, r ∈ l) {net : FlatNet} {np : Nat} {y : Weight}
    (hy : y ∈ netFarkas prune net np) (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 np) :
    Semiflow net np y :=
  have hs := farkas_output_semiflow hprune hy
  ⟨⟨h1, dotInc_zero_of_lin hs.2.2.2⟩, hs.1⟩

/-- **Farkas correctness end to end.** Every vector the enumeration returns that passes H1 is
a conservation law of the net: `y·M = y·M0` (the emitted `constant`) on every reachable
marking. -/
theorem farkas_output_sound {prune : Nat → List GenRow → List GenRow}
    (hprune : ∀ t l, ∀ r ∈ prune t l, r ∈ l) {net : FlatNet} {np : Nat} {y : Weight}
    {a0 a : AMarking}
    (hy : y ∈ netFarkas prune net np) (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 np)
    (hr : ReachA net a0 a) : dot y a np = dot y a0 np :=
  certificate_sound h1 (farkas_output_semiflow hprune hy).2.2.2 hr

/-- The shipped instance: `keep_support_minimal` then `truncate(MAX_SEMIFLOW_ROWS = 8192)`. -/
theorem shipped_farkas_output_is_semiflow {net : FlatNet} {np : Nat} {y : Weight}
    (hy : y ∈ netFarkas (shippedPrune np 8192) net np)
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 np) :
    Semiflow net np y :=
  farkas_output_is_semiflow (shippedPrune_sub np 8192) hy h1

end Libpetri.Novel.Farkas
