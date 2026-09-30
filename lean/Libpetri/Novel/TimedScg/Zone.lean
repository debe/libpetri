import Libpetri.Novel.Dbm

/-!
# The firing-domain operations of the timed state-class graph ([VER-010], [VER-011])

`Novel/Dbm.lean` models `Dbm` as a `Fin d`-indexed matrix and proves what canonicalisation and
the emptiness flag do. This file models the four operations the successor step of
`state_class_graph.rs::compute_successor` applies to a firing domain, positionally, on the
row-major `data` of `rust/libpetri-verification/src/dbm.rs`:

* `createPre` — `Dbm::create` before its `canonicalize` (`dbm.rs:35-47`);
* `ltpPre` — `Dbm::let_time_pass` before its `canonicalize` (`dbm.rs:137-147`): row 0 zeroed
  from column 1 on, `(0, 0)` untouched;
* `constrainPre` — step 1 of `Dbm::fire_transition` (`dbm.rs:171-181`): `D[f][i] := min(D[f][i], 0)`
  for every other clock `i`, the "fired fires first" constraint `θ_f ≤ θ_i`;
* `fireMat` — steps 3–5 of `fire_transition` (`dbm.rs:188-224`): persistent clocks copied with
  shifted bounds, newly enabled clocks with their static interval, `∞` elsewhere, `0` on the
  diagonal of the fresh rows;
* `permMat` — `Dbm::permuted` (`dbm.rs:251-275`), `(0, 0)` set to `0`.

A matrix is `NMat := Nat → Nat → Bound`, a dimension travels beside it, and `canonN d` is the
Rust Floyd–Warshall (`Dbm.fwSteps`, same loop order) on the first `d` indices. `toFin_canonN`
ties it to `Dbm.canon`, so `Dbm.sat_canon`, `Dbm.canon_le`, `Dbm.up_canon` and
`Dbm.flagged_empty` apply unchanged (`satN_canonN`, `canonN_le`, `canonN_le_walk`,
`flaggedN_empty`).

The semantic lemmas (`sat_createPre`, `sat_ltpPre`, `sat_ltpPre_shift`, `sat_constrainPre`,
`sat_fireMat`, `sat_permMat`) say which valuations each operation keeps; the successor theorem
of `TimedScg/Succ.lean` composes them. Valuations `θ : Nat → ℚ` carry the reference clock at
index `0`; entry `D a b` bounds `θ a - θ b`, as in `Dbm.lean`. `θ a` for a clock `a ≥ 1` is the
Berthomieu–Diaz firing-time variable: how long from now until that transition fires.

Out of scope, as in `Dbm.lean`: floating point (bounds are exact rationals, `f64::INFINITY` is
`⊤`), and the string rendering of `zone_key`.
-/

namespace Libpetri.Novel.TimedScg

open Libpetri.Novel.Dbm (Bound)

/-- A positional DBM: `D a b` bounds `θ a - θ b`; `a = 0` is the reference clock. -/
abbrev NMat := Nat → Nat → Bound

/-- The `d × d` corner, as a `Dbm.lean` matrix. -/
def toFin (d : Nat) (D : NMat) : Dbm.Matrix d := fun i j => D i j

/-- The zone of the first `d` indices. -/
def SatN (d : Nat) (D : NMat) (θ : Nat → ℚ) : Prop :=
  ∀ i j, i < d → j < d → ((θ i - θ j : ℚ) : Bound) ≤ D i j

theorem satN_iff {d : Nat} {D : NMat} {θ : Nat → ℚ} :
    SatN d D θ ↔ Dbm.Sat (toFin d D) (fun i => θ i) :=
  ⟨fun h i j => h i j i.isLt j.isLt, fun h i j hi hj => h ⟨i, hi⟩ ⟨j, hj⟩⟩

/-! ## Canonicalisation on positional matrices -/

/-- One Floyd–Warshall step, as `Dbm.relax`, on natural-number indices. -/
def relaxN (D : NMat) (k i j : Nat) : NMat :=
  fun a b => if a = i ∧ b = j then min (D i j) (D i k + D k j) else D a b

/-- `canonicalize` on the first `d` indices, in the Rust loop order `Dbm.fwSteps`. -/
def canonN (d : Nat) (D : NMat) : NMat :=
  (Dbm.fwSteps d).foldl (fun D s => relaxN D s.1 s.2.1 s.2.2) D

theorem toFin_relaxN {d : Nat} (D : NMat) (k i j : Fin d) :
    toFin d (relaxN D k i j) = Dbm.relax (toFin d D) k i j := by
  funext a b
  simp only [toFin, relaxN, Dbm.relax, Fin.ext_iff]

theorem toFin_foldl {d : Nat} :
    ∀ (l : List (Fin d × Fin d × Fin d)) (D : NMat),
      toFin d (l.foldl (fun D s => relaxN D s.1 s.2.1 s.2.2) D) = Dbm.runSteps (toFin d D) l
  | [], _ => rfl
  | s :: l, D => by
    simp only [List.foldl_cons]
    rw [toFin_foldl l]
    show Dbm.runSteps (toFin d (relaxN D s.1 s.2.1 s.2.2)) l = _
    rw [toFin_relaxN]
    rfl

/-- **`canonN` is `Dbm.canon`** on the `d × d` corner. -/
theorem toFin_canonN {d : Nat} (D : NMat) : toFin d (canonN d D) = Dbm.canon (toFin d D) :=
  toFin_foldl _ _

theorem satN_canonN {d : Nat} {D : NMat} {θ : Nat → ℚ} : SatN d (canonN d D) θ ↔ SatN d D θ := by
  rw [satN_iff, satN_iff, toFin_canonN]
  exact Dbm.sat_canon _ _

theorem canonN_le {d : Nat} (D : NMat) {a b : Nat} (ha : a < d) (hb : b < d) :
    canonN d D a b ≤ D a b := by
  have h := Dbm.canon_le (toFin d D) ⟨a, ha⟩ ⟨b, hb⟩
  rw [← toFin_canonN] at h
  exact h

/-- A two-step detour bounds every canonical entry (`Dbm.up_canon` with the walk `[k]`). -/
theorem canonN_le_walk {d : Nat} (D : NMat) {a k b : Nat} (ha : a < d) (hk : k < d)
    (hb : b < d) : canonN d D a b ≤ D a k + D k b := by
  have h := Dbm.up_canon (toFin d D) (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (l := [⟨k, hk⟩])
    (List.nodup_singleton _)
  rw [← toFin_canonN] at h
  exact h

/-- The Rust emptiness flag of `canonicalize` on the first `d` indices. -/
def FlaggedN (eps : ℚ) (d : Nat) (D : NMat) : Prop := Dbm.Flagged eps (toFin d D)

instance (eps : ℚ) (d : Nat) (D : NMat) : Decidable (FlaggedN eps d D) := by
  unfold FlaggedN Dbm.Flagged
  infer_instance

/-- A flagged zone is empty (`Dbm.flagged_empty`). -/
theorem flaggedN_empty {eps : ℚ} (heps : 0 ≤ eps) {d : Nat} {D : NMat} (h : FlaggedN eps d D) :
    ¬ ∃ θ, SatN d D θ := by
  rintro ⟨θ, hθ⟩
  exact Dbm.flagged_empty heps h ⟨_, satN_iff.mp hθ⟩

/-- A zone with a solution is never flagged: the successor it guards is kept. -/
theorem not_flagged_of_sat {eps : ℚ} (heps : 0 ≤ eps) {d : Nat} {D : NMat} {θ : Nat → ℚ}
    (h : SatN d D θ) : ¬ FlaggedN eps d D :=
  fun hf => flaggedN_empty heps hf ⟨θ, h⟩

/-- A cycle through two indices of weight below `-eps` raises the flag. -/
theorem flaggedN_of_cycle {eps : ℚ} {d : Nat} {D : NMat} {a k : Nat} (ha : a < d) (hk : k < d)
    (h : D a k + D k a < ((-eps : ℚ) : Bound)) : FlaggedN eps d D :=
  ⟨⟨a, ha⟩, by
    have := canonN_le_walk D ha hk ha
    rw [← toFin_canonN]
    exact lt_of_le_of_lt this h⟩

/-! ## The operations -/

/-- `Dbm::create` before `canonicalize`: `Dbm::new(n + 1)` (`∞` off the diagonal, `0` on it),
then `set(0, i+1, -lb[i])` and `set(i+1, 0, ub[i])` for `i < n`. -/
def createPre (n : Nat) (lb : List ℚ) (ub : List Bound) : NMat := fun a b =>
  if a = b then 0
  else if a = 0 ∧ 1 ≤ b ∧ b ≤ n then (((-(lb.getD (b - 1) 0)) : ℚ) : Bound)
  else if b = 0 ∧ 1 ≤ a ∧ a ≤ n then ub.getD (a - 1) ⊤
  else ⊤

/-- `let_time_pass` before `canonicalize`: `for i in 1..dim { set(0, i, 0) }`. -/
def ltpPre (d : Nat) (D : NMat) : NMat := fun a b =>
  if a = 0 ∧ 1 ≤ b ∧ b < d then 0 else D a b

/-- Step 1 of `fire_transition` on `n` clocks, fired clock `k`:
`constrained[f][i+1] := min(constrained[f][i+1], 0)` for every `i ≠ k`, `f = k + 1`. -/
def constrainPre (n k : Nat) (D : NMat) : NMat := fun a b =>
  if a = k + 1 ∧ 1 ≤ b ∧ b ≤ n ∧ b ≠ k + 1 then min (D a b) 0 else D a b

/-- Steps 3–5 of `fire_transition`: the new matrix before its final `canonicalize`, from the
canonical constrained matrix `C`, fired clock `k`, the persistent clocks `ps` (old positions,
0-based, in old order) and the newly enabled clocks' bounds `lb` / `ub`.

* persistent `p` (new index `p + 1`, old index `o = ps[p] + 1`): `(p+1, 0) = C[o][f]`,
  `(0, p+1) = -max(0, -C[f][o]) = min 0 C[f][o]` (`∞ ↦ 0` as in `f64`),
  `(p+1, q+1) = C[o][o']`, the diagonal included;
* newly enabled `j` (new index `P + j + 1`): `(0, ·) = -lb[j]`, `(·, 0) = ub[j]`;
* everything else `∞`, the diagonal of non-persistent rows `0`. -/
def fireMat (C : NMat) (k : Nat) (ps : List Nat) (lb : List ℚ) (ub : List Bound) : NMat :=
  fun a b =>
    if a = 0 then
      if b = 0 then 0
      else if b ≤ ps.length then min 0 (C (k + 1) (ps.getD (b - 1) 0 + 1))
      else if b ≤ ps.length + lb.length then (((-(lb.getD (b - ps.length - 1) 0)) : ℚ) : Bound)
      else ⊤
    else if a ≤ ps.length then
      if b = 0 then C (ps.getD (a - 1) 0 + 1) (k + 1)
      else if b ≤ ps.length then C (ps.getD (a - 1) 0 + 1) (ps.getD (b - 1) 0 + 1)
      else if a = b then 0 else ⊤
    else if a ≤ ps.length + lb.length then
      if b = 0 then ub.getD (a - ps.length - 1) ⊤
      else if a = b then 0 else ⊤
    else if a = b then 0 else ⊤

/-- The index map of `permuted`: new clock `i` is old clock `ord[i]`; the reference stays. -/
def pm (ord : List Nat) (a : Nat) : Nat :=
  if a = 0 then 0 else ord.getD (a - 1) (a - 1) + 1

/-- `Dbm::permuted`: `out[0] = 0`, `out[i+1][·] = data[ord[i]+1][·]`, reference row and column
moved with their clocks. -/
def permMat (ord : List Nat) (D : NMat) : NMat := fun a b =>
  if a = 0 ∧ b = 0 then 0 else D (pm ord a) (pm ord b)

/-! ## Which valuations each operation keeps -/

section Semantics

open WithTop

theorem coe_sub_le_iff {x y : ℚ} {c : ℚ} : ((x - y : ℚ) : Bound) ≤ (c : Bound) ↔ x - y ≤ c :=
  WithTop.coe_le_coe

/-- The initial box: every clock between its bounds. -/
theorem sat_createPre {n : Nat} {lb : List ℚ} {ub : List Bound} {θ : Nat → ℚ} (h0 : θ 0 = 0)
    (hlo : ∀ i, i < n → lb.getD i 0 ≤ θ (i + 1))
    (hhi : ∀ i, i < n → ((θ (i + 1) : ℚ) : Bound) ≤ ub.getD i ⊤) :
    SatN (n + 1) (createPre n lb ub) θ := by
  intro a b ha hb
  unfold createPre
  by_cases hab : a = b
  · subst hab; simp
  rw [if_neg hab]
  by_cases h1 : a = 0 ∧ 1 ≤ b ∧ b ≤ n
  · rw [if_pos h1]
    obtain ⟨rfl, hb1, hbn⟩ := h1
    have := hlo (b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega] at this
    rw [WithTop.coe_le_coe, h0]
    linarith
  rw [if_neg h1]
  by_cases h2 : b = 0 ∧ 1 ≤ a ∧ a ≤ n
  · rw [if_pos h2]
    obtain ⟨rfl, ha1, han⟩ := h2
    have := hhi (a - 1) (by omega)
    rw [show a - 1 + 1 = a by omega] at this
    rw [h0, sub_zero]
    exact this
  rw [if_neg h2]
  exact le_top

/-- `let_time_pass` keeps every valuation of `Y` whose clocks are not behind the reference. -/
theorem sat_ltpPre {d : Nat} {Y : NMat} {θ : Nat → ℚ} (h : SatN d Y θ)
    (hpos : ∀ j, 1 ≤ j → j < d → θ 0 ≤ θ j) : SatN d (ltpPre d Y) θ := by
  intro a b ha hb
  unfold ltpPre
  split_ifs with h1
  · obtain ⟨rfl, hb1, hbd⟩ := h1
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    linarith [hpos b hb1 hbd]
  · exact h a b ha hb

/-- A valuation of a let-time-pass zone with every clock at least the reference. -/
theorem ltpPre_pos {d : Nat} {Y : NMat} {θ : Nat → ℚ} (h : SatN d (ltpPre d Y) θ) :
    ∀ j, 1 ≤ j → j < d → θ 0 ≤ θ j := by
  intro j hj1 hjd
  have := h 0 j (by omega) hjd
  simp only [ltpPre, hj1, hjd, and_self, if_true] at this
  rw [← WithTop.coe_zero, WithTop.coe_le_coe] at this
  linarith

/-- The shift of every clock by `δ`, the reference kept: `δ` time units pass. -/
def shift (θ : Nat → ℚ) (δ : ℚ) : Nat → ℚ := fun a => if a = 0 then θ 0 else θ a - δ

/-- **A let-time-pass zone is closed under the passage of time** that keeps every clock at or
above the reference: this is why a class stays the class while time passes. -/
theorem sat_ltpPre_shift {d : Nat} {Y : NMat} {θ : Nat → ℚ} {δ : ℚ}
    (h : SatN d (ltpPre d Y) θ) (hδ : 0 ≤ δ) (hpos : ∀ j, 1 ≤ j → j < d → θ 0 ≤ θ j - δ) :
    SatN d (ltpPre d Y) (shift θ δ) := by
  intro a b ha hb
  have hab := h a b ha hb
  unfold shift
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; simpa using hab
    · simp only [if_true, hb0, if_false]
      simp only [ltpPre] at hab ⊢
      have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      simp only [hb1, hb, and_self, if_true]
      rw [← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith [hpos b hb1 hb]
  · by_cases hb0 : b = 0
    · subst hb0
      simp only [ha0, if_false, if_true]
      have : ((θ a - δ - θ 0 : ℚ) : Bound) ≤ ((θ a - θ 0 : ℚ) : Bound) :=
        WithTop.coe_le_coe.mpr (by linarith)
      exact this.trans hab
    · simp only [ha0, hb0, if_false]
      have : θ a - δ - (θ b - δ) = θ a - θ b := by ring
      rw [this]
      exact hab

/-- "The fired clock fires first": a valuation in which clock `k` is the smallest satisfies the
constrained matrix. -/
theorem sat_constrainPre {n k : Nat} {D : NMat} {θ : Nat → ℚ} (h : SatN (n + 1) D θ)
    (hmin : ∀ i, i < n → θ (k + 1) ≤ θ (i + 1)) : SatN (n + 1) (constrainPre n k D) θ := by
  intro a b ha hb
  unfold constrainPre
  split_ifs with h1
  · obtain ⟨rfl, hb1, hbn, -⟩ := h1
    refine le_min (h _ _ ha hb) ?_
    have := hmin (b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega] at this
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    linarith
  · exact h a b ha hb

/-- `constrainPre` only tightens. -/
theorem constrainPre_le {n k : Nat} (D : NMat) (a b : Nat) : constrainPre n k D a b ≤ D a b := by
  unfold constrainPre
  split_ifs
  · exact min_le_left _ _
  · exact le_refl _

/-- **The successor matrix keeps the shifted valuations.** `θ` is a valuation of the constrained
old zone in which the fired clock `k` is at zero (`θ (k+1) = 0`: the moment it fires); `θ'`
keeps every persistent clock's value (`θ' (p+1) = θ (ps[p] + 1)`, not behind the reference)
and puts every newly enabled clock inside its static interval. Then `θ'` satisfies the new
matrix. -/
theorem sat_fireMat {n k : Nat} {C : NMat} {ps : List Nat} {lb : List ℚ} {ub : List Bound}
    {θ θ' : Nat → ℚ} (hC : SatN (n + 1) C θ) (hk : k < n) (hps : ∀ x ∈ ps, x < n)
    (hk0 : θ (k + 1) = 0) (h0' : θ' 0 = 0)
    (hpers : ∀ p, p < ps.length → θ' (p + 1) = θ (ps.getD p 0 + 1))
    (hpos : ∀ p, p < ps.length → 0 ≤ θ' (p + 1))
    (hlo : ∀ j, j < lb.length → lb.getD j 0 ≤ θ' (ps.length + j + 1))
    (hhi : ∀ j, j < lb.length → ((θ' (ps.length + j + 1) : ℚ) : Bound) ≤ ub.getD j ⊤) :
    SatN (ps.length + lb.length + 1) (fireMat C k ps lb ub) θ' := by
  have hpsl : ∀ p, p < ps.length → ps.getD p 0 < n := fun p hp => by
    have : ps.getD p 0 ∈ ps := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
      exact List.getElem_mem hp
    exact hps _ this
  intro a b ha hb
  unfold fireMat
  by_cases ha0 : a = 0
  · subst ha0
    rw [if_pos rfl]
    by_cases hb0 : b = 0
    · subst hb0; simp
    rw [if_neg hb0]
    by_cases hbP : b ≤ ps.length
    · rw [if_pos hbP]
      have hp : b - 1 < ps.length := by omega
      have e := hpers (b - 1) hp
      have ps0 := hpos (b - 1) hp
      rw [show b - 1 + 1 = b by omega] at e ps0
      refine le_min ?_ ?_
      · rw [← WithTop.coe_zero, WithTop.coe_le_coe, h0']
        linarith
      · have hc := hC (k + 1) (ps.getD (b - 1) 0 + 1) (by omega) (by have := hpsl _ hp; omega)
        rw [hk0] at hc
        rw [h0', e]
        simpa using hc
    rw [if_neg hbP]
    by_cases hbM : b ≤ ps.length + lb.length
    · rw [if_pos hbM]
      have hj : b - ps.length - 1 < lb.length := by omega
      have := hlo _ hj
      rw [show ps.length + (b - ps.length - 1) + 1 = b by omega] at this
      rw [WithTop.coe_le_coe, h0']
      linarith
    · rw [if_neg hbM]; exact le_top
  rw [if_neg ha0]
  by_cases haP : a ≤ ps.length
  · rw [if_pos haP]
    have hp : a - 1 < ps.length := by omega
    have e := hpers (a - 1) hp
    rw [show a - 1 + 1 = a by omega] at e
    by_cases hb0 : b = 0
    · subst hb0
      rw [if_pos rfl]
      have hc := hC (ps.getD (a - 1) 0 + 1) (k + 1) (by have := hpsl _ hp; omega) (by omega)
      rw [hk0] at hc
      rw [h0', e]
      simpa using hc
    rw [if_neg hb0]
    by_cases hbP : b ≤ ps.length
    · rw [if_pos hbP]
      have hq : b - 1 < ps.length := by omega
      have e' := hpers (b - 1) hq
      rw [show b - 1 + 1 = b by omega] at e'
      rw [e, e']
      exact hC _ _ (by have := hpsl _ hp; omega) (by have := hpsl _ hq; omega)
    · rw [if_neg hbP]
      split_ifs with hab
      · subst hab; simp
      · exact le_top
  rw [if_neg haP]
  by_cases haM : a ≤ ps.length + lb.length
  · rw [if_pos haM]
    by_cases hb0 : b = 0
    · subst hb0
      rw [if_pos rfl]
      have hj : a - ps.length - 1 < lb.length := by omega
      have := hhi _ hj
      rw [show ps.length + (a - ps.length - 1) + 1 = a by omega] at this
      rw [h0', sub_zero]
      exact this
    · rw [if_neg hb0]
      split_ifs with hab
      · subst hab; simp
      · exact le_top
  · rw [if_neg haM]
    split_ifs with hab
    · subst hab; simp
    · exact le_top

/-- **Permuting the clocks keeps the valuations read through the permutation.** -/
theorem sat_permMat {d : Nat} {Y : NMat} {ord : List Nat} {θ θ' : Nat → ℚ} (hY : SatN d Y θ)
    (hord : ∀ a, a < d → pm ord a < d) (h' : ∀ a, a < d → θ' a = θ (pm ord a)) :
    SatN d (permMat ord Y) θ' := by
  intro a b ha hb
  unfold permMat
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [h' a ha, h' b hb]
    exact hY _ _ (hord a ha) (hord b hb)

end Semantics

end Libpetri.Novel.TimedScg
