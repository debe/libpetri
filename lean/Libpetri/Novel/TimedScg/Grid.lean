import Libpetri.Novel.TimedScg.Run
import Libpetri.Novel.TimedScg.Timing

/-!
# Every zone of the graph stays on the millisecond grid (premise 4, `EPSILON = 1e-9`)

The Rust emptiness flag is `D[i][i] < -EPSILON` with `EPSILON = 1e-9` (`dbm.rs:1`, `:128`), so a
zone whose most negative cycle lies in `[-1e-9, 0)` would be stored although empty. This file
shows that cannot happen on a net whose static bounds are multiples of a grid step `g > eps`:

* every operation of the successor (`createPre`, `ltpPre`, `constrainPre`, `canonN`, `fireMat`,
  `permMat`) keeps a matrix on the grid `g · ℤ ∪ {⊤}` (`gridM_*`);
* so every class the graph reaches has its zone on the grid (`graph_grid`);
* and on such a zone the flag at any `eps ∈ [0, g)` is the exact flag (`flagged_of_flagged_zero`).

`Timing.netGrid_of_timings` puts every faithful net on the millisecond grid `g = 1/1000`, and
`1e-9 < 1/1000`. `Progress.reachable_quiescent_iff_dead_grid` uses this. Floating-point rounding
itself stays out of scope (premise 4).
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

variable {g : ℚ}

/-- A positional matrix whose every entry is on the grid. -/
def GridM (g : ℚ) (D : NMat) : Prop := ∀ a b, GridB g (D a b)

theorem gridB_top : GridB g ⊤ := Or.inl rfl

theorem gridB_coe {x : ℚ} (h : GridQ g x) : GridB g (x : Bound) := by
  obtain ⟨z, rfl⟩ := h
  exact Or.inr ⟨z, rfl⟩

theorem gridQ_zero : GridQ g 0 := ⟨0, by simp⟩

theorem gridB_zero : GridB g 0 := gridB_coe gridQ_zero

theorem gridQ_neg {x : ℚ} (h : GridQ g x) : GridQ g (-x) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨-z, by push_cast; ring⟩

theorem gridB_add {x y : Bound} (hx : GridB g x) (hy : GridB g y) : GridB g (x + y) := by
  rcases hx with rfl | ⟨a, rfl⟩
  · exact Or.inl (by simp)
  rcases hy with rfl | ⟨b, rfl⟩
  · exact Or.inl (by simp)
  exact Or.inr ⟨a + b, by rw [← WithTop.coe_add]; congr 1; push_cast; ring⟩

theorem gridB_min {x y : Bound} (hx : GridB g x) (hy : GridB g y) : GridB g (min x y) := by
  rcases min_choice x y with h | h <;> rw [h]
  · exact hx
  · exact hy

theorem gridQ_getD {l : List ℚ} (h : ∀ x ∈ l, GridQ g x) (i : Nat) : GridQ g (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact gridQ_zero
  | some x => exact h x (List.mem_of_getElem? hx)

theorem gridB_getD {l : List Bound} (h : ∀ x ∈ l, GridB g x) (i : Nat) : GridB g (l.getD i ⊤) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact gridB_top
  | some x => exact h x (List.mem_of_getElem? hx)

/-! ## The operations keep the grid -/

theorem gridM_relaxN {D : NMat} (h : GridM g D) (k i j : Nat) : GridM g (relaxN D k i j) := by
  intro a b
  unfold relaxN
  split_ifs
  · exact gridB_min (h _ _) (gridB_add (h _ _) (h _ _))
  · exact h _ _

theorem gridM_foldl :
    ∀ (l : List (Nat × Nat × Nat)) (D : NMat), GridM g D →
      GridM g (l.foldl (fun D s => relaxN D s.1 s.2.1 s.2.2) D)
  | [], _, h => h
  | _ :: l, _, h => gridM_foldl l _ (gridM_relaxN h _ _ _)

theorem gridM_canonN {d : Nat} {D : NMat} (h : GridM g D) : GridM g (canonN d D) := by
  unfold canonN
  have := gridM_foldl ((Dbm.fwSteps d).map fun s => ((s.1 : Nat), (s.2.1 : Nat), (s.2.2 : Nat)))
    D h
  rw [List.foldl_map] at this
  exact this

theorem gridM_ltpPre {d : Nat} {D : NMat} (h : GridM g D) : GridM g (ltpPre d D) := by
  intro a b
  unfold ltpPre
  split_ifs
  · exact gridB_zero
  · exact h _ _

theorem gridM_constrainPre {n k : Nat} {D : NMat} (h : GridM g D) : GridM g (constrainPre n k D) := by
  intro a b
  unfold constrainPre
  split_ifs
  · exact gridB_min (h _ _) gridB_zero
  · exact h _ _

theorem gridM_createPre {n : Nat} {lb : List ℚ} {ub : List Bound} (hlb : ∀ x ∈ lb, GridQ g x)
    (hub : ∀ x ∈ ub, GridB g x) : GridM g (createPre n lb ub) := by
  intro a b
  unfold createPre
  split_ifs
  · exact gridB_zero
  · exact gridB_coe (gridQ_neg (gridQ_getD hlb _))
  · exact gridB_getD hub _
  · exact gridB_top

theorem gridM_fireMat {C : NMat} {k : Nat} {ps : List Nat} {lb : List ℚ} {ub : List Bound}
    (hC : GridM g C) (hlb : ∀ x ∈ lb, GridQ g x) (hub : ∀ x ∈ ub, GridB g x) :
    GridM g (fireMat C k ps lb ub) := by
  intro a b
  unfold fireMat
  split_ifs
  all_goals first
    | exact gridB_zero
    | exact gridB_top
    | exact gridB_min gridB_zero (hC _ _)
    | exact gridB_coe (gridQ_neg (gridQ_getD hlb _))
    | exact gridB_getD hub _
    | exact hC _ _

theorem gridM_permMat {ord : List Nat} {D : NMat} (h : GridM g D) : GridM g (permMat ord D) := by
  intro a b
  unfold permMat
  split_ifs
  · exact gridB_zero
  · exact h _ _

theorem gridM_reorderMat {co : List Nat → Option (List Nat)} {all : List Nat} {D : NMat}
    (h : GridM g D) : GridM g (reorderMat co all D) := by
  unfold reorderMat
  cases co all with
  | none => exact h
  | some ord => exact gridM_permMat h

/-! ## Classes of the graph -/

variable {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}

theorem lb_grid (hN : NetGrid g N) (l : List Nat) : ∀ x ∈ l.map (eftOf N), GridQ g x := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact (hN i).1

theorem ub_grid (hN : NetGrid g N) (l : List Nat) : ∀ x ∈ l.map (lftOf N), GridB g x := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact (hN i).2

theorem init_grid (hN : NetGrid g N) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co eps m0 = some C0) : GridM g C0.D := by
  obtain ⟨-, -, hD⟩ := initCls_eq h0
  rw [hD]
  exact gridM_canonN (gridM_ltpPre (gridM_canonN (gridM_createPre (lb_grid hN _) (ub_grid hN _))))

theorem succ_grid (hN : NetGrid g N) {C C' : Cls} {k : Nat} {d : Deposit} (hC : GridM g C.D)
    (h : succ N co eps C k d = some C') : GridM g C'.D := by
  unfold succ succWith at h
  cases hk : C.cs[k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some f =>
    rw [hk] at h
    simp only at h
    obtain ⟨Y, hz, hfin⟩ := Option.bind_eq_some_iff.mp h
    have hY : GridM g Y := by
      unfold zoneStep at hz
      split_ifs at hz
      cases hz
      exact gridM_canonN (gridM_fireMat (gridM_canonN (gridM_constrainPre hC))
        (lb_grid hN _) (ub_grid hN _))
    unfold finish at hfin
    split_ifs at hfin
    cases hfin
    exact gridM_canonN (gridM_ltpPre (gridM_reorderMat hY))

/-- **Every class the graph reaches has its zone on the grid.** -/
theorem graph_grid (hN : NetGrid g N) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co eps m0 = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge N co eps) C0 C) : GridM g C.D := by
  induction h with
  | refl => exact init_grid hN h0
  | tail _ hstep ih =>
    simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_filterMap] at hstep
    obtain ⟨k, -, d, -, hs⟩ := hstep
    exact succ_grid hN ih hs

/-! ## On the grid, the `EPSILON` flag is the exact flag -/

theorem flaggedN_iff {d : Nat} {D : NMat} :
    FlaggedN eps d D ↔ ∃ i, i < d ∧ canonN d D i i < ((-eps : ℚ) : Bound) := by
  unfold FlaggedN Dbm.Flagged
  rw [← toFin_canonN]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩

/-- **A grid zone flagged by the exact check is flagged at every `eps < g`.** -/
theorem flagged_of_flagged_zero (hg : 0 < g) (hepsg : eps < g) {d : Nat} {D : NMat}
    (hD : GridM g (canonN d D)) (h : FlaggedN 0 d D) : FlaggedN eps d D := by
  obtain ⟨i, hi, hlt⟩ := flaggedN_iff.mp h
  refine flaggedN_iff.mpr ⟨i, hi, ?_⟩
  rcases hD i i with htop | ⟨z, hz⟩
  · rw [htop] at hlt
    exact absurd hlt (not_lt.mpr le_top)
  · rw [hz, WithTop.coe_lt_coe] at hlt ⊢
    have hz0 : z < 0 := by
      by_contra hc
      have : (0 : ℚ) ≤ z * g := mul_nonneg (by exact_mod_cast not_lt.mp hc) hg.le
      linarith
    have hz1 : (z : ℚ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    nlinarith

end Libpetri.Novel.TimedScg
