import Libpetri.Novel.TimedScg.Grid
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD

/-!
# No timed deadlock the net does not have ([VER-023], [VER-010])

[VER-023] reads "this class has no successor" as "no transition can ever fire again" on the timed
graph, and requires that it hold: "a class with an enabled transition has a successor whatever
its interval". The doc comment of `timed_counterexample_check` (`smt_verifier.rs`) states the
same. This file proves it for the model.

* `succ_exists`: in a well-formed class whose zone has a solution, the clock whose solution value
  is smallest fires: for that position `k` and **every** row `d`, `succ C k d` is `some`. The
  argument is the textbook one: the minimum of a solution satisfies "fired fires first", and the
  successor matrix is then satisfied by the shifted persistent values and the newly enabled
  clocks' earliest times.
* `succ_wf` / `graph_classes_ok`: every class the graph builds is well-formed and `Stored`: its
  zone is a `let_time_pass` zone the Rust did not flag, with a finite reference entry.
* `nonempty_of_not_flagged`: at `eps = 0`, such a zone has a solution (`Dbm.empty_iff_flagged`,
  exactness of the diagonal check, with the reference row `0 … 0` as the finite row).
* `reachable_quiescent_iff_dead`: for every class reachable in the graph, with the exact check
  (`eps = 0`) and every transition of the net having at least one row, "no successor" is exactly
  "no transition enabled".
* `reachable_quiescent_iff_dead_grid`: the same at every `eps ∈ [0, g)` on a net whose bounds lie
  on the grid `g · ℤ` (`Grid.lean`). `faithful_quiescent_iff_dead` instantiates it with the
  Rust `EPSILON = 1e-9` and the millisecond grid of every net built from `Timing`s
  (`Timing.netGrid_of_timings`), under premise 6 (`TimingWF`: no `delayed` past
  `MAX_DURATION_MS`).

What this does **not** give `timed_counterexample_check`: only the `SPURIOUS_UNDER_TIMING` half
of that function and its quiescence reading are covered (`Run.timed_safety_of_closed`, and this
file for "no successor ⇔ nothing enabled"). The `TIMED_CONFIRMED` half needs every class, and
every path, of the graph to be realised by a timed run (completeness of the Berthomieu–Diaz
construction), which is not proven here. Premise 4 (exact rationals, no `f64` rounding) still
applies.
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

variable {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}

theorem satN_translate {d : Nat} {D : NMat} {θ : Nat → ℚ} (c : ℚ) (h : SatN d D θ) :
    SatN d D (fun a => θ a - c) := by
  intro i j hi hj
  have := h i j hi hj
  rwa [show θ i - c - (θ j - c) = θ i - θ j by ring]

/-- The tail of the successor keeps a class whenever the fired zone has a solution with every
clock at or above the reference. -/
theorem finish_some (hco : CoWF co) (heps : 0 ≤ eps) {a' : AMarking} {all : List Nat} {Y : NMat}
    {θ : Nat → ℚ} (hY : SatN (all.length + 1) Y θ) (h0 : θ 0 = 0)
    (hpos : ∀ j, 1 ≤ j → j < all.length + 1 → 0 ≤ θ j) :
    ∃ C', finish eps co a' all Y = some C' := by
  have hR : ∃ θ'', SatN (all.length + 1) (ltpPre (all.length + 1) (reorderMat co all Y)) θ'' := by
    unfold reorderMat
    cases h : co all with
    | none => exact ⟨θ, sat_ltpPre hY fun j hj1 hjd => by rw [h0]; exact hpos j hj1 hjd⟩
    | some ord =>
      obtain ⟨hlen, hlt, -⟩ := hco all ord h
      have hpm : ∀ a, a < all.length + 1 → pm ord a < all.length + 1 := by
        intro a ha
        unfold pm
        split_ifs with h0
        · omega
        · have : a - 1 < ord.length := by omega
          have := hlt _ (getD_mem (a - 1) this)
          omega
      refine ⟨fun a => θ (pm ord a), sat_ltpPre (sat_permMat hY hpm fun a _ => rfl) ?_⟩
      intro j hj1 hjd
      have hj0 : j ≠ 0 := by omega
      simp only [pm, if_true, h0, hj0, if_false]
      exact hpos _ (by omega) (by have := hpm j hjd; simp only [pm, hj0, if_false] at this; omega)
  obtain ⟨θ'', hθ''⟩ := hR
  exact ⟨_, by unfold finish; rw [if_neg (not_flagged_of_sat heps hθ'')]⟩

theorem getD_nonneg_eft (hT : TimingWF N) (l : List Nat) (j : Nat) :
    0 ≤ (l.map (eftOf N)).getD j 0 := by
  by_cases hj : j < l.length
  · rw [getD_map (eftOf N) 0 0 hj]
    exact (hT _).1
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]

/-- **A class with a solution and an enabled transition has a successor**, whatever the
intervals: the clock with the smallest solution value fires, with every row. -/
theorem succ_exists (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {C : Cls}
    (hC : ClsWF N C) {θ : Nat → ℚ} (hθ : SatN (C.cs.length + 1) C.D θ) (hcs : C.cs ≠ []) :
    ∃ k, k < C.cs.length ∧ ∀ d, ∃ C', succ N co eps C k d = some C' := by
  obtain ⟨mC, cs, D⟩ := C
  obtain ⟨Y, hD, -⟩ := hC.down
  simp only at hD hθ hcs ⊢
  set n := cs.length with hn
  have hn0 : 0 < n := List.length_pos_of_ne_nil hcs
  rw [hD, satN_canonN] at hθ
  -- normalise the reference to `0`
  have hθn := satN_translate (θ 0) hθ
  set θn : Nat → ℚ := fun a => θ a - θ 0 with hθndef
  have hθn0 : θn 0 = 0 := by simp [θn]
  have hθnpos : ∀ j, 1 ≤ j → j < n + 1 → 0 ≤ θn j := fun j h1 h2 => by
    have := ltpPre_pos hθn j h1 h2
    rwa [hθn0] at this
  -- the clock with the smallest value
  obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image (Finset.range n) (fun i => θn (i + 1))
    ⟨0, Finset.mem_range.mpr hn0⟩
  rw [Finset.mem_range] at hk
  set δ := θn (k + 1) with hδ
  have hδ0 : 0 ≤ δ := hθnpos (k + 1) (by omega) (by omega)
  have hθ1 := sat_ltpPre_shift hθn hδ0 fun j hj1 hjd => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := hkmin i (Finset.mem_range.mpr (by omega))
    rw [hθn0]
    linarith
  set θ1 := shift θn δ with hθ1def
  have hθ10 : θ1 0 = 0 := by simp [θ1, shift, hθn0]
  have hθ1k : θ1 (k + 1) = 0 := by simp [θ1, shift, hδ]
  have hθ1pos : ∀ i, i < n → 0 ≤ θ1 (i + 1) := fun i hi => by
    have := hkmin i (Finset.mem_range.mpr hi)
    simp only [θ1, shift, Nat.add_one_ne_zero, if_false]
    linarith
  have hθ1D : SatN (n + 1) (canonN (n + 1) (ltpPre (n + 1) Y)) θ1 := satN_canonN.mpr hθ1
  rw [← hD] at hθ1D
  have hK : SatN (n + 1) (constrainPre n k D) θ1 :=
    sat_constrainPre hθ1D fun i hi => by rw [hθ1k]; exact hθ1pos i hi
  refine ⟨k, hk, fun d => ?_⟩
  have hkf : ∃ f, cs[k]? = some f := ⟨cs[k], List.getElem?_eq_getElem hk⟩
  obtain ⟨f, hkf⟩ := hkf
  set C : Cls := ⟨mC, cs, D⟩ with hCdef
  set a' := fireAD mC (trOf N f) d with ha'
  set mid := inter mC (trOf N f) with hmid
  set ps := persPos (survives N) C f a' mid with hps
  set pers := ps.map (fun i => cs.getD i 0) with hpers
  set newly := (enabledIds N a').filter (fun j => !pers.contains j) with hnewly
  set lb := newly.map (eftOf N) with hlb
  set ub := newly.map (lftOf N) with hub
  set all := pers ++ newly with hall
  have hallL : all.length = ps.length + lb.length := by
    simp only [hall, List.length_append, hpers, hlb, List.length_map]
  set θ' : Nat → ℚ := fun a =>
    if a = 0 then 0 else if a ≤ ps.length then θ1 (ps.getD (a - 1) 0 + 1)
    else lb.getD (a - ps.length - 1) 0 with hθ'def
  have hθ'0 : θ' 0 = 0 := by simp [θ']
  have hpsl : ∀ p, p < ps.length → ps.getD p 0 < n := fun p hp =>
    persPos_lt _ (getD_mem 0 hp)
  have hX : SatN (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub) θ' := by
    refine sat_fireMat (satN_canonN.mpr hK) hk (fun x hx => persPos_lt x hx) hθ1k hθ'0
      (fun p hp => ?_) (fun p hp => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · simp [θ', show p + 1 ≤ ps.length by omega]
    · simp only [θ', Nat.add_one_ne_zero, if_false, show p + 1 ≤ ps.length by omega, if_true,
        Nat.add_sub_cancel]
      exact hθ1pos _ (hpsl p hp)
    · simp only [θ', show ps.length + j + 1 ≠ 0 by omega, if_false,
        show ¬ (ps.length + j + 1 ≤ ps.length) by omega,
        show ps.length + j + 1 - ps.length - 1 = j by omega, le_refl]
    · simp only [θ', show ps.length + j + 1 ≠ 0 by omega, if_false,
        show ¬ (ps.length + j + 1 ≤ ps.length) by omega,
        show ps.length + j + 1 - ps.length - 1 = j by omega]
      have hjn : j < newly.length := by simpa [hlb] using hj
      rw [hlb, hub, getD_map (eftOf N) 0 0 hjn, getD_map (lftOf N) 0 ⊤ hjn]
      exact (hT _).2
  have hnfK : ¬ FlaggedN eps (n + 1) (constrainPre n k D) := not_flagged_of_sat heps hK
  have hnfX := not_flagged_of_sat (eps := eps) heps hX
  have hzone : zoneStep eps n k D ps lb ub = some (canonN (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub)) := by
    unfold zoneStep
    rw [if_neg hnfK, if_neg hnfX]
  have hYsat : SatN (all.length + 1) (canonN (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub)) θ' := by
    rw [hallL, satN_canonN]
    exact hX
  have hθ'pos : ∀ j, 1 ≤ j → j < all.length + 1 → 0 ≤ θ' j := by
    intro j hj1 hjd
    simp only [θ', show j ≠ 0 by omega, if_false]
    split_ifs with hjP
    · exact hθ1pos _ (hpsl _ (by omega))
    · exact getD_nonneg_eft hT newly _
  obtain ⟨C', hfin⟩ := finish_some (a' := a') hco heps hYsat hθ'0 hθ'pos
  refine ⟨C', ?_⟩
  show succWith (survives N) N co eps C k d = some C'
  unfold succWith
  simp only [hCdef, hkf]
  rw [← ha', ← hmid, ← hCdef, ← hps, ← hpers, ← hnewly, ← hlb, ← hub, hzone, Option.bind_some,
    ← hall]
  exact hfin

/-! ## Every stored class has a solution (at `eps = 0`) -/

/-- The zone of a class the Rust stores: a `let_time_pass` zone it did not flag, with a finite
reference entry. -/
def Stored (eps : ℚ) (C : Cls) : Prop :=
  ∃ Y : NMat, C.D = canonN (C.cs.length + 1) (ltpPre (C.cs.length + 1) Y) ∧
    ¬ FlaggedN eps (C.cs.length + 1) (ltpPre (C.cs.length + 1) Y) ∧ Y 0 0 ≠ ⊤

/-- **An unflagged let-time-pass zone has a solution** when the check is exact (`eps = 0`). -/
theorem nonempty_of_not_flagged {d : Nat} (hd : 0 < d) {Y : NMat} (hY00 : Y 0 0 ≠ ⊤)
    (h : ¬ FlaggedN 0 d (ltpPre d Y)) : ∃ θ, SatN d (canonN d (ltpPre d Y)) θ := by
  have hrow : ∀ i, toFin d (ltpPre d Y) ⟨0, hd⟩ i ≠ ⊤ := by
    intro i
    simp only [toFin, ltpPre]
    split_ifs with h1
    · exact WithTop.zero_ne_top
    · have : (i : Nat) = 0 := by
        by_contra hi0
        exact h1 ⟨trivial, by omega, i.isLt⟩
      rw [this]
      exact hY00
  by_contra hne
  apply h
  refine (Dbm.empty_iff_flagged hrow).mp ?_
  rintro ⟨θ, hθ⟩
  refine hne ⟨fun a => if ha : a < d then θ ⟨a, ha⟩ else 0, satN_canonN.mpr (satN_iff.mpr ?_)⟩
  have e : (fun i : Fin d => (fun a => if ha : a < d then θ ⟨a, ha⟩ else 0) (i : Nat)) = θ := by
    funext i
    simp [i.isLt]
  rw [e]
  exact hθ

/-- Every successor is a well-formed, stored class. -/
theorem succ_wf (hco : CoWF co) {C C' : Cls} {k : Nat} {d : Deposit}
    (h : succ N co eps C k d = some C') : ClsWF N C' ∧ Stored eps C' := by
  unfold succ succWith at h
  cases hk : C.cs[k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some f =>
    rw [hk] at h
    simp only at h
    obtain ⟨Y, hz, hfin⟩ := Option.bind_eq_some_iff.mp h
    set a' := fireAD C.m (trOf N f) d
    set ps := persPos (survives N) C f a' (inter C.m (trOf N f))
    set pers := ps.map (fun i => C.cs.getD i 0) with hpers
    set newly := (enabledIds N a').filter (fun j => !pers.contains j) with hnewly
    have hY00 : Y 0 0 ≠ ⊤ := by
      unfold zoneStep at hz
      split_ifs at hz
      cases hz
      refine ne_top_of_le_ne_top (b := (fireMat _ k ps _ _) 0 0) ?_ (canonN_le _ (by omega) (by omega))
      simp [fireMat]
    unfold finish at hfin
    split_ifs at hfin with hnf
    cases hfin
    refine ⟨⟨fun c => ?_, ⟨_, by rw [reorder_length hco], ?_⟩⟩, ⟨_, by rw [reorder_length hco], by
      rw [reorder_length hco]; exact hnf, ?_⟩⟩
    · show c ∈ reorder co (pers ++ newly) ↔ _
      rw [mem_reorder hco, List.mem_append, hnewly, List.mem_filter, mem_enabledIds,
        Bool.not_eq_true', contains_false_iff]
      constructor
      · rintro (hc | ⟨hc, -⟩)
        · have := (mem_pers_iff.mp hc).2
          simp only [survives, Bool.and_eq_true] at this
          exact this.1.2
        · exact hc
      · intro hc
        by_cases hp : c ∈ pers
        · exact Or.inl hp
        · exact Or.inr ⟨hc, hp⟩
    all_goals
      unfold reorderMat
      cases co (pers ++ newly) with
      | none => exact hY00
      | some ord => simp [permMat]

/-- The initial class is well-formed and stored. -/
theorem init_wf (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co eps m0 = some C0) : ClsWF N C0 ∧ Stored eps C0 := by
  obtain ⟨C, hC, -, hwf⟩ := init_sound hT hco heps m0
  rw [h0] at hC
  cases hC
  refine ⟨hwf, ?_⟩
  have h0' := h0
  unfold initCls at h0'
  simp only at h0'
  split_ifs at h0' with h1 h2
  cases h0'
  refine ⟨_, rfl, h2, ?_⟩
  refine ne_top_of_le_ne_top (b := (createPre _ _ _) 0 0) ?_ (canonN_le _ (by omega) (by omega))
  simp [createPre]

/-- **Every class the graph reaches is well-formed and stored.** -/
theorem graph_classes_ok (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge N co eps) C0 C) : ClsWF N C ∧ Stored eps C := by
  induction h with
  | refl => exact init_wf hT hco heps h0
  | tail _ hstep _ =>
    simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_filterMap] at hstep
    obtain ⟨k, -, d, -, hs⟩ := hstep
    exact succ_wf hco hs

/-- **"No successor" is "nothing enabled"** for every class of the graph ([VER-023]), with the
exact emptiness check and every transition of the net having at least one row (`outcomes` of a
transition with no output spec is one empty row, premise 3). -/
theorem reachable_quiescent_iff_dead (hT : TimingWF N) (hco : CoWF co)
    (hrows : ∀ i, i < N.length → rowsOf N i ≠ []) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co 0 m0 = some C0)
    {C : Cls} (h : Relation.ReflTransGen (Edge N co 0) C0 C) :
    succList N co 0 C = [] ↔ ∀ i, en N C.m i = false := by
  obtain ⟨hwf, Y, hD, hnf, hY00⟩ := graph_classes_ok hT hco le_rfl h0 h
  constructor
  · intro hnil
    by_contra hsome
    obtain ⟨i, hi⟩ := not_forall.mp hsome
    have hi' : en N C.m i = true := by simpa using hi
    have hcs : C.cs ≠ [] := fun hc => by
      have := (hwf.mem i).mpr hi'
      rw [hc] at this
      exact List.not_mem_nil this
    obtain ⟨θ, hθ⟩ := nonempty_of_not_flagged (by omega) hY00 hnf
    rw [← hD] at hθ
    obtain ⟨k, hk, hall⟩ := succ_exists hT hco le_rfl hwf hθ hcs
    have hkc : en N C.m (C.cs.getD k 0) = true := (hwf.mem _).mp (getD_mem 0 hk)
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (hrows _ (en_lt hkc))
    obtain ⟨C', hC'⟩ := hall d
    have := succ_mem_succList hk hd hC'
    rw [hnil] at this
    exact List.not_mem_nil this
  · intro hdead
    have hcs : C.cs = [] := List.eq_nil_iff_forall_not_mem.mpr fun c hc => by
      have := (hwf.mem c).mp hc
      rw [hdead c] at this
      exact absurd this (by simp)
    simp [succList, succListWith, hcs]

/-- **"No successor" is "nothing enabled" at the Rust tolerance** on a grid net: for every
`eps ∈ [0, g)` and every class the graph reaches. -/
theorem reachable_quiescent_iff_dead_grid (hT : TimingWF N) (hco : CoWF co) {g : ℚ} (hg : 0 < g)
    (hN : NetGrid g N) (heps0 : 0 ≤ eps) (hepsg : eps < g)
    (hrows : ∀ i, i < N.length → rowsOf N i ≠ []) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co eps m0 = some C0)
    {C : Cls} (h : Relation.ReflTransGen (Edge N co eps) C0 C) :
    succList N co eps C = [] ↔ ∀ i, en N C.m i = false := by
  obtain ⟨hwf, Y, hD, hnf, hY00⟩ := graph_classes_ok hT hco heps0 h0 h
  have hgrid := graph_grid hN h0 h
  have hnf0 : ¬ FlaggedN 0 (C.cs.length + 1) (ltpPre (C.cs.length + 1) Y) := fun hf =>
    hnf (flagged_of_flagged_zero hg hepsg (by rw [← hD]; exact hgrid) hf)
  constructor
  · intro hnil
    by_contra hsome
    obtain ⟨i, hi⟩ := not_forall.mp hsome
    have hi' : en N C.m i = true := by simpa using hi
    have hcs : C.cs ≠ [] := fun hc => by
      have := (hwf.mem i).mpr hi'
      rw [hc] at this
      exact List.not_mem_nil this
    obtain ⟨θ, hθ⟩ := nonempty_of_not_flagged (by omega) hY00 hnf0
    rw [← hD] at hθ
    obtain ⟨k, hk, hall⟩ := succ_exists hT hco heps0 hwf hθ hcs
    have hkc : en N C.m (C.cs.getD k 0) = true := (hwf.mem _).mp (getD_mem 0 hk)
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (hrows _ (en_lt hkc))
    obtain ⟨C', hC'⟩ := hall d
    have := succ_mem_succList hk hd hC'
    rw [hnil] at this
    exact List.not_mem_nil this
  · intro hdead
    have hcs : C.cs = [] := List.eq_nil_iff_forall_not_mem.mpr fun c hc => by
      have := (hwf.mem c).mp hc
      rw [hdead c] at this
      exact absurd this (by simp)
    simp [succList, succListWith, hcs]

/-- **The faithful instantiation**: a net built from valid `Timing`s (`hmax` is implied by
`hv` since the R6 fix, `Timing.timingWF_of_valid`; it is kept so the statement also reads for
the old constructors), the Rust `EPSILON = 1e-9`. For every class the graph reaches, "no successor"
is "nothing enabled". -/
theorem faithful_quiescent_iff_dead {tms : Nat → Timing} (hN : FromTimings N tms)
    (hv : ∀ i, i < N.length → (tms i).Valid)
    (hmax : ∀ i, i < N.length → ∀ a, tms i = .delayed a → a ≤ maxDurationMs) (hco : CoWF co)
    (hrows : ∀ i, i < N.length → rowsOf N i ≠ []) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co (1 / 10 ^ 9) m0 = some C0)
    {C : Cls} (h : Relation.ReflTransGen (Edge N co (1 / 10 ^ 9)) C0 C) :
    succList N co (1 / 10 ^ 9) C = [] ↔ ∀ i, en N C.m i = false :=
  reachable_quiescent_iff_dead_grid (timingWF_of_timings hN (fun i hi => (hv i hi).pre) hmax) hco
    (by norm_num)
    (netGrid_of_timings hN) (by norm_num) (by norm_num) hrows h0 h

end Libpetri.Novel.TimedScg
