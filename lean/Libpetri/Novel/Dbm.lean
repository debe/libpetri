import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# DBM zones: canonicalisation preserves the zone, emptiness detection is exact ([VER-011])

Model of `Dbm` (`rust/libpetri-verification/src/dbm.rs`), the difference bound matrix of the
state-class graph. Entry `D i j` bounds `θᵢ - θⱼ` (the struct's doc comment, and `get`,
`dbm.rs:74-77`);
`f64::INFINITY` is `⊤` of `WithTop ℚ`. The zone of `D` is its solution set `Sat D`.

* `canonicalize` (`dbm.rs:107-133`, `canonicalize_in_place`, `dbm.rs:318-339`) is in-place
  Floyd–Warshall. Each inner step replaces `D i j` by `D i k + D k j` when that is smaller and
  both are finite. That is `relax`: `min (D i j) (D i k + D k j)`, where `⊤ + x = ⊤` covers the
  finiteness guard. `canon` runs the relaxations in the Rust loop order (`fwSteps`: `k`, then
  `i`, then `j`), each one reading the matrix as the previous one left it, so the in-place
  semantics is exact.
* The zone is flagged empty when some diagonal entry is below `-EPSILON` (`dbm.rs:126-132`),
  which is `Flagged eps`. The `EPSILON = 1e-9` of the Rust code is any `eps ≥ 0` here.
* `permuted` (`dbm.rs:251-275`) reorders the clocks, which is `permD` with the reference clock
  left in place; the Rust comment says a permuted canonical matrix is canonical.

Results:
* `sat_canon` (AC3/AC2 groundwork): canonicalisation changes the matrix but not the zone. Every
  single relaxation, and so any sequence of them, has exactly the same solutions.
* `flagged_empty` (AC2, soundness): a zone the Rust check flags as empty really has no
  solution. A false "empty" would drop a reachable state class, so this is the direction that
  guards against a false `Proven`.
* `nonempty_iff_diag_of_closed` (AC2, exactness on canonical matrices): for a closed matrix
  (`D i j ≤ D i k + D k j`) with a finite reference row, the zone is nonempty iff every
  diagonal entry is `≥ 0`, so on a closed DBM the diagonal check decides emptiness exactly.
  The witness is `θᵢ = -D r i`.
* `closed_canon`: the in-place Floyd–Warshall pass, run in the Rust loop order, returns a
  closed matrix whenever the input has no negative cycle.
* `flagged_of_neg`: a negative cycle always pushes a diagonal entry of `canon` below zero.
* `empty_iff_flagged` (AC2, exactness): with a finite reference row, the zone is empty **iff**
  the Rust check (at `eps = 0`) flags it.
* `sat_permD` / `closed_permD` (AC4): permuting the clocks maps the zone bijectively
  (`θ ↦ θ ∘ σ⁻¹`) and keeps a closed matrix closed, so the reordered key denotes the same zone.

Out of scope: floating-point rounding (bounds are exact rationals). Exactness is at
`eps = 0`: with `EPSILON = 1e-9` a zone whose most negative cycle lies in `[-1e-9, 0)` is
empty but not flagged. That is an over-approximation, never a lost class. Also out of scope:
`let_time_pass` and `fire_transition` (AC3's successor formula), and the string rendering of
`zone_key`.
-/

namespace Libpetri.Novel.Dbm

/-- A bound: a rational, or `⊤` for `f64::INFINITY`. -/
abbrev Bound := WithTop ℚ

/-- A `d × d` difference bound matrix: `D i j` bounds `θᵢ - θⱼ`. -/
abbrev Matrix (d : Nat) := Fin d → Fin d → Bound

variable {d : Nat}

/-- The zone of `D`: clock valuations satisfying every difference bound. -/
def Sat (D : Matrix d) (θ : Fin d → ℚ) : Prop :=
  ∀ i j, ((θ i - θ j : ℚ) : Bound) ≤ D i j

/-! ## Canonicalisation preserves the zone -/

/-- One in-place Floyd–Warshall step at `(k, i, j)`: `D i j := min (D i j) (D i k + D k j)`. -/
def relax (D : Matrix d) (k i j : Fin d) : Matrix d :=
  fun a b => if a = i ∧ b = j then min (D i j) (D i k + D k j) else D a b

theorem relax_le (D : Matrix d) (k i j a b : Fin d) : relax D k i j a b ≤ D a b := by
  unfold relax
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact min_le_left _ _
  · exact le_refl _

theorem sat_relax (D : Matrix d) (k i j : Fin d) (θ : Fin d → ℚ) :
    Sat (relax D k i j) θ ↔ Sat D θ := by
  constructor
  · intro h a b
    exact (h a b).trans (relax_le D k i j a b)
  · intro h a b
    unfold relax
    split_ifs with hab
    · obtain ⟨rfl, rfl⟩ := hab
      refine le_min (h a b) ?_
      have e : ((θ a - θ b : ℚ) : Bound) = ((θ a - θ k : ℚ) : Bound) + ((θ k - θ b : ℚ) : Bound) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
      rw [e]
      exact add_le_add (h a k) (h k b)
    · exact h a b

/-- Round `k` of the Rust loop: `for i { for j { relax(k, i, j) } }`. -/
def roundSteps (k : Fin d) : List (Fin d × Fin d × Fin d) :=
  (List.finRange d).flatMap fun i => (List.finRange d).map fun j => (k, i, j)

/-- Rounds `0, …, m - 1`. -/
def stepsUpTo (d m : Nat) : List (Fin d × Fin d × Fin d) :=
  (List.range m).flatMap fun k => if h : k < d then roundSteps ⟨k, h⟩ else []

/-- The relaxation steps in the Rust loop order: `for k { for i { for j { … } } }`. -/
def fwSteps (d : Nat) : List (Fin d × Fin d × Fin d) := stepsUpTo d d

/-- Run a list of relaxation steps in order, each on the matrix the previous one left. -/
def runSteps (D : Matrix d) (l : List (Fin d × Fin d × Fin d)) : Matrix d :=
  l.foldl (fun D s => relax D s.1 s.2.1 s.2.2) D

/-- `canonicalize`'s Floyd–Warshall pass. -/
def canon (D : Matrix d) : Matrix d := runSteps D (fwSteps d)

theorem sat_runSteps (θ : Fin d → ℚ) :
    ∀ (l : List (Fin d × Fin d × Fin d)) (D : Matrix d), Sat (runSteps D l) θ ↔ Sat D θ
  | [], _ => Iff.rfl
  | s :: l, D => by
    show Sat (runSteps (relax D s.1 s.2.1 s.2.2) l) θ ↔ Sat D θ
    rw [sat_runSteps θ l, sat_relax]

/-- **Canonicalisation preserves the zone**, for any relaxation order and so for the Rust one. -/
theorem sat_canon (D : Matrix d) (θ : Fin d → ℚ) : Sat (canon D) θ ↔ Sat D θ :=
  sat_runSteps θ _ D

/-- Canonicalisation only tightens bounds. -/
theorem runSteps_le :
    ∀ (l : List (Fin d × Fin d × Fin d)) (D : Matrix d) (a b : Fin d), runSteps D l a b ≤ D a b
  | [], _, _, _ => le_refl _
  | s :: l, D, a, b =>
    (runSteps_le l (relax D s.1 s.2.1 s.2.2) a b).trans (relax_le D s.1 s.2.1 s.2.2 a b)

theorem canon_le (D : Matrix d) (a b : Fin d) : canon D a b ≤ D a b :=
  runSteps_le _ D a b

/-! ## Emptiness detection -/

/-- The Rust emptiness flag after canonicalisation: some diagonal entry below `-eps`. -/
def Flagged (eps : ℚ) (D : Matrix d) : Prop :=
  ∃ i, canon D i i < ((-eps : ℚ) : Bound)

/-- A satisfiable matrix has a non-negative diagonal. -/
theorem diag_nonneg_of_sat {D : Matrix d} {θ : Fin d → ℚ} (h : Sat D θ) (i : Fin d) :
    ((0 : ℚ) : Bound) ≤ D i i := by
  have := h i i
  rwa [sub_self] at this

/-- **The empty flag is sound** ([VER-011] AC2): a zone the Rust check flags as empty has no
solution. -/
theorem flagged_empty {eps : ℚ} (heps : 0 ≤ eps) {D : Matrix d} (hf : Flagged eps D) :
    ¬ ∃ θ, Sat D θ := by
  rintro ⟨θ, hθ⟩
  obtain ⟨i, hi⟩ := hf
  have h0 := diag_nonneg_of_sat ((sat_canon D θ).mpr hθ) i
  have hlt : ((0 : ℚ) : Bound) < ((-eps : ℚ) : Bound) := lt_of_le_of_lt h0 hi
  rw [WithTop.coe_lt_coe] at hlt
  linarith

/-- Closed (canonical) form: every bound is at most every two-step detour. -/
def Closed (D : Matrix d) : Prop :=
  ∀ i j k, D i j ≤ D i k + D k j

/-- A closed matrix with a finite reference row `r` has a solution: `θᵢ = -D r i`. -/
theorem nonempty_of_closed {D : Matrix d} (hc : Closed D) {r : Fin d}
    (hrow : ∀ i, D r i ≠ ⊤) : ∃ θ, Sat D θ := by
  refine ⟨fun i => -(D r i).untop (hrow i), fun i j => ?_⟩
  have hri : D r i = (((D r i).untop (hrow i) : ℚ) : Bound) := (WithTop.coe_untop _ _).symm
  have hrj : D r j = (((D r j).untop (hrow j) : ℚ) : Bound) := (WithTop.coe_untop _ _).symm
  have hcl := hc r j i
  rw [hri, hrj] at hcl
  cases hij : D i j using WithTop.recTopCoe with
  | top => exact le_top
  | coe c =>
    rw [hij, ← WithTop.coe_add, WithTop.coe_le_coe] at hcl
    rw [WithTop.coe_le_coe]
    linarith

/-- **On a closed matrix the diagonal check is exact** ([VER-011] AC2): with a finite reference
row, the zone is nonempty iff every diagonal entry is `≥ 0`, i.e. iff the Rust flag (at
`eps = 0`) is not raised. -/
theorem nonempty_iff_diag_of_closed {D : Matrix d} (hc : Closed D) {r : Fin d}
    (hrow : ∀ i, D r i ≠ ⊤) : (∃ θ, Sat D θ) ↔ ∀ i, ((0 : ℚ) : Bound) ≤ D i i :=
  ⟨fun ⟨_, hθ⟩ => diag_nonneg_of_sat hθ, fun _ => nonempty_of_closed hc hrow⟩

/-- The same for the Rust pipeline: if the Floyd–Warshall output is closed with a finite
reference row, then the original zone is empty **iff** the flag is raised at `eps = 0`. -/
theorem canon_empty_iff_flagged {D : Matrix d} (hc : Closed (canon D)) {r : Fin d}
    (hrow : ∀ i, canon D r i ≠ ⊤) : (¬ ∃ θ, Sat D θ) ↔ Flagged 0 D := by
  have hsat : (∃ θ, Sat D θ) ↔ ∃ θ, Sat (canon D) θ :=
    ⟨fun ⟨θ, h⟩ => ⟨θ, (sat_canon D θ).mpr h⟩, fun ⟨θ, h⟩ => ⟨θ, (sat_canon D θ).mp h⟩⟩
  rw [hsat, nonempty_iff_diag_of_closed hc hrow]
  unfold Flagged
  simp only [neg_zero, not_forall, not_le]

/-! ## Floyd–Warshall: the canonical matrix is closed, and the flag is exact

Walks are the proof device. `W D₀ i l j` is the weight of the walk from `i` through the
intermediate clocks `l` to `j` in the input matrix `D₀`. The in-place loop keeps two facts:
* `Lo`: every entry is at least the weight of some walk;
* `Up k`: after rounds `0, …, k - 1`, every entry is at most the weight of every walk whose
  intermediates are distinct and all below `k`.
No hypothesis is needed for either. A matrix without negative cycles is then closed, because
every walk weighs at least some simple walk with the same ends. A negative closed walk always
contains a negative simple one, which pushes a diagonal entry of `canon` below zero. -/

section Walks

variable (D₀ : Matrix d)

/-- Weight of the walk `i → l₁ → … → lₙ → j` in `D₀`. -/
def W : Fin d → List (Fin d) → Fin d → Bound
  | i, [], j => D₀ i j
  | i, x :: l, j => D₀ i x + W x l j

theorem W_append (i : Fin d) (l₁ : List (Fin d)) (x : Fin d) (l₂ : List (Fin d)) (j : Fin d) :
    W D₀ i (l₁ ++ x :: l₂) j = W D₀ i l₁ x + W D₀ x l₂ j := by
  induction l₁ generalizing i with
  | nil => rfl
  | cons y l₁ ih =>
    show D₀ i y + W D₀ y (l₁ ++ x :: l₂) j = (D₀ i y + W D₀ y l₁ x) + W D₀ x l₂ j
    rw [ih, add_assoc]

/-- No closed walk has negative weight. -/
def NoNegCycle : Prop := ∀ x l, (0 : Bound) ≤ W D₀ x l x

/-- `Lo`: every entry is at least the weight of some walk. -/
def Lo (D : Matrix d) : Prop := ∀ i j, ∃ l, W D₀ i l j ≤ D i j

/-- `Up k`: every entry is at most every simple walk with intermediates below `k`. -/
def Up (k : Nat) (D : Matrix d) : Prop :=
  ∀ i j (l : List (Fin d)), l.Nodup → (∀ x ∈ l, (x : Nat) < k) → D i j ≤ W D₀ i l j

end Walks

theorem exists_dup_split {α : Type} : ∀ {l : List α}, ¬ l.Nodup →
    ∃ a x b c, l = a ++ x :: (b ++ x :: c)
  | [], h => absurd List.nodup_nil h
  | y :: t, h => by
    rw [List.nodup_cons] at h
    by_cases hy : y ∈ t
    · obtain ⟨b, c, rfl⟩ := List.append_of_mem hy
      exact ⟨[], y, b, c, rfl⟩
    · obtain ⟨a, x, b, c, rfl⟩ := exists_dup_split fun hn => h ⟨hy, hn⟩
      exact ⟨y :: a, x, b, c, rfl⟩

theorem lo_init (D₀ : Matrix d) : Lo D₀ D₀ := fun _ _ => ⟨[], le_refl _⟩

theorem lo_runSteps (D₀ : Matrix d) :
    ∀ (l : List (Fin d × Fin d × Fin d)) (D : Matrix d), Lo D₀ D → Lo D₀ (runSteps D l)
  | [], _, h => h
  | s :: l, D, h => by
    refine lo_runSteps D₀ l _ fun a b => ?_
    show ∃ l, W D₀ a l b ≤ relax D s.1 s.2.1 s.2.2 a b
    unfold relax
    split_ifs with hab
    · obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨l₀, h₀⟩ := h s.2.1 s.2.2
      obtain ⟨l₁, h₁⟩ := h s.2.1 s.1
      obtain ⟨l₂, h₂⟩ := h s.1 s.2.2
      rcases le_total (D s.2.1 s.2.2) (D s.2.1 s.1 + D s.1 s.2.2) with hle | hle
      · exact ⟨l₀, by rw [min_eq_left hle]; exact h₀⟩
      · refine ⟨l₁ ++ s.1 :: l₂, ?_⟩
        rw [min_eq_right hle, W_append]
        exact add_le_add h₁ h₂
    · exact h a b

theorem up_mono {D₀ D D' : Matrix d} {k : Nat} (h : Up D₀ k D) (hle : ∀ a b, D' a b ≤ D a b) :
    Up D₀ k D' :=
  fun i j l hn hs => (hle i j).trans (h i j l hn hs)

theorem up_zero (D₀ : Matrix d) : Up D₀ 0 D₀ := by
  intro i j l _ hs
  cases l with
  | nil => exact le_refl _
  | cons x l => exact absurd (hs x List.mem_cons_self) (Nat.not_lt_zero _)

/-- What round `k` establishes for the pair `(i, j)`. -/
def Q (D₀ : Matrix d) (k : Fin d) (D : Matrix d) (i j : Fin d) : Prop :=
  ∀ l₁ l₂ : List (Fin d), l₁.Nodup → l₂.Nodup → (∀ x ∈ l₁, (x : Nat) < k) →
    (∀ x ∈ l₂, (x : Nat) < k) → D i j ≤ W D₀ i l₁ k + W D₀ k l₂ j

theorem round_run (D₀ : Matrix d) (k : Fin d) :
    ∀ (ps : List (Fin d × Fin d × Fin d)), (∀ s ∈ ps, s.1 = k) → ∀ D, Up D₀ k D →
      Up D₀ k (runSteps D ps) ∧ ∀ s ∈ ps, Q D₀ k (runSteps D ps) s.2.1 s.2.2
  | [], _, _, h => ⟨h, fun _ hs => absurd hs List.not_mem_nil⟩
  | s :: ps, hps, D, h => by
    have hk : s.1 = k := hps s List.mem_cons_self
    have h1 : Up D₀ k (relax D s.1 s.2.1 s.2.2) := up_mono h (relax_le D _ _ _)
    obtain ⟨hU, hQ⟩ :=
      round_run D₀ k ps (fun s' hs' => hps s' (List.mem_cons_of_mem s hs')) _ h1
    refine ⟨hU, fun s' hs' => ?_⟩
    rcases List.mem_cons.mp hs' with rfl | hs'
    · intro l₁ l₂ hn₁ hn₂ hs₁ hs₂
      refine (runSteps_le ps _ s'.2.1 s'.2.2).trans ?_
      have hr : relax D s'.1 s'.2.1 s'.2.2 s'.2.1 s'.2.2
          = min (D s'.2.1 s'.2.2) (D s'.2.1 s'.1 + D s'.1 s'.2.2) := by
        simp only [relax, and_self, if_true]
      show relax D s'.1 s'.2.1 s'.2.2 s'.2.1 s'.2.2 ≤ _
      rw [hr, hk]
      exact (min_le_right _ _).trans (add_le_add (h _ _ l₁ hn₁ hs₁) (h _ _ l₂ hn₂ hs₂))
    · exact hQ s' hs'

theorem up_succ {D₀ D : Matrix d} {k : Fin d} (hU : Up D₀ k D) (hQ : ∀ i j, Q D₀ k D i j) :
    Up D₀ (k + 1) D := by
  intro i j l hn hs
  by_cases hk : k ∈ l
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hk
    have hn' := List.nodup_middle.mp hn
    rw [List.nodup_cons, List.mem_append, not_or] at hn'
    obtain ⟨⟨hk₁, hk₂⟩, hn₁₂⟩ := hn'
    have below : ∀ l' : List (Fin d), (∀ x ∈ l', x ∈ l₁ ++ k :: l₂) → k ∉ l' →
        ∀ x ∈ l', (x : Nat) < k :=
      fun l' hsub hkl x hx => by
        have h1 := hs x (hsub x hx)
        have h2 : (x : Nat) ≠ k := fun e => hkl (Fin.ext e ▸ hx)
        omega
    rw [W_append]
    exact hQ i j l₁ l₂ (hn₁₂.sublist (List.sublist_append_left _ _))
      (hn₁₂.sublist (List.sublist_append_right _ _))
      (below l₁ (fun x hx => List.mem_append_left _ hx) hk₁)
      (below l₂ (fun x hx => List.mem_append_right _ (List.mem_cons_of_mem k hx)) hk₂)
  · refine hU i j l hn fun x hx => ?_
    have h1 := hs x hx
    have h2 : (x : Nat) ≠ k := fun e => hk (Fin.ext e ▸ hx)
    omega

theorem mem_roundSteps {k : Fin d} {s : Fin d × Fin d × Fin d} (h : s ∈ roundSteps k) :
    s.1 = k := by
  simp only [roundSteps, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem self_mem_roundSteps (k i j : Fin d) : (k, i, j) ∈ roundSteps k := by
  simp only [roundSteps, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, j, rfl⟩

theorem runSteps_append (D : Matrix d) (l₁ l₂ : List (Fin d × Fin d × Fin d)) :
    runSteps D (l₁ ++ l₂) = runSteps (runSteps D l₁) l₂ :=
  List.foldl_append

theorem up_stepsUpTo (D₀ : Matrix d) :
    ∀ m, m ≤ d → Up D₀ m (runSteps D₀ (stepsUpTo d m))
  | 0, _ => up_zero D₀
  | m + 1, hm => by
    have hlt : m < d := by omega
    have e : stepsUpTo d (m + 1) = stepsUpTo d m ++ roundSteps ⟨m, hlt⟩ := by
      simp only [stepsUpTo, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, dif_pos hlt]
    rw [e, runSteps_append]
    obtain ⟨hU, hQ⟩ := round_run D₀ ⟨m, hlt⟩ (roundSteps ⟨m, hlt⟩)
      (fun s hs => mem_roundSteps hs) _ (up_stepsUpTo D₀ m (by omega))
    exact up_succ (k := ⟨m, hlt⟩) hU fun i j => hQ (⟨m, hlt⟩, i, j) (self_mem_roundSteps _ i j)

/-- After the full pass, every entry is at most every simple walk. -/
theorem up_canon (D₀ : Matrix d) {i j : Fin d} {l : List (Fin d)} (hn : l.Nodup) :
    canon D₀ i j ≤ W D₀ i l j :=
  up_stepsUpTo D₀ d le_rfl i j l hn fun x _ => x.isLt

/-- Without negative cycles, every walk weighs at least some simple walk with the same ends. -/
theorem exists_nodup_le {D₀ : Matrix d} (h : NoNegCycle D₀) :
    ∀ n (l : List (Fin d)), l.length ≤ n → ∀ i j, ∃ l', l'.Nodup ∧ W D₀ i l' j ≤ W D₀ i l j
  | 0, l, hl, _, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact ⟨[], List.nodup_nil, le_refl _⟩
  | n + 1, l, hl, i, j => by
    by_cases hn : l.Nodup
    · exact ⟨l, hn, le_refl _⟩
    obtain ⟨a, x, b, c, rfl⟩ := exists_dup_split hn
    have hlen : (a ++ x :: c).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    obtain ⟨l', hn', hle⟩ := exists_nodup_le h n (a ++ x :: c) hlen i j
    refine ⟨l', hn', hle.trans ?_⟩
    rw [W_append, W_append, W_append]
    exact add_le_add_right (le_add_of_nonneg_left (h x b)) _

/-- **Floyd–Warshall closes the matrix**: without negative cycles, `canon D₀` is closed. -/
theorem closed_canon {D₀ : Matrix d} (h : NoNegCycle D₀) : Closed (canon D₀) := by
  intro i j k
  have hlo := lo_runSteps D₀ (fwSteps d) D₀ (lo_init D₀)
  obtain ⟨l₁, h₁⟩ := hlo i k
  obtain ⟨l₂, h₂⟩ := hlo k j
  obtain ⟨l', hn', hle⟩ :=
    exists_nodup_le h _ (l₁ ++ k :: l₂) le_rfl i j
  calc canon D₀ i j ≤ W D₀ i l' j := up_canon D₀ hn'
    _ ≤ W D₀ i (l₁ ++ k :: l₂) j := hle
    _ = W D₀ i l₁ k + W D₀ k l₂ j := W_append D₀ i l₁ k l₂ j
    _ ≤ canon D₀ i k + canon D₀ k j := add_le_add h₁ h₂

/-- A negative closed walk contains a negative closed simple walk. -/
theorem exists_nodup_neg (D₀ : Matrix d) :
    ∀ n (x : Fin d) (l : List (Fin d)), l.length ≤ n → W D₀ x l x < 0 →
      ∃ y l', l'.Nodup ∧ W D₀ y l' y < 0
  | 0, x, l, hl, hneg => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hneg
    exact ⟨x, [], List.nodup_nil, hneg⟩
  | n + 1, x, l, hl, hneg => by
    by_cases hn : l.Nodup
    · exact ⟨x, l, hn, hneg⟩
    obtain ⟨a, z, b, c, rfl⟩ := exists_dup_split hn
    simp only [List.length_append, List.length_cons] at hl
    rw [W_append, W_append] at hneg
    by_cases hb : W D₀ z b z < 0
    · exact exists_nodup_neg D₀ n z b (by omega) hb
    · have hac : W D₀ x (a ++ z :: c) x < 0 := by
        rw [W_append]
        by_contra hac
        rw [not_lt] at hac hb
        have : (0 : Bound) ≤ W D₀ x a z + (W D₀ z b z + W D₀ z c x) := by
          rw [add_left_comm]
          exact add_nonneg hb hac
        exact absurd hneg (not_lt.mpr this)
      exact exists_nodup_neg D₀ n x (a ++ z :: c)
        (by simp only [List.length_append, List.length_cons]; omega) hac

/-- A negative cycle always raises the Rust flag (at `eps = 0`). -/
theorem flagged_of_neg {D₀ : Matrix d} {x : Fin d} {l : List (Fin d)}
    (hneg : W D₀ x l x < 0) : Flagged 0 D₀ := by
  obtain ⟨y, l', hn, hlt⟩ := exists_nodup_neg D₀ _ x l le_rfl hneg
  refine ⟨y, lt_of_le_of_lt (up_canon D₀ hn) ?_⟩
  rw [neg_zero, WithTop.coe_zero]
  exact hlt

/-- **The Rust emptiness check is exact** ([VER-011] AC2). For a DBM whose reference row `r` is
finite (the negated lower bounds `create` writes), the zone is empty **iff** canonicalisation
leaves a negative diagonal entry. Soundness at any `eps ≥ 0` is `flagged_empty`. -/
theorem empty_iff_flagged {D : Matrix d} {r : Fin d} (hrow : ∀ i, D r i ≠ ⊤) :
    (¬ ∃ θ, Sat D θ) ↔ Flagged 0 D := by
  refine ⟨fun hempty => ?_, flagged_empty le_rfl⟩
  by_contra hnf
  have hnn : NoNegCycle D := fun x l => by
    by_contra hlt
    exact hnf (flagged_of_neg (not_le.mp hlt))
  have hrow' : ∀ i, canon D r i ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hrow i) (canon_le D r i)
  obtain ⟨θ, hθ⟩ := nonempty_of_closed (closed_canon hnn) hrow'
  exact hempty ⟨θ, (sat_canon D θ).mp hθ⟩

/-! ## Clock permutation ([VER-011] AC4) -/

/-- `permuted`: clock `a` of the result is clock `σ a` of `D`. The reference clock stays put
when `σ` fixes it; nothing below needs that. -/
def permD (D : Matrix d) (σ : Equiv.Perm (Fin d)) : Matrix d :=
  fun a b => D (σ a) (σ b)

/-- Permuting the clocks maps the zone bijectively. -/
theorem sat_permD (D : Matrix d) (σ : Equiv.Perm (Fin d)) (θ : Fin d → ℚ) :
    Sat (permD D σ) (θ ∘ σ) ↔ Sat D θ := by
  constructor
  · intro h a b
    have := h (σ.symm a) (σ.symm b)
    simpa [permD] using this
  · intro h a b
    exact h (σ a) (σ b)

/-- A permuted closed matrix is closed: `permuted` need not re-canonicalise. -/
theorem closed_permD {D : Matrix d} (hc : Closed D) (σ : Equiv.Perm (Fin d)) :
    Closed (permD D σ) :=
  fun a b c => hc (σ a) (σ b) (σ c)

end Libpetri.Novel.Dbm
