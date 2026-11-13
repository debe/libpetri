import Libpetri.Spec.Registry
import Libpetri.Novel.Dbm
import Libpetri.Novel.TimedScg.Grid
import Libpetri.Spec.Text.VER_011

set_option linter.missingDocs true

/-!
# VER-011: DBM zone representation (`spec/07-verification.md`)

The firing domain of a state class is a difference bound matrix: entry `D a b` bounds
`θ a - θ b`, index `0` is the reference clock and index `i + 1` is the firing time of clock `i`
(the time from entering the class until that transition fires). The requirement is a predicate
over a zone library `Z : ZoneLib`, the six operations the state-class graph applies to a firing
domain, on positional matrices (`TimedScg.NMat`, a dimension beside each matrix):

* `create n lb ub`, the initial domain of `n` clocks from one lower and one upper bound each;
* `canon d D`, canonicalisation;
* `empty d D`, the emptiness flag;
* `fire n D k ps lb ub`, the successor domain after clock `k` fires, with the persistent clocks
  `ps` and the bounds `lb`, `ub` of the newly enabled clocks;
* `perm ord D`, the clock permutation of the canonical order ([VER-010] AC1);
* `sameKey d D D'`, equality of the dedup keys.

The witness is `refZoneLib`, the model of `dbm.rs` (`Novel/Dbm.lean`, `Novel/TimedScg/Zone.lean`)
with the Rust `EPSILON = 1e-9`, the three early returns of `fire_transition` (a fired clock out
of range, an empty input zone, a constrained matrix flagged empty) giving an empty zone, and a
key that renders every bound to the millisecond, as the three runtimes render it at three
decimals of a second, and gives every flagged zone one key (`DBM[empty]`). The statement is
checked against it (`VER_011_reference`) and against one wrong library per line: a `create`
that drops the upper bounds, a canonicalisation that resets the diagonal, one that does not
close the matrix, a flag raised on a zero diagonal, a flag never raised, a successor that keeps
the persistent clocks' old lower bounds, a permutation that does not move the matrix, one that
keeps the old reference entry in place of `0`, and a key over the projections alone.
`VER_011_key_submillisecond` shows the whole-millisecond premise of the key line is needed
(ruling D58).

The successor line is the sound half of AC3 (the successor holds every firing time the rule
allows). That it holds no other is the exact half, a later block under ruling D67.
-/

namespace Libpetri.Spec

open Libpetri.Novel.Dbm (Bound)
open Libpetri.Novel.TimedScg (NMat SatN canonN FlaggedN createPre constrainPre fireMat pm permMat
  GridB GridM toFin)

/-! ## The model -/

/-- A bound is a whole number of milliseconds: `⊤`, or a multiple of `1/1000` (bounds are in
seconds, as the runtimes divide the millisecond timings by `1000`). -/
def WholeMs (x : Bound) : Prop := GridB (1 / 1000) x

/-- Every bound of the `d × d` corner of `D` is a whole number of milliseconds. -/
def MatWholeMs (d : Nat) (D : NMat) : Prop := ∀ i j, i < d → j < d → WholeMs (D i j)

/-- The `d × d` corner of `D` is closed: no bound exceeds a two-step detour. -/
def ClosedN (d : Nat) (D : NMat) : Prop :=
  ∀ i j k, i < d → j < d → k < d → D i j ≤ D i k + D k j

/-- A zone library: the operations of `Dbm` the state-class graph applies to a firing domain. -/
structure ZoneLib where
  /-- `create n lb ub`: the domain of `n` clocks (dimension `n + 1`), clock `i` between `lb[i]`
  and `ub[i]` (`Dbm::create`). -/
  create : Nat → List ℚ → List Bound → NMat
  /-- `canon d D`: canonicalisation of the `d × d` matrix (`canonicalize`). -/
  canon : Nat → NMat → NMat
  /-- `empty d D`: the emptiness flag of the `d × d` matrix (`is_empty` after `canonicalize`). -/
  empty : Nat → NMat → Prop
  /-- `fire n D k ps lb ub`: the successor of the `n`-clock domain `D` when clock `k` fires, with
  the persistent clocks `ps` (old indices) and the newly enabled clocks' bounds `lb`, `ub`
  (`fire_transition`); dimension `ps.length + lb.length + 1`. -/
  fire : Nat → NMat → Nat → List Nat → List ℚ → List Bound → NMat
  /-- `perm ord D`: clock `i` of the result is clock `ord[i]` of `D` (`permuted`). -/
  perm : List Nat → NMat → NMat
  /-- `sameKey d D D'`: the dedup keys of the two `d × d` zones are equal (`zone_key`). -/
  sameKey : Nat → NMat → NMat → Prop

/-- The constant `EPSILON = 1e-9` of `dbm.rs`, in seconds. -/
def ver011_eps : ℚ := 1 / 1000000000

/-- A bound rendered to the nearest millisecond (half up), `⊤` for `∞`: a bound in seconds
printed at three decimals, as `format_bound` prints it. -/
def ver011_render (x : Bound) : WithTop ℤ := WithTop.map (fun q : ℚ => Rat.floor (q * 1000 + 1 / 2)) x

/-- The reference key: every bound of the `d × d` corner rendered to the millisecond
(`ver011_render`); `⊤` outside the corner. -/
def ver011_key (d : Nat) (D : NMat) : Nat → Nat → WithTop ℤ :=
  fun i j => if i < d ∧ j < d then ver011_render (D i j) else ⊤

/-- The empty zone of the model: every bound `-1`, so `θ 0 - θ 0 ≤ -1` holds for no valuation.
Rust's `Dbm::empty_dbm()` carries its emptiness in a flag beside the matrix; the model has no
flag beside a matrix, so the emptiness is in the matrix. -/
def ver011_emptyMat : NMat := fun _ _ => ((-1 : ℚ) : Bound)

/-- **The reference zone library**: the model of `dbm.rs`. `create` and `fire` canonicalise
their result, `fire` returns an empty zone on the three early returns of `fire_transition`
(`fired_clock >= n`, `self.empty`, and step 2 `canonicalize_in_place` flagging the constrained
matrix) and otherwise canonicalises the constrained matrix first (steps 1 to 5), the flag is the
Rust check at `EPSILON = 1e-9`, and the key renders the matrix to the millisecond, every flagged
zone sharing one key (`zone_key` returns `DBM[empty]`, `PartialEq` calls two empty zones
equal). -/
def refZoneLib : ZoneLib where
  create n lb ub := canonN (n + 1) (createPre n lb ub)
  canon d D := canonN d D
  empty d D := FlaggedN ver011_eps d D
  fire n D k ps lb ub :=
    if n ≤ k ∨ FlaggedN ver011_eps (n + 1) D ∨ FlaggedN ver011_eps (n + 1) (constrainPre n k D)
    then ver011_emptyMat
    else canonN (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub)
  perm ord D := permMat ord D
  sameKey d D D' := (FlaggedN ver011_eps d D ∧ FlaggedN ver011_eps d D') ∨
    (¬ FlaggedN ver011_eps d D ∧ ¬ FlaggedN ver011_eps d D' ∧ ver011_key d D = ver011_key d D')

#spec_witness refZoneLib

/-! ## VER-011: DBM zone representation -/

requirement VER_011
  id "VER-011"
  title "DBM Zone Representation"
  kind F
  scope "the zone library of every state class graph, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_011.s1, VER_011.s2, VER_011.s3, VER_011.s4, VER_011.s5, VER_011.s6, VER_011.s7,
        VER_011.s8
  reading "create n lb ub (one lower and one upper bound per clock) holds a valuation θ exactly when every clock i < n lies between lb[i] and ub[i], relative to the reference clock."
          "canon d D holds exactly the valuations D holds, on every matrix, empty ones included."
          "When D holds some valuation, canon d D is closed on its d × d corner: D i j ≤ D i k + D k j for every i, j, k < d, the reference index 0 and repeated indices included."
          "empty d D implies D holds no valuation."
          "For d > 0, every entry D 0 i of the reference row finite (i = 0 included) and every bound of the corner ⊤ or a whole number of milliseconds: empty d D holds exactly when D holds no valuation."
          "For a fired clock k < n, persistent clocks below n and one lower and one upper bound per newly enabled clock: if θ is a valuation of D in which clock k is not later than any clock, and θ' gives each persistent clock p (at index p + 1, in the order of ps) the time θ(ps[p]) - θ(k) and each newly enabled clock j (at index |ps| + j + 1) a time between its bounds (all relative to the reference), then fire n D k ps lb ub holds θ'."
          "For ord a permutation of 0 … n - 1 and D holding some valuation: perm ord D has 0 at (0, 0), D (ord[i] + 1) 0 at (i + 1, 0), D 0 (ord[j] + 1) at (0, j + 1) and D (ord[i] + 1) (ord[j] + 1) at (i + 1, j + 1)."
          "For two matrices that each hold some valuation and whose d × d corners have every bound ⊤ or a whole number of milliseconds: sameKey d D D' holds exactly when the corners are equal entry by entry."
  assumes "The model is a zone library ZoneLib on positional matrices (TimedScg.NMat, entry D a b bounds θ a - θ b, index 0 the reference clock, clock i at index i + 1), a dimension beside each matrix, and valuations θ : Nat → ℚ. θ a - θ 0 for a clock a is the firing time the body sentence names: the time from entering the class until that transition fires. Bounds are exact rationals in seconds with ⊤ for infinity; floating point is out of the model (Dbm.lean). The model has no emptiness flag beside a matrix: an empty zone is a matrix that holds no valuation (ver011_emptyMat stands for Rust's empty_dbm). The witness is refZoneLib (createPre, canonN, FlaggedN at EPSILON = 1e-9, constrainPre then fireMat behind the three early returns, permMat, and ver011_key with one key for every flagged zone)."
          "A whole number of milliseconds is WholeMs, which also accepts ⊤: 'every finite bound' in the fifth and eighth sentences, so a zone with an unbounded clock (a transition with no deadline) is covered. Every zone has the reference clock, so its dimension is at least 1 (the 0 < d premise of line 5), and 'every clock, the reference clock included, has a finite lower bound' is the finite reference row D 0 i for every i < d, D 0 0 included."
          "AC1 (lower and upper bounds for each transition clock) is line 1 and the first quoted sentence; a create that drops the upper bounds is killed (VER_011_forbids_noUpper)."
          "AC2 (zone emptiness is detectable) is lines 4 and 5 and the fourth and fifth quoted sentences: the flag is sound on every matrix (line 4, so a flagged zone never drops a reachable class; a flag raised on a zero diagonal is killed, VER_011_forbids_zeroDiag) and exact on whole-millisecond matrices with a finite reference row (line 5; a flag never raised is killed, VER_011_forbids_neverEmpty). The finite reference row is the premise of Dbm.empty_iff_flagged; every matrix create and fire build has one (each clock gets a finite lower bound and the reference entry is 0). The whole-millisecond premise is ruling D58: the Rust flag is the diagonal below -1e-9, exact only when no negative cycle lies in [-1e-9, 0), which Grid.flagged_of_flagged_zero shows for matrices on the millisecond grid."
          "Lines 2 and 3 (the second and third quoted sentences) are what canonical means in AC4: canonicalisation keeps the zone (Dbm.sat_canon) and closes a satisfiable matrix (Dbm.closed_canon). Line 3 quantifies over every index of the matrix, the reference index 0 and repeated indices included, which is what the third sentence's detour through any clock of the matrix, the reference clock included, says. A canonicalisation that resets the diagonal hides an empty zone (VER_011_forbids_diagReset); one that returns the matrix unchanged keeps the zone but is not closed, which a detour through the reference clock shows (VER_011_forbids_noClose). Lines 2 and 3 do not fix one canonical matrix per zone: on a clock with no upper bound a closed matrix of the same zone may carry any non-negative diagonal entry. That two matrices of one zone canonicalise to one matrix (closure with a zero diagonal) is out of scope here. Every matrix create and fire build starts from a zero diagonal, which canonicalisation only lowers and which stays non-negative while the zone holds a valuation (canonN_le, Dbm.diag_nonneg_of_sat), and the dedup over canonical matrices is VER-010's key block."
          "AC3 (the successor DBM is computed correctly after transition firing) is line 6 and the sixth quoted sentence, its sound half: the successor holds every firing time the Berthomieu-Diaz rule allows (TimedScg.sat_constrainPre, sat_fireMat, satN_canonN). A successor that keeps a persistent clock's old lower bound instead of the time it has left is killed (VER_011_forbids_noShift). The successor's layout (persistent clock p at index p + 1 in the order given, then newly enabled clock j at index |ps| + j + 1) is part of line 6 and of the sixth sentence; VER-010's permutation into the canonical order relies on it. The exact half (the successor holds no other firing time) is a later block under ruling D67: Lean proves the sound half only, and VER-023's TIMED_CONFIRMED block waits on the exact half. Until that block lands AC3 is partly covered, and 'computed correctly' is not discharged: a successor that drops every constraint, or one built without the constraint that the fired clock fires first, meets line 6. The reference models Rust's three early returns (a fired clock out of range, an empty input zone, a constrained matrix flagged empty) by returning an empty zone; under line 6's premises none is taken (k < n, and the input and the constrained matrix hold a valuation, so neither is flagged), so they bear on the exact half only, and VER_011_fire_first shows the reference returns an empty successor when the fired clock cannot fire first."
          "AC4, first half (a permutation of the clocks that reorders the matrix with them) is line 7 and the seventh quoted sentence, for a zone that holds a firing time: Rust and TypeScript return an empty zone unchanged (permuted returns self when the zone is flagged), so the line does not speak of empty zones. Every entry moves with its two clocks, the reference row and column stay first, and the reference entry (0, 0) is written as 0 as all three runtimes write it (out[0] = 0); on a zone that holds a firing time D 0 0 is non-negative, so writing 0 keeps the zone. A permutation that does not move the matrix is killed (VER_011_forbids_noMove), and so is one that keeps the old reference entry (VER_011_forbids_keepRef). That a permuted zone holds the permuted valuations is Dbm.sat_permD (cited for VER-011), and that it stays closed is Dbm.closed_permD."
          "AC4, second half (a dedup key over the full canonical matrix; equality positional over the canonical order; exact at millisecond resolution) is line 8 and the eighth quoted sentence, for zones that hold some firing time. All three runtimes give every flagged zone the key DBM[empty] and call two empty zones equal, so two different empty matrices share a key (VER_011_empty_one_key on the reference); the line therefore speaks of zones that hold firing times, which are the only zones the state class graph keys (it drops an empty successor before keying, state_class_graph.rs). The key is a relation sameKey, not a string: the rendering (clock names joined by commas, entries row-major joined by bars) is kind N, and the clock names belong to VER-010's class key. The runtimes render each bound at three decimals of a second (format_bound), so the key is exact only on whole-millisecond bounds, which is ruling D58: always in Rust and Python, after truncation in Java's graph, and not for a fractional TypeScript bound, where VER_011_key_submillisecond shows two zones that differ by a tenth of a millisecond with one key. A key over the projections alone merges zones that differ in a difference bound and is killed (VER_011_forbids_projectionKey). That the matrices are canonical and in the canonical order is VER-010's (AC1), which applies canon and perm before it keys."
          "let_time_pass (zeroing the lower bounds after the successor) is part of VER-010's successor step and is not listed in VER-011's criteria; TimedScg.sat_ltpPre and sat_ltpPre_shift cover it. The test derivation (three timed clocks, fire one, check the successor's constraints) is line 6 on a concrete zone, VER_011_nonvacuous."
  signoff "2026-11-13 c25a6c8c7bda6335 ai"
  statement : ZoneLib → Prop :=
    fun Z =>
      (∀ (n : Nat) (lb : List ℚ) (ub : List Bound) (θ : Nat → ℚ),
        lb.length = n → ub.length = n →
          (SatN (n + 1) (Z.create n lb ub) θ ↔
            ∀ i, i < n → lb.getD i 0 ≤ θ (i + 1) - θ 0 ∧
              ((θ (i + 1) - θ 0 : ℚ) : Bound) ≤ ub.getD i ⊤)) ∧
      (∀ (d : Nat) (D : NMat) (θ : Nat → ℚ), SatN d (Z.canon d D) θ ↔ SatN d D θ) ∧
      (∀ (d : Nat) (D : NMat), (∃ θ, SatN d D θ) → ClosedN d (Z.canon d D)) ∧
      (∀ (d : Nat) (D : NMat), Z.empty d D → ¬ ∃ θ, SatN d D θ) ∧
      (∀ (d : Nat) (D : NMat), 0 < d → (∀ i, i < d → D 0 i ≠ ⊤) → MatWholeMs d D →
        (Z.empty d D ↔ ¬ ∃ θ, SatN d D θ)) ∧
      (∀ (n : Nat) (D : NMat) (k : Nat) (ps : List Nat) (lb : List ℚ) (ub : List Bound)
          (θ θ' : Nat → ℚ),
        k < n → (∀ x ∈ ps, x < n) → lb.length = ub.length →
          SatN (n + 1) D θ → (∀ i, i < n → θ (k + 1) ≤ θ (i + 1)) →
          (∀ p, p < ps.length → θ' (p + 1) - θ' 0 = θ (ps.getD p 0 + 1) - θ (k + 1)) →
          (∀ j, j < lb.length → lb.getD j 0 ≤ θ' (ps.length + j + 1) - θ' 0 ∧
            ((θ' (ps.length + j + 1) - θ' 0 : ℚ) : Bound) ≤ ub.getD j ⊤) →
          SatN (ps.length + lb.length + 1) (Z.fire n D k ps lb ub) θ') ∧
      (∀ (n : Nat) (ord : List Nat) (D : NMat), ord.Perm (List.range n) →
        (∃ θ, SatN (n + 1) D θ) →
        Z.perm ord D 0 0 = 0 ∧
        (∀ i, i < n → Z.perm ord D (i + 1) 0 = D (ord.getD i 0 + 1) 0 ∧
          Z.perm ord D 0 (i + 1) = D 0 (ord.getD i 0 + 1)) ∧
        (∀ i j, i < n → j < n →
          Z.perm ord D (i + 1) (j + 1) = D (ord.getD i 0 + 1) (ord.getD j 0 + 1))) ∧
      (∀ (d : Nat) (D D' : NMat), (∃ θ, SatN d D θ) → (∃ θ, SatN d D' θ) →
        MatWholeMs d D → MatWholeMs d D' →
        (Z.sameKey d D D' ↔ ∀ i j, i < d → j < d → D i j = D' i j))

/- The pinned readable form of VER-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_011 : ZoneLib → Prop :=
fun Z =>
  (∀ (n : ℕ) (lb : List ℚ) (ub : List Bound) (θ : ℕ → ℚ),
      lb.length = n →
        ub.length = n →
          (SatN (n + 1) (Z.create n lb ub) θ ↔
            ∀ i < n, lb.getD i 0 ≤ θ (i + 1) - θ 0 ∧ ↑(θ (i + 1) - θ 0) ≤ ub.getD i ⊤)) ∧
    (∀ (d : ℕ) (D : NMat) (θ : ℕ → ℚ), SatN d (Z.canon d D) θ ↔ SatN d D θ) ∧
      (∀ (d : ℕ) (D : NMat), (∃ θ, SatN d D θ) → ClosedN d (Z.canon d D)) ∧
        (∀ (d : ℕ) (D : NMat), Z.empty d D → ¬∃ θ, SatN d D θ) ∧
          (∀ (d : ℕ) (D : NMat), 0 < d → (∀ i < d, D 0 i ≠ ⊤) → MatWholeMs d D → (Z.empty d D ↔ ¬∃ θ, SatN d D θ)) ∧
            (∀ (n : ℕ) (D : NMat) (k : ℕ) (ps : List ℕ) (lb : List ℚ) (ub : List Bound) (θ θ' : ℕ → ℚ),
                k < n →
                  (∀ x ∈ ps, x < n) →
                    lb.length = ub.length →
                      SatN (n + 1) D θ →
                        (∀ i < n, θ (k + 1) ≤ θ (i + 1)) →
                          (∀ p < ps.length, θ' (p + 1) - θ' 0 = θ (ps.getD p 0 + 1) - θ (k + 1)) →
                            (∀ j < lb.length,
                                lb.getD j 0 ≤ θ' (ps.length + j + 1) - θ' 0 ∧
                                  ↑(θ' (ps.length + j + 1) - θ' 0) ≤ ub.getD j ⊤) →
                              SatN (ps.length + lb.length + 1) (Z.fire n D k ps lb ub) θ') ∧
              (∀ (n : ℕ) (ord : List ℕ) (D : NMat),
                  ord.Perm (List.range n) →
                    (∃ θ, SatN (n + 1) D θ) →
                      Z.perm ord D 0 0 = 0 ∧
                        (∀ i < n,
                            Z.perm ord D (i + 1) 0 = D (ord.getD i 0 + 1) 0 ∧
                              Z.perm ord D 0 (i + 1) = D 0 (ord.getD i 0 + 1)) ∧
                          ∀ (i j : ℕ),
                            i < n → j < n → Z.perm ord D (i + 1) (j + 1) = D (ord.getD i 0 + 1) (ord.getD j 0 + 1)) ∧
                ∀ (d : ℕ) (D D' : NMat),
                  (∃ θ, SatN d D θ) →
                    (∃ θ, SatN d D' θ) →
                      MatWholeMs d D →
                        MatWholeMs d D' → (Z.sameKey d D D' ↔ ∀ (i j : ℕ), i < d → j < d → D i j = D' i j)
-/
#guard_msgs in #print VER_011

/-! ## The reference -/

open Libpetri.Novel.TimedScg (satN_iff satN_canonN canonN_le flaggedN_empty toFin_canonN)

/-- Translating every clock by `c` keeps a valuation in the zone: a zone constrains differences
only. -/
theorem ver011_satN_add {d : Nat} {D : NMat} {θ : Nat → ℚ} (c : ℚ) :
    SatN d D (fun a => θ a + c) ↔ SatN d D θ := by
  simp only [SatN, add_sub_add_right_eq_sub]

/-- **The initial domain is the box**: `createPre` holds exactly the valuations with every clock
between its bounds, relative to the reference clock (`Zone.sat_createPre` is the `⇐` half at
`θ 0 = 0`). -/
theorem ver011_create {n : Nat} {lb : List ℚ} {ub : List Bound} {θ : Nat → ℚ} :
    SatN (n + 1) (createPre n lb ub) θ ↔
      ∀ i, i < n → lb.getD i 0 ≤ θ (i + 1) - θ 0 ∧
        ((θ (i + 1) - θ 0 : ℚ) : Bound) ≤ ub.getD i ⊤ := by
  constructor
  · intro h i hi
    have h1 := h 0 (i + 1) (by omega) (by omega)
    have h2 := h (i + 1) 0 (by omega) (by omega)
    have e1 : createPre n lb ub 0 (i + 1) = (((-(lb.getD i 0)) : ℚ) : Bound) := by
      unfold createPre
      rw [if_neg (show ¬ ((0 : Nat) = i + 1) by omega),
        if_pos (show ((0 : Nat) = 0 ∧ 1 ≤ i + 1 ∧ i + 1 ≤ n) by omega), Nat.add_sub_cancel]
    have e2 : createPre n lb ub (i + 1) 0 = ub.getD i ⊤ := by
      unfold createPre
      rw [if_neg (show ¬ (i + 1 = 0) by omega),
        if_neg (show ¬ (i + 1 = 0 ∧ 1 ≤ 0 ∧ 0 ≤ n) by omega),
        if_pos (show ((0 : Nat) = 0 ∧ 1 ≤ i + 1 ∧ i + 1 ≤ n) by omega), Nat.add_sub_cancel]
    rw [e1, WithTop.coe_le_coe] at h1
    rw [e2] at h2
    exact ⟨by linarith, h2⟩
  · intro h a b ha hb
    unfold createPre
    by_cases hab : a = b
    · subst hab; simp
    rw [if_neg hab]
    by_cases h1 : a = 0 ∧ 1 ≤ b ∧ b ≤ n
    · rw [if_pos h1]
      obtain ⟨rfl, hb1, hbn⟩ := h1
      have := (h (b - 1) (by omega)).1
      rw [show b - 1 + 1 = b by omega] at this
      rw [WithTop.coe_le_coe]
      linarith
    rw [if_neg h1]
    by_cases h2 : b = 0 ∧ 1 ≤ a ∧ a ≤ n
    · rw [if_pos h2]
      obtain ⟨rfl, ha1, han⟩ := h2
      have := (h (a - 1) (by omega)).2
      rw [show a - 1 + 1 = a by omega] at this
      exact this
    rw [if_neg h2]
    exact le_top

/-- A zone with a solution has no negative cycle, so its canonical matrix is closed
(`Dbm.flagged_of_neg`, `Dbm.flagged_empty`, `Dbm.closed_canon`). -/
theorem ver011_closed {d : Nat} {D : NMat} (h : ∃ θ, SatN d D θ) : ClosedN d (canonN d D) := by
  obtain ⟨θ, hθ⟩ := h
  have hs : Novel.Dbm.Sat (toFin d D) (fun i => θ i) := satN_iff.mp hθ
  have hnn : Novel.Dbm.NoNegCycle (toFin d D) := fun x l => by
    by_contra hlt
    exact Novel.Dbm.flagged_empty le_rfl (Novel.Dbm.flagged_of_neg (not_le.mp hlt)) ⟨_, hs⟩
  have hc := Novel.Dbm.closed_canon hnn
  rw [← toFin_canonN] at hc
  intro i j k hi hj hk
  exact hc ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩

/-- A positional zone has a solution exactly when its `d × d` corner does. -/
theorem ver011_exists_satN {d : Nat} {D : NMat} :
    (∃ θ, SatN d D θ) ↔ ∃ θ, Novel.Dbm.Sat (toFin d D) θ := by
  constructor
  · rintro ⟨θ, h⟩
    exact ⟨_, satN_iff.mp h⟩
  · rintro ⟨θ, h⟩
    refine ⟨fun a => if ha : a < d then θ ⟨a, ha⟩ else 0, fun i j hi hj => ?_⟩
    have := h ⟨i, hi⟩ ⟨j, hj⟩
    simpa [hi, hj, toFin] using this

/-- **The flag is exact on whole-millisecond zones**: with a finite reference row, the Rust flag
at `EPSILON = 1e-9` is raised exactly when the zone has no solution (`Dbm.empty_iff_flagged` at
`eps = 0`, then `Grid.flagged_of_flagged_zero` on the millisecond grid). -/
theorem ver011_empty_exact {d : Nat} {D : NMat} (hd : 0 < d)
    (hrow : ∀ i, i < d → D 0 i ≠ ⊤) (hms : MatWholeMs d D) :
    FlaggedN ver011_eps d D ↔ ¬ ∃ θ, SatN d D θ := by
  refine ⟨fun h => flaggedN_empty (by norm_num [ver011_eps]) h, fun he => ?_⟩
  let D' : NMat := fun a b => if a < d ∧ b < d then D a b else ⊤
  have hfin : toFin d D' = toFin d D := by
    funext i j
    simp [D', toFin, i.isLt, j.isLt]
  have hg : GridM (1 / 1000) D' := fun a b => by
    by_cases h : a < d ∧ b < d
    · simp only [D', if_pos h]
      exact hms a b h.1 h.2
    · simp only [D', if_neg h]
      exact Novel.TimedScg.gridB_top
  have h0 : FlaggedN 0 d D' := by
    show Novel.Dbm.Flagged 0 (toFin d D')
    rw [hfin]
    exact (Novel.Dbm.empty_iff_flagged (r := ⟨0, hd⟩) (fun i => hrow i i.isLt)).mp
      (fun hx => he (ver011_exists_satN.mpr hx))
  have := Novel.TimedScg.flagged_of_flagged_zero (g := 1 / 1000) (eps := ver011_eps)
    (by norm_num) (by norm_num [ver011_eps]) (Novel.TimedScg.gridM_canonN hg) h0
  show Novel.Dbm.Flagged ver011_eps (toFin d D)
  rw [← hfin]
  exact this

/-- **The successor holds every firing time the rule allows** (AC3, the sound half): translate
the old valuation so the fired clock is at zero and the new one so the reference is at zero,
then `sat_constrainPre`, `satN_canonN` and `sat_fireMat`. -/
theorem ver011_fire_sound {n : Nat} {D : NMat} {k : Nat} {ps : List Nat} {lb : List ℚ}
    {ub : List Bound} {θ θ' : Nat → ℚ} (hk : k < n) (hps : ∀ x ∈ ps, x < n)
    (hD : SatN (n + 1) D θ) (hmin : ∀ i, i < n → θ (k + 1) ≤ θ (i + 1))
    (hpers : ∀ p, p < ps.length → θ' (p + 1) - θ' 0 = θ (ps.getD p 0 + 1) - θ (k + 1))
    (hnew : ∀ j, j < lb.length → lb.getD j 0 ≤ θ' (ps.length + j + 1) - θ' 0 ∧
      ((θ' (ps.length + j + 1) - θ' 0 : ℚ) : Bound) ≤ ub.getD j ⊤) :
    SatN (ps.length + lb.length + 1)
      (canonN (ps.length + lb.length + 1)
        (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub)) θ' := by
  have hpsl : ∀ p, p < ps.length → ps.getD p 0 < n := fun p hp => by
    have : ps.getD p 0 ∈ ps := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
      exact List.getElem_mem hp
    exact hps _ this
  have hDn : SatN (n + 1) D (fun a => θ a + -θ (k + 1)) := (ver011_satN_add _).mpr hD
  have hC : SatN (n + 1) (canonN (n + 1) (constrainPre n k D)) (fun a => θ a + -θ (k + 1)) :=
    satN_canonN.mpr (Novel.TimedScg.sat_constrainPre hDn (fun i hi => by
      have := hmin i hi
      linarith))
  have hF := Novel.TimedScg.sat_fireMat (θ' := fun a => θ' a + -θ' 0) hC hk hps
    (by simp) (by simp)
    (fun p hp => by
      have := hpers p hp
      linarith)
    (fun p hp => by
      have h1 := hpers p hp
      have h2 := hmin _ (hpsl p hp)
      linarith)
    (fun j hj => by
      have := (hnew j hj).1
      linarith)
    (fun j hj => by
      have := (hnew j hj).2
      rwa [sub_eq_add_neg] at this)
  exact (ver011_satN_add (θ := θ') (-θ' 0)).mp (satN_canonN.mpr hF)

/-- Two defaults of `getD` agree inside the list. -/
theorem ver011_getD {ord : List Nat} {i : Nat} (h : i < ord.length) (a b : Nat) :
    ord.getD i a = ord.getD i b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- **`permMat` moves every entry with its two clocks** and writes `0` at the reference entry. -/
theorem ver011_perm (n : Nat) (ord : List Nat) (D : NMat) (hp : ord.Perm (List.range n)) :
    permMat ord D 0 0 = 0 ∧
      (∀ i, i < n → permMat ord D (i + 1) 0 = D (ord.getD i 0 + 1) 0 ∧
        permMat ord D 0 (i + 1) = D 0 (ord.getD i 0 + 1)) ∧
      (∀ i j, i < n → j < n →
        permMat ord D (i + 1) (j + 1) = D (ord.getD i 0 + 1) (ord.getD j 0 + 1)) := by
  have hl : ord.length = n := by simpa using hp.length_eq
  refine ⟨by simp [permMat], fun i hi => ⟨?_, ?_⟩, fun i j hi hj => ?_⟩
  · simp only [permMat, pm, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, false_and,
      if_true, ver011_getD (hl ▸ hi) i 0]
  · simp only [permMat, pm, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, and_false,
      if_true, ver011_getD (hl ▸ hi) i 0]
  · simp only [permMat, pm, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, false_and,
      ver011_getD (hl ▸ hi) i 0, ver011_getD (hl ▸ hj) j 0]

/-- `⌊a⌋ = 0` on `[0, 1)`. -/
theorem ver011_floor_zero {a : ℚ} (h0 : 0 ≤ a) (h1 : a < 1) : a.floor = 0 := by
  have h1' : a.floor < 1 := Rat.floor_lt_iff.mpr (by simpa using h1)
  have h0' : ¬ a.floor < 0 := fun h => by
    have := Rat.floor_lt_iff.mp h
    simp at this
    linarith
  omega

/-- A whole number `z` of milliseconds renders as `z`. -/
theorem ver011_render_ms (z : ℤ) :
    ver011_render (((z * (1 / 1000) : ℚ)) : Bound) = ((z : ℤ) : WithTop ℤ) := by
  simp only [ver011_render, WithTop.map_coe]
  congr 1
  rw [show (z : ℚ) * (1 / 1000) * 1000 + 1 / 2 = 1 / 2 + (z : ℚ) by ring, Rat.floor_add_intCast,
    ver011_floor_zero (by norm_num) (by norm_num)]
  simp

/-- On whole-millisecond bounds the rendering is injective. -/
theorem ver011_render_inj {x y : Bound} (hx : WholeMs x) (hy : WholeMs y)
    (h : ver011_render x = ver011_render y) : x = y := by
  rcases hx with rfl | ⟨a, rfl⟩ <;> rcases hy with rfl | ⟨b, rfl⟩
  · rfl
  · rw [ver011_render_ms] at h
    simp [ver011_render] at h
  · rw [ver011_render_ms] at h
    simp [ver011_render] at h
  · rw [ver011_render_ms, ver011_render_ms, WithTop.coe_inj] at h
    subst h
    rfl

/-- **The reference key is exact on whole-millisecond zones.** -/
theorem ver011_key_iff {d : Nat} {D D' : NMat} (h1 : MatWholeMs d D) (h2 : MatWholeMs d D') :
    ver011_key d D = ver011_key d D' ↔ ∀ i j, i < d → j < d → D i j = D' i j := by
  constructor
  · intro h i j hi hj
    have := congrFun (congrFun h i) j
    simp only [ver011_key, if_pos (And.intro hi hj)] at this
    exact ver011_render_inj (h1 i j hi hj) (h2 i j hi hj) this
  · intro h
    funext i j
    unfold ver011_key
    split_ifs with hij
    · rw [h i j hij.1 hij.2]
    · rfl

/-- Under the premises of the successor line none of the three early returns is taken: the
fired clock is in range, and the input and the constrained matrix hold a valuation, so neither is
flagged (`not_flagged_of_sat`). -/
theorem ver011_fire_ref {n : Nat} {D : NMat} {k : Nat} {ps : List Nat} {lb : List ℚ}
    {ub : List Bound} {θ : Nat → ℚ} (hk : k < n) (hD : SatN (n + 1) D θ)
    (hmin : ∀ i, i < n → θ (k + 1) ≤ θ (i + 1)) :
    refZoneLib.fire n D k ps lb ub = canonN (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub) := by
  have heps : (0 : ℚ) ≤ ver011_eps := by norm_num [ver011_eps]
  have hC : SatN (n + 1) (constrainPre n k D) θ := Novel.TimedScg.sat_constrainPre hD hmin
  show (if n ≤ k ∨ FlaggedN ver011_eps (n + 1) D ∨
      FlaggedN ver011_eps (n + 1) (constrainPre n k D) then ver011_emptyMat else _) = _
  rw [if_neg (not_or.mpr ⟨by omega, not_or.mpr
    ⟨Novel.TimedScg.not_flagged_of_sat heps hD, Novel.TimedScg.not_flagged_of_sat heps hC⟩⟩)]

/-- **The reference key is exact on whole-millisecond zones that hold a firing time**: neither
is flagged, so the key compares the rendered matrices. -/
theorem ver011_sameKey_iff {d : Nat} {D D' : NMat} (hs : ∃ θ, SatN d D θ)
    (hs' : ∃ θ, SatN d D' θ) (h1 : MatWholeMs d D) (h2 : MatWholeMs d D') :
    refZoneLib.sameKey d D D' ↔ ∀ i j, i < d → j < d → D i j = D' i j := by
  have heps : (0 : ℚ) ≤ ver011_eps := by norm_num [ver011_eps]
  obtain ⟨θ, hθ⟩ := hs
  obtain ⟨θ', hθ'⟩ := hs'
  have n1 := Novel.TimedScg.not_flagged_of_sat heps hθ
  have n2 := Novel.TimedScg.not_flagged_of_sat heps hθ'
  show (FlaggedN ver011_eps d D ∧ FlaggedN ver011_eps d D') ∨
    (¬ FlaggedN ver011_eps d D ∧ ¬ FlaggedN ver011_eps d D' ∧
      ver011_key d D = ver011_key d D') ↔ _
  rw [← ver011_key_iff h1 h2]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
    · exact absurd h n1
    · exact h
  · exact fun h => Or.inr ⟨n1, n2, h⟩

/-- The reference zone library satisfies VER-011. -/
@[evidence holds VER_011]
theorem VER_011_reference : VER_011 refZoneLib :=
  ⟨fun _ _ _ _ _ _ => satN_canonN.trans ver011_create,
   fun _ _ _ => satN_canonN,
   fun _ _ h => ver011_closed h,
   fun _ _ h => flaggedN_empty (by norm_num [ver011_eps]) h,
   fun _ _ hd hrow hms => ver011_empty_exact hd hrow hms,
   fun _ _ _ _ _ _ _ _ hk hps _ hD hmin hpers hnew => by
     rw [ver011_fire_ref hk hD hmin]
     exact ver011_fire_sound hk hps hD hmin hpers hnew,
   fun n ord D hp _ => ver011_perm n ord D hp,
   fun _ _ _ hs hs' h1 h2 => ver011_sameKey_iff hs hs' h1 h2⟩



/-! ## Examples on the reference -/

/-- An integer bound, in seconds, is a whole number of milliseconds. -/
theorem ver011_wholeMs_int (z : ℤ) : WholeMs (((z : ℚ)) : Bound) :=
  Or.inr ⟨z * 1000, by push_cast; ring_nf⟩

/-- A matrix built by `createPre` from whole-millisecond bounds is on the millisecond grid. -/
theorem ver011_createPre_ms {n : Nat} {lb : List ℚ} {ub : List Bound}
    (hlb : ∀ x ∈ lb, Novel.TimedScg.GridQ (1 / 1000) x) (hub : ∀ x ∈ ub, WholeMs x) :
    MatWholeMs (n + 1) (createPre n lb ub) :=
  fun a b _ _ => Novel.TimedScg.gridM_createPre hlb hub a b

/-- An integer is a whole number of milliseconds. -/
theorem ver011_gridQ_int (z : ℤ) : Novel.TimedScg.GridQ (1 / 1000) (z : ℚ) :=
  ⟨z * 1000, by push_cast; ring⟩

/-- The firing times of the three-clock example: clocks `0`, `1`, `2` at `3/2`, `2`, `4`. -/
def ver011_θ : Nat → ℚ := fun i => if i = 1 then 3 / 2 else if i = 2 then 2 else if i = 3 then 4 else 0

/-- The successor's firing times: the persistent clocks `1`, `2` have `1/2` and `5/2` left, the
newly enabled clock is at `1`. -/
def ver011_θ' : Nat → ℚ := fun i => if i = 1 then 1 / 2 else if i = 2 then 5 / 2 else if i = 3 then 1 else 0

/-- The upper bounds `[2, 2, 5]` of the three-clock example. -/
def ver011_ub3 : List Bound := [((2 : ℚ) : Bound), ((2 : ℚ) : Bound), ((5 : ℚ) : Bound)]

/-- A `3 × 3` matrix of zeros. -/
def ver011_Z : NMat := fun _ _ => ((0 : ℚ) : Bound)

/-- The same matrix with no bound on `θ 1 - θ 2`: it agrees with `ver011_Z` on every
projection (row and column 0) and differs in a difference bound. -/
def ver011_Z12 : NMat := fun a b => if a = 1 ∧ b = 2 then ⊤ else ((0 : ℚ) : Bound)

/-- The zero zone holds the valuation `0`. -/
theorem ver011_Z_sat (d : Nat) : ∃ θ, SatN d ver011_Z θ :=
  ⟨fun _ => 0, fun _ _ _ _ => by simp [ver011_Z]⟩

/-- `ver011_Z12` holds the valuation `0`. -/
theorem ver011_Z12_sat (d : Nat) : ∃ θ, SatN d ver011_Z12 θ :=
  ⟨fun _ => 0, fun i j _ _ => by
    unfold ver011_Z12
    split_ifs
    · exact le_top
    · simp⟩

/-- ✓ The reference on the test derivation and on each criterion. AC1: the one-clock zone
`[1, 2]` holds the firing time `3/2` and not `3`. AC2: the zone `[2, 1]` is reported empty and
the zone `[1, 2]` is not. AC3: three clocks in `[1, 2]`, `[1, 2]`, `[0, 5]` at `3/2`, `2`, `4`;
clock 0 fires, clocks 1 and 2 persist with `1/2` and `5/2` left and a new clock in `[0, 1]` is at
`1`: the successor holds these times. AC4: the permutation `[1, 0]` puts `D 2 1` at `(1, 2)`,
and two zones that agree on every projection but differ in a difference bound get two keys. -/
@[evidence nonvacuous VER_011]
theorem VER_011_nonvacuous :
    SatN 2 (refZoneLib.create 1 [1] [((2 : ℚ) : Bound)]) (fun i => if i = 1 then 3 / 2 else 0) ∧
    ¬ SatN 2 (refZoneLib.create 1 [1] [((2 : ℚ) : Bound)]) (fun i => if i = 1 then 3 else 0) ∧
    refZoneLib.empty 2 (createPre 1 [2] [((1 : ℚ) : Bound)]) ∧
    ¬ refZoneLib.empty 2 (createPre 1 [1] [((2 : ℚ) : Bound)]) ∧
    SatN 4 (refZoneLib.fire 3 (createPre 3 [1, 1, 0] ver011_ub3) 0 [1, 2] [0] [((1 : ℚ) : Bound)])
      ver011_θ' ∧
    refZoneLib.perm [1, 0] ver011_Z12 1 2 = ver011_Z12 2 1 ∧
    ¬ refZoneLib.sameKey 3 ver011_Z ver011_Z12 := by
  obtain ⟨h1, -, -, h4, h5, h6, h7, h8⟩ := VER_011_reference
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (h1 1 [1] _ _ rfl rfl).mpr fun i hi => ?_
    obtain rfl : i = 0 := by omega
    refine ⟨by norm_num, ?_⟩
    simp only [List.getD_cons_zero]
    rw [WithTop.coe_le_coe]
    norm_num
  · intro h
    have := ((h1 1 [1] _ _ rfl rfl).mp h 0 (by omega)).2
    simp only [List.getD_cons_zero] at this
    rw [WithTop.coe_le_coe] at this
    norm_num at this
  · refine (h5 2 _ (by omega) (fun i hi => ?_) (ver011_createPre_ms (fun x hx => ?_)
      (fun x hx => ?_))).mpr ?_
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · simp [createPre]
      · simp [createPre]
    · simp only [List.mem_singleton] at hx
      subst hx
      exact_mod_cast ver011_gridQ_int 2
    · simp only [List.mem_singleton] at hx
      subst hx
      exact_mod_cast ver011_wholeMs_int 1
    · rintro ⟨θ, hθ⟩
      have := (ver011_create.mp hθ 0 (by omega))
      simp only [List.getD_cons_zero] at this
      obtain ⟨ha, hb⟩ := this
      rw [WithTop.coe_le_coe] at hb
      linarith
  · intro h
    exact h4 2 _ h ⟨fun i => if i = 1 then 3 / 2 else 0, ver011_create.mpr fun i hi => by
      obtain rfl : i = 0 := by omega
      refine ⟨by norm_num, ?_⟩
      simp only [List.getD_cons_zero]
      rw [WithTop.coe_le_coe]
      norm_num⟩
  · refine h6 3 _ 0 [1, 2] [0] _ ver011_θ ver011_θ' (by omega) (by decide) rfl
      (ver011_create.mpr fun i hi => ?_) (fun i hi => ?_) (fun p hp => ?_) (fun j hj => ?_)
    · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals
        refine ⟨by norm_num [ver011_θ], ?_⟩
        simp only [ver011_ub3, List.getD_cons_zero, List.getD_cons_succ]
        rw [WithTop.coe_le_coe]
        norm_num [ver011_θ]
    · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals norm_num [ver011_θ]
    · obtain rfl | rfl : p = 0 ∨ p = 1 := by
        simp only [List.length_cons, List.length_nil] at hp
        omega
      all_goals norm_num [ver011_θ, ver011_θ']
    · obtain rfl : j = 0 := by
        simp only [List.length_cons, List.length_nil] at hj
        omega
      refine ⟨by norm_num [ver011_θ'], ?_⟩
      simp only [List.getD_cons_zero, List.length_cons, List.length_nil]
      rw [WithTop.coe_le_coe]
      norm_num [ver011_θ']
  · exact (h7 2 [1, 0] ver011_Z12 (by decide) (ver011_Z12_sat 3)).2.2 0 1 (by omega) (by omega)
  · intro h
    have := (h8 3 _ _ (ver011_Z_sat 3) (ver011_Z12_sat 3)
      (fun i j _ _ => by simpa [ver011_Z] using ver011_wholeMs_int 0)
      (fun i j _ _ => by
        unfold ver011_Z12
        split_ifs
        · exact Novel.TimedScg.gridB_top
        · simpa using ver011_wholeMs_int 0)).mp h 1 2 (by omega) (by omega)
    simp [ver011_Z, ver011_Z12] at this

/-- **The key line needs whole milliseconds** (ruling D58): two one-entry zones whose bound
differs by a tenth of a millisecond (`0.0001 s` against `0.0002 s`) get one reference key, as
the runtimes' three-decimal rendering gives them one, although the matrices differ. -/
theorem VER_011_key_submillisecond :
    refZoneLib.sameKey 1 (fun _ _ => ((1 / 10000 : ℚ) : Bound))
        (fun _ _ => ((2 / 10000 : ℚ) : Bound)) ∧
      ((1 / 10000 : ℚ) : Bound) ≠ ((2 / 10000 : ℚ) : Bound) := by
  have heps : (0 : ℚ) ≤ ver011_eps := by norm_num [ver011_eps]
  have hs : ∀ q : ℚ, 0 ≤ q → SatN 1 (fun _ _ => ((q : ℚ) : Bound)) (fun _ => 0) :=
    fun q hq _ _ _ _ => by
      rw [sub_self, WithTop.coe_le_coe]
      exact hq
  refine ⟨Or.inr ⟨Novel.TimedScg.not_flagged_of_sat heps (hs _ (by norm_num)),
    Novel.TimedScg.not_flagged_of_sat heps (hs _ (by norm_num)), ?_⟩, ?_⟩
  · funext i j
    unfold ver011_key
    split_ifs
    · simp only [ver011_render, WithTop.map_coe]
      rw [ver011_floor_zero (by norm_num) (by norm_num),
        ver011_floor_zero (by norm_num) (by norm_num)]
    · rfl
  · rw [Ne, WithTop.coe_inj]
    norm_num

/-- Two clocks, clock 0 in `[5, 5]` and clock 1 in `[0, 1]`: clock 0 cannot fire first. -/
def ver011_late : NMat := createPre 2 [5, 0] [((5 : ℚ) : Bound), ((1 : ℚ) : Bound)]

/-- ✓ **The reference keeps Rust's step-2 early return**: firing clock 0 of `ver011_late` (no
persistent and no newly enabled clocks) gives an empty successor, as `fire_transition` returns
`Dbm::empty_dbm()` when the constrained matrix is flagged. The firing rule allows no firing
time here, so the exact half of AC3 (a later block under D67) holds of the reference on this
zone; a successor built without the constraint would hold the valuation `0`. -/
@[evidence nonvacuous VER_011]
theorem VER_011_fire_first : ¬ ∃ θ, SatN 1 (refZoneLib.fire 2 ver011_late 0 [] [] []) θ := by
  have hfl : FlaggedN ver011_eps 3 (constrainPre 2 0 ver011_late) := by
    refine (ver011_empty_exact (by omega) (fun i hi => ?_) (fun a b _ _ => ?_)).mpr ?_
    · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals simp [constrainPre, ver011_late, createPre]
    · refine Novel.TimedScg.gridM_constrainPre
        (Novel.TimedScg.gridM_createPre (fun x hx => ?_) (fun x hx => ?_)) a b
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact_mod_cast ver011_gridQ_int 5
        · exact_mod_cast ver011_gridQ_int 0
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact_mod_cast ver011_wholeMs_int 5
        · exact_mod_cast ver011_wholeMs_int 1
    · rintro ⟨θ, hθ⟩
      have a := hθ 0 1 (by omega) (by omega)
      have b := hθ 2 0 (by omega) (by omega)
      have c := hθ 1 2 (by omega) (by omega)
      have e1 : constrainPre 2 0 ver011_late 0 1 = ((-5 : ℚ) : Bound) := by
        simp [constrainPre, ver011_late, createPre]
      have e2 : constrainPre 2 0 ver011_late 2 0 = ((1 : ℚ) : Bound) := by
        simp [constrainPre, ver011_late, createPre]
      have e3 : constrainPre 2 0 ver011_late 1 2 = ((0 : ℚ) : Bound) := by
        simp [constrainPre, ver011_late, createPre]
      rw [e1, WithTop.coe_le_coe] at a
      rw [e2, WithTop.coe_le_coe] at b
      rw [e3, WithTop.coe_le_coe] at c
      linarith
  rintro ⟨θ, hθ⟩
  have e : refZoneLib.fire 2 ver011_late 0 [] [] [] = ver011_emptyMat := by
    show (if 2 ≤ 0 ∨ FlaggedN ver011_eps (2 + 1) ver011_late ∨
      FlaggedN ver011_eps (2 + 1) (constrainPre 2 0 ver011_late) then ver011_emptyMat
      else _) = _
    rw [if_pos (Or.inr (Or.inr hfl))]
  rw [e] at hθ
  have := hθ 0 0 (by omega) (by omega)
  simp only [ver011_emptyMat, WithTop.coe_le_coe] at this
  norm_num at this

/-- ✓ **Every flagged zone has one key**, as `zone_key` returns `DBM[empty]` in all three
runtimes: the one-entry zones `θ 0 - θ 0 ≤ -1` and `θ 0 - θ 0 ≤ -2` hold no firing time, differ,
and share a key. Line 8 speaks of zones that hold firing times, so it allows this. -/
@[evidence nonvacuous VER_011]
theorem VER_011_empty_one_key :
    refZoneLib.sameKey 1 (fun _ _ => ((-1 : ℚ) : Bound)) (fun _ _ => ((-2 : ℚ) : Bound)) ∧
      ((-1 : ℚ) : Bound) ≠ ((-2 : ℚ) : Bound) := by
  have hf : ∀ z : ℤ, z < 0 → FlaggedN ver011_eps 1 (fun _ _ => (((z : ℚ)) : Bound)) := fun z hz =>
    (ver011_empty_exact (by omega) (fun _ _ => WithTop.coe_ne_top)
      (fun _ _ _ _ => ver011_wholeMs_int z)).mpr fun ⟨θ, hθ⟩ => by
        have := hθ 0 0 (by omega) (by omega)
        rw [WithTop.coe_le_coe, sub_self] at this
        have : (0 : ℤ) ≤ z := by exact_mod_cast this
        omega
  refine ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
  · exact_mod_cast hf (-1) (by omega)
  · exact_mod_cast hf (-2) (by omega)
  · rw [Ne, WithTop.coe_inj]
    norm_num

/-! ## Wrong libraries -/

/-- A `create` that drops the upper bounds. -/
def ver011_noUpper : ZoneLib :=
  { refZoneLib with create := fun n lb _ => canonN (n + 1) (createPre n lb []) }

/-- ✗ Line 1 forbids a `create` that drops the upper bounds: the clock `[0, 1]` at `2`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_noUpper : ¬ VER_011 ver011_noUpper := by
  intro h
  have hs : SatN 2 (ver011_noUpper.create 1 [0] [((1 : ℚ) : Bound)])
      (fun i => if i = 1 then 2 else 0) :=
    satN_canonN.mpr (ver011_create.mpr fun i hi => by
      obtain rfl : i = 0 := by omega
      exact ⟨by norm_num, by simp⟩)
  have := ((h.1 1 [0] _ _ rfl rfl).mp hs 0 (by omega)).2
  simp only [List.getD_cons_zero] at this
  rw [WithTop.coe_le_coe] at this
  norm_num at this

/-- A canonicalisation that resets the diagonal to `0`. -/
def ver011_diagReset : ZoneLib :=
  { refZoneLib with canon := fun d D a b => if a = b then 0 else canonN d D a b }

/-- ✗ Line 2 forbids a canonicalisation that resets the diagonal: it turns the empty one-entry
zone `θ 0 - θ 0 ≤ -1` into a zone that holds every valuation. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_diagReset : ¬ VER_011 ver011_diagReset := by
  intro h
  have := (h.2.1 1 (fun _ _ => ((-1 : ℚ) : Bound)) (fun _ => 0)).mp (fun i j hi hj => by
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    simp [ver011_diagReset]) 0 0 (by omega) (by omega)
  rw [WithTop.coe_le_coe] at this
  norm_num at this

/-- A canonicalisation that returns the matrix unchanged. -/
def ver011_noClose : ZoneLib := { refZoneLib with canon := fun _ D => D }

/-- ✗ Line 3 forbids a canonicalisation that does not close the matrix: `θ 1 - θ 2` unbounded
although the detour through the reference bounds it by `0`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_noClose : ¬ VER_011 ver011_noClose := by
  intro h
  have := h.2.2.1 3 ver011_Z12 (ver011_Z12_sat 3) 1 2 0 (by omega) (by omega) (by omega)
  simp [ver011_noClose, ver011_Z12] at this

/-- A flag raised on a zero diagonal. -/
def ver011_zeroDiag : ZoneLib :=
  { refZoneLib with empty := fun d D => ∃ i, i < d ∧ canonN d D i i ≤ 0 }

/-- ✗ Line 4 forbids a flag raised on a zero diagonal: it reports the zero zone empty, which holds
the valuation `0`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_zeroDiag : ¬ VER_011 ver011_zeroDiag := by
  intro h
  refine h.2.2.2.1 1 ver011_Z ⟨0, by omega, ?_⟩ ⟨fun _ => 0, fun i j _ _ => by simp [ver011_Z]⟩
  exact (canonN_le ver011_Z (by omega) (by omega)).trans (by simp [ver011_Z])

/-- A flag never raised. -/
def ver011_neverEmpty : ZoneLib := { refZoneLib with empty := fun _ _ => False }

/-- ✗ Line 5 forbids a flag never raised: the one-entry zone `θ 0 - θ 0 ≤ -1` (a whole number of
milliseconds, a finite reference row) has no solution. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_neverEmpty : ¬ VER_011 ver011_neverEmpty := by
  intro h
  refine (h.2.2.2.2.1 1 (fun _ _ => ((-1 : ℚ) : Bound)) (by omega)
    (fun _ _ => WithTop.coe_ne_top) (fun _ _ _ _ => by exact_mod_cast ver011_wholeMs_int (-1))).mpr
    ?_
  rintro ⟨θ, hθ⟩
  have := hθ 0 0 (by omega) (by omega)
  rw [WithTop.coe_le_coe] at this
  norm_num at this

/-- `fireMat` with the persistent clocks' old lower bounds (`C 0 o`) in place of the time they
have left after the fired clock (`C f o`). -/
def ver011_fireMatNoShift (C : NMat) (k : Nat) (ps : List Nat) (lb : List ℚ) (ub : List Bound) :
    NMat := fun a b =>
  if a = 0 ∧ 1 ≤ b ∧ b ≤ ps.length then min 0 (C 0 (ps.getD (b - 1) 0 + 1))
  else fireMat C k ps lb ub a b

/-- A successor that keeps the persistent clocks' old lower bounds. -/
def ver011_noShift : ZoneLib :=
  { refZoneLib with
    fire := fun n D k ps lb ub => canonN (ps.length + lb.length + 1)
      (ver011_fireMatNoShift (canonN (n + 1) (constrainPre n k D)) k ps lb ub) }

/-- ✗ Line 6 forbids a successor that keeps a persistent clock's old lower bound: clocks in
`[1, 2]` at `3/2` and `2`, clock 0 fires, and clock 1 has `1/2` left, below its old lower bound
`1`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_noShift : ¬ VER_011 ver011_noShift := by
  intro h
  let D := createPre 2 [1, 1] [((2 : ℚ) : Bound), ((2 : ℚ) : Bound)]
  let θ : Nat → ℚ := fun i => if i = 1 then 3 / 2 else if i = 2 then 2 else 0
  let θ' : Nat → ℚ := fun i => if i = 1 then 1 / 2 else 0
  have hs := satN_canonN.mp (h.2.2.2.2.2.1 2 D 0 [1] [] [] θ θ' (by omega) (by simp) rfl
    (ver011_create.mpr fun i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      all_goals
        refine ⟨by norm_num [θ], ?_⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [WithTop.coe_le_coe]
        norm_num [θ])
    (fun i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      all_goals norm_num [θ])
    (fun p hp => by
      obtain rfl : p = 0 := by simpa using hp
      norm_num [θ, θ'])
    (fun j hj => absurd hj (by simp)))
  have e := hs 0 1 (by simp) (by simp)
  have h1 : ver011_fireMatNoShift (canonN (2 + 1) (constrainPre 2 0 D)) 0 [1] [] [] 0 1 =
      min 0 (canonN (2 + 1) (constrainPre 2 0 D) 0 2) := by
    simp [ver011_fireMatNoShift]
  have h2 : canonN (2 + 1) (constrainPre 2 0 D) 0 2 ≤ ((-1 : ℚ) : Bound) :=
    (canonN_le _ (by omega) (by omega)).trans (by simp [constrainPre, D, createPre])
  rw [h1] at e
  have := (e.trans (min_le_right _ _)).trans h2
  rw [WithTop.coe_le_coe] at this
  norm_num [θ'] at this

/-- A permutation that does not move the matrix. -/
def ver011_noMove : ZoneLib := { refZoneLib with perm := fun _ D => D }

/-- ✗ Line 7 forbids a permutation that does not move the matrix: under `[1, 0]` the bound at
`(1, 2)` must be the old `(2, 1)`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_noMove : ¬ VER_011 ver011_noMove := by
  intro h
  have := (h.2.2.2.2.2.2.1 2 [1, 0] ver011_Z12 (by decide) (ver011_Z12_sat 3)).2.2 0 1
    (by omega) (by omega)
  simp [ver011_noMove, ver011_Z12] at this

/-- A permutation that keeps the old reference entry `D 0 0` in place of writing `0`. -/
def ver011_keepRef : ZoneLib :=
  { refZoneLib with perm := fun ord D a b => if a = 0 ∧ b = 0 then D 0 0 else permMat ord D a b }

/-- ✗ Line 7 forbids a permutation that keeps the old reference entry: the zone with every bound
`1` holds the valuation `0`, and its permutation must have `0` at `(0, 0)`, not `1`. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_keepRef : ¬ VER_011 ver011_keepRef := by
  intro h
  have := (h.2.2.2.2.2.2.1 0 [] (fun _ _ => ((1 : ℚ) : Bound)) (by decide)
    ⟨fun _ => 0, fun _ _ _ _ => by simp⟩).1
  simp [ver011_keepRef] at this

/-- A key over the projections alone: row and column 0. -/
def ver011_projectionKey : ZoneLib :=
  { refZoneLib with sameKey := fun d D D' => ∀ i, i < d → D 0 i = D' 0 i ∧ D i 0 = D' i 0 }

/-- ✗ Line 8 forbids a key over the projections alone: the zero zone and the zone with no bound
on `θ 1 - θ 2` agree on every projection and differ in a difference bound. -/
@[evidence forbids VER_011]
theorem VER_011_forbids_projectionKey : ¬ VER_011 ver011_projectionKey := by
  intro h
  have := (h.2.2.2.2.2.2.2 3 ver011_Z ver011_Z12 (ver011_Z_sat 3) (ver011_Z12_sat 3)
    (fun _ _ _ _ => by simpa [ver011_Z] using ver011_wholeMs_int 0)
    (fun i j _ _ => by
      unfold ver011_Z12
      split_ifs
      · exact Novel.TimedScg.gridB_top
      · simpa using ver011_wholeMs_int 0)).mp
    (fun i _ => by simp [ver011_Z, ver011_Z12]) 1 2 (by omega) (by omega)
  simp [ver011_Z, ver011_Z12] at this

end Libpetri.Spec
