import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Novel.RouteA.Simulate
import Libpetri.Spec.Text.VER_005

set_option linter.missingDocs true

/-!
# VER-005: P-invariant computation (`spec/07-verification.md`)

The verifier computes conservation laws `w · M = c` of the verified net from its incidence
matrix and lists them in the result. The requirement is a predicate over one function:

* `I : InvFn`, the invariant computation: `I rows envs n a0` is the list of reported pairs
  `(w, c)` (weights and constant) for the flat net whose deposit rows are `rows` (`n` places),
  the environment places `envs` into which the verifier models injection ([VER-006]) and the
  initial marking `a0`.

Line 1 is "computed from the incidence matrix" on the reporting side: every reported vector is
nonzero and zero on every column of the matrix. Line 2 is the conservation the definition
promises: `w · M = c` on every marking reachable in the untimed abstraction of the verified net,
with injection (`ReachADInj`, integer posts, so a timeout row that forwards two tokens is
covered). Line 2 forces zero weight on every injected place (`ver005_conserves_env`), which is
the injector column of `incidence_matrix.rs` `from_flat_net`. Line 3 is the computing side: on a
net with a transition and without reset, `All` or `AtLeast` arcs, every 0/1 vector that is zero
on every column (the injector columns included) is a rational combination of the reported
vectors, so a computation that finds nothing is not a P-invariant computation.

The witness is `refPInv`: any candidate source, with the all-zero row skipped as the elimination
skips it, filtered by the runtimes' exact gate (`validate_invariants_exact`: `y·C = 0` on every
column, zero weight on every consume-all, `AtLeast` and reset place, the constant recomputed as
`y·M0`), instantiated with the enumeration of the 0/1 vectors as its source. `refPInv_sound`
shows the gate makes every source meet lines 1 and 2, which is the runtimes' argument: the
null-space elimination is unchecked, the gate is the backstop. Line 3 holds of the enumeration
(`ver005_units_complete`). The wrong models are: four computations killed by line 2 (no H1 guard
on a consume-all place, no H1 guard on a reset place, no injector column, a wrong constant); the
reachability reading of the definition, killed by line 1's columns; the trivial law `0 · M = 0`,
killed by line 1's nonzero clause; the computation that reports nothing and the one that reports
nothing once a place is injected, killed by line 3.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.RouteA Libpetri.Novel.LinearBound

/-! ## The model -/

/-- An invariant computation: `I rows envs n a0` lists the reported P-invariants, each a weight
vector and its constant, of the flat net with the deposit rows `rows` and `n` places, the
environment places `envs` into which injection is modelled and the initial marking `a0`. -/
abbrev InvFn : Type :=
  List (Transition × Deposit) → List PlaceId → Nat → AMarking → List (Weight × Int)

/-- The exact gate of the runtimes (`validate_invariants_exact`, `p_invariant.rs`): for every
row, zero weight on the row's reset and consume-all places (H1, the [VER-007] guard) and a zero
incidence column (H2); zero weight on every injected place (the injector columns); the constant
equal to `y·M0`. -/
def ver005_gate (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat)
    (a0 : AMarking) (yc : Weight × Int) : Bool :=
  rows.all (fun tr =>
      (List.range n).all (fun p =>
        !(tr.1.resets.contains p || consumeAllAt tr.1 p) || decide (yc.1 p = 0)) &&
      decide (dotIncD yc.1 tr n = 0)) &&
    envs.all (fun p => decide (yc.1 p = 0)) &&
    decide (yc.2 = dot yc.1 a0 n)

/-- Some weight below `n` is nonzero: the elimination never emits the all-zero row
(`p_invariant.rs` `compute_p_invariants`, `if weights.iter().all(|&w| w == 0) { continue; }`;
Java `PInvariantComputer`, TS `p-invariant-computer.ts`: `if (!hasPositive && !hasNegative)
continue`). -/
def ver005_nonzero (n : Nat) (y : Weight) : Bool :=
  (List.range n).any fun p => y p != 0

/-- The reference computation: the nonzero candidates of a source, filtered by the exact gate.
The source stands for the unchecked null-space elimination (`compute_p_invariants`) or the
semiflow enumeration of [VER-007]; whatever it returns, only what the gate accepts is
reported. -/
def refPInv (src : InvFn) : InvFn := fun rows envs n a0 =>
  (src rows envs n a0).filter fun yc => ver005_nonzero n yc.1 && ver005_gate rows envs n a0 yc

#spec_witness refPInv

/-- The indicator vector of a list of places. -/
def ver005_vec (s : List PlaceId) : Weight := fun p => if p ∈ s then 1 else 0

/-- A candidate source: every 0/1 vector over the `n` places, with its constant at `a0`. -/
def ver005_units : InvFn := fun _ _ n a0 =>
  (List.range n).sublists.map fun s => (ver005_vec s, dot (ver005_vec s) a0 n)

/-! ## VER-005: P-invariant computation -/

requirement VER_005
  id "VER-005"
  title "P-Invariant Computation"
  kind F
  scope "the SMT pipeline's invariant phase, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_005.s1, VER_005.s2, VER_005.s3
  reading "For every invariant computation I, all deposit rows rows, environment places envs, place counts n and initial markings a0:"
          "every pair (w, c) in I rows envs n a0 has a nonzero weight below n, and the product of w with the incidence column of every row is zero (dotIncD);"
          "every pair (w, c) in I rows envs n a0 has w · a = c for every marking a reachable from a0 over rows with injection into envs (ReachADInj);"
          "if rows is not empty and no row has a reset or consume-all place below n, then every vector w with weights 0 and 1, zero from n on, zero on the incidence column of every row and zero on every place in envs, is, scaled by some nonzero integer k, an integer combination of weight vectors reported in I rows envs n a0."
  assumes "The verified net is its flat rows: one deposit row per flat transition and outcome, with the integer post vector the encoder writes (ForwardDeposit.flatRows, fireAD), after the in-flight split of VER-004 and after the Arrivals rewrite of VER-006, so `rows` is the net the matrix is built from and `n` its place count. A forward that drains its source (VER-001 F3) has no row; the computation is not run on such a net, and the statement says nothing about it. Reachability is the untimed atomic abstraction (ReachADInj): firings fire atomically, so the markings of an executor with an action in flight, whose consumed tokens are in no place, are not among them (clash ver-a#9, the D20 wording 'reachable in the untimed abstraction of the verified net', which the spec edit also applies to the prose definition and to AC2). The executor's own reachable markings are tied to this abstraction by VER-004 (Proposition 1, forward_reachability_simulated) and, for the named reference, by Reference.Link.reach_iff_reachAD."
          "Injection is unbounded in ReachADInj. Under Bounded(k) the verifier caps it, so the capped markings are a subset and line 2 holds on them; under AlwaysAvailable the injection is the uncapped one; under Ignore and Arrivals `envs` is empty (VER-006). The injector columns are not a separate line: line 2 alone forces zero weight on every place in envs below n, because one injection from a0 is a reachable step (ver005_conserves_env). They appear in line 3 as the premise that w is zero on every place in envs. 'Conservation laws (P-invariants) derived from the closed net MUST NOT be applied to injected environment places' is VER-006's sentence; here a computation without the injector columns is killed by line 2 (VER_005_forbids_noInjector), and one that avoids that by reporting nothing once a place is injected is killed by line 3 (VER_005_forbids_noEnvColumns)."
          "The first quoted sentence (AC1, 'P-invariants are computed from the incidence matrix') is lines 1 and 3, and the third quoted sentence is line 3. Line 1 is the reporting side: each reported vector is zero on every column of the matrix. Line 3 is the computing side, stated where every runtime meets it: on a net with a transition and without reset, All or AtLeast arcs the gate drops nothing, so the reported vectors are the whole null-space basis the elimination returns, and every 0/1 vector of the null space is a rational combination of them. On a net with such an arc the gate may drop basis vectors whose combinations it would accept, so no completeness is claimed there, and reporting nothing is allowed. A net with no transition and no injected place has an empty matrix and every runtime returns no invariant (`rows == 0 || cols == 0`, `P == 0 || T == 0`), hence the premise that rows is not empty, which is stricter than needed when a place is injected. Line 3 claims the 0/1 vectors only, the conservation of a set of places such as the test derivation's token conservation; the runtimes span the whole null space on such nets, but this block's witness enumerates 0/1 vectors and has no verified elimination, so the wider claim is not a line. Arithmetic is exact in the model; a runtime row whose elimination overflows is dropped by the gate's overflow check, an implementation limit outside the statement. A vector that is constant on the reachable markings without being zero on the columns (the reading of the prose definition 'w · M = constant' alone) satisfies line 2 and is killed by line 1 (VER_005_mutant_reachOnly). The computation that reports nothing satisfies lines 1 and 2 and is killed by line 3 (VER_005_mutant_none). The trigger 'builds its CHC encoding' is the pipeline's (VER-001, VER-003): a route that builds no encoding computes none, and the result says so (VER-003 AC4)."
          "The second quoted sentence (AC2, 'Each invariant satisfies sum(weights[i] * marking[i]) = constant') is lines 1 and 2. Line 2 at the initial marking gives c = w · M0, the constant the runtimes recompute; a computation that reports another constant is killed (VER_005_forbids_constZero). 'Nonzero' is the elimination's skip of the all-zero row in all three runtimes; the trivial law 0 · M = 0 satisfies lines 2 and 3 and is killed by line 1 (VER_005_mutant_zero). Line 1 alone is not enough for line 2: a vector with weight on a consume-all, AtLeast or reset place can be zero on every column and still change along a firing, because the fire relation is not linear there (Strengthening.lean H1). The gate that drops such vectors is VER-007's ([VER-007] 'exact gate'); here the computations without it are killed by line 2 (VER_005_forbids_noH1, VER_005_forbids_noReset)."
          "AC3 ('Invariants are reported in the verification result') is the sentence '*When* the verifier computes P-invariants, it *shall* list each one it reports in the verification result, with its weights and its constant.' It is about the result record, kind N, and is not a line of this kind F block: the result's invariant list holds the pairs this computation reports, after the semiflow union of VER-007, in the canonical order of VER-013. That an empty list off the SMT route means 'not computed' is VER-003 AC4. VER-003's line 8 (the block VER_003) says that every P-invariant a result reports, on any route, is conserved on every marking reachable in the verified net; it reads the result's list and not this computation, so that the list holds exactly the pairs this computation reports is carried by this assumes sentence only."
          "The test derivation ('Net with known invariant (e.g., token conservation); verify invariant is discovered') is line 3 on the net t: one(p0) -> p1, where p0 + p1 is a 0/1 vector of the null space: a computation that does not report it, or a multiple of it, is killed (VER_005_mutant_none). On the reference the witness reports p0 + p1 = 1 (VER_005_nonvacuous)."
          "The prose 'P-invariants provide structural proofs that do not require state enumeration' is a motivation, not a requirement; the use of the laws in the encoding is VER-007's strengthening (invariant_strengthening_sound)."
  signoff "2026-11-13 31974fa0fc93c0df ai"
  statement : InvFn → Prop :=
    fun I =>
      (∀ rows envs n a0, ∀ yc ∈ I rows envs n a0,
        (∃ p < n, yc.1 p ≠ 0) ∧ ∀ tr ∈ rows, dotIncD yc.1 tr n = 0) ∧
      (∀ rows envs n a0, ∀ yc ∈ I rows envs n a0, ∀ a,
        ReachADInj rows envs a0 a → dot yc.1 a n = yc.2) ∧
      (∀ rows envs (n : Nat) a0, rows ≠ [] →
        (∀ tr ∈ rows, ∀ p < n, tr.1.resets.contains p = false ∧ consumeAllAt tr.1 p = false) →
        ∀ w : Weight, (∀ p, w p = 0 ∨ w p = 1) → SupportBelow n w →
          (∀ tr ∈ rows, dotIncD w tr n = 0) → (∀ p ∈ envs, w p = 0) →
          ∃ k : Int, k ≠ 0 ∧ ∃ cs : List (Int × (Weight × Int)),
            (∀ x ∈ cs, x.2 ∈ I rows envs n a0) ∧
            ∀ p < n, k * w p = (cs.map fun x => x.1 * x.2.1 p).sum)

/- The pinned readable form of VER-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_005 : InvFn → Prop :=
fun I =>
  (∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking),
      ∀ yc ∈ I rows envs n a0, (∃ p < n, yc.1 p ≠ 0) ∧ ∀ tr ∈ rows, dotIncD yc.1 tr n = 0) ∧
    (∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking),
        ∀ yc ∈ I rows envs n a0, ∀ (a : AMarking), ReachADInj rows envs a0 a → dot yc.1 a n = yc.2) ∧
      ∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking),
        rows ≠ [] →
          (∀ tr ∈ rows, ∀ p < n, tr.1.resets.contains p = false ∧ consumeAllAt tr.1 p = false) →
            ∀ (w : Weight),
              (∀ (p : PlaceId), w p = 0 ∨ w p = 1) →
                SupportBelow n w →
                  (∀ tr ∈ rows, dotIncD w tr n = 0) →
                    (∀ p ∈ envs, w p = 0) →
                      ∃ k,
                        k ≠ 0 ∧
                          ∃ cs,
                            (∀ x ∈ cs, x.2 ∈ I rows envs n a0) ∧
                              ∀ p < n, k * w p = (List.map (fun x => x.1 * x.2.1 p) cs).sum
-/
#guard_msgs in #print VER_005

/-- Line 2 alone: every reported pair is conserved on the reachable markings. The reading of
the prose definition without "from the incidence matrix". -/
def ver005_conserves (I : InvFn) : Prop :=
  ∀ rows envs n a0, ∀ yc ∈ I rows envs n a0, ∀ a,
    ReachADInj rows envs a0 a → dot yc.1 a n = yc.2

/-- Lines 1 and 2: what the gate guarantees for any candidate source. -/
def ver005_sound (I : InvFn) : Prop :=
  (∀ rows envs n a0, ∀ yc ∈ I rows envs n a0,
    (∃ p < n, yc.1 p ≠ 0) ∧ ∀ tr ∈ rows, dotIncD yc.1 tr n = 0) ∧
  ver005_conserves I

/-! ## Injection -/

/-- One injection into `p` adds `y p` to `y·M` when `p` is below `n`. -/
theorem ver005_dot_inj (y : Weight) (a : AMarking) (n p : Nat) :
    dot y (fun q => if q == p then a q + 1 else a q) n =
      dot y a n + if p < n then y p else 0 := by
  rw [dot_eq_isum, dot_eq_isum]
  have hf : (fun q => y q * ((if q == p then a q + 1 else a q : Nat) : Int)) =
      fun q => y q * (a q : Int) + (if q = p then y q else 0) := by
    funext q
    by_cases hq : q = p
    · subst hq; simp; ring
    · simp [hq]
  rw [hf, isum_add]
  congr 1
  unfold isum
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

/-- One injection leaves `y·M` unchanged when `y` is zero on the injected place. -/
theorem ver005_dot_inject {y : Weight} {a : AMarking} {n p : Nat} (hp : y p = 0) :
    dot y (fun q => if q == p then a q + 1 else a q) n = dot y a n := by
  rw [ver005_dot_inj]
  split <;> simp [hp]

/-- **The injector columns follow from line 2.** A conserved vector is zero on every injected
place below `n`: one injection from `a0` is reachable and adds `y p` to the sum. -/
@[evidence cites "VER-005" "the injector column of each environment place: a vector conserved on every marking reachable with injection has zero weight on every injected place, so the injector columns are implied by line 2"]
theorem ver005_conserves_env {I : InvFn} (h : ver005_conserves I) :
    ∀ rows envs n a0, ∀ yc ∈ I rows envs n a0, ∀ p ∈ envs, p < n → yc.1 p = 0 := by
  intro rows envs n a0 yc hy p hp hpn
  have h0 := h rows envs n a0 yc hy a0 Relation.ReflTransGen.refl
  have h1 := h rows envs n a0 yc hy _ (Relation.ReflTransGen.single (Or.inr ⟨p, hp, rfl⟩))
  rw [ver005_dot_inj, if_pos hpn] at h1
  omega

/-! ## The reference -/

/-- `ver005_nonzero` is "some weight below `n` is nonzero". -/
theorem ver005_nonzero_iff {n : Nat} {y : Weight} :
    ver005_nonzero n y = true ↔ ∃ p < n, y p ≠ 0 := by
  simp [ver005_nonzero]

/-- What the exact gate gives: H1 and H2 on every row, zero weight on the injected places, the
constant at the initial marking. -/
theorem ver005_gate_spec {rows : List (Transition × Deposit)} {envs : List PlaceId} {n : Nat}
    {a0 : AMarking} {yc : Weight × Int} (hg : ver005_gate rows envs n a0 yc = true) :
    (∀ tr ∈ rows, ZeroOnNonlinear yc.1 tr.1 n ∧ dotIncD yc.1 tr n = 0) ∧
    (∀ p ∈ envs, yc.1 p = 0) ∧ yc.2 = dot yc.1 a0 n := by
  simp only [ver005_gate, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hrows, henv⟩, hc⟩ := hg
  refine ⟨fun tr htr => ⟨fun p hp hnl => ?_, (hrows tr htr).2⟩, henv, hc⟩
  have := (hrows tr htr).1 p (List.mem_range.mpr hp)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_true_eq] at this
  rcases this with ⟨hr', hc'⟩ | h0
  · rcases hnl with h' | h'
    · rw [hr'] at h'; exact absurd h' (by simp)
    · rw [hc'] at h'; exact absurd h' (by simp)
  · exact h0

/-- **The exact gate makes every candidate source sound.** Whatever the source returns, the
pairs reported satisfy lines 1 and 2 of VER-005: the nonzero clause is the skipped all-zero row,
the columns are H2, and line 2 is `laws_conserved` extended to injection steps by
`ver005_dot_inject`. -/
@[evidence cites "VER-005" "AC1 and AC2: whatever candidates the null-space elimination returns, the exact gate (H1, a zero incidence column, zero weight on every injected place, the constant recomputed as y.M0) reports only nonzero vectors zero on every column and conserved on every marking reachable over the deposit rows with injection"]
theorem refPInv_sound (src : InvFn) : ver005_sound (refPInv src) := by
  constructor
  · intro rows envs n a0 yc hy
    obtain ⟨-, hg⟩ := List.mem_filter.mp hy
    rw [Bool.and_eq_true] at hg
    obtain ⟨hl, -, -⟩ := ver005_gate_spec hg.2
    exact ⟨ver005_nonzero_iff.mp hg.1, fun tr htr => (hl tr htr).2⟩
  · intro rows envs n a0 yc hy a hr
    obtain ⟨-, hg⟩ := List.mem_filter.mp hy
    rw [Bool.and_eq_true] at hg
    obtain ⟨hl, henv, hc⟩ := ver005_gate_spec hg.2
    rw [hc]
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      rcases hs with ⟨tr, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
      · exact (dot_fireAD_eq yc.1 (hl tr hmem).1 (hl tr hmem).2 hen).trans ih
      · exact (ver005_dot_inject (henv p hp)).trans ih

/-- The 0/1 vector of a sublist of the places is a candidate of `ver005_units`. -/
theorem ver005_mem_units {rows : List (Transition × Deposit)} {envs : List PlaceId} {n : Nat}
    {a0 : AMarking} {s : List PlaceId} (hs : s.Sublist (List.range n)) :
    (ver005_vec s, dot (ver005_vec s) a0 n) ∈ ver005_units rows envs n a0 :=
  List.mem_map.mpr ⟨s, List.mem_sublists.mpr hs, rfl⟩

/-- **The enumeration is complete for the 0/1 laws of a linear net.** On a net without reset
or consume-all places below `n`, every nonzero 0/1 vector zero on every column and on every
injected place passes the gate, so the reference reports it itself (`k = 1`, one coefficient
1); the zero vector is the empty combination. -/
@[evidence cites "VER-005" "the test derivation: on a net with a transition and without reset, All or AtLeast arcs, every 0/1 conservation law whose vector is zero on every column of the matrix, injector columns included, is among the laws the reference computation reports"]
theorem ver005_units_complete :
    ∀ rows envs (n : Nat) a0, rows ≠ [] →
      (∀ tr ∈ rows, ∀ p < n, tr.1.resets.contains p = false ∧ consumeAllAt tr.1 p = false) →
      ∀ w : Weight, (∀ p, w p = 0 ∨ w p = 1) → SupportBelow n w →
        (∀ tr ∈ rows, dotIncD w tr n = 0) → (∀ p ∈ envs, w p = 0) →
        ∃ k : Int, k ≠ 0 ∧ ∃ cs : List (Int × (Weight × Int)),
          (∀ x ∈ cs, x.2 ∈ refPInv ver005_units rows envs n a0) ∧
          ∀ p < n, k * w p = (cs.map fun x => x.1 * x.2.1 p).sum := by
  intro rows envs n a0 _ hlin w h01 hsup hcol henv
  by_cases hz : ∀ p < n, w p = 0
  · exact ⟨1, one_ne_zero, [], by simp, fun p hp => by simp [hz p hp]⟩
  obtain ⟨q, hq, hwq⟩ : ∃ q < n, w q ≠ 0 :=
    Classical.byContradiction fun hc => hz fun p hp => Classical.byContradiction fun hne =>
      hc ⟨p, hp, hne⟩
  have hvec : ver005_vec ((List.range n).filter fun p => w p == 1) = w := by
    funext p
    unfold ver005_vec
    by_cases hp : p < n
    · rcases h01 p with h | h <;> simp [hp, h]
    · have := hsup p (Nat.not_lt.mp hp)
      simp [hp, this]
  refine ⟨1, one_ne_zero, [(1, (w, dot w a0 n))], ?_, fun p _ => by simp⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · have := ver005_mem_units (rows := rows) (envs := envs) (a0 := a0)
      (List.filter_sublist (p := fun p => w p == 1) (l := List.range n))
    rw [hvec] at this
    exact this
  · rw [Bool.and_eq_true]
    refine ⟨ver005_nonzero_iff.mpr ⟨q, hq, hwq⟩, ?_⟩
    simp only [ver005_gate, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨⟨fun tr htr => ⟨fun p hp => ?_, hcol tr htr⟩, henv⟩, trivial⟩
    obtain ⟨h1, h2⟩ := hlin tr htr p (List.mem_range.mp hp)
    rw [h1, h2]
    rfl

/-- The reference computation satisfies VER-005. -/
@[evidence holds VER_005]
theorem VER_005_reference : VER_005 (refPInv ver005_units) :=
  ⟨(refPInv_sound ver005_units).1, (refPInv_sound ver005_units).2, ver005_units_complete⟩

/-! ## Examples -/

/-- A transition with the given inputs and resets and no other arc. -/
def ver005_t (inputs : List InSpec) (resets : List PlaceId) : Transition :=
  { name := "t", inputs := inputs, inhibitors := [], reads := [], resets := resets }

/-- The token-conservation net of the test derivation: `t: one(p0) -> p1`. -/
def ver005_move : List (Transition × Deposit) :=
  [(ver005_t [⟨0, .one, none⟩] [], [1])]

/-- A count marking from a list of `(place, count)` pairs; unlisted places hold nothing. -/
def ver005_mk (l : List (Nat × Nat)) : AMarking :=
  fun p => ((l.find? (·.1 == p)).map (·.2)).getD 0

/-- The test derivation on the reference: on `t: one(p0) -> p1` with one token in `p0`, the
reference reports `p0 + p1 = 1`. -/
@[evidence nonvacuous VER_005]
theorem VER_005_nonvacuous :
    ∃ yc ∈ refPInv ver005_units ver005_move [] 2 (ver005_mk [(0, 1)]),
      yc.1 0 = 1 ∧ yc.1 1 = 1 ∧ yc.2 = 1 := by
  refine ⟨_, List.mem_filter.mpr ⟨ver005_mem_units (s := [0, 1]) (List.Sublist.refl _), ?_⟩,
    by decide, by decide, ?_⟩
  · decide
  · decide

/-- An indicator vector has weights 0 and 1. -/
theorem ver005_vec_01 (s : List PlaceId) (p : PlaceId) : ver005_vec s p = 0 ∨ ver005_vec s p = 1 := by
  unfold ver005_vec
  split <;> simp

/-- An indicator vector of places below `n` is zero from `n` on. -/
theorem ver005_vec_below {s : List PlaceId} {n : Nat} (h : ∀ p ∈ s, p < n) :
    SupportBelow n (ver005_vec s) := by
  intro p hp
  unfold ver005_vec
  rw [if_neg fun hm => absurd (h p hm) (Nat.not_lt.mpr hp)]

/-- Line 3 fails when the computation reports nothing for a net that has a nonzero vector the
line covers: an empty combination is zero, and `k` times a nonzero weight is not. -/
theorem ver005_empty_misses {I : InvFn} {rows envs n a0} {w : Weight}
    (hI : I rows envs n a0 = []) (hw : ∃ p < n, w p ≠ 0) :
    ¬ ∃ k : Int, k ≠ 0 ∧ ∃ cs : List (Int × (Weight × Int)),
        (∀ x ∈ cs, x.2 ∈ I rows envs n a0) ∧
        ∀ p < n, k * w p = (cs.map fun x => x.1 * x.2.1 p).sum := by
  rintro ⟨k, hk, cs, hcs, hsum⟩
  have hnil : cs = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    have := hcs x hx
    rw [hI] at this
    simp at this
  subst hnil
  obtain ⟨p, hp, hwp⟩ := hw
  have := hsum p hp
  simp at this
  rcases this with h | h
  · exact hk h
  · exact hwp h

/-! ## Wrong models -/

/-- The gate without H1 on consume-all places: the incidence-only reading on an `In::All` net. -/
def ver005_gateNoH1 (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat)
    (a0 : AMarking) (yc : Weight × Int) : Bool :=
  rows.all (fun tr =>
      (List.range n).all (fun p => !(tr.1.resets.contains p) || decide (yc.1 p = 0)) &&
      decide (dotIncD yc.1 tr n = 0)) &&
    envs.all (fun p => decide (yc.1 p = 0)) &&
    decide (yc.2 = dot yc.1 a0 n)

/-- The gate without H1 on reset places. -/
def ver005_gateNoReset (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat)
    (a0 : AMarking) (yc : Weight × Int) : Bool :=
  rows.all (fun tr =>
      (List.range n).all (fun p => !(consumeAllAt tr.1 p) || decide (yc.1 p = 0)) &&
      decide (dotIncD yc.1 tr n = 0)) &&
    envs.all (fun p => decide (yc.1 p = 0)) &&
    decide (yc.2 = dot yc.1 a0 n)

/-- The gate without the injector columns (the matrix of the closed net). -/
def ver005_gateNoInj (rows : List (Transition × Deposit)) (_envs : List PlaceId) (n : Nat)
    (a0 : AMarking) (yc : Weight × Int) : Bool :=
  ver005_gate rows [] n a0 yc

/-- The reference source, all-zero row skipped, filtered by another gate. -/
def ver005_with (g : List (Transition × Deposit) → List PlaceId → Nat → AMarking →
    Weight × Int → Bool) : InvFn := fun rows envs n a0 =>
  (ver005_units rows envs n a0).filter fun yc => ver005_nonzero n yc.1 && g rows envs n a0 yc

/-- The reference with every constant reported as 0. -/
def ver005_constZero : InvFn := fun rows envs n a0 =>
  (refPInv ver005_units rows envs n a0).map fun yc => (yc.1, 0)

/-- Line 2 forbids dropping H1 on a consume-all place: `t: all(p0) -> p1` from two tokens in
`p0`. The vector `p0 + p1` is zero on the column, `t` empties `p0` and puts one token in `p1`,
so the sum goes from 2 to 1. -/
@[evidence forbids VER_005]
theorem VER_005_forbids_noH1 : ¬ VER_005 (ver005_with ver005_gateNoH1) := by
  intro h
  let rows : List (Transition × Deposit) := [(ver005_t [⟨0, .all, none⟩] [], [1])]
  have hy : (ver005_vec [0, 1], dot (ver005_vec [0, 1]) (ver005_mk [(0, 2)]) 2) ∈
      ver005_with ver005_gateNoH1 rows [] 2 (ver005_mk [(0, 2)]) :=
    List.mem_filter.mpr ⟨ver005_mem_units (List.Sublist.refl _), by decide⟩
  have hr : ReachADInj rows [] (ver005_mk [(0, 2)])
      (fireAD (ver005_mk [(0, 2)]) (ver005_t [⟨0, .all, none⟩] []) [1]) :=
    Relation.ReflTransGen.single (Or.inl ⟨_, List.mem_singleton_self _, by decide, rfl⟩)
  have := h.2.1 rows [] 2 _ _ hy _ hr
  revert this
  decide

/-- Line 2 forbids dropping H1 on a reset place: `t` resets `p0` and does nothing else, from one
token in `p0`. The vector `p0` is zero on the column and the firing takes the count from 1 to
0. -/
@[evidence forbids VER_005]
theorem VER_005_forbids_noReset : ¬ VER_005 (ver005_with ver005_gateNoReset) := by
  intro h
  let rows : List (Transition × Deposit) := [(ver005_t [] [0], [])]
  have hy : (ver005_vec [0], dot (ver005_vec [0]) (ver005_mk [(0, 1)]) 1) ∈
      ver005_with ver005_gateNoReset rows [] 1 (ver005_mk [(0, 1)]) :=
    List.mem_filter.mpr ⟨ver005_mem_units (List.Sublist.refl _), by decide⟩
  have hr : ReachADInj rows [] (ver005_mk [(0, 1)])
      (fireAD (ver005_mk [(0, 1)]) (ver005_t [] [0]) []) :=
    Relation.ReflTransGen.single (Or.inl ⟨_, List.mem_singleton_self _, by decide, rfl⟩)
  have := h.2.1 rows [] 1 _ _ hy _ hr
  revert this
  decide

/-- Line 2 forbids dropping the injector column: no row, `p0` an environment place. The vector
`p0` passes the closed-net gate, and one injection takes its count from 0 to 1. -/
@[evidence forbids VER_005]
theorem VER_005_forbids_noInjector : ¬ VER_005 (ver005_with ver005_gateNoInj) := by
  intro h
  have hy : (ver005_vec [0], dot (ver005_vec [0]) (fun _ => 0) 1) ∈
      ver005_with ver005_gateNoInj [] [0] 1 (fun _ => 0) :=
    List.mem_filter.mpr ⟨ver005_mem_units (List.Sublist.refl _), by decide⟩
  have hr : ReachADInj [] [0] (fun _ => 0) (fun q => if q == 0 then (fun _ => 0) q + 1 else 0) :=
    Relation.ReflTransGen.single (Or.inr ⟨0, by simp, rfl⟩)
  have := h.2.1 [] [0] 1 _ _ hy _ hr
  revert this
  decide

/-- Line 2 forbids a wrong constant: no row, one token in `p0`; the reference reports `p0 = 1`,
the mutant `p0 = 0`, and the initial marking is reachable. -/
@[evidence forbids VER_005]
theorem VER_005_forbids_constZero : ¬ VER_005 ver005_constZero := by
  intro h
  have hy0 : (ver005_vec [0], dot (ver005_vec [0]) (ver005_mk [(0, 1)]) 1) ∈
      refPInv ver005_units [] [] 1 (ver005_mk [(0, 1)]) :=
    List.mem_filter.mpr ⟨ver005_mem_units (List.Sublist.refl _), by decide⟩
  have hy : (ver005_vec [0], (0 : Int)) ∈ ver005_constZero [] [] 1 (ver005_mk [(0, 1)]) :=
    List.mem_map.mpr ⟨_, hy0, rfl⟩
  have := h.2.1 [] [] 1 _ _ hy _ Relation.ReflTransGen.refl
  revert this
  decide

/-- From the empty marking, `t: one(p0) -> nothing` never fires: the only reachable marking is
the initial one. -/
theorem ver005_dead_reach {a : AMarking}
    (h : ReachADInj [(ver005_t [⟨0, .one, none⟩] [], [])] [] (fun _ => 0) a) :
    a = fun _ => 0 := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    rcases hs with ⟨tr, hmem, hen, -⟩ | ⟨p, hp, -⟩
    · rw [List.mem_singleton] at hmem
      subst hmem
      exact absurd hen (by decide)
    · simp at hp

/-- The reachability reading of the definition: the reference, plus `p0` with its initial count
whenever there is a place and the count of `p0` is the same on every reachable marking, whatever
the incidence matrix says. -/
noncomputable def ver005_reachOnly : InvFn := fun rows envs n a0 => by
  classical
  exact refPInv ver005_units rows envs n a0 ++
    if 0 < n ∧ ∀ a, ReachADInj rows envs a0 a →
        dot (ver005_vec [0]) a n = dot (ver005_vec [0]) a0 n
    then [(ver005_vec [0], dot (ver005_vec [0]) a0 n)] else []

/-- The reachability reading satisfies line 2 by construction. -/
theorem ver005_reachOnly_conserves : ver005_conserves ver005_reachOnly := by
  intro rows envs n a0 yc hy a hr
  unfold ver005_reachOnly at hy
  rcases List.mem_append.mp hy with hy | hy
  · exact (refPInv_sound ver005_units).2 rows envs n a0 yc hy a hr
  · split at hy
    · rename_i hc
      rw [List.mem_singleton] at hy
      subst hy
      exact hc.2 a hr
    · simp at hy

/-- **The columns of line 1 are load-bearing.** The reachability reading conserves every vector
it reports, and VER-005 still rejects it: on `t: one(p0) -> nothing` from the empty marking, `t`
never fires, so the count of `p0` is constant on the reachable markings, but the vector `p0` is
not zero on `t`'s column. "Computed from the incidence matrix" is not "constant on what happens
to be reachable". -/
@[evidence mutant VER_005]
theorem VER_005_mutant_reachOnly :
    ver005_conserves ver005_reachOnly ∧ ¬ VER_005 ver005_reachOnly := by
  refine ⟨ver005_reachOnly_conserves, fun h => ?_⟩
  let rows : List (Transition × Deposit) := [(ver005_t [⟨0, .one, none⟩] [], [])]
  have hy : (ver005_vec [0], dot (ver005_vec [0]) (fun _ => 0) 1) ∈
      ver005_reachOnly rows [] 1 (fun _ => 0) := by
    unfold ver005_reachOnly
    rw [if_pos ⟨by decide, fun a ha => by rw [ver005_dead_reach ha]⟩]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have := (h.1 rows [] 1 _ _ hy).2 _ (List.mem_singleton_self _)
  revert this
  decide

/-- The reference with the trivial law `0 · M = 0` in front, the row every runtime skips. -/
def ver005_withZero : InvFn := fun rows envs n a0 =>
  (ver005_vec [], 0) :: refPInv ver005_units rows envs n a0

/-- **The nonzero clause of line 1 is load-bearing.** The trivial law is conserved (and the
mutant still reports everything the reference does, so line 3 holds too), yet VER-005 rejects
it: no weight below `n` is nonzero. -/
@[evidence mutant VER_005]
theorem VER_005_mutant_zero :
    ver005_conserves ver005_withZero ∧ ¬ VER_005 ver005_withZero := by
  refine ⟨fun rows envs n a0 yc hy a hr => ?_, fun h => ?_⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · rw [dot_eq_isum]
      simp [ver005_vec, isum]
    · exact (refPInv_sound ver005_units).2 rows envs n a0 yc hy a hr
  · obtain ⟨p, hp, hne⟩ := (h.1 [] [] 1 (fun _ => 0) _ (List.mem_cons_self ..)).1
    exact hne (by simp [ver005_vec])

/-- **Line 3 is load-bearing.** The computation that reports nothing meets lines 1 and 2
vacuously, and VER-005 rejects it: on the token-conservation net `t: one(p0) -> p1` the vector
`p0 + p1` is a 0/1 vector zero on the column, and no combination of nothing is a nonzero multiple
of it. This is the test derivation's "verify invariant is discovered". -/
@[evidence mutant VER_005]
theorem VER_005_mutant_none :
    ver005_sound (fun _ _ _ _ => []) ∧ ¬ VER_005 (fun _ _ _ _ => []) := by
  refine ⟨⟨fun _ _ _ _ yc hy => by simp at hy, fun _ _ _ _ yc hy => by simp at hy⟩, fun h => ?_⟩
  exact ver005_empty_misses (I := fun _ _ _ _ => []) (rows := ver005_move) (envs := [])
    (n := 2) (a0 := ver005_mk [(0, 1)]) rfl ⟨0, by decide, by decide⟩
    (h.2.2 ver005_move [] 2 (ver005_mk [(0, 1)]) (by simp [ver005_move]) (by decide)
      (ver005_vec [0, 1]) (ver005_vec_01 _) (ver005_vec_below (by decide)) (by decide)
      (by simp))

/-- The computation without injector columns that stays sound by reporting nothing once a place
is injected (`AlwaysAvailable`, `Bounded(k)`). -/
def ver005_noEnvColumns : InvFn := fun rows envs n a0 =>
  if envs = [] then refPInv ver005_units rows envs n a0 else []

/-- Line 3 forbids it: on `t: one(p0) -> p1` with an unrelated environment place `p2`, the
vector `p0 + p1` is zero on the column and on `p2`'s injector column, and the mutant reports
nothing. -/
@[evidence forbids VER_005]
theorem VER_005_forbids_noEnvColumns : ¬ VER_005 ver005_noEnvColumns := by
  intro h
  exact ver005_empty_misses (I := ver005_noEnvColumns) (rows := ver005_move) (envs := [2])
    (n := 3) (a0 := ver005_mk [(0, 1)]) (by simp [ver005_noEnvColumns])
    ⟨0, by decide, by decide⟩
    (h.2.2 ver005_move [2] 3 (ver005_mk [(0, 1)]) (by simp [ver005_move]) (by decide)
      (ver005_vec [0, 1]) (ver005_vec_01 _) (ver005_vec_below (by decide)) (by decide)
      (by simp [ver005_vec]))

end Libpetri.Spec
