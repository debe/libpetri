import Libpetri.Strengthening
import Libpetri.Novel.ForwardDeposit
import Libpetri.Novel.Pairwise

/-!
# The linear state-equation bound ([VER-015])

[VER-015]: a reachability-safety property is proven structurally, without the fixpoint search,
when some weighting `y` makes the violation's demand exceed a decreasing conservation law.

The Rust behaviour (`rust/libpetri-verification/src/linear_bound.rs`):
* `violation_demand` turns the property into a demand `d`: `m_p ≥ 1` for every resolved place
  of `Unreachable` / a two-place `MutualExclusion`, `m_p ≥ bound + 1` for `PlaceBound` /
  `BranchPlaceBound`, and `None` for the four quiescence properties and for a `MutualExclusion`
  of three or more entries. The violating markings are exactly the markings covering `d`:
  `encode_property_violation` (`smt_encoder.rs`) emits the conjunction `(>= m_p 1)` over the
  same resolved places for `Unreachable` and a two-entry `MutualExclusion` (`pairwise_marked`),
  and `m_p > bound` for a bound.
* A `MutualExclusion` of three or more entries is pairwise ([VER-002]): a disjunction of the
  two-place demands, one per position pair. `SmtProperty::linear_parts` splits it into those
  pairs and `SmtVerifier::linear_bound_proof` proves it only when every part is separated,
  each by its own weighting (`linear_bound_part`); `pairwise_linear_bound_sound` below is that
  composition.
* `check_linear_bound_exact` accepts the solver's `y` only if, in checked `i128`:
  `y ≥ 0`; `y = 0` on every place of `zero_weight_places` (H1: consume-all or reset place of
  some flat transition, via `p_invariant.rs` `nonlinear_places`; H3′: every injected
  environment place); `y·(post − pre) ≤ 0` for every flat transition, the column
  `IncidenceMatrix::from_flat_net` would build (`pre = required_count`); and
  `y·d ≥ y·M0 + 1`. An overflow fails the check. The model uses unbounded `Int`, so it covers
  every `y` the checked arithmetic accepts.
* `SmtVerifier::linear_bound_proof` (`smt_verifier.rs`) reports `Proven` (route
  `Structural`) only on a `sat` whose model passes that re-check, and the call site skips the
  bound under `EnvironmentAnalysisMode::Ignore` with environment places.

Results:
* `linear_bound_sound` — every weighting the shipped check accepts (`ShippedCheck`) proves that
  no marking reachable from `M0`, injections included (`ReachAInj`), covers `d`.
* `linear_bound_sound_noH1` — the same **without H1**. For an inequality `y·M ≤ y·M0` with
  `y ≥ 0` the consume-all and reset arms are harmless: at an enabled firing the arm's successor
  `post[p]` is at most the linear prediction `m_p − pre[p] + post[p]`, because enablement
  gives `pre[p] ≤ m_p`, and a non-negative weight preserves `≤`. H1 is needed for the
  *equalities* of [VER-005] (`consume_all_hypothesis_is_necessary`), not for [VER-015].
  `h1_drop_gains` shows dropping it is not vacuous: on `netDrain` the shipped check admits no
  weighting, the relaxed one admits `yDrain`, and the property it proves holds.
* `env_zero_is_necessary` — H3′ is load-bearing: on `Retrodict.lean`'s `netEnv` a weighting
  that is non-negative, decreasing and separating, but weights the injected place, "proves"
  `PlaceBound(p₁, 0)` while injection reaches `p₁ = 1`.
* `linear_bound_proven` — the verdict shape: `ProvenFor (ReachAInj …) (safetyBad …)` for the
  modelled properties.
* `linear_bound_concrete` — composed with `proposition_one`: on a `WellFormed` env-free net,
  no marking the concrete executor semantics reaches (`ReachC`) covers `d` under `alpha`.
* **Deposit rows.** The flat net's column for a row is its deposit count minus `pre`
  (`post[pid] += n` in `flatten`, so a timeout forward from an `exactly(k)` input has
  `post[to] = k`). `fireA` / `dotInc` read `post` as membership, so the results above cover
  duplicate-free rows only. `fireAD_le_linear`, `dot_le_initial_rows` and
  `linear_bound_sound_rows` are the same argument over `fireAD` and the count column `dotIncD`
  (`ShippedCheckD`, the re-check the Rust runs on those columns), with injection
  (`ReachADInj`); `linear_bound_forward_concrete` composes it with
  `ForwardDeposit.forward_reachability_simulated`, so a weighting the check accepts excludes the
  violation from every concrete run, timeout outcomes included. On a duplicate-free row the two
  columns agree (`dotIncD_eq_dotInc`).

Out of scope, shared with the rest of axis 1: the seed `M0` is taken as `alpha m0` (the
encoder reads `initial_marking.count(flat.places[i])`), place names are dense indices, and the
four property kinds are modelled by their demand. `proposition_one`, and therefore
`linear_bound_concrete`, needs `UnitOutput` (one token per place of the row); the deposit-row
corollary `linear_bound_forward_concrete` does not, and covers every row `fixedRows` builds
(a forward from a `One` / `Exactly` input). A drained forward has no row and is refused before
the bound runs.
-/

namespace Libpetri.Novel.LinearBound

open Libpetri

/-! ## Per-step decrease -/

/-- `Σ_{p<n}` is monotone. -/
theorem isum_le {f g : PlaceId → Int} {n : Nat} (h : ∀ p, p < n → f p ≤ g p) :
    isum f n ≤ isum g n :=
  Finset.sum_le_sum fun p hp => h p (Finset.mem_range.mp hp)

/-- At an enabled firing every place ends at most where the linear column predicts: the linear
arm meets it exactly, and the two clearing arms (reset, consume-all: `m'_p = post[p]`) stay
below it because `pre[p] ≤ m_p`. No weight appears, so no H1. -/
theorem fireA_le_linear {m : AMarking} {t : Transition} (br : List PlaceId)
    (hEn : enabledA m t = true) (p : PlaceId) :
    (fireA m t br p : Int) ≤ (m p : Int) + ((post br p : Int) - (pre t p : Int)) := by
  have hle : pre t p ≤ m p := pre_le_of_enabledA hEn p
  unfold fireA
  by_cases hR : t.resets.contains p = true
  · rw [if_pos hR]; omega
  · rw [if_neg hR]
    by_cases hCA : consumeAllAt t p = true
    · rw [if_pos hCA]; omega
    · rw [if_neg hCA]; omega

/-- **One firing does not raise `y·M` beyond its column** for `y ≥ 0`, with no hypothesis on
consume-all or reset places. -/
theorem dot_fireA_le (y : Weight) {m : AMarking} {t : Transition} {br : List PlaceId}
    {n : Nat} (hpos : ∀ p, p < n → 0 ≤ y p) (hEn : enabledA m t = true) :
    dot y (fireA m t br) n ≤ dot y m n + dotInc y (t, br) n := by
  rw [dot_eq_isum, dot_eq_isum, dotInc, ← isum_add]
  refine isum_le fun p hp => ?_
  have h := Int.mul_le_mul_of_nonneg_left (fireA_le_linear br hEn p) (hpos p hp)
  show y p * (fireA m t br p : Int) ≤ y p * (m p : Int) + y p * ((post br p : Int) - (pre t p : Int))
  rw [← Int.mul_add]
  exact h

/-- An injection into a zero-weight place leaves `y·M` unchanged (H3′). -/
theorem dot_inject {y : Weight} {a : AMarking} {p : PlaceId} {n : Nat} (hy : y p = 0) :
    dot y (fun q => if q == p then a q + 1 else a q) n = dot y a n := by
  rw [dot_eq_isum, dot_eq_isum]
  refine isum_congr fun q _ => ?_
  show y q * ((if q == p then a q + 1 else a q : Nat) : Int) = y q * (a q : Int)
  by_cases hqp : (q == p) = true
  · have hq : q = p := by simpa using hqp
    subst hq
    rw [hy]; omega
  · rw [if_neg hqp]

/-- **The decreasing law.** `y ≥ 0`, `y·C ≤ 0` on every flat transition and `y = 0` on every
injected place give `y·M ≤ y·M₀` on all of `ReachAInj` — without H1. -/
theorem dot_le_initial {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {y : Weight} {n : Nat}
    (hpos : ∀ p, p < n → 0 ≤ y p)
    (hdec : ∀ ft ∈ net, dotInc y ft n ≤ 0)
    (henv : ∀ p ∈ envs, y p = 0)
    (h : ReachAInj net envs a0 a) :
    dot y a n ≤ dot y a0 n := by
  induction h with
  | init => exact le_refl _
  | @step a1 ft _ hmem hen ih =>
    have h1 : dot y (fireA a1 ft.1 ft.2) n ≤ dot y a1 n + dotInc y ft n :=
      dot_fireA_le y (br := ft.2) hpos hen
    have h2 := hdec ft hmem
    omega
  | @inject a1 p _ hp ih =>
    rw [dot_inject (henv p hp)]
    exact ih

/-! ## Demand, violation and the verdict -/

/-- `a` meets the demand `d` on the flat places: the violating markings. -/
def Covers (d a : AMarking) (n : Nat) : Prop :=
  ∀ p, p < n → d p ≤ a p

/-- A weighting `y ≥ 0` gives `y·d ≤ y·a` whenever `a` covers `d`. -/
theorem dot_le_of_covers {y : Weight} {d a : AMarking} {n : Nat}
    (hpos : ∀ p, p < n → 0 ≤ y p) (hc : Covers d a n) : dot y d n ≤ dot y a n := by
  rw [dot_eq_isum, dot_eq_isum]
  refine isum_le fun p hp => ?_
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hc p hp) (hpos p hp)

/-- **Soundness without H1.** Any weighting with `y ≥ 0`, `y = 0` on injected places,
`y·C ≤ 0` per flat transition and `y·M₀ < y·d` excludes every reachable marking covering `d`. -/
theorem linear_bound_sound_noH1 {net : FlatNet} {envs : List PlaceId} {a0 d : AMarking}
    {y : Weight} {n : Nat}
    (hpos : ∀ p, p < n → 0 ≤ y p)
    (hdec : ∀ ft ∈ net, dotInc y ft n ≤ 0)
    (henv : ∀ p ∈ envs, y p = 0)
    (hsep : dot y a0 n < dot y d n) :
    ∀ a, ReachAInj net envs a0 a → ¬ Covers d a n := by
  intro a h hc
  have h1 := dot_le_initial hpos hdec henv h
  have h2 := dot_le_of_covers hpos hc
  omega

/-- `check_linear_bound_exact` (`linear_bound.rs`) as a predicate on `y`: every conjunct it
re-checks, over the `n = place_count` flat places. `zero_weight_places` is `h1` (consume-all
and reset places of every flat transition, `nonlinear_places`) together with `henv`
(the resolved injection list). `sep` is `y·d ≥ y·M0 + 1`. -/
structure ShippedCheck (net : FlatNet) (envs : List PlaceId) (a0 d : AMarking) (y : Weight)
    (n : Nat) : Prop where
  pos : ∀ p, p < n → 0 ≤ y p
  h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n
  henv : ∀ p ∈ envs, y p = 0
  dec : ∀ ft ∈ net, dotInc y ft n ≤ 0
  sep : dot y a0 n + 1 ≤ dot y d n

/-- **[VER-015] soundness.** A weighting that passes the shipped exact re-check proves that no
marking reachable from `M0` — environment injections included — meets the violation's
demand. H1 is carried by the check but not used by the proof. -/
theorem linear_bound_sound {net : FlatNet} {envs : List PlaceId} {a0 d : AMarking}
    {y : Weight} {n : Nat} (hc : ShippedCheck net envs a0 d y n) :
    ∀ a, ReachAInj net envs a0 a → ¬ Covers d a n :=
  linear_bound_sound_noH1 hc.pos hc.dec hc.henv (by have := hc.sep; omega)

/-- The four reachability-safety properties `is_reachability_safety` admits, by their demand:
`Unreachable` / `MutualExclusion` over resolved places, `PlaceBound` / `BranchPlaceBound`. -/
inductive SafetyProp where
  | allMarked (places : List PlaceId)
  | placeBound (place : PlaceId) (bound : Nat)

/-- `violation_demand` (`linear_bound.rs`). -/
def demand : SafetyProp → AMarking
  | .allMarked ps => fun p => if p ∈ ps then 1 else 0
  | .placeBound q k => fun p => if p = q then k + 1 else 0

/-- The violation `encode_property_violation` emits for the property (`smt_encoder.rs`):
every listed place holds a token, or the bounded place exceeds its bound. -/
def safetyBad : SafetyProp → AMarking → Prop
  | .allMarked ps => fun a => ∀ p ∈ ps, 1 ≤ a p
  | .placeBound q k => fun a => k < a q

/-- The property's places are resolved flat places — the verifier refuses any other property
before a route runs ([VER-003] AC5). -/
def Resolved (n : Nat) : SafetyProp → Prop
  | .allMarked ps => ∀ p ∈ ps, p < n
  | .placeBound q _ => q < n

/-- The demand is exact: a marking violates iff it covers the demand. -/
theorem safetyBad_iff_covers {n : Nat} {prop : SafetyProp} (hr : Resolved n prop)
    (a : AMarking) : safetyBad prop a ↔ Covers (demand prop) a n := by
  cases prop with
  | allMarked ps =>
    simp only [safetyBad, Covers, demand]
    constructor
    · intro h p _
      by_cases hp : p ∈ ps
      · rw [if_pos hp]; exact h p hp
      · rw [if_neg hp]; exact Nat.zero_le _
    · intro h p hp
      have := h p (hr p hp)
      rwa [if_pos hp] at this
  | placeBound q k =>
    simp only [safetyBad, Covers, demand]
    constructor
    · intro h p _
      by_cases hp : p = q
      · subst hp; rw [if_pos rfl]; omega
      · rw [if_neg hp]; exact Nat.zero_le _
    · intro h
      have := h q hr
      rw [if_pos rfl] at this
      omega

/-- **The `Proven` verdict of the structural route** for the modelled properties. -/
theorem linear_bound_proven {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {prop : SafetyProp} {y : Weight} {n : Nat} (hr : Resolved n prop)
    (hc : ShippedCheck net envs a0 (demand prop) y n) :
    ProvenFor (ReachAInj net envs a0) (safetyBad prop) := fun a h hbad =>
  linear_bound_sound hc a h ((safetyBad_iff_covers hr a).mp hbad)

/-- **A pairwise `MutualExclusion` proven pair by pair** (`linear_parts`, `linear_bound_proof`).
If the shipped check accepts a weighting for the two-place demand of every position pair of
`ps` (resolved places), no marking reachable from `M0` — injections included — marks two entries
of `ps` at once: the pairwise violation `pairwise_marked` encodes (`Seam/Bad.lean`
`pairMarkedBad_iff`). -/
theorem pairwise_linear_bound_sound {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {ps : List PlaceId} {n : Nat} (hres : ∀ p ∈ ps, p < n)
    (hpair : ∀ pq ∈ Pairwise.pairsOf ps,
      ∃ y, ShippedCheck net envs a0 (demand (.allMarked [pq.1, pq.2])) y n) :
    ∀ a, ReachAInj net envs a0 a → ¬ 2 ≤ (ps.filter (fun p => decide (1 ≤ a p))).length := by
  intro a hr htwo
  obtain ⟨pq, hpq, hboth⟩ := List.any_eq_true.mp
    ((Pairwise.any_pairsOf_iff (fun p => decide (1 ≤ a p)) ps).mpr htwo)
  obtain ⟨y, hc⟩ := hpair pq hpq
  have hm := Pairwise.mem_pairsOf hpq
  have hR : Resolved n (.allMarked [pq.1, pq.2]) := by
    intro p hp
    rcases List.mem_pair.mp hp with rfl | rfl
    · exact hres _ hm.1
    · exact hres _ hm.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
  refine linear_bound_sound hc a hr ((safetyBad_iff_covers hR a).mp ?_)
  intro p hp
  rcases List.mem_pair.mp hp with rfl | rfl
  · exact hboth.1
  · exact hboth.2

/-! ## The concrete-level consequence -/

/-- The env-free relation is the `envs = []` case of the injected one. -/
theorem reachA_sub_inj {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    (h : ReachA net a0 a) : ReachAInj net envs a0 a := by
  induction h with
  | init => exact ReachAInj.init
  | step _ hmem hen ih => exact ReachAInj.step ih hmem hen

/-- **Composed with `proposition_one`.** On a `WellFormed` net, a weighting that is
non-negative, decreasing on every flat transition and separates `α(m₀)` from `d` excludes
every marking the concrete semantics reaches (`ReachC`, token counts under `alpha`). No H1. -/
theorem linear_bound_concrete {net : FlatNet} {m0 : CMarking} {d : AMarking} {y : Weight}
    {n : Nat} (hWF : WellFormed net)
    (hpos : ∀ p, p < n → 0 ≤ y p)
    (hdec : ∀ ft ∈ net, dotInc y ft n ≤ 0)
    (hsep : dot y (alpha m0) n < dot y d n) :
    ∀ m, ReachC net m0 m → ¬ Covers d (alpha m) n := fun m h =>
  linear_bound_sound_noH1 (envs := []) hpos hdec (by simp) hsep _
    (reachA_sub_inj (proposition_one hWF h))

/-- The concrete consequence for a property the shipped check proved. -/
theorem linear_bound_concrete_proven {net : FlatNet} {m0 : CMarking} {prop : SafetyProp}
    {y : Weight} {n : Nat} (hWF : WellFormed net) (hr : Resolved n prop)
    (hc : ShippedCheck net [] (alpha m0) (demand prop) y n) :
    ∀ m, ReachC net m0 m → ¬ safetyBad prop (alpha m) := fun _ h hbad =>
  linear_bound_sound hc _ (reachA_sub_inj (proposition_one hWF h))
    ((safetyBad_iff_covers hr _).mp hbad)

/-! ## H3′ is necessary -/

/-- Weight `1` on the environment place `0` and its successor `1` of `Retrodict.lean`'s
`netEnv`. -/
def yEnv : Weight := fun p => if p < 2 then 1 else 0

/-- `PlaceBound(p₁, 0)`: demand one token on `p₁`. -/
def dEnv : AMarking := demand (.placeBound outPlace 0)

/-- **H3′ is load-bearing.** `yEnv` is non-negative, decreasing (the column `−e₀ + e₁` has
weight `0`) and separating (`y·M₀ = 0 < 1 = y·d`) — everything but zero on the injected place.
Yet injection reaches `p₁ = 1`. `zero_weight_places` pinning injected places is what stops it. -/
theorem env_zero_is_necessary :
    (∀ p, p < 2 → 0 ≤ yEnv p)
    ∧ (∀ ft ∈ netEnv, dotInc yEnv ft 2 ≤ 0)
    ∧ dot yEnv m0A 2 < dot yEnv dEnv 2
    ∧ yEnv envPlace ≠ 0
    ∧ ∃ a, ReachAInj netEnv [envPlace] m0A a ∧ Covers dEnv a 2 := by
  refine ⟨fun p _ => by unfold yEnv; split <;> omega, ?_, ?_, by decide, ?_⟩
  · intro ft hft
    have : ft = (tConsume, [outPlace]) := by simpa [netEnv] using hft
    subst this
    decide
  · decide
  · obtain ⟨a, ha, h1⟩ := injection_reaches_violation
    refine ⟨a, ha, fun p hp => ?_⟩
    show (if p = outPlace then 0 + 1 else 0) ≤ a p
    split
    · subst_vars; omega
    · exact Nat.zero_le _

/-! ## Dropping H1 gains proofs -/

/-- Drains place `0` with `In::All` into place `1`. -/
def tDrain : Transition :=
  { name := "drain"
  , inputs := [{ place := 0, card := .all, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def netDrain : FlatNet := [(tDrain, [1])]

/-- One token on place `0`. -/
def a0Drain : AMarking := fun p => if p = 0 then 1 else 0

/-- `Unreachable {p₀, p₁}`: both places marked at once. -/
def propDrain : SafetyProp := .allMarked [0, 1]

/-- The weighting only the relaxed check admits: it weights the consume-all place. -/
def yDrain : Weight := fun p => if p < 2 then 1 else 0

theorem dotInc_two (y : Weight) (ft : FlatTransition) :
    dotInc y ft 2 = y 0 * ((post ft.2 0 : Int) - (pre ft.1 0 : Int))
      + y 1 * ((post ft.2 1 : Int) - (pre ft.1 1 : Int)) := by
  simp [dotInc, isum, Finset.sum_range_succ]

/-- **Dropping H1 is not vacuous.** On `netDrain`, (1) no weighting passes the shipped check
for `Unreachable {p₀, p₁}`: H1 zeroes `y₀`, the column then forces `y₁ ≤ 0`, and nothing
separates; (2) `yDrain` passes every conjunct except H1, so `linear_bound_sound_noH1` proves
the property; (3) the property indeed holds on the reachable set. -/
theorem h1_drop_gains :
    (¬ ∃ y, ShippedCheck netDrain [] a0Drain (demand propDrain) y 2)
    ∧ ((∀ p, p < 2 → 0 ≤ yDrain p)
      ∧ (∀ ft ∈ netDrain, dotInc yDrain ft 2 ≤ 0)
      ∧ dot yDrain a0Drain 2 < dot yDrain (demand propDrain) 2
      ∧ ¬ ZeroOnNonlinear yDrain tDrain 2)
    ∧ ProvenFor (ReachAInj netDrain [] a0Drain) (safetyBad propDrain) := by
  have hmem : ((tDrain, [1]) : FlatTransition) ∈ netDrain := by simp [netDrain]
  have hpos : ∀ p, p < 2 → 0 ≤ yDrain p := fun p _ => by unfold yDrain; split <;> omega
  have hdec : ∀ ft ∈ netDrain, dotInc yDrain ft 2 ≤ 0 := by
    intro ft hft
    have : ft = (tDrain, [1]) := by simpa [netDrain] using hft
    subst this
    decide
  have hsep : dot yDrain a0Drain 2 < dot yDrain (demand propDrain) 2 := by decide
  refine ⟨?_, ⟨hpos, hdec, hsep, ?_⟩, ?_⟩
  · rintro ⟨y, hc⟩
    have hy0 : y 0 = 0 := hc.h1 _ hmem 0 (by decide) (Or.inr (by decide))
    have hy1 : 0 ≤ y 1 := hc.pos 1 (by decide)
    have hcol := hc.dec _ hmem
    have hs := hc.sep
    rw [dotInc_two] at hcol
    rw [dot_two, dot_two] at hs
    have e1 : (post [1] 0 : Int) - (pre tDrain 0 : Int) = -1 := by decide
    have e2 : (post [1] 1 : Int) - (pre tDrain 1 : Int) = 1 := by decide
    have e3 : ((a0Drain 0 : Nat) : Int) = 1 := by decide
    have e4 : ((a0Drain 1 : Nat) : Int) = 0 := by decide
    have e5 : ((demand propDrain 0 : Nat) : Int) = 1 := by decide
    have e6 : ((demand propDrain 1 : Nat) : Int) = 1 := by decide
    simp only [e1, e2] at hcol
    rw [e3, e4, e5, e6, hy0] at hs
    rw [hy0] at hcol
    omega
  · intro h
    have := h 0 (by decide) (Or.inr (by decide))
    exact absurd this (by decide)
  · intro a h hbad
    exact linear_bound_sound_noH1 hpos hdec (by simp) hsep a h
      ((safetyBad_iff_covers (n := 2) (by simp [Resolved, propDrain]) a).mp hbad)

/-! ## Deposit rows -/

section DepositRows

open ForwardDeposit

/-- `y·(post − pre)` for a deposit row, `post[p]` the row's count of `p`: the column
`IncidenceMatrix::from_flat_net` builds from the flat transition `flatten` writes. -/
def dotIncD (y : Weight) (tr : Transition × Deposit) (n : Nat) : Int :=
  isum (fun p => y p * ((tr.2.count p : Int) - (pre tr.1 p : Int))) n

/-- On a duplicate-free row the count column is `dotInc`'s. -/
theorem dotIncD_eq_dotInc (y : Weight) {ft : FlatTransition} (h : ft.2.Nodup) (n : Nat) :
    dotIncD y ft n = dotInc y ft n := by
  unfold dotIncD dotInc
  refine isum_congr fun p _ => ?_
  rw [post_eq_count h]

/-- `fireA_le_linear` for a deposit row: the two clearing arms stay below the linear arm, for
any multiplicity. -/
theorem fireAD_le_linear {m : AMarking} {t : Transition} (d : Deposit)
    (hEn : enabledA m t = true) (p : PlaceId) :
    (fireAD m t d p : Int) ≤ (m p : Int) + ((d.count p : Int) - (pre t p : Int)) := by
  have hle : pre t p ≤ m p := pre_le_of_enabledA hEn p
  unfold fireAD
  by_cases hR : t.resets.contains p = true
  · rw [if_pos hR]; omega
  · rw [if_neg hR]
    by_cases hCA : consumeAllAt t p = true
    · rw [if_pos hCA]; omega
    · rw [if_neg hCA]; omega

theorem dot_fireAD_le (y : Weight) {m : AMarking} {t : Transition} {d : Deposit}
    {n : Nat} (hpos : ∀ p, p < n → 0 ≤ y p) (hEn : enabledA m t = true) :
    dot y (fireAD m t d) n ≤ dot y m n + dotIncD y (t, d) n := by
  rw [dot_eq_isum, dot_eq_isum, dotIncD, ← isum_add]
  refine isum_le fun p hp => ?_
  have h := Int.mul_le_mul_of_nonneg_left (fireAD_le_linear d hEn p) (hpos p hp)
  show y p * (fireAD m t d p : Int) ≤ y p * (m p : Int) + y p * ((d.count p : Int) - (pre t p : Int))
  rw [← Int.mul_add]
  exact h

/-- The decreasing law over deposit rows. -/
theorem dot_le_initial_rows {rows : List (Transition × Deposit)} {envs : List PlaceId}
    {a0 a : AMarking} {y : Weight} {n : Nat}
    (hpos : ∀ p, p < n → 0 ≤ y p)
    (hdec : ∀ tr ∈ rows, dotIncD y tr n ≤ 0)
    (henv : ∀ p ∈ envs, y p = 0)
    (h : ReachADInj rows envs a0 a) :
    dot y a n ≤ dot y a0 n := by
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih =>
    rcases hs with ⟨tr, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · have h1 : dot y (fireAD _ tr.1 tr.2) n ≤ _ + dotIncD y tr n :=
        dot_fireAD_le y (d := tr.2) hpos hen
      have h2 := hdec tr hmem
      omega
    · rw [dot_inject (henv p hp)]
      exact ih

/-- `check_linear_bound_exact` over deposit rows: `ShippedCheck` with the count column. -/
structure ShippedCheckD (rows : List (Transition × Deposit)) (envs : List PlaceId)
    (a0 d : AMarking) (y : Weight) (n : Nat) : Prop where
  pos : ∀ p, p < n → 0 ≤ y p
  h1 : ∀ tr ∈ rows, ZeroOnNonlinear y tr.1 n
  henv : ∀ p ∈ envs, y p = 0
  dec : ∀ tr ∈ rows, dotIncD y tr n ≤ 0
  sep : dot y a0 n + 1 ≤ dot y d n

/-- **[VER-015] soundness over deposit rows**: `linear_bound_sound` for rows of any
multiplicity, injections included. H1 is carried, not used. -/
theorem linear_bound_sound_rows {rows : List (Transition × Deposit)} {envs : List PlaceId}
    {a0 d : AMarking} {y : Weight} {n : Nat} (hc : ShippedCheckD rows envs a0 d y n) :
    ∀ a, ReachADInj rows envs a0 a → ¬ Covers d a n := by
  intro a h hcov
  have h1 := dot_le_initial_rows hc.pos hc.dec hc.henv h
  have h2 := dot_le_of_covers hc.pos hcov
  have := hc.sep
  omega

/-- **The concrete consequence, timeout outcomes included.** Over the fixed rows of a net whose
every forward draws from a `One` / `Exactly` input, a weighting the check accepts excludes the
property's violation from every marking a concrete run reaches, whichever way each firing
ends. -/
theorem linear_bound_forward_concrete {net : SpecNet} {m0 : CMarking} {prop : SafetyProp}
    {y : Weight} {n : Nat}
    (hWF : ∀ x ∈ net, GuardFreeConsumeAll x.1 ∧ FixedForwards x.1 x.2) (hr : Resolved n prop)
    (hc : ShippedCheckD (flatRows net) [] (alpha m0) (demand prop) y n) {m : CMarking}
    (h : Relation.ReflTransGen (StepCD net) m0 m) : ¬ safetyBad prop (alpha m) := fun hbad =>
  linear_bound_sound_rows hc _ (reachAD_sub_inj (forward_reachability_simulated hWF h))
    ((safetyBad_iff_covers hr _).mp hbad)

end DepositRows

end Libpetri.Novel.LinearBound
