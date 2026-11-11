import Libpetri.Spec.Registry
import Libpetri.Novel.LinearBound
import Libpetri.Reference.Semantics

set_option linter.missingDocs true

/-!
# VER-015: Linear state-equation bound (`spec/07-verification.md`)

Before the fixpoint query a reachability-safety property is tried against the state equation:
one `QF_LIA` query per demand asks for a weighting `y ≥ 0` that no flat transition increases and
that separates the violation's demand from the initial marking; a `sat` model is re-checked in
exact integer arithmetic and only then believed. The requirement is a predicate over a triple
`(C, Dm, Ph)`:

* `C : LinCheckRel`, the exact re-check: `C rows envs a0 d y n` says the check accepts the
  weighting `y` for the demand `d` on the flat net `rows` (deposit rows, `n` places) with the
  injected places `envs` and the seed `a0` (the shape of `ShippedCheckD`, `check_linear_bound_exact`);
* `Dm : LinDemandFn`, the demands of a property, one per part (`violation_demand` after
  `SmtProperty::linear_parts`);
* `Ph : LinPhaseRel`, the phase: `Ph rows envs a0 n prop ans` says the phase returns `Proven`
  on `prop` when the solver answers `ans i` to the query of the `i`-th demand
  (`SmtVerifier::linear_bound_proof`).

The witness triple is `refBoundCheck` (`ShippedCheckD`), `refBoundDemands` and `refBoundPhase`
(a loop over the demands that stops at the first part that does not prove). The statement is
checked against them (`VER_015_reference`), against seven wrong re-checks (one that never accepts,
one that weights an injected place, one with non-strict separation, one without `y ≥ 0`, one
without the zero weights on consume-all places, one without the row condition, one that reads a
deposit row as one token per place), with a re-check that rejects outside the integer range
allowed (`VER_015_allows_checked`), six wrong demand functions (a `PlaceBound` and
a `BranchPlaceBound` read as `m_p ≥ k`, a three-place `MutualExclusion` read as one demand or
with its pairs reversed, an `Unreachable` split per place or counted per position) and two
wrong phases (one that
believes a model without the re-check, one that proves a three-place `MutualExclusion` from its
first pair). What a `Proven` of the phase means is derived from the statement alone
(`VER_015_sound`): no marking reachable with injection violates the property.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.LinearBound Libpetri.Novel.ForwardDeposit

/-! ## The model -/

/-- A reachability-safety property that carries a demand: `Unreachable`, `MutualExclusion`,
`PlaceBound` and `BranchPlaceBound` over flat place indices. -/
inductive BoundProp where
  /-- `Unreachable(places)`: violated when every listed place is marked. -/
  | unreachable (places : List PlaceId)
  /-- `MutualExclusion(places)`: violated when two entries, at different positions, are marked. -/
  | mutualExclusion (places : List PlaceId)
  /-- `PlaceBound(place, bound)`: violated when the place holds more than `bound`. -/
  | placeBound (place : PlaceId) (bound : Nat)
  /-- `BranchPlaceBound(place, bound)`: the same violation as `PlaceBound` ([NU-040]). -/
  | branchPlaceBound (place : PlaceId) (bound : Nat)

/-- The solver's answer to one bound query, a `sat` answer with the weighting its model gives. -/
inductive BoundAnswer where
  /-- `sat`, with the weighting read from the model. -/
  | sat (y : Weight)
  /-- `unsat`: no weighting separates the demand. -/
  | unsat
  /-- `unknown`. -/
  | unknown
  /-- A transport failure ([VER-013]). -/
  | failure

/-- The flat net as deposit rows: each row is a transition and the multiset of places it
deposits into (`flatten`, `post[pid] += n`). -/
abbrev LinRows : Type := List (Transition × Deposit)

/-- An exact re-check: `C rows envs a0 d y n` says the check accepts the weighting `y` for the
demand `d` on the flat net `rows` with `n` places, the injected places `envs` and the seed `a0`. -/
abbrev LinCheckRel : Type := LinRows → List PlaceId → AMarking → AMarking → Weight → Nat → Prop

/-- The integer range the statement guarantees acceptance within: `2^127 − 2`, one below the
largest `i128` (`check_linear_bound_exact`, linear_bound.rs, computes in checked `i128`; Java and
TypeScript compute in unbounded integers), so that `y·M0 + 1` fits as well. -/
def linRange : Int := 170141183460469231731687303715884105726

/-- `LinFits B rows a0 d y n`: every weight, and for each sum of the re-check the sum of the
absolute values of its terms, is at most `B`: each row's `y·C[t]`, the seed's `y·M0` and the
demand's `y·d`. Under it no partial sum of the re-check leaves `[-B, B]`, whatever the order of
the terms. -/
def LinFits (B : Int) (rows : LinRows) (a0 d : AMarking) (y : Weight) (n : Nat) : Prop :=
  (∀ p, p < n → ((y p).natAbs : Int) ≤ B) ∧
  (∀ tr ∈ rows,
    isum (fun p => ((y p * ((tr.2.count p : Int) - (pre tr.1 p : Int))).natAbs : Int)) n ≤ B) ∧
  isum (fun p => ((y p * (a0 p : Int)).natAbs : Int)) n ≤ B ∧
  isum (fun p => ((y p * (d p : Int)).natAbs : Int)) n ≤ B

instance (B : Int) (rows : LinRows) (a0 d : AMarking) (y : Weight) (n : Nat) :
    Decidable (LinFits B rows a0 d y n) := by
  unfold LinFits; infer_instance

/-- The demands of a property, one per part: a demand is the least count a violating marking
holds on each place. -/
abbrev LinDemandFn : Type := BoundProp → List AMarking

/-- The bound phase: `Ph rows envs a0 n prop ans` says the phase returns `Proven` on `prop`
when the solver answers `ans i` to the query of the `i`-th demand. -/
abbrev LinPhaseRel : Type :=
  LinRows → List PlaceId → AMarking → Nat → BoundProp → (Nat → BoundAnswer) → Prop

/-- **The reference re-check**: `check_linear_bound_exact` over the count columns of the deposit
rows (`ShippedCheckD`). -/
def refBoundCheck : LinCheckRel := fun rows envs a0 d y n => ShippedCheckD rows envs a0 d y n

/-- **The reference demands**: `violation_demand` after `linear_parts`. A `MutualExclusion` of at
most two entries is one demand over its places; beyond two it is one demand per position pair
(`pairsOf`, `mutex_pairs`). A bound `k` demands `k + 1` on its place. -/
def refBoundDemands : LinDemandFn
  | .unreachable ps => [demand (.allMarked ps)]
  | .mutualExclusion ps =>
    if ps.length ≤ 2 then [demand (.allMarked ps)]
    else (Novel.Pairwise.pairsOf ps).map fun pq => demand (.allMarked [pq.1, pq.2])
  | .placeBound q k => [demand (.placeBound q k)]
  | .branchPlaceBound q k => [demand (.placeBound q k)]

/-- One part proves when the solver answered `sat` and the re-check accepts its weighting. -/
def ver015_partOk (rows : LinRows) (envs : List PlaceId) (a0 : AMarking) (n : Nat)
    (d : AMarking) : BoundAnswer → Prop
  | .sat y => ShippedCheckD rows envs a0 d y n
  | _ => False

/-- The loop of `linear_bound_proof`: the parts in order, each with its own query, `?` on the
first part that does not prove. -/
def ver015_loop (rows : LinRows) (envs : List PlaceId) (a0 : AMarking) (n : Nat)
    (ans : Nat → BoundAnswer) : Nat → List AMarking → Prop
  | _, [] => True
  | i, d :: ds => ver015_partOk rows envs a0 n d (ans i) ∧ ver015_loop rows envs a0 n ans (i + 1) ds

/-- **The reference phase**: the loop over the reference demands. -/
def refBoundPhase : LinPhaseRel := fun rows envs a0 n prop ans =>
  ver015_loop rows envs a0 n ans 0 (refBoundDemands prop)

/- The reference re-check, demands and phase are the witness triple of VER-015's `holds`
theorem. -/
#spec_witness refBoundCheck
#spec_witness refBoundDemands
#spec_witness refBoundPhase

/-! ## VER-015: Linear state-equation bound -/

requirement VER_015
  id "VER-015"
  title "Linear State-Equation Bound"
  kind F
  scope "the bound phase of the SMT verifier, all implementations"
  source verbatim "spec/07-verification.md"
  quote "The violation of such a property is a lower demand `d` on some places (`m_p ≥ 1` for each place of an `Unreachable` or a two-place `MutualExclusion`, `m_p ≥ k+1` for a bound `k`); if `y·d > y·M0` for some such `y`, no reachable marking meets the demand and the property is **proven structurally**, without IC3."
        "A pairwise `MutualExclusion` over three or more places ([VER-002]) is a disjunction of demands, one per pair: it is proven when every pair's demand is separated, each pair with its own query."
        "A `sat` model is **re-checked in exact integer arithmetic** (`y ≥ 0`, the zero weights, every row, the demand) before it is believed; a model that fails the check is discarded."
        "The verifier *shall* accept a weighting `y` for a demand `d` in the exact re-check only when `y_p ≥ 0` on every flat place, `y_p = 0` on every consume-all, reset and injected environment place, `Σ_p C[p][t]·y_p ≤ 0` for every flat transition `t`, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`, and *shall* accept every weighting that meets these conditions when every weight, and the sum of the absolute values of the terms of each of these sums, is at most `2^127 − 2`."
        "A weighting whose sums overflow the implementation's integer arithmetic is rejected; that costs a proof and never makes one."
        "In the re-check, `C[p][t]` is the number of tokens the flat transition `t` deposits on `p` minus the number its input on `p` requires, which for a consume-all input (`all`, `atLeast`) is its required minimum."
        "The verifier *shall* take as the demands of a property one demand `m_p ≥ 1` on every listed place for `Unreachable`, one demand `m ≥ 1` on the entries at positions `i` and `j` for every pair of positions `i < j` of a `MutualExclusion` of two or more entries, in lexicographic order of `(i, j)`, and one demand `m_q ≥ k + 1` on the bounded place `q` for `PlaceBound` and `BranchPlaceBound` with bound `k`."
        "A `MutualExclusion` of fewer than two entries is never violated ([VER-002]), so its demands are left to the implementation and every choice is sound."
        "*When* the verifier runs the bound phase on a property, it *shall* return `Proven` exactly when, for every demand of the property, the query returned a `sat` model whose weighting the exact re-check accepts for that demand."
        "The verifier *shall not* return `Violated` from the bound phase; every outcome of the phase other than `Proven` hands over to the next phase of the dispatch."
  reading "For every flat net (deposit rows, n places), injected places envs, seed a0, demand d and weighting y: the re-check C accepts y for d only when y is non-negative on every place below n, zero on every place below n that some row resets or consumes all of, zero on every injected place, does not increase along any row (y·(post − pre) ≤ 0 over the row's count column), and y·a0 + 1 ≤ y·d; and C accepts every y that meets these conditions and fits the range 2^127 − 2 (LinFits: every weight, and the sum of the absolute values of the terms of each row's y·C, of y·a0 and of y·d, at most 2^127 − 2);"
          "the demands of Unreachable(ps) are the one demand 1 on every place of ps and 0 elsewhere;"
          "the demands of MutualExclusion(ps) with at least two entries are, per position pair i < j of ps in lexicographic order of (i, j) (pairsOf), the demand 1 on the entries ps[i] and ps[j] and 0 elsewhere;"
          "the demands of PlaceBound(q, k) are the one demand k + 1 on q and 0 elsewhere;"
          "the demands of BranchPlaceBound(q, k) are the one demand k + 1 on q and 0 elsewhere;"
          "the phase Ph returns Proven on a property exactly when, for every index i of the property's demand list with demand d, the answer to query i is sat with a weighting y that C accepts for d."
  assumes "The model is the triple (C, Dm, Ph) of LinCheckRel, LinDemandFn and LinPhaseRel. The flat net is a list of deposit rows (a transition and the multiset of places it deposits into, the count column IncidenceMatrix::from_flat_net builds, so a timeout forward from an exactly(k) input deposits k), the places are the flat indices below n, a marking is a count per place (AMarking), and the injected places envs are the resolved injection list. The witness triple is refBoundCheck (ShippedCheckD, Novel/LinearBound.lean), refBoundDemands and refBoundPhase."
          "Line 1 is the third, fourth, fifth and sixth quoted sentences. Its first half is the 'only when' of the fourth: a check that demands less than the listed conditions is killed (VER_015_forbids_checkNoEnv, checkNonStrict, checkNoPos, checkNoH1, checkNoRows, checkUnitColumn). Its second half is the 'shall accept every weighting' of the fourth, guarded by LinFits linRange: a check that demands more than the listed conditions on a weighting that fits (one that never accepts) is killed as well (VER_015_forbids_checkNever). The count column of the sixth quoted sentence is dotIncD: the row's deposit count on p minus pre, the input's required count, which for an all or atLeast input is its required minimum. The fifth quoted sentence is the slack between the halves: Rust computes in checked 128-bit integers and treats an overflow as a failed check (`check_linear_bound_exact`, linear_bound.rs), while Java and TypeScript compute in unbounded integers (LinearBound.checkExact, linear-bound.ts). Under LinFits no partial sum leaves [-(2^127 − 2), 2^127 − 2] whatever the order of the terms, and the seed sum plus one still fits, so the checked Rust re-check meets the second half; a weighting outside the range may be rejected, which the first half allows. VER_015_allows_checked shows a re-check that rejects every weighting outside the range, with the phase built on it, satisfies the statement. A weight outside 128 bits is a model Rust cannot decode, which line 6 reads as a sat answer whose weighting the check rejects; LinFits bounds every weight, so that case is outside the range as well. The reference refBoundCheck computes in unbounded integers and accepts every weighting that meets the conditions."
          "The zero weights on consume-all and reset places (H1) are stricter than soundness needs: a weighting that passes every other conjunct already excludes the violation (linear_bound_sound_noH1), and on the net netDrain dropping H1 proves a property the shipped check cannot (VER_015_h1_unused, h1_drop_gains). The line keeps H1 because the query and its golden scripts carry it; dropping it is a feature decision outside this migration (ruling D91, option b). The zero weights on injected places (H3') are needed for soundness: VER_015_env_zero (env_zero_is_necessary) shows a weighting that is non-negative, decreasing and separating but weights an injected place, on a net whose injections reach the violation."
          "Lines 2 to 5 are the first quoted sentence's demand and the seventh quoted sentence. Line 3 is the second quoted sentence: at two entries the one pair is the whole list (pairsOf_two), so the demand of a two-place MutualExclusion is both of its places; the lexicographic order is load-bearing because line 6 indexes the answers by the demand's position (VER_015_forbids_demandsMutexReversed). A MutualExclusion with fewer than two entries is the eighth quoted sentence: the statement leaves its demands free, and VER_015_sound holds for every choice because such a property is never violated (its Violates needs two marked entries). The Rust reference takes one demand over the whole list there; Java and TypeScript accept exactly two places, so AC4 byte-identity is not at stake. A place listed twice pairs with itself, and its pair demands 1 on that place, which a marked place meets, as VER-002's pairwise reading does. The property's places are resolved flat places: the verifier refuses a property naming a place the net does not resolve before any route runs (VER-003 AC5), so an unresolved name is not modelled."
          "Quiescence properties (DeadlockFree, TerminatesAtSink, QuiescentCount, JoinedOrDeadLettered) and the name-alignment properties of NU-055 have no demand (`violation_demand` returns None) and are not BoundProp values; that the phase is skipped for them, and under Ignore with environment places registered (VER-006 AC4), is a dispatch condition of the verifier pipeline, the B line deferred to RefVerifier (wave W10)."
          "Line 6 is the ninth quoted sentence and the second: the answers are indexed by the demand's position, each demand with its own query; a model whose weighting cannot be decoded is a sat answer whose weighting the check rejects. The runtime stops at the first part that does not prove and sends no later query; the line fixes the outcome only, which does not depend on the answers after that part. A Proven of the phase is sound from the statement alone: VER_015_sound derives, for every triple satisfying VER-015, that no marking reachable with injection (ReachADInj) violates the property under the conformance reference's Violates (VER-002), which is the first quoted sentence's 'no reachable marking meets the demand and the property is proven structurally'."
          "AC1 (when the bound query returns, for every demand, a weighting that passes the exact re-check, the property is Proven with method structural, without a fixpoint query, and the report names the bound and the demand) is line 6 for the verdict and VER_015_sound for what it means; method, the absence of a fixpoint query and the report line are the result record, the dispatch and the report text, outside the model (kind Q for the line; the dispatch is W10's)."
          "AC2 (unsat proceeds to the fixpoint query with the report line 'none separates the violation') and AC3 (a model that fails the exact re-check is reported inconclusive and the fixpoint query runs) are line 6 for 'not Proven' (VER_015_nonvacuous: an unsat answer and a failing model both leave the phase unproven); the hand-over to the next phase and the report lines are the pipeline's (W10) and the report text (kind Q)."
          "AC4 (the bound script of the first demand is byte-identical across implementations and reported by encodeScripts()) is about the SMT-LIB text, checked by the golden-file parity tests of VER-013 (kind Q); the query and its text are not modelled."
          "AC5 (a genuine violation is never masked: the phase can only return Proven) and the tenth quoted sentence's first clause (the phase never returns Violated) are the type of the model: Ph is a Prop that says only whether the phase returns Proven, so no model of this type has a Violated outcome; with VER_015_sound, a Proven of the phase holds on every reachable marking. The tenth quoted sentence's second clause, the hand-over of every other outcome to the next phase of the dispatch, is the pipeline's (W10)."
          "AC6 (on a nu-net with an exact name-coloured plan the bound runs before the coloured query) and AC7 (on a net the enumeration route takes, the bound runs before the enumeration, sends its query at most once per demand, and a drained forward lets the enumeration decide first), with the two closing paragraphs (On nu-nets, On nets the enumeration route takes), are the dispatch order, deferred to the RefVerifier pipeline (W10). Their soundness argument for nu-nets, that every marking the nu semantics reaches is reachable on the flat name-blind net, is NU-053's and Novel/RouteA/SlotBound.lean's."
          "The paragraph on the query (variables per flat place, the rows, the demand inequality, phase bound) describes the script, not modelled (kind Q, VER-013 golden scripts); its constraints are those of line 1. The sentence that unsat, unknown and any transport failure hand over to the next phase of the dispatch is the pipeline's (W10). The NU-050 over-approximation note on a nu-net's verdict is NU-050's. The paragraph 'This closes the class of proofs IC3 does not find' and the timings in the closing paragraphs are motivation and measurement, not requirements."
          "The option (on by default, linearBound(false) disables the phase) is configuration (kind N), as are the Implementation notes. The test derivation (the fork that may halt: unreachable{ra, rb, halt} proven by the bound 2·p0 + a + b + 2·done + halt + ra + rb ≤ 2, mutualExclusion(ra, rb) reachable and handed over) is AC1 and AC2 on one net, as above; the bound it names is checked by the ports' tests, and VER_015_nonvacuous shows the same shape on the chain t1: p0 to p1, t2: p1 to p2."
  signoff "pending"
  statement : LinCheckRel → LinDemandFn → LinPhaseRel → Prop :=
    fun C Dm Ph =>
      (∀ rows envs a0 d y n,
        (C rows envs a0 d y n →
          (∀ p, p < n → 0 ≤ y p) ∧
          (∀ tr ∈ rows, ∀ p, p < n →
            tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
          (∀ p ∈ envs, y p = 0) ∧
          (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
          dot y a0 n + 1 ≤ dot y d n) ∧
        ((∀ p, p < n → 0 ≤ y p) ∧
          (∀ tr ∈ rows, ∀ p, p < n →
            tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
          (∀ p ∈ envs, y p = 0) ∧
          (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
          dot y a0 n + 1 ≤ dot y d n →
          LinFits linRange rows a0 d y n → C rows envs a0 d y n)) ∧
      (∀ ps, Dm (.unreachable ps) = [fun p => if p ∈ ps then 1 else 0]) ∧
      (∀ ps, 2 ≤ ps.length → Dm (.mutualExclusion ps) =
        (Novel.Pairwise.pairsOf ps).map fun pq => fun p => if p ∈ [pq.1, pq.2] then 1 else 0) ∧
      (∀ q k, Dm (.placeBound q k) = [fun p => if p = q then k + 1 else 0]) ∧
      (∀ q k, Dm (.branchPlaceBound q k) = [fun p => if p = q then k + 1 else 0]) ∧
      (∀ rows envs a0 n prop ans, Ph rows envs a0 n prop ans ↔
        ∀ i d, (Dm prop)[i]? = some d → ∃ y, ans i = .sat y ∧ C rows envs a0 d y n)

/- The pinned readable form of VER-015: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_015 : LinCheckRel → LinDemandFn → LinPhaseRel → Prop :=
fun C Dm Ph =>
  (∀ (rows : LinRows) (envs : List PlaceId) (a0 d : AMarking) (y : Weight) (n : ℕ),
      (C rows envs a0 d y n →
          (∀ p < n, 0 ≤ y p) ∧
            (∀ tr ∈ rows, ∀ p < n, tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
              (∀ p ∈ envs, y p = 0) ∧ (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ dot y a0 n + 1 ≤ dot y d n) ∧
        ((∀ p < n, 0 ≤ y p) ∧
            (∀ tr ∈ rows, ∀ p < n, tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
              (∀ p ∈ envs, y p = 0) ∧ (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ dot y a0 n + 1 ≤ dot y d n →
          LinFits linRange rows a0 d y n → C rows envs a0 d y n)) ∧
    (∀ (ps : List PlaceId), Dm (BoundProp.unreachable ps) = [fun p => if p ∈ ps then 1 else 0]) ∧
      (∀ (ps : List PlaceId),
          2 ≤ ps.length →
            Dm (BoundProp.mutualExclusion ps) =
              List.map (fun pq p => if p ∈ [pq.1, pq.2] then 1 else 0) (Novel.Pairwise.pairsOf ps)) ∧
        (∀ (q : PlaceId) (k : ℕ), Dm (BoundProp.placeBound q k) = [fun p => if p = q then k + 1 else 0]) ∧
          (∀ (q : PlaceId) (k : ℕ), Dm (BoundProp.branchPlaceBound q k) = [fun p => if p = q then k + 1 else 0]) ∧
            ∀ (rows : LinRows) (envs : List PlaceId) (a0 : AMarking) (n : ℕ) (prop : BoundProp) (ans : ℕ → BoundAnswer),
              Ph rows envs a0 n prop ans ↔
                ∀ (i : ℕ) (d : AMarking), (Dm prop)[i]? = some d → ∃ y, ans i = BoundAnswer.sat y ∧ C rows envs a0 d y n
-/
#guard_msgs in #print VER_015

/-! ## The reference -/

/-- The reference re-check is line 1. -/
theorem ver015_check_iff (rows : LinRows) (envs : List PlaceId) (a0 d : AMarking) (y : Weight)
    (n : Nat) :
    ShippedCheckD rows envs a0 d y n ↔
      (∀ p, p < n → 0 ≤ y p) ∧
      (∀ tr ∈ rows, ∀ p, p < n →
        tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
      (∀ p ∈ envs, y p = 0) ∧
      (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
      dot y a0 n + 1 ≤ dot y d n :=
  ⟨fun h => ⟨h.pos, h.h1, h.henv, h.dec, h.sep⟩, fun ⟨a, b, c, e, f⟩ => ⟨a, b, c, e, f⟩⟩

/-- One part proves exactly when its answer is `sat` with a weighting the check accepts. -/
theorem ver015_partOk_iff (rows : LinRows) (envs : List PlaceId) (a0 : AMarking) (n : Nat)
    (d : AMarking) (x : BoundAnswer) :
    ver015_partOk rows envs a0 n d x ↔ ∃ y, x = .sat y ∧ ShippedCheckD rows envs a0 d y n := by
  cases x <;> simp [ver015_partOk]

/-- The loop proves exactly when every part from index `i` on proves. -/
theorem ver015_loop_iff (rows : LinRows) (envs : List PlaceId) (a0 : AMarking) (n : Nat)
    (ans : Nat → BoundAnswer) (ds : List AMarking) (i : Nat) :
    ver015_loop rows envs a0 n ans i ds ↔
      ∀ j d, ds[j]? = some d → ∃ y, ans (i + j) = .sat y ∧ ShippedCheckD rows envs a0 d y n := by
  induction ds generalizing i with
  | nil => simp [ver015_loop]
  | cons d ds ih =>
    simp only [ver015_loop, ver015_partOk_iff, ih]
    constructor
    · rintro ⟨h0, hr⟩ j e hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simpa using h0
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        obtain ⟨y, hy, hc⟩ := hr j e hj
        exact ⟨y, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hy, hc⟩
    · intro h
      refine ⟨by simpa using h 0 d rfl, fun j e hj => ?_⟩
      obtain ⟨y, hy, hc⟩ := h (j + 1) e (by simpa using hj)
      exact ⟨y, by rw [show i + 1 + j = i + (j + 1) by omega]; exact hy, hc⟩

/-- At two or more entries the reference demands of a `MutualExclusion` are its pairs. -/
theorem ver015_demands_mutex (ps : List PlaceId) (h : 2 ≤ ps.length) :
    refBoundDemands (.mutualExclusion ps) =
      (Novel.Pairwise.pairsOf ps).map fun pq => demand (.allMarked [pq.1, pq.2]) := by
  show (if ps.length ≤ 2 then [demand (.allMarked ps)]
    else (Novel.Pairwise.pairsOf ps).map fun pq => demand (.allMarked [pq.1, pq.2])) = _
  by_cases hl : ps.length ≤ 2
  · rw [if_pos hl]
    match ps, h, hl with
    | [p, q], _, _ => simp [Novel.Pairwise.pairsOf]
  · rw [if_neg hl]

/-- The reference triple satisfies VER-015. -/
@[evidence holds VER_015]
theorem VER_015_reference : VER_015 refBoundCheck refBoundDemands refBoundPhase := by
  refine ⟨fun rows envs a0 d y n => ⟨(ver015_check_iff rows envs a0 d y n).mp,
      fun hc _ => (ver015_check_iff rows envs a0 d y n).mpr hc⟩, fun _ => rfl,
    fun ps h => ver015_demands_mutex ps h, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro rows envs a0 n prop ans
  rw [refBoundPhase, ver015_loop_iff]
  simp only [Nat.zero_add]
  rfl

/-- A re-check that also rejects every weighting outside the range, as Rust's checked `i128`
arithmetic may. -/
def ver015_checkChecked : LinCheckRel := fun rows envs a0 d y n =>
  ShippedCheckD rows envs a0 d y n ∧ LinFits linRange rows a0 d y n

/-- The phase over the checked re-check. -/
def ver015_phaseChecked : LinPhaseRel := fun rows envs a0 n prop ans =>
  ∀ i d, (refBoundDemands prop)[i]? = some d →
    ∃ y, ans i = .sat y ∧ ver015_checkChecked rows envs a0 d y n

/-- ✓ The fifth quoted sentence: a re-check that rejects a weighting whose sums leave the range,
with the phase built on it, still satisfies VER-015. Line 1 promises acceptance only inside
`LinFits linRange`. -/
@[evidence allows VER_015]
theorem VER_015_allows_checked :
    VER_015 ver015_checkChecked refBoundDemands ver015_phaseChecked := by
  obtain ⟨-, h2, h3, h4, h5, -⟩ := VER_015_reference
  exact ⟨fun rows envs a0 d y n =>
      ⟨fun hc => (ver015_check_iff rows envs a0 d y n).mp hc.1,
        fun hc hf => ⟨(ver015_check_iff rows envs a0 d y n).mpr hc, hf⟩⟩,
    h2, h3, h4, h5, fun _ _ _ _ _ _ => Iff.rfl⟩

/-! ## What a `Proven` of the phase means -/

/-- The property as the conformance reference reads it ([VER-002]): `BranchPlaceBound` is a
place bound. -/
def BoundProp.toRef : BoundProp → Reference.Property PlaceId
  | .unreachable ps => .unreachable ps
  | .mutualExclusion ps => .mutualExclusion ps
  | .placeBound q k => .placeBound q k
  | .branchPlaceBound q k => .placeBound q k

/-- From the statement alone, the re-check `C` is the shipped one. -/
theorem ver015_check_of {C : LinCheckRel} {Dm : LinDemandFn} {Ph : LinPhaseRel}
    (h : VER_015 C Dm Ph) {rows : LinRows} {envs : List PlaceId} {a0 d : AMarking} {y : Weight}
    {n : Nat} (hc : C rows envs a0 d y n) : ShippedCheckD rows envs a0 d y n :=
  (ver015_check_iff rows envs a0 d y n).mpr ((h.1 rows envs a0 d y n).1 hc)

/-- **A `Proven` of the phase is sound**, from the statement alone: on every triple satisfying
VER-015, when the phase returns `Proven` on a property, no marking reachable from the seed with
injection (`ReachADInj`, the deposit rows) violates the property as the conformance reference
reads it (`Reference.Violates`), whatever net the reference reads quiescence on. This is the
sound direction of AC1 and the content of AC5. -/
@[evidence cites "VER-015" "if y·d > y·M0 for some such y, no reachable marking meets the demand and the property is proven structurally; a pairwise MutualExclusion is proven when every pair's demand is separated"]
theorem VER_015_sound {C : LinCheckRel} {Dm : LinDemandFn} {Ph : LinPhaseRel}
    (h : VER_015 C Dm Ph) {rows : LinRows} {envs : List PlaceId} {a0 : AMarking} {n : Nat}
    {prop : BoundProp} {ans : Nat → BoundAnswer} (hp : Ph rows envs a0 n prop ans)
    (net : Reference.Net PlaceId) :
    ∀ a, ReachADInj rows envs a0 a → ¬ Reference.Violates net prop.toRef a := by
  have ⟨_, hU, hM, hP, hB, h3⟩ := h
  have hparts := (h3 rows envs a0 n prop ans).mp hp
  -- every demand of the list excludes the reachable markings that cover it
  have part : ∀ i d, (Dm prop)[i]? = some d → ∀ a, ReachADInj rows envs a0 a → ¬ Covers d a n :=
    fun i d hd a ha => by
      obtain ⟨y, -, hc⟩ := hparts i d hd
      exact linear_bound_sound_rows (ver015_check_of h hc) a ha
  intro a ha hv
  cases prop with
  | unreachable ps =>
    refine part 0 _ (by rw [hU]; rfl) a ha fun p _ => ?_
    have hv' : ∀ q ∈ ps, a q ≠ 0 := hv
    by_cases hq : p ∈ ps
    · rw [if_pos hq]; exact Nat.one_le_iff_ne_zero.mpr (hv' p hq)
    · rw [if_neg hq]; exact Nat.zero_le _
  | mutualExclusion ps =>
    have hv' : 2 ≤ (ps.filter (fun p => a p != 0)).length := hv
    have hlen : 2 ≤ ps.length := le_trans hv' (List.length_filter_le _ _)
    have hf : (fun p => a p != 0) = (fun p => decide (1 ≤ a p)) := by
      funext p; cases a p <;> simp
    rw [hf] at hv'
    obtain ⟨pq, hpq, hboth⟩ := List.any_eq_true.mp
      ((Novel.Pairwise.any_pairsOf_iff (fun p => decide (1 ≤ a p)) ps).mpr hv')
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
    have hmem : (fun p => if p ∈ [pq.1, pq.2] then 1 else 0) ∈ Dm (.mutualExclusion ps) := by
      rw [hM ps hlen]; exact List.mem_map.mpr ⟨pq, hpq, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    refine part i _ hi a ha fun p _ => ?_
    show (if p ∈ [pq.1, pq.2] then 1 else 0) ≤ a p
    by_cases hq : p ∈ [pq.1, pq.2]
    · rw [if_pos hq]
      rcases List.mem_pair.mp hq with rfl | rfl
      · exact hboth.1
      · exact hboth.2
    · rw [if_neg hq]; exact Nat.zero_le _
  | placeBound q k =>
    have hv' : k < a q := hv
    refine part 0 _ (by rw [hP]; rfl) a ha fun p _ => ?_
    by_cases hq : p = q
    · subst hq; rw [if_pos rfl]; omega
    · rw [if_neg hq]; exact Nat.zero_le _
  | branchPlaceBound q k =>
    have hv' : k < a q := hv
    refine part 0 _ (by rw [hB]; rfl) a ha fun p _ => ?_
    by_cases hq : p = q
    · subst hq; rw [if_pos rfl]; omega
    · rw [if_neg hq]; exact Nat.zero_le _

/-- **H3′ is needed** (`env_zero_is_necessary`): a weighting that is non-negative, decreasing and
separating, but weights the injected place, would prove `PlaceBound(p₁, 0)` on `netEnv`, whose
injection reaches `p₁ = 1`. -/
@[evidence cites "VER-015" "y_p = 0 on every injected environment place (H3'): without it the bound proves a property injection violates"]
theorem VER_015_env_zero :
    (∀ p, p < 2 → 0 ≤ yEnv p)
    ∧ (∀ ft ∈ netEnv, dotInc yEnv ft 2 ≤ 0)
    ∧ dot yEnv m0A 2 < dot yEnv dEnv 2
    ∧ yEnv envPlace ≠ 0
    ∧ ∃ a, ReachAInj netEnv [envPlace] m0A a ∧ Covers dEnv a 2 :=
  env_zero_is_necessary

/-- **H1 is stricter than soundness needs** (`h1_drop_gains`): on `netDrain` no weighting passes
the shipped check, one that passes every conjunct but H1 exists, and the property holds. -/
@[evidence cites "VER-015" "y_p = 0 on every consume-all / reset place (H1): carried by the check, not needed for the soundness of a decreasing law"]
theorem VER_015_h1_unused :
    (¬ ∃ y, ShippedCheck netDrain [] a0Drain (demand propDrain) y 2)
    ∧ ((∀ p, p < 2 → 0 ≤ yDrain p)
      ∧ (∀ ft ∈ netDrain, dotInc yDrain ft 2 ≤ 0)
      ∧ dot yDrain a0Drain 2 < dot yDrain (demand propDrain) 2
      ∧ ¬ ZeroOnNonlinear yDrain tDrain 2)
    ∧ ProvenFor (ReachAInj netDrain [] a0Drain) (safetyBad propDrain) :=
  h1_drop_gains

/-! ## Examples -/

/-- `t1`: one token from place `0` to place `1`. -/
def ver015_t1 : Transition :=
  { name := "t1", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- `t2`: one token from place `1` to place `2`. -/
def ver015_t2 : Transition :=
  { name := "t2", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The chain `t1: p0 → p1`, `t2: p1 → p2`, as deposit rows. -/
def ver015_chain : LinRows := [(ver015_t1, [1]), (ver015_t2, [2])]

/-- One token on `p0`. -/
def ver015_a0 : AMarking := fun p => if p = 0 then 1 else 0

/-- Weight `1` on each of the three places: the one token is conserved. -/
def ver015_y1 : Weight := fun p => if p < 3 then 1 else 0

/-- ✓ On the chain from `{p0: 1}`, the conserved count `p0 + p1 + p2 ≤ 1` separates every pair of
`MutualExclusion(p0, p1, p2)`, so the phase proves it with three `sat` answers; it proves
`PlaceBound(p2, 1)`; it does not prove `PlaceBound(p2, 0)` from the same weighting (the chain
reaches `p2 = 1`); and an `unsat` answer to the last pair's query, or a model whose weighting
fails the re-check, leaves the three-place `MutualExclusion` unproven. -/
@[evidence nonvacuous VER_015]
theorem VER_015_nonvacuous :
    refBoundPhase ver015_chain [] ver015_a0 3 (.mutualExclusion [0, 1, 2])
      (fun _ => .sat ver015_y1) ∧
    refBoundPhase ver015_chain [] ver015_a0 3 (.placeBound 2 1) (fun _ => .sat ver015_y1) ∧
    ¬ refBoundPhase ver015_chain [] ver015_a0 3 (.placeBound 2 0) (fun _ => .sat ver015_y1) ∧
    ¬ refBoundPhase ver015_chain [] ver015_a0 3 (.mutualExclusion [0, 1, 2])
      (fun i => if i = 2 then .unsat else .sat ver015_y1) ∧
    ¬ refBoundPhase ver015_chain [] ver015_a0 3 (.mutualExclusion [0, 1, 2])
      (fun _ => .sat (fun _ => 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(ver015_check_iff _ _ _ _ _ _).mpr (by decide),
      (ver015_check_iff _ _ _ _ _ _).mpr (by decide),
      (ver015_check_iff _ _ _ _ _ _).mpr (by decide), trivial⟩
  · exact ⟨(ver015_check_iff _ _ _ _ _ _).mpr (by decide), trivial⟩
  · rintro ⟨hc, -⟩
    have := hc.sep
    revert this
    decide
  · rintro ⟨-, -, hc, -⟩
    exact hc
  · rintro ⟨hc, -⟩
    have := hc.sep
    revert this
    decide

/-! ## Wrong models -/

/-- A re-check that never accepts: the phase then never proves. -/
def ver015_checkNever : LinCheckRel := fun _ _ _ _ _ _ => False

/-- ✗ Line 1 forbids a re-check that never accepts: on the empty net, `y = d = 1` on place `0`
from the empty seed passes every listed condition. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNever :
    ¬ VER_015 ver015_checkNever refBoundDemands refBoundPhase := by
  intro h
  exact (h.1 [] [] (fun _ => 0) (fun p => if p = 0 then 1 else 0)
    (fun p => if p = 0 then 1 else 0) 1).2 (by decide) (by decide)

/-- A re-check that does not zero the injected places (H3′ dropped). -/
def ver015_checkNoEnv : LinCheckRel := fun rows _ a0 d y n =>
  (∀ p, p < n → 0 ≤ y p) ∧
  (∀ tr ∈ rows, ∀ p, p < n →
    tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
  (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
  dot y a0 n + 1 ≤ dot y d n

/-- ✗ Line 1 forbids weighting an injected place: with place `0` injected, the weighting `1` on
it passes the relaxed check but not the shipped one. `VER_015_env_zero` is why this matters. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNoEnv :
    ¬ VER_015 ver015_checkNoEnv refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [] [0] (fun _ => 0) (fun p => if p = 0 then 1 else 0)
    (fun p => if p = 0 then 1 else 0) 1).1 (by unfold ver015_checkNoEnv; decide)
  revert this
  decide

/-- A re-check with non-strict separation: `y·a0 ≤ y·d`. -/
def ver015_checkNonStrict : LinCheckRel := fun rows envs a0 d y n =>
  (∀ p, p < n → 0 ≤ y p) ∧
  (∀ tr ∈ rows, ∀ p, p < n →
    tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
  (∀ p ∈ envs, y p = 0) ∧
  (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
  dot y a0 n ≤ dot y d n

/-- ✗ Line 1 forbids non-strict separation: the zero weighting would "separate" any demand. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNonStrict :
    ¬ VER_015 ver015_checkNonStrict refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [] [] (fun _ => 0) (fun p => if p = 0 then 1 else 0) (fun _ => 0) 1).1
    (by unfold ver015_checkNonStrict; decide)
  revert this
  decide

/-- A re-check without `y ≥ 0`. -/
def ver015_checkNoPos : LinCheckRel := fun rows envs a0 d y n =>
  (∀ tr ∈ rows, ∀ p, p < n →
    tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
  (∀ p ∈ envs, y p = 0) ∧
  (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
  dot y a0 n + 1 ≤ dot y d n

/-- ✗ Line 1 forbids a negative weight: `y = −1` on place `0` "separates" the demand `1` from the
seed `2`, which already meets it. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNoPos :
    ¬ VER_015 ver015_checkNoPos refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [] [] (fun _ => 2) (fun _ => 1) (fun _ => -1) 1).1 (by unfold ver015_checkNoPos; decide)
  revert this
  decide

/-- A re-check without the zero weights on consume-all and reset places (H1 dropped). -/
def ver015_checkNoH1 : LinCheckRel := fun rows envs a0 d y n =>
  (∀ p, p < n → 0 ≤ y p) ∧
  (∀ p ∈ envs, y p = 0) ∧
  (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
  dot y a0 n + 1 ≤ dot y d n

/-- ✗ Line 1 forbids dropping H1: on `netDrain` (`all(p₀) → p₁`) the weighting `yDrain` passes
the relaxed check but weights the consume-all place. The relaxed check is still sound
(`VER_015_h1_unused`); the statement follows the shipped check and its scripts. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNoH1 :
    ¬ VER_015 ver015_checkNoH1 refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [(tDrain, [1])] [] a0Drain (demand propDrain) yDrain 2).1 (by unfold ver015_checkNoH1; decide)
  revert this
  decide

/-- A re-check without the row condition `y·C[t] ≤ 0`. -/
def ver015_checkNoRows : LinCheckRel := fun rows envs a0 d y n =>
  (∀ p, p < n → 0 ≤ y p) ∧
  (∀ tr ∈ rows, ∀ p, p < n →
    tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
  (∀ p ∈ envs, y p = 0) ∧
  dot y a0 n + 1 ≤ dot y d n

/-- ✗ Line 1 forbids dropping the row condition, the conjunct soundness rests on: on the one row
`t1: p0 → p1` from `{p0: 1}`, the weighting `1` on `p1` separates the demand `m_{p1} ≥ 1` from
the seed, but `t1` increases it and reaches that demand. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkNoRows :
    ¬ VER_015 ver015_checkNoRows refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [(ver015_t1, [1])] [] ver015_a0 (fun p => if p = 1 then 1 else 0)
    (fun p => if p = 1 then 1 else 0) 2).1 (by unfold ver015_checkNoRows; decide)
  revert this
  decide

/-- A re-check that reads a deposit row as one token per claimed place (`dotInc`, the column
before the IO-014 fix) in place of its count column. -/
def ver015_checkUnitColumn : LinCheckRel := fun rows envs a0 d y n =>
  (∀ p, p < n → 0 ≤ y p) ∧
  (∀ tr ∈ rows, ∀ p, p < n →
    tr.1.resets.contains p = true ∨ consumeAllAt tr.1 p = true → y p = 0) ∧
  (∀ p ∈ envs, y p = 0) ∧
  (∀ tr ∈ rows, dotInc y tr n ≤ 0) ∧
  dot y a0 n + 1 ≤ dot y d n

/-- ✗ Line 1 forbids the one-token column (the sixth quoted sentence's count): on the timeout row
`[b, b]` of `exactly(2, a)` from `{a: 2}`, the weighting `a + 2b` is zero on the one-token column
and separates `m_b ≥ 2`, but the row deposits two tokens on `b` and reaches `{b: 2}`. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_checkUnitColumn :
    ¬ VER_015 ver015_checkUnitColumn refBoundDemands refBoundPhase := by
  intro h
  have := (h.1 [(tFwd, [pb, pb])] [] (fun p => if p = 0 then 2 else 0)
    (fun p => if p = 1 then 2 else 0) (fun p => if p = 0 then 1 else if p = 1 then 2 else 0)
    3).1 (by unfold ver015_checkUnitColumn; decide)
  revert this
  decide

/-- Demands that read a bound `k` as `m_p ≥ k`. -/
def ver015_demandsOffByOne : LinDemandFn
  | .placeBound q k => [fun p => if p = q then k else 0]
  | prop => refBoundDemands prop

/-- ✗ Line 4 forbids the demand `m_p ≥ k` for `PlaceBound(p, k)`: a marking holding exactly the
bound is no violation. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsOffByOne :
    ¬ VER_015 refBoundCheck ver015_demandsOffByOne refBoundPhase := by
  intro h
  have h4 := congrArg (fun l : List AMarking => l.map (· 0)) (h.2.2.2.1 0 0)
  revert h4
  decide

/-- Demands that read a `MutualExclusion` of three or more places as one demand over all of
them. -/
def ver015_demandsMutexAll : LinDemandFn
  | .mutualExclusion ps => [demand (.allMarked ps)]
  | prop => refBoundDemands prop

/-- ✗ Line 3 forbids reading `MutualExclusion(p0, p1, p2)` as one demand: "all three marked" is
not the pairwise violation, and its bound would prove a property two marked places violate. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsMutexAll :
    ¬ VER_015 refBoundCheck ver015_demandsMutexAll refBoundPhase := by
  intro h
  have h3 := congrArg List.length (h.2.2.1 [0, 1, 2] (by decide))
  revert h3
  decide

/-- Demands that list the pairs of a `MutualExclusion` in reverse order. -/
def ver015_demandsMutexReversed : LinDemandFn
  | .mutualExclusion ps => (refBoundDemands (.mutualExclusion ps)).reverse
  | prop => refBoundDemands prop

/-- ✗ Line 3 forbids any other order of the pairs: the first demand of
`MutualExclusion(p0, p1, p2)` is the pair `(p0, p1)`, not `(p1, p2)`. The order matters because
line 6 matches the `i`-th answer with the `i`-th demand. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsMutexReversed :
    ¬ VER_015 refBoundCheck ver015_demandsMutexReversed refBoundPhase := by
  intro h
  have h3 := congrArg (fun l : List AMarking => l.map (· 2)) (h.2.2.1 [0, 1, 2] (by decide))
  revert h3
  decide

/-- Demands that read `Unreachable` as "some listed place marked": one demand per place. -/
def ver015_demandsUnreachSplit : LinDemandFn
  | .unreachable ps => ps.map fun q => fun p => if p = q then 1 else 0
  | prop => refBoundDemands prop

/-- ✗ Line 2 forbids splitting `Unreachable(p0, p1)` into one demand per place: the violation
needs both places marked, and the split reading would also refuse proofs the bound owes. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsUnreachSplit :
    ¬ VER_015 refBoundCheck ver015_demandsUnreachSplit refBoundPhase := by
  intro h
  have h2 := congrArg List.length (h.2.1 [0, 1])
  revert h2
  decide

/-- Demands that add one unit per listed position, the way `flatten` builds `post`. -/
def ver015_demandsUnreachCount : LinDemandFn
  | .unreachable ps => [fun p => ps.count p]
  | prop => refBoundDemands prop

/-- ✗ Line 2 forbids counting positions: `Unreachable(p0, p0)` is violated by one token on `p0`,
but the counted demand asks for two, so its bound could prove a property the seed violates. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsUnreachCount :
    ¬ VER_015 refBoundCheck ver015_demandsUnreachCount refBoundPhase := by
  intro h
  have h2 := congrArg (fun l : List AMarking => l.map (· 0)) (h.2.1 [0, 0])
  revert h2
  decide

/-- Demands that read a `BranchPlaceBound` `k` as `m_p ≥ k`. -/
def ver015_demandsBranchOffByOne : LinDemandFn
  | .branchPlaceBound q k => [fun p => if p = q then k else 0]
  | prop => refBoundDemands prop

/-- ✗ Line 5 forbids the demand `m_p ≥ k` for `BranchPlaceBound(p, k)`: like `PlaceBound`, a
marking holding exactly the bound is no violation ([NU-040]). -/
@[evidence forbids VER_015]
theorem VER_015_forbids_demandsBranchOffByOne :
    ¬ VER_015 refBoundCheck ver015_demandsBranchOffByOne refBoundPhase := by
  intro h
  have h5 := congrArg (fun l : List AMarking => l.map (· 0)) (h.2.2.2.2.1 0 0)
  revert h5
  decide

/-- A phase that believes a `sat` model without the re-check. -/
def ver015_phaseUnchecked : LinPhaseRel := fun _ _ _ _ prop ans =>
  ∀ i d, (refBoundDemands prop)[i]? = some d → ∃ y, ans i = .sat y

/-- ✗ Line 6 forbids believing a model without the re-check: the zero weighting from a `sat`
answer separates nothing, yet the phase would prove `PlaceBound(p0, 0)` on the empty net. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_phaseUnchecked :
    ¬ VER_015 refBoundCheck refBoundDemands ver015_phaseUnchecked := by
  intro h
  have hp : ver015_phaseUnchecked [] [] (fun _ => 0) 1 (.placeBound 0 0)
      (fun _ => .sat fun _ => 0) := fun _ _ _ => ⟨_, rfl⟩
  obtain ⟨y, hy, hc⟩ := (h.2.2.2.2.2 [] [] (fun _ => 0) 1 (.placeBound 0 0) _).mp hp 0 _ rfl
  cases hy
  have := hc.sep
  revert this
  decide

/-- A phase that proves a property as soon as its first demand is separated. -/
def ver015_phaseFirstPart : LinPhaseRel := fun rows envs a0 n prop ans =>
  ∃ d, (refBoundDemands prop).head? = some d ∧ ∃ y, ans 0 = .sat y ∧
    ShippedCheckD rows envs a0 d y n

/-- The seed `{p1: 1, p2: 1}`: the pair `(p1, p2)` is already marked. -/
def ver015_a12 : AMarking := demand (.allMarked [1, 2])

/-- Weight `1` on `p0` only. -/
def ver015_y0 : Weight := fun p => if p = 0 then 1 else 0

/-- ✗ Line 6 forbids proving a three-place `MutualExclusion` from its first pair: on the empty
net from `{p1: 1, p2: 1}`, the weighting `p0` separates the pair `(p0, p1)`, but the seed
itself violates the property through `(p1, p2)`. -/
@[evidence forbids VER_015]
theorem VER_015_forbids_phaseFirstPart :
    ¬ VER_015 refBoundCheck refBoundDemands ver015_phaseFirstPart := by
  intro h
  have hp : ver015_phaseFirstPart [] [] ver015_a12 3 (.mutualExclusion [0, 1, 2])
      (fun _ => .sat ver015_y0) :=
    ⟨_, rfl, ver015_y0, rfl, (ver015_check_iff _ _ _ _ _ _).mpr (by decide)⟩
  obtain ⟨y, -, hc⟩ := (h.2.2.2.2.2 [] [] ver015_a12 3 (.mutualExclusion [0, 1, 2]) _).mp hp 2
    ver015_a12 rfl
  have := hc.sep
  omega

end Libpetri.Spec
