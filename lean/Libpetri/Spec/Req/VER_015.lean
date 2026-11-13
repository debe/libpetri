import Libpetri.Spec.Registry
import Libpetri.Novel.LinearBound
import Libpetri.Reference.Semantics
import Libpetri.Spec.Verifier.Pipeline

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

A second block, `VER_015_order`, places the phase in the verifier's dispatch. It is a predicate
over a dispatch `D`, a list of pipeline steps (`GStep` of `Spec/Verifier/Pipeline.lean`) over a
`BoundCall`, the facts the runtimes' guards read of one call. In every run of `D`: Route B comes
before the bound, the bound before the colour-slot bound and the fixpoint query; the bound runs
only for a property with a demand with the phase on and not under `Ignore` with environment
places, at most once, and is never skipped on the way to the coloured plan or the fixpoint
query; on a net the enumeration route takes (no drained forward) it runs before the enumeration,
which comes next when the bound hands over, and on every other net not before it; each demand's
`bound` script is sent at most once. A bound step returns only `Proven` with method `structural`
or an aside, and it proves exactly when every demand's query was answered `sat` with a weighting
that passes the re-check, which ties it to the first block's phase
(`VER_015_order_follows_phase`). The witness `refBoundDispatch` is the runtimes' thirteen steps
with the bound in its two slots; eleven wrong dispatches and seven wrong bound steps are killed
on small calls. `Ver015OrderCovers` is the offer the block leaves to coverage: the dispatch runs
the bound and can prove there.
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
          "Quiescence properties (DeadlockFree, TerminatesAtSink, QuiescentCount, JoinedOrDeadLettered) and the name-alignment properties of NU-055 have no demand (`violation_demand` returns None) and are not BoundProp values. That the phase is skipped for a property without a demand, and under Ignore with environment places registered (VER-006 AC4), is line 4 of the block VER_015_order, whose BoundCall.safety means 'the property has a demand'. NU-055 calls NameAligned a reachability-safety property, and the runtimes' is_reachability_safety (isReachabilitySafety) answers true for it; it still never reaches the bound, because Route B alone decides a name-alignment property (NU-055), so the runtimes agree with line 4."
          "Line 6 is the ninth quoted sentence and the second: the answers are indexed by the demand's position, each demand with its own query; a model whose weighting cannot be decoded is a sat answer whose weighting the check rejects. The runtime stops at the first part that does not prove and sends no later query; the line fixes the outcome only, which does not depend on the answers after that part. A Proven of the phase is sound from the statement alone: VER_015_sound derives, for every triple satisfying VER-015, that no marking reachable with injection (ReachADInj) violates the property under the conformance reference's Violates (VER-002), which is the first quoted sentence's 'no reachable marking meets the demand and the property is proven structurally'."
          "AC1 (when the bound query returns, for every demand, a weighting that passes the exact re-check, the property is Proven with method structural, without a fixpoint query, and the report names the bound and the demand) is line 6 for the verdict and VER_015_sound for what it means; method, the absence of a fixpoint query and the report line are the result record, the dispatch and the report text, outside the model (kind Q for the line; the dispatch is the block VER_015_order)."
          "AC2 (unsat proceeds to the fixpoint query with the report line 'none separates the violation') and AC3 (a model that fails the exact re-check is reported inconclusive and the fixpoint query runs) are line 6 for 'not Proven' (VER_015_nonvacuous: an unsat answer and a failing model both leave the phase unproven); the hand-over to the next phase is line 9 of the block VER_015_order, and the report lines are report text (kind Q)."
          "AC4 (the bound script of the first demand is byte-identical across implementations and reported by encodeScripts()) is about the SMT-LIB text, checked by the golden-file parity tests of VER-013 (kind Q); the query and its text are not modelled."
          "AC5 (a genuine violation is never masked: the phase can only return Proven) and the tenth quoted sentence's first clause (the phase never returns Violated) are the type of the model: Ph is a Prop that says only whether the phase returns Proven, so no model of this type has a Violated outcome; with VER_015_sound, a Proven of the phase holds on every reachable marking. The tenth quoted sentence's second clause, the hand-over of every other outcome to the next phase of the dispatch, is line 9 of the block VER_015_order."
          "AC6 (on a nu-net with an exact name-coloured plan the bound runs before the coloured query) and AC7 (on a net the enumeration route takes, the bound runs before the enumeration, sends its query at most once per demand, and a drained forward lets the enumeration decide first), with the two closing paragraphs (On nu-nets, On nets the enumeration route takes), are the dispatch order, the block VER_015_order. Their soundness argument for nu-nets, that every marking the nu semantics reaches is reachable on the flat name-blind net, is NU-053's and Novel/RouteA/SlotBound.lean's."
          "The paragraph on the query (variables per flat place, the rows, the demand inequality, phase bound) describes the script, not modelled (kind Q, VER-013 golden scripts); its constraints are those of line 1. The sentence that unsat, unknown and any transport failure hand over to the next phase of the dispatch is line 9 of the block VER_015_order. The NU-050 over-approximation note on a nu-net's verdict is NU-050's. The paragraph 'This closes the class of proofs IC3 does not find' and the timings in the closing paragraphs are motivation and measurement, not requirements."
          "The option (on by default, linearBound(false) disables the phase) is configuration (kind N), as are the Implementation notes. The test derivation (the fork that may halt: unreachable{ra, rb, halt} proven by the bound 2·p0 + a + b + 2·done + halt + ra + rb ≤ 2, mutualExclusion(ra, rb) reachable and handed over) is AC1 and AC2 on one net, as above; the bound it names is checked by the ports' tests, and VER_015_nonvacuous shows the same shape on the chain t1: p0 to p1, t2: p1 to p2."
  signoff "2026-11-13 dd4294169756b836 ai"
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
  have part : ∀ i d, (Dm prop)[i]? = some d → ∀ a, ReachADInj rows envs a0 a →
      ¬ Novel.LinearBound.Covers d a n :=
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
    ∧ ∃ a, ReachAInj netEnv [envPlace] m0A a ∧ Novel.LinearBound.Covers dEnv a 2 :=
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

/-! ## The dispatch order: what a run of the pipeline reads -/

open Libpetri.Spec.Verifier

/-- **What the bound's place in the dispatch reads of one verification call**: the facts the
runtimes' guards test, the bound scripts of the property's demands, and, for every other step of
the pipeline, whether it runs and what it returns. -/
structure BoundCall where
  /-- The property has a demand: it is a `PlaceBound`, `BranchPlaceBound`, `MutualExclusion` or
  `Unreachable` property. The name-alignment properties of [NU-055] have none. -/
  safety : Bool
  /-- The bound phase is on (`linearBound`, on by default). -/
  enabled : Bool
  /-- The environment mode is `Ignore` ([VER-006]). -/
  ignore : Bool
  /-- Environment places are registered on the net the dispatcher receives. -/
  envPlaces : Bool
  /-- The rest of the enumeration route's guard ([VER-017]): no ν-join, every transition
  `immediate`, a positive class budget. -/
  enumGate : Bool
  /-- The net has a drained forward ([IO-014], [VER-001] AC5). -/
  drained : Bool
  /-- The solver can be started ([VER-013]). -/
  solverUp : Bool
  /-- One entry per demand, in demand order: the demand's `bound` script, and whether the
  weighting of a `sat` model passes the exact re-check. -/
  checks : List (String × Bool)
  /-- Whether each other step of the pipeline runs on this call. -/
  applies : String → Bool
  /-- What each other step of the pipeline returns on this call. -/
  outcome : String → PhaseOut

namespace BoundCall

/-- The bound phase may run: a property with a demand, the phase on, and not `Ignore` with
environment places registered. -/
def phaseOk (q : BoundCall) : Bool := q.safety && q.enabled && !(q.ignore && q.envPlaces)

/-- The enumeration route of [VER-017] applies: its guard, and no environment place. -/
def enumRoute (q : BoundCall) : Bool := q.enumGate && !q.envPlaces

/-- The bound runs ahead of the enumeration: the enumeration route applies, the net has no
drained forward, and the phase may run. -/
def early (q : BoundCall) : Bool := q.enumRoute && !q.drained && q.phaseOk

end BoundCall

/-- **A dispatch**: the pipeline's steps over a verification call. -/
abbrev BoundDispatch : Type := List (GStep BoundCall)

/-- The steps a run of the dispatch `D` enters, in order, from a trail `t`. -/
def boundLog (D : BoundDispatch) (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall)
    (t : Trail) : List String :=
  (runPipeline O stop o q D t).2.entered

/-! ## The reference dispatch -/

/-- **The bound phase as a program**: one `bound` query per demand, in demand order. A `sat`
answer whose weighting passes the exact re-check goes on to the next demand; anything else
hands over. Every demand separated is `Proven` with method `structural`. -/
def boundProg : List (String × Bool) → PhaseProg PhaseOut
  | [] => .done (.decided (.proven "structural") [] none)
  | (s, ok) :: rest => .ask s fun r =>
    match r with
    | .answer .sat =>
      if ok then boundProg rest
      else .done (.aside "inconclusive (solver model failed the exact re-check)")
    | .answer .unsat => .done (.aside "none separates the violation")
    | .answer .unknown => .done (.aside "inconclusive (Z3 answered unknown)")
    | .failure _ why => .done (.aside ("inconclusive (" ++ why ++ ")"))

/-- **The bound ahead of the enumeration**: entered when the enumeration route applies to a net
with no drained forward; when the solver cannot be started it hands over without a query. -/
def earlyBoundStep : GStep BoundCall :=
  { name := "linear bound", route := .structural, applies := fun _ q => q.early,
    run := fun _ q =>
      if q.solverUp then boundProg q.checks
      else .done (.aside "skipped, z3 unavailable") }

/-- **The bound in its slot after the P-invariants**: entered when the phase may run and the
bound did not run ahead of the enumeration. -/
def lateBoundStep : GStep BoundCall :=
  { name := "linear bound", route := .structural,
    applies := fun _ q => q.phaseOk && !q.early, run := fun _ q => boundProg q.checks }

/-- The enumeration step: entered when the enumeration route applies. -/
def enumBoundStep : GStep BoundCall :=
  { name := "state-space enumeration", route := .enumeration, applies := fun _ q => q.enumRoute,
    run := fun _ q => .done (q.outcome "state-space enumeration") }

/-- Any other step: entered and answered as the call says. -/
def otherBoundStep (name : String) (route : Route) : GStep BoundCall :=
  { name, route, applies := fun _ q => q.applies name, run := fun _ q => .done (q.outcome name) }

/-- The steps before the early bound: Route B. -/
def refBoundA : BoundDispatch := [otherBoundStep "Route B (ν name-partition graph)" .nuScg]

/-- The steps between the two bound slots. -/
def refBoundB : BoundDispatch :=
  [enumBoundStep, otherBoundStep "flattening" .smt, otherBoundStep "structural pre-check" .smt,
   otherBoundStep "P-invariant computation" .smt]

/-- The steps after the late bound. -/
def refBoundC : BoundDispatch :=
  [otherBoundStep "state-equation phase" .smt, otherBoundStep "firing-bound phase" .smt,
   otherBoundStep "colour-slot bound" .smt, otherBoundStep "witness phase" .smt,
   otherBoundStep "IC3/PDR query" .smt, otherBoundStep "certificate check" .smt]

/-- **The reference dispatch**: the runtimes' thirteen steps, with the bound in its two slots. -/
def refBoundDispatch : BoundDispatch :=
  refBoundA ++ earlyBoundStep :: (refBoundB ++ lateBoundStep :: refBoundC)

/- The reference dispatch is the witness of `VER_015_order`'s `holds` theorem. -/
#spec_witness refBoundDispatch

/-- The reference dispatch carries the runtimes' step names. -/
theorem refBoundDispatch_names : refBoundDispatch.map GStep.name = rtStepNames := rfl

/-! ## Runs of a pipeline -/

section RunLemmas

variable {Q : Type} {O : Oracle} {stop : Stop} {o : Options} {q : Q}

/-- The names of the steps of `steps` that apply to the call. -/
def ver015_applied (o : Options) (q : Q) (steps : List (GStep Q)) : List String :=
  (steps.filter fun s => s.applies o q).map GStep.name

/-- **A run enters a prefix of the steps that apply**: it never skips an applicable step, and it
ends at a stop or a decision. -/
theorem ver015_run_prefix : ∀ (steps : List (GStep Q)) (t : Trail),
    ∃ l, (runPipeline O stop o q steps t).2.entered = t.entered ++ l ∧
      l <+: ver015_applied o q steps
  | [], t => ⟨[], by simp [runPipeline], List.nil_prefix⟩
  | s :: ss, t => by
    simp only [runPipeline, ver015_applied, List.filter_cons]
    split
    · rename_i happ
      simp only [List.map_cons]
      split
      · exact ⟨[], by rw [pollStop_frame.2.2.1]; simp, List.nil_prefix⟩
      · have hf := (execProg_frame (O := O) (stop := stop) (s.run o q)
          ((pollStop stop t).2.enter s)).2.2
        have he : ((pollStop stop t).2.enter s).entered = t.entered ++ [s.name] := by
          simp only [Trail.enter]; rw [pollStop_frame.2.2.1]
        split
        · rename_i n t' hx
          rw [hx] at hf
          obtain ⟨l, hl, hsub⟩ := ver015_run_prefix ss t'
          refine ⟨s.name :: l, ?_, List.cons_prefix_cons.mpr ⟨rfl, hsub⟩⟩
          rw [hl, hf, he]; simp
        · rename_i v tr c t' hx
          rw [hx] at hf
          exact ⟨[s.name], by rw [hf, he],
            List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
    · rename_i happ
      exact ver015_run_prefix ss t

/-- The applied names are a sublist of all the step names. -/
theorem ver015_applied_sublist (steps : List (GStep Q)) :
    (ver015_applied o q steps).Sublist (steps.map GStep.name) :=
  List.filter_sublist.map _

/-- A step that does not apply drops out of the applied names. -/
theorem ver015_applied_skip {P S : List (GStep Q)} {s : GStep Q} (h : s.applies o q = false) :
    (ver015_applied o q (P ++ s :: S)).Sublist ((P ++ S).map GStep.name) := by
  have : ver015_applied o q (P ++ s :: S) = ver015_applied o q (P ++ S) := by
    simp [ver015_applied, List.filter_append, h]
  rw [this]
  exact ver015_applied_sublist _

/-- A step that applies is in the applied names, after those of the steps before it. -/
theorem ver015_applied_split {P S : List (GStep Q)} {s : GStep Q} (h : s.applies o q = true) :
    ver015_applied o q (P ++ s :: S) = ver015_applied o q P ++ s.name :: ver015_applied o q S := by
  simp [ver015_applied, List.filter_append, h]

/-- In a prefix of `A ++ a :: B`, a name that is not in `A` comes with `a`. -/
theorem ver015_prefix_reach {A B l : List String} {a b : String} (hl : l <+: A ++ a :: B)
    (hA : b ∉ A) (hm : b ∈ l) : a ∈ l := by
  induction A generalizing l with
  | nil =>
    rcases List.prefix_cons_iff.mp hl with rfl | ⟨r, rfl, -⟩
    · simp at hm
    · exact List.mem_cons_self
  | cons x A ih =>
    rcases List.prefix_cons_iff.mp hl with rfl | ⟨r, rfl, hr⟩
    · simp at hm
    · have hbx : b ≠ x := fun h => hA (h ▸ List.mem_cons_self)
      have hmr : b ∈ r := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h hbx
        · exact h
      exact List.mem_cons_of_mem _ (ih hr (fun h => hA (List.mem_cons_of_mem _ h)) hmr)

/-- In a prefix of `A ++ a :: e :: R`, the entry after an `a` that is not in `A` is `e`. -/
theorem ver015_prefix_next {A R pre post : List String} {a x e : String}
    (hl : pre ++ a :: x :: post <+: A ++ a :: e :: R) (hA : a ∉ A) (hp : a ∉ pre) : x = e := by
  induction A generalizing pre with
  | nil =>
    cases pre with
    | nil =>
      simp only [List.nil_append] at hl
      exact (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hl).2).1
    | cons p pre' =>
      simp only [List.nil_append, List.cons_append] at hl
      exact absurd ((List.cons_prefix_cons.mp hl).1 ▸ List.mem_cons_self) hp
  | cons y A ih =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons_append] at hl
      exact absurd ((List.cons_prefix_cons.mp hl).1 ▸ List.mem_cons_self) hA
    | cons p pre' =>
      simp only [List.cons_append] at hl
      exact ih (List.cons_prefix_cons.mp hl).2 (fun h => hA (List.mem_cons_of_mem _ h))
        (fun h => hp (List.mem_cons_of_mem _ h))

/-- **An applicable step is not passed over**: if a run enters a step named `b` that no step
before the applicable step `s` carries, it entered `s` too. -/
theorem ver015_run_reach {P S : List (GStep Q)} {s : GStep Q} {t : Trail} (ht : t.entered = [])
    (h : s.applies o q = true) {b : String} (hP : b ∉ P.map GStep.name)
    (hm : b ∈ (runPipeline O stop o q (P ++ s :: S) t).2.entered) :
    s.name ∈ (runPipeline O stop o q (P ++ s :: S) t).2.entered := by
  obtain ⟨l, hl, hp⟩ := ver015_run_prefix (O := O) (stop := stop) (o := o) (q := q) (P ++ s :: S) t
  rw [hl, ht, List.nil_append] at hm ⊢
  rw [ver015_applied_split h] at hp
  exact ver015_prefix_reach hp (fun h' => hP ((ver015_applied_sublist P).subset h')) hm

/-- **What a run enters applies**: every step a run enters from an empty log is a step of the
pipeline that applies to the call. -/
theorem ver015_run_mem {steps : List (GStep Q)} {t : Trail} (ht : t.entered = []) {n : String}
    (hm : n ∈ (runPipeline O stop o q steps t).2.entered) :
    ∃ s ∈ steps, s.applies o q = true ∧ s.name = n := by
  obtain ⟨l, hl, hp⟩ := ver015_run_prefix (O := O) (stop := stop) (o := o) (q := q) steps t
  rw [hl, ht, List.nil_append] at hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (hp.subset hm)
  obtain ⟨hs, ha⟩ := List.mem_filter.mp hs
  exact ⟨s, hs, ha, rfl⟩

/-- The log of a run from an empty log is a sublist of the applied names. -/
theorem ver015_run_sublist (steps : List (GStep Q)) {t : Trail} (ht : t.entered = []) :
    (runPipeline O stop o q steps t).2.entered.Sublist (ver015_applied o q steps) := by
  obtain ⟨l, hl, hp⟩ := ver015_run_prefix (O := O) (stop := stop) (o := o) (q := q) steps t
  rw [hl, ht, List.nil_append]
  exact hp.sublist

/-- **The scripts a run starts**: if every step's program, from any trail, starts a sublist of
`asks s`, a run of the pipeline starts a sublist of the `asks` of the steps that apply. -/
theorem ver015_run_started (asks : GStep Q → List String) : ∀ (steps : List (GStep Q)) (t : Trail),
    (∀ s ∈ steps, ∀ t' : Trail, ∃ l, (execProg O stop (s.run o q) t').2.started = t'.started ++ l ∧
      l.Sublist (asks s)) →
    ∃ l, (runPipeline O stop o q steps t).2.started = t.started ++ l ∧
      l.Sublist ((steps.filter fun s => s.applies o q).flatMap asks)
  | [], t, _ => ⟨[], by simp [runPipeline], by simp⟩
  | s :: ss, t, h => by
    simp only [runPipeline, List.filter_cons]
    split
    · rename_i happ
      simp only [List.flatMap_cons]
      split
      · exact ⟨[], by rw [pollStop_frame.2.2.2]; simp, List.nil_sublist _⟩
      · obtain ⟨l1, hl1, hs1⟩ := h s List.mem_cons_self ((pollStop stop t).2.enter s)
        have he : ((pollStop stop t).2.enter s).started = t.started := by
          simp only [Trail.enter]; exact pollStop_frame.2.2.2
        split
        · rename_i n t' hx
          rw [hx] at hl1
          obtain ⟨l2, hl2, hs2⟩ := ver015_run_started asks ss t'
            (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
          refine ⟨l1 ++ l2, ?_, hs1.append hs2⟩
          rw [hl2, hl1, he]; simp
        · rename_i v tr c t' hx
          rw [hx] at hl1
          exact ⟨l1, by rw [hl1, he], hs1.trans (List.sublist_append_left _ _)⟩
    · exact ver015_run_started asks ss t (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

end RunLemmas

/-- **`Ordered` by its cut point**, which `decide` can check. -/
theorem ver015_ordered_iff {e : List String} {a b : String} :
    Ordered e a b ↔ ∃ k, k < e.length + 1 ∧ b ∉ e.take k ∧ a ∉ e.drop k := by
  constructor
  · rintro ⟨e₁, e₂, rfl, h1, h2⟩
    exact ⟨e₁.length, by simp; omega, by simpa using h1, by simpa using h2⟩
  · rintro ⟨k, -, h1, h2⟩
    exact ⟨e.take k, e.drop k, (List.take_append_drop k e).symm, h1, h2⟩

/-! ## The reference steps of the bound -/

/-- **The bound phase only proves or hands over**: whatever the solver replies, the program
returns `Proven` with method `structural` and no trace, or steps aside. -/
theorem boundProg_out {R : String → SolverReply → Prop} :
    ∀ (l : List (String × Bool)) (out : PhaseOut), Yields R (boundProg l) out →
      (∃ n, out = .aside n) ∨ out = .decided (.proven "structural") [] none
  | [], out, h => by
    rw [boundProg, Yields.done_iff] at h
    exact Or.inr h
  | (s, ok) :: rest, out, h => by
    rw [boundProg] at h
    cases h with
    | @ask _ _ r _ _ hk =>
      rcases r with (_ | _ | _) | ⟨f, why⟩
      · by_cases hok : ok = true
        · simp only [hok, if_true] at hk
          exact boundProg_out rest out hk
        · simp only [hok, Bool.false_eq_true, if_false, Yields.done_iff] at hk
          exact Or.inl ⟨_, hk⟩
      · simp only [Yields.done_iff] at hk
        exact Or.inl ⟨_, hk⟩
      · simp only [Yields.done_iff] at hk
        exact Or.inl ⟨_, hk⟩
      · simp only [Yields.done_iff] at hk
        exact Or.inl ⟨_, hk⟩

/-- **The bound program proves only when every demand was separated**: a `Proven` means every
demand's query was answered `sat` and its weighting passed the re-check. -/
theorem boundProg_proves {R : String → SolverReply → Prop} :
    ∀ (l : List (String × Bool)) (out : PhaseOut), Yields R (boundProg l) out →
      out = .decided (.proven "structural") [] none → ∀ c ∈ l, c.2 = true ∧ R c.1 (.answer .sat)
  | [], _, _, _ => by simp
  | (s, ok) :: rest, out, h, hp => by
    rw [boundProg] at h
    cases h with
    | @ask _ _ r _ hr hk =>
      rcases r with (_ | _ | _) | ⟨f, why⟩
      · by_cases hok : ok = true
        · simp only [hok, if_true] at hk
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨hok, hr⟩
          · exact boundProg_proves rest out hk hp c hc
        · simp only [hok, Bool.false_eq_true, if_false, Yields.done_iff] at hk
          subst hk; cases hp
      all_goals (simp only [Yields.done_iff] at hk; subst hk; cases hp)

/-- **The bound program proves when every demand is separated**: when every demand's model
passes the re-check and the solver answers `sat` to every demand's script, the program returns
`Proven`. -/
theorem boundProg_conv {R : String → SolverReply → Prop} :
    ∀ (l : List (String × Bool)) (out : PhaseOut),
      (∀ c ∈ l, c.2 = true ∧ ∀ r, R c.1 r → r = .answer .sat) →
      Yields R (boundProg l) out → out = .decided (.proven "structural") [] none
  | [], out, _, h => by rw [boundProg, Yields.done_iff] at h; exact h
  | (s, ok) :: rest, out, hc, h => by
    rw [boundProg] at h
    cases h with
    | @ask _ _ r _ hr hk =>
      obtain ⟨hok, hsat⟩ := hc (s, ok) List.mem_cons_self
      have := hsat r hr
      subst this
      rw [if_pos hok] at hk
      exact boundProg_conv rest out (fun c h' => hc c (List.mem_cons_of_mem _ h')) hk

/-- Every program can return something when every script has an allowed reply. -/
theorem ver015_yields_exists {α : Type} {R : String → SolverReply → Prop}
    (hR : ∀ s, ∃ r, R s r) : ∀ P : PhaseProg α, ∃ a, Yields R P a
  | .done a => ⟨a, .done a⟩
  | .ask s k => by
    obtain ⟨r, hr⟩ := hR s
    obtain ⟨a, ha⟩ := ver015_yields_exists hR (k r)
    exact ⟨a, .ask hr ha⟩
  | .poll k => by
    obtain ⟨a, ha⟩ := ver015_yields_exists hR (k true)
    exact ⟨a, .poll true ha⟩

/-- A run of the bound program starts a sublist of its scripts, in order. -/
theorem boundProg_started {O : Oracle} {stop : Stop} :
    ∀ (l : List (String × Bool)) (t : Trail), ∃ l',
      (execProg O stop (boundProg l) t).2.started = t.started ++ l' ∧
        l'.Sublist (l.map Prod.fst)
  | [], t => ⟨[], by rw [boundProg, execProg_done]; simp, List.nil_sublist _⟩
  | (s, ok) :: rest, t => by
    rw [boundProg]
    simp only [execProg]
    split
    · refine ⟨[], ?_, List.nil_sublist _⟩
      show (pollStop stop t).2.started = _
      rw [List.append_nil]; exact pollStop_frame.2.2.2
    · have h2 : (pollStop stop { (pollStop stop t).2 with
          started := (pollStop stop t).2.started ++ [s] }).2.started = t.started ++ [s] := by
        rw [pollStop_frame.2.2.2, pollStop_frame.2.2.2]
      rcases hO : O s with (_ | _ | _) | ⟨f, why⟩
      · by_cases hok : ok = true
        · simp only [hok, if_true]
          obtain ⟨l', hl, hs⟩ := boundProg_started rest (pollStop stop { (pollStop stop t).2 with
            started := (pollStop stop t).2.started ++ [s] }).2
          exact ⟨s :: l', by rw [hl, h2]; simp, hs.cons_cons _⟩
        · simp only [hok, Bool.false_eq_true, if_false, execProg_done]
          exact ⟨[s], h2, by simp⟩
      all_goals
        simp only [execProg_done]
        exact ⟨[s], h2, by simp⟩

/-- The only steps of the reference dispatch named `linear bound` are its two bound steps. -/
theorem refBound_steps {s : GStep BoundCall} (hs : s ∈ refBoundDispatch)
    (hn : s.name = "linear bound") : s = earlyBoundStep ∨ s = lateBoundStep := by
  simp only [refBoundDispatch, refBoundA, refBoundB, refBoundC, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | simp [otherBoundStep, enumBoundStep] at hn

/-- The reference dispatch with its bound ahead of the enumeration singled out. -/
theorem refBound_split_early :
    refBoundDispatch = refBoundA ++ earlyBoundStep :: (refBoundB ++ lateBoundStep :: refBoundC) :=
  rfl

/-- The reference dispatch with its bound after the P-invariants singled out. -/
theorem refBound_split_late :
    refBoundDispatch = (refBoundA ++ earlyBoundStep :: refBoundB) ++ lateBoundStep :: refBoundC :=
  rfl

/-- The scripts a step of the reference dispatch may start: a bound step its demands' scripts,
every other step none. -/
def refBoundAsks (q : BoundCall) (s : GStep BoundCall) : List String :=
  if s.name = "linear bound" then q.checks.map Prod.fst else []

/-- Each step of the reference dispatch starts a sublist of the scripts `refBoundAsks` gives it. -/
theorem refBound_started_step {O : Oracle} {stop : Stop} {o : Options} {q : BoundCall} :
    ∀ s ∈ refBoundDispatch, ∀ t' : Trail, ∃ l,
      (execProg O stop (s.run o q) t').2.started = t'.started ++ l ∧ l.Sublist (refBoundAsks q s) := by
  intro s hs t'
  simp only [refBoundDispatch, refBoundA, refBoundB, refBoundC, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (refine ⟨[], ?_, List.nil_sublist _⟩
       simp only [otherBoundStep, enumBoundStep, execProg_done, List.append_nil]; done)
    | skip
  · simp only [earlyBoundStep, refBoundAsks, if_true]
    split
    · exact boundProg_started _ _
    · exact ⟨[], by simp [execProg_done], List.nil_sublist _⟩
  · simp only [lateBoundStep, refBoundAsks, if_true]
    exact boundProg_started _ _

/-- **What the reference bound steps return**: lines 9 to 11 of the order block for the two bound
steps of the reference dispatch. -/
theorem refBound_bound_steps :
    (∀ s ∈ refBoundDispatch, s.name = "linear bound" →
      ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
        Yields R (s.run o q) out →
          ((∃ n, out = .aside n) ∨ out = .decided (.proven "structural") [] none) ∧
          (out = .decided (.proven "structural") [] none →
            ∀ c ∈ q.checks, c.2 = true ∧ R c.1 (.answer .sat))) ∧
    (∀ s ∈ refBoundDispatch, s.name = "linear bound" →
      ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
        q.solverUp = true → (∀ c ∈ q.checks, c.2 = true ∧ ∀ r, R c.1 r → r = .answer .sat) →
        Yields R (s.run o q) out → out = .decided (.proven "structural") [] none) := by
  refine ⟨fun s hs hn o q R out h => ?_, fun s hs hn o q R out hup hc h => ?_⟩
  · rcases refBound_steps hs hn with rfl | rfl
    · simp only [earlyBoundStep] at h
      split at h
      · exact ⟨boundProg_out _ _ h, boundProg_proves _ _ h⟩
      · rw [Yields.done_iff] at h
        subst h
        exact ⟨Or.inl ⟨_, rfl⟩, fun hp => by cases hp⟩
    · exact ⟨boundProg_out _ _ h, boundProg_proves _ _ h⟩
  · rcases refBound_steps hs hn with rfl | rfl
    · simp only [earlyBoundStep, hup, if_true] at h
      exact boundProg_conv _ _ hc h
    · exact boundProg_conv _ _ hc h

/-- **The reference hands over to the enumeration and sends each script once**: lines 12 and 13 of
the order block for the reference dispatch. -/
theorem refBound_next_and_scripts (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall) (t : Trail)
    (ht : t.entered = []) :
    (q.early = true → ∀ pre x post, boundLog refBoundDispatch O stop o q t =
        pre ++ "linear bound" :: x :: post → x = "state-space enumeration") ∧
    (t.started = [] → (q.checks.map Prod.fst).Nodup →
      ∀ c ∈ q.checks, (runPipeline O stop o q refBoundDispatch t).2.started.count c.1 ≤ 1) := by
  constructor
  · intro he pre x post hl
    obtain ⟨l, hl0, hp⟩ := ver015_run_prefix (O := O) (stop := stop) (o := o) (q := q)
      refBoundDispatch t
    rw [ht, List.nil_append] at hl0
    have hea : earlyBoundStep.applies o q = true := by simp [earlyBoundStep, he]
    have hen : enumBoundStep.applies o q = true := by
      simp only [BoundCall.early, Bool.and_eq_true] at he
      simp [enumBoundStep, he.1.1]
    have hla : lateBoundStep.applies o q = false := by simp [lateBoundStep, he]
    have happ : ver015_applied o q refBoundDispatch = ver015_applied o q refBoundA ++
        "linear bound" :: "state-space enumeration" ::
          ver015_applied o q (refBoundB.drop 1 ++ lateBoundStep :: refBoundC) := by
      rw [refBound_split_early, ver015_applied_split hea]
      simp only [ver015_applied, refBoundB, List.cons_append, List.drop_succ_cons, List.drop_zero]
      simp only [List.filter_cons, hen, if_true, List.map_cons]
      rfl
    have hA : "linear bound" ∉ ver015_applied o q refBoundA := fun h =>
      absurd ((ver015_applied_sublist (o := o) (q := q) refBoundA).subset h) (by decide)
    -- the bound is entered once, so not before its own entry
    have hcount : (boundLog refBoundDispatch O stop o q t).count "linear bound" ≤ 1 := by
      have hsub := ver015_run_sublist (O := O) (stop := stop) (o := o) (q := q) refBoundDispatch ht
      have : (boundLog refBoundDispatch O stop o q t).Sublist
          (List.map GStep.name ((refBoundA ++ earlyBoundStep :: refBoundB) ++ refBoundC)) := by
        refine hsub.trans ?_
        rw [refBound_split_late]
        exact ver015_applied_skip hla
      exact (this.count_le _).trans (by decide)
    have hpre : "linear bound" ∉ pre := by
      intro hm
      rw [hl] at hcount
      have : 2 ≤ (pre ++ "linear bound" :: x :: post).count "linear bound" := by
        rw [List.count_append, List.count_cons_self]
        have := List.count_pos_iff.mpr hm
        omega
      omega
    have hl' : boundLog refBoundDispatch O stop o q t = l := hl0
    rw [hl'] at hl
    rw [hl, happ] at hp
    exact ver015_prefix_next hp hA hpre
  · intro hs hnd c hc
    obtain ⟨l, hl, hsub⟩ := ver015_run_started (O := O) (stop := stop) (o := o) (q := q)
      (refBoundAsks q) refBoundDispatch t refBound_started_step
    rw [hl, hs, List.nil_append]
    have hall : ((refBoundDispatch.filter fun s => s.applies o q).flatMap (refBoundAsks q)).Sublist
        (q.checks.map Prod.fst) := by
      cases he : q.early
      · have hea : earlyBoundStep.applies o q = false := by simp [earlyBoundStep, he]
        have : refBoundDispatch.filter (fun s => s.applies o q) =
            (refBoundA ++ (refBoundB ++ lateBoundStep :: refBoundC)).filter
              (fun s => s.applies o q) := by
          rw [refBound_split_early]; simp [List.filter_append, hea]
        rw [this]
        refine (List.filter_sublist.flatMap _).trans ?_
        simp [refBoundAsks, refBoundA, refBoundB, refBoundC, otherBoundStep, enumBoundStep,
          lateBoundStep]
      · have hla : lateBoundStep.applies o q = false := by simp [lateBoundStep, he]
        have : refBoundDispatch.filter (fun s => s.applies o q) =
            ((refBoundA ++ earlyBoundStep :: refBoundB) ++ refBoundC).filter
              (fun s => s.applies o q) := by
          rw [refBound_split_late]
          simp only [List.filter_append, List.filter_cons, hla, Bool.false_eq_true, if_false]
        rw [this]
        refine (List.filter_sublist.flatMap _).trans ?_
        simp [refBoundAsks, refBoundA, refBoundB, refBoundC, otherBoundStep, enumBoundStep,
          earlyBoundStep]
    refine ((hsub.trans hall).count_le _).trans ?_
    exact List.nodup_iff_count_le_one.mp hnd _

/-! ## VER-015 (B): the bound's place in the dispatch -/

requirement VER_015_order
  id "VER-015"
  title "Linear State-Equation Bound: Place in the Dispatch"
  kind B
  scope "the dispatch of the SMT verifier, all implementations (SHOULD; the shall sentences bind an implementation that offers the bound phase)"
  source verbatim "spec/07-verification.md"
  quote "*When* the bound phase proves the property, it *shall* return `Proven` with method `structural`, an empty counterexample trace and no `counterexampleConfirmed`."
        "A property with a demand is a `PlaceBound`, `BranchPlaceBound`, `MutualExclusion` or `Unreachable` property; the name-alignment properties of [NU-055] have no demand."
        "The verifier *shall not* run the bound phase on a property without a demand, while the phase is disabled, or under `Ignore` with environment places registered."
        "The verifier *shall* run the bound phase at most once in one verification call."
        "The verifier *shall* send the `bound` query of each demand at most once in one verification call."
        "The verifier *shall not* run Route B ([VER-012]) after the bound phase, and *shall not* run the bound phase after the colour-slot bound of the coloured encoding ([NU-053]) or after the fixpoint query."
        "*When* the bound phase is enabled and the verifier runs the colour-slot bound or the fixpoint query on a property with a demand, not under `Ignore` with environment places registered, it *shall* have run the bound phase earlier in the same call."
        "*When* the bound phase is enabled and the verifier runs the enumeration of [VER-017] on a property with a demand, and the enumeration route applies to a net with no drained forward, it *shall* have run the bound phase earlier in the same call, and *shall not* run the bound phase after the enumeration."
        "*When* the bound phase runs ahead of the enumeration and does not prove the property, the next phase the verifier runs *shall* be the enumeration."
        "On a net where the enumeration route does not apply, or that has a drained forward, the verifier *shall not* run the bound phase before the enumeration."
        "*When* the verifier runs the bound phase on a property, it *shall* return `Proven` exactly when, for every demand of the property, the query returned a `sat` model whose weighting the exact re-check accepts for that demand."
        "The verifier *shall not* return `Violated` from the bound phase; every outcome of the phase other than `Proven` hands over to the next phase of the dispatch."
        "`unsat`, `unknown` and any transport failure hand over to the next phase of the dispatch."
        "The phase is skipped under `Ignore` with environment places registered ([VER-006] AC4) and for the quiescence properties, whose violation is not a linear demand."
        "Route B ([VER-012]) keeps its place in the dispatch: the bound runs after it, never before."
        "The coloured plan is built only after the bound fails to prove; nothing before it reads the plan."
        "When the enumeration route of [VER-017] applies to a net with no ν-join (untimed, no environment places, a positive class budget) and the net has no drained forward ([IO-014], [VER-001] AC5), the bound runs **before** the enumeration, not after it."
        "Anything else falls through to the enumeration, and the fixpoint query later does not send the `bound` query again."
        "When the solver cannot be started, the early bound sends no query and hands over with a report line, and the enumeration runs without a solver, as it did before; the `Unknown` with route `Unavailable` of [VER-013] comes only from the later phases."
  reading "For every dispatch D, solver O, stop, options o, call q and trail t whose log of entered steps is empty, in the log of the steps the run of D enters from t: no step named Route B (ν name-partition graph) is entered after a step named linear bound;"
          "no linear bound is entered after a colour-slot bound;"
          "no linear bound is entered after an IC3/PDR query;"
          "a linear bound is entered only when q.phaseOk holds: the property has a demand, the phase is on, and the call is not under Ignore with environment places registered;"
          "linear bound is entered at most once;"
          "when q.phaseOk holds and a colour-slot bound or an IC3/PDR query is entered, a linear bound is entered too;"
          "when q.early holds (the enumeration route applies, the net has no drained forward, and q.phaseOk holds) and the state-space enumeration is entered, a linear bound is entered and none is entered after the enumeration;"
          "when q.early does not hold, no linear bound is entered before the state-space enumeration;"
          "every step of D named linear bound, under any options, call and replies R, can return only an aside, which hands over to the next step, or Proven with method structural, the empty trace and no confirmation field;"
          "and when it returns Proven, every demand's check of the call passed and R allows the answer sat to every demand's script;"
          "every step of D named linear bound, on a call where the solver can be started and every demand's check passes, under replies R that answer only sat to every demand's script, returns Proven with method structural, the empty trace and no confirmation field;"
          "for every solver O, stop, options o, call q and trail t whose log is empty: when q.early holds, the step entered right after a linear bound, if any, is the state-space enumeration;"
          "and when t has started no script and the demands' scripts are distinct, the run starts each demand's script at most once."
  assumes "The model is a dispatch D: a list of pipeline steps (GStep of Spec/Verifier/Pipeline.lean) over a BoundCall, run by runPipeline. A step whose guard fails is skipped; an applicable step polls the stop, is entered and logged; an aside goes on to the next step and a decision ends the run. The run semantics are Pipeline.lean's, fixed, not a variable: the statement constrains the order of the logged steps, the scripts the run starts and what the bound steps return. To run a phase is to enter its step, whether or not it then sends a query. The step names are the runtimes' (rtStepNames: Rust step!, Java and TypeScript enter; refBoundDispatch_names pins them), so linear bound is the bound phase in either of its two slots and on the flat and the ν path alike ('with the same phase name'), colour-slot bound builds the coloured plan of NU-053, IC3/PDR query is the fixpoint query and state-space enumeration is the route of VER-017. The statement identifies a phase by its name: a dispatch that ran the fixpoint query under another name would escape lines 3 and 6, so the names are part of the model, not a variable."
          "A BoundCall carries what the runtimes' guards read of one call: whether the property has a demand (the second quoted sentence; NU-055 calls NameAligned a reachability-safety property, but it has no demand, and Route B alone decides it), the linearBound option, the Ignore mode, whether environment places are registered on the net the dispatcher receives (after the Arrivals rewrite of VER-006, which clears them), the rest of VER-017's guard (no ν-join, untimed, a positive class budget), a drained forward, whether the solver can be started, and per demand its bound script and whether the weighting of a sat model passes the exact re-check. For every other step it says whether the step runs and what it returns: the reference leaves those steps free (otherBoundStep), so the lines hold whatever they do, and their guards and phases are their own blocks' (VER-017, VER-018, VER-019, VER-020, VER-025, NU-053). The scripts of different demands differ in the runtimes, since the demand is part of the script; line 13 assumes it (Nodup)."
          "The witness is refBoundDispatch, the runtimes' thirteen steps with the bound in its two slots: ahead of the enumeration (guard q.early; with no solver it hands over without a query) and after the P-invariants (guard q.phaseOk and not q.early). The runtimes gate the later slot on 'not tried ahead of the enumeration' (bound_tried in smt_verifier.rs, boundTried in SmtVerifier.java and smt-verifier.ts), which is set only once the solver started. The two gates differ only when the early slot found no solver; the flat path then resolves the solver again and returns Unknown with route Unavailable before the later slot (smt_verifier.rs, the Z3Solver::resolve ahead of the linear bound; SmtVerifier.java and smt-verifier.ts likewise), so the runtimes too enter the bound at most once. The model takes the solver's availability as fixed for one call. The runtimes' early gate does not test the Ignore conjunct of q.phaseOk; it needs none, because the enumeration route requires that no environment place is registered."
          "Line 4 is the second quoted sentence, which defines a property with a demand, 'The verifier shall not run the bound phase on a property without a demand, while the phase is disabled, or under Ignore with environment places registered' and 'The phase is skipped under Ignore with environment places registered ([VER-006] AC4) and for the quiescence properties, whose violation is not a linear demand'. A bound entered for a DeadlockFree property is killed (VER_015_order_forbids_quiescence), and so is one entered under Ignore with environment places (VER_015_order_forbids_ignore). The option itself (on by default; linearBound(false) MAY disable it) is configuration (kind N); line 4 says a disabled phase is not run. That the verifier offers the phase at all, and that it can prove a property there, is an offer, not a safety line: it is the coverage condition Ver015OrderCovers (the convention of GlossaryExec), shown of the reference by ver015OrderCovers_reference."
          "Line 1 is 'The verifier shall not run Route B ([VER-012]) after the bound phase' and 'Route B ([VER-012]) keeps its place in the dispatch: the bound runs after it, never before', killed by VER_015_order_forbids_beforeRouteB. Lines 2 and 3 are the rest of that EARS sentence and 'The coloured plan is built only after the bound fails to prove; nothing before it reads the plan', killed by VER_015_order_forbids_afterSlot and VER_015_order_forbids_afterFixpoint. That nothing before the plan reads it is also the shape of the model: a BoundCall carries no plan, so the bound cannot read one."
          "Line 5 is 'The verifier shall run the bound phase at most once in one verification call', killed by VER_015_order_forbids_twice (the later slot gated on the phase alone). Line 13 is 'The verifier shall send the bound query of each demand at most once in one verification call' and the second half of 'Anything else falls through to the enumeration, and the fixpoint query later does not send the bound query again': a run from an empty log that has started no script starts each demand's script at most once, whichever step would send it. It is killed by VER_015_order_forbids_resend (the fixpoint query sends the bound script again) and VER_015_order_forbids_retry (the bound asks a demand again after unknown). Lines 5 and 13 are AC7's 'the run sends the bound query at most once per demand'; VER_015_order_nonvacuous shows one bound script started on a call the enumeration then decides."
          "Line 6 is 'When the bound phase is enabled and the verifier runs the colour-slot bound or the fixpoint query on a property with a demand, not under Ignore with environment places registered, it shall have run the bound phase earlier in the same call' (earlier by lines 2 and 3), the body's 'Before the fixpoint query, a reachability-safety property ... is tried against the state equation' and the nu-net paragraph's 'under the same conditions as the flat path'. A dispatch whose only bound sits ahead of the enumeration is killed (VER_015_order_forbids_earlyOnly)."
          "Line 7 is the EARS sentence on the enumeration of VER-017 and 'When the enumeration route of [VER-017] applies to a net with no ν-join (untimed, no environment places, a positive class budget) and the net has no drained forward ([IO-014], [VER-001] AC5), the bound runs before the enumeration, not after it'; the dispatch that keeps the bound in its later slot only, as the runtimes did before, is killed (VER_015_order_forbids_lateOnly). Line 8 is 'On a net where the enumeration route does not apply, or that has a drained forward, the verifier shall not run the bound phase before the enumeration', killed by VER_015_order_forbids_drained. On a net with a drained forward the runtimes refuse every flat route before flattening, so the bound never runs there; that refusal is VER-003's and VER-001 AC5's. Line 12 is 'When the bound phase runs ahead of the enumeration and does not prove the property, the next phase the verifier runs shall be the enumeration' and the first half of 'Anything else falls through to the enumeration': when q.early holds, the step entered right after the bound is the enumeration. A dispatch that skips the enumeration once the bound ran ahead of it is killed (VER_015_order_forbids_enumSkip). When the run ends at the bound (a Proven, or a stop) no step follows, and the line asks nothing."
          "Line 9 is 'When the bound phase proves the property, it shall return Proven with method structural, an empty counterexample trace and no counterexampleConfirmed', 'The verifier shall not return Violated from the bound phase; every outcome of the phase other than Proven hands over to the next phase of the dispatch' (also quoted by the first block), 'unsat, unknown and any transport failure hand over to the next phase of the dispatch' and 'When the solver cannot be started, the early bound sends no query and hands over with a report line, and the enumeration runs without a solver, as it did before; the Unknown with route Unavailable of [VER-013] comes only from the later phases'. The absent counterexampleConfirmed is also VER-003's 'Absent where no replay applies'. Line 9 is killed by VER_015_order_forbids_strict (Unknown on a solver failure), VER_015_order_forbids_violated (Violated on unsat) and VER_015_order_forbids_confirmed (a Proven that carries counterexampleConfirmed). The hand-over is the pipeline's: an aside goes on to the next applicable step. When the total budget or cancellation of VER-013 fires during the bound, the run ends without a next step; that is the stop of runPipeline (VER-013's block), so 'hands over to the next phase' holds of every run that is not stopped. The report lines are report text (kind Q)."
          "Lines 10 and 11 are 'When the verifier runs the bound phase on a property, it shall return Proven exactly when, for every demand of the property, the query returned a sat model whose weighting the exact re-check accepts for that demand', the first block's line 6, said of the step program. Line 10, the 'only when': a Proven means every demand's re-check passed and its query was answered sat; killed by VER_015_order_forbids_anyDemand (proves once one demand is separated, a find_map slip in linear_bound_proof) and VER_015_order_forbids_noRecheck (believes a sat model without the re-check). Line 11, the 'when': with the solver up, every re-check passing and only sat answers to the demands' scripts, the step proves; killed by VER_015_order_forbids_neverProves. Line 11 asks nothing of a run whose replies include a refusal, so a stop is outside it. VER_015_order_follows_phase derives from the two blocks together that, for every triple (C, Dm, Ph) satisfying VER_015 and every dispatch satisfying this block, a bound step whose checks are C applied to the answers of the demands Dm gives proves exactly when Ph proves."
          "GStep has one route for its decision and for a stop charged to it. The reference bound steps carry route structural, the route of their Proven (VerificationRoute::Structural in the runtimes), while the runtimes charge a stop found during the bound to route Smt; the route of a stopped call is VER-013's and VER-003's, not a line here. A Proven of the bound passes, like every flat proof, through the nu guard of the runtimes (apply_nu_guard in smt_verifier.rs, applyNuGuard in Java and TypeScript): on a nu-net with unbounded fresh names it becomes Unknown, as NU-040 requires, and otherwise it carries the NU-050 over-approximation note. Both are NU-040's and NU-050's, not lines here."
          "AC1 (the property is Proven with method structural, without a fixpoint query, and the report names the bound and the demand) is lines 9 and 11 for the verdict and the method, and the pipeline with lines 3 and 6 for 'without a fixpoint query': a bound that proves ends the call before the IC3/PDR query step (VER_015_order_nonvacuous, first two conjuncts). The report line is kind Q. AC2 and AC3 (unsat, or a model that fails the re-check, goes on to the fixpoint query) are lines 9 and 10 (an aside, never a Proven) and the pipeline; their report lines are kind Q."
          "AC6 (on a nu-net with an exact name-coloured plan, a property the bound separates is Proven without the coloured query; one it does not separate reaches the coloured query and gets the verdict it got before) is lines 2, 3, 6, 9 and 11: the bound runs after Route B and before the colour-slot bound and the fixpoint query (VER_015_order_nonvacuous on bqNu), a Proven ends the call, and an aside hands over unchanged, since a step reads only the call and never the trail. 'Keeps any ν-encoding notes already in the report' is report text (kind Q). That the flat Proven is sound on a nu-net ('every marking the ν semantics reaches is reachable there too') is NU-053's and Novel/RouteA/SlotBound.lean's."
          "AC7 (on a net the enumeration route would take, a property the bound separates is Proven with no enumeration report line, whatever the class budget; one it does not separate is decided by the enumeration as before; the bound query at most once per demand; with a drained forward the enumeration decides first) is lines 5, 7, 8, 9, 12 and 13: VER_015_order_nonvacuous shows the Proven with only the bound entered, and the enumeration deciding after an unsat answer with one bound script sent. 'A bound that proves returns as in AC1, with the report line of [VER-017] AC3 for the invariants it did not compute' is the verdict of lines 9 and 11 and report text (kind Q)."
          "The total budget and cancellation of VER-013 ('the total budget and cancellation of [VER-013] respected') are the stop of runPipeline, VER-013's block: every line holds for every stop. The measurements of the closing paragraphs (about 17 s per claim, under 0.1 s with the bound first, the six PNID nu-nets) and 'This closes the class of proofs IC3 does not find' are motivation and measurement, not requirements. The Implementation notes and the bound.smt2 goldens are kind N and Q."
  signoff "2026-11-13 b3ef7bbb9ddbcd29 ai"
  statement : BoundDispatch → Prop :=
    fun D =>
      (∀ (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall) (t : Trail), t.entered = [] →
        Ordered (boundLog D O stop o q t) "Route B (ν name-partition graph)" "linear bound" ∧
        Ordered (boundLog D O stop o q t) "linear bound" "colour-slot bound" ∧
        Ordered (boundLog D O stop o q t) "linear bound" "IC3/PDR query" ∧
        ("linear bound" ∈ boundLog D O stop o q t → q.phaseOk = true) ∧
        (boundLog D O stop o q t).count "linear bound" ≤ 1 ∧
        (q.phaseOk = true →
          ("colour-slot bound" ∈ boundLog D O stop o q t ∨ "IC3/PDR query" ∈ boundLog D O stop o q t) →
          "linear bound" ∈ boundLog D O stop o q t) ∧
        (q.early = true → "state-space enumeration" ∈ boundLog D O stop o q t →
          "linear bound" ∈ boundLog D O stop o q t ∧
          Ordered (boundLog D O stop o q t) "linear bound" "state-space enumeration") ∧
        (q.early = false →
          Ordered (boundLog D O stop o q t) "state-space enumeration" "linear bound")) ∧
      (∀ s ∈ D, s.name = "linear bound" →
        ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
          Yields R (s.run o q) out →
            ((∃ n, out = .aside n) ∨ out = .decided (.proven "structural") [] none) ∧
            (out = .decided (.proven "structural") [] none →
              ∀ c ∈ q.checks, c.2 = true ∧ R c.1 (.answer .sat))) ∧
      (∀ s ∈ D, s.name = "linear bound" →
        ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
          q.solverUp = true → (∀ c ∈ q.checks, c.2 = true ∧ ∀ r, R c.1 r → r = .answer .sat) →
          Yields R (s.run o q) out → out = .decided (.proven "structural") [] none) ∧
      (∀ (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall) (t : Trail), t.entered = [] →
        (q.early = true → ∀ pre x post,
          boundLog D O stop o q t = pre ++ "linear bound" :: x :: post →
          x = "state-space enumeration") ∧
        (t.started = [] → (q.checks.map Prod.fst).Nodup → ∀ c ∈ q.checks,
          (runPipeline O stop o q D t).2.started.count c.1 ≤ 1))

/- The pinned readable form of the order block: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_015_order : BoundDispatch → Prop :=
fun D =>
  (∀ (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall) (t : Trail),
      t.entered = [] →
        Ordered (boundLog D O stop o q t) "Route B (ν name-partition graph)" "linear bound" ∧
          Ordered (boundLog D O stop o q t) "linear bound" "colour-slot bound" ∧
            Ordered (boundLog D O stop o q t) "linear bound" "IC3/PDR query" ∧
              ("linear bound" ∈ boundLog D O stop o q t → q.phaseOk = true) ∧
                List.count "linear bound" (boundLog D O stop o q t) ≤ 1 ∧
                  (q.phaseOk = true →
                      "colour-slot bound" ∈ boundLog D O stop o q t ∨ "IC3/PDR query" ∈ boundLog D O stop o q t →
                        "linear bound" ∈ boundLog D O stop o q t) ∧
                    (q.early = true →
                        "state-space enumeration" ∈ boundLog D O stop o q t →
                          "linear bound" ∈ boundLog D O stop o q t ∧
                            Ordered (boundLog D O stop o q t) "linear bound" "state-space enumeration") ∧
                      (q.early = false → Ordered (boundLog D O stop o q t) "state-space enumeration" "linear bound")) ∧
    (∀ s ∈ D,
        s.name = "linear bound" →
          ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
            Yields R (s.run o q) out →
              ((∃ n, out = PhaseOut.aside n) ∨ out = PhaseOut.decided (Verdict.proven "structural") [] none) ∧
                (out = PhaseOut.decided (Verdict.proven "structural") [] none →
                  ∀ c ∈ q.checks, c.2 = true ∧ R c.1 (SolverReply.answer SolverAnswer.sat))) ∧
      (∀ s ∈ D,
          s.name = "linear bound" →
            ∀ (o : Options) (q : BoundCall) (R : String → SolverReply → Prop) (out : PhaseOut),
              q.solverUp = true →
                (∀ c ∈ q.checks, c.2 = true ∧ ∀ (r : SolverReply), R c.1 r → r = SolverReply.answer SolverAnswer.sat) →
                  Yields R (s.run o q) out → out = PhaseOut.decided (Verdict.proven "structural") [] none) ∧
        ∀ (O : Oracle) (stop : Stop) (o : Options) (q : BoundCall) (t : Trail),
          t.entered = [] →
            (q.early = true →
                ∀ (pre : List String) (x : String) (post : List String),
                  boundLog D O stop o q t = pre ++ "linear bound" :: x :: post → x = "state-space enumeration") ∧
              (t.started = [] →
                (List.map Prod.fst q.checks).Nodup →
                  ∀ c ∈ q.checks, List.count c.1 (runPipeline O stop o q D t).2.started ≤ 1)
-/
#guard_msgs in #print VER_015_order

/-- **The runtimes' dispatch meets the order block.** In the reference, Route B comes first, the
bound has a slot ahead of the enumeration (taken on an untimed net the enumeration route takes,
with no drained forward) and a slot after the P-invariants (taken otherwise), and the colour-slot
bound and the fixpoint query come after both. Since a run enters a prefix of the steps that
apply, at most one slot is taken, and a run that reaches a later step has passed the slot that
applied. The bound program sends one query per demand and returns `Proven` only when every
answer is a `sat` model that passes the re-check; anything else is an aside. -/
@[evidence holds VER_015_order]
theorem VER_015_order_reference : VER_015_order refBoundDispatch := by
  refine ⟨fun O stop o q t ht => ?_, refBound_bound_steps.1, refBound_bound_steps.2,
    refBound_next_and_scripts⟩
  · have hsub := ver015_run_sublist (O := O) (stop := stop) (o := o) (q := q) refBoundDispatch ht
    have hall : (boundLog refBoundDispatch O stop o q t).Sublist rtStepNames := by
      rw [← refBoundDispatch_names]; exact hsub.trans (ver015_applied_sublist _)
    -- the late bound does not apply when the bound ran ahead of the enumeration
    have hlate : q.early = true → (boundLog refBoundDispatch O stop o q t).Sublist
        (List.map GStep.name ((refBoundA ++ earlyBoundStep :: refBoundB) ++ refBoundC)) := by
      intro he
      refine hsub.trans ?_
      rw [refBound_split_late]
      exact ver015_applied_skip (by simp [lateBoundStep, he])
    have hearly : q.early = false → (boundLog refBoundDispatch O stop o q t).Sublist
        (List.map GStep.name (refBoundA ++ (refBoundB ++ lateBoundStep :: refBoundC))) := by
      intro he
      refine hsub.trans ?_
      rw [refBound_split_early]
      exact ver015_applied_skip (by simp [earlyBoundStep, he])
    refine ⟨(by decide : Before rtStepNames _ _).ordered hall,
      (by decide : Before rtStepNames _ _).ordered hall,
      (by decide : Before rtStepNames _ _).ordered hall, fun hm => ?_, ?_, fun hok hb => ?_,
      fun he hm => ?_, fun he => ?_⟩
    · obtain ⟨s, hs, ha, hn⟩ := ver015_run_mem ht hm
      rcases refBound_steps hs hn with rfl | rfl
      · simp only [earlyBoundStep, BoundCall.early, Bool.and_eq_true] at ha
        exact ha.2
      · simp only [lateBoundStep, Bool.and_eq_true] at ha
        exact ha.1
    · cases he : q.early
      · exact ((hearly he).count_le _).trans (by decide)
      · exact ((hlate he).count_le _).trans (by decide)
    · cases he : q.early
      · have ha : lateBoundStep.applies o q = true := by simp [lateBoundStep, hok, he]
        rw [refBound_split_late] at hb ⊢
        rcases hb with hb | hb
        · exact ver015_run_reach ht ha (by decide) hb
        · exact ver015_run_reach ht ha (by decide) hb
      · have ha : earlyBoundStep.applies o q = true := by simp [earlyBoundStep, he]
        rw [refBound_split_early] at hb ⊢
        rcases hb with hb | hb
        · exact ver015_run_reach ht ha (by decide) hb
        · exact ver015_run_reach ht ha (by decide) hb
    · have ha : earlyBoundStep.applies o q = true := by simp [earlyBoundStep, he]
      refine ⟨?_, (by decide : Before (List.map GStep.name
        ((refBoundA ++ earlyBoundStep :: refBoundB) ++ refBoundC)) _ _).ordered (hlate he)⟩
      rw [refBound_split_early] at hm ⊢
      exact ver015_run_reach ht ha (by decide) hm
    · exact (by decide : Before (List.map GStep.name
        (refBoundA ++ (refBoundB ++ lateBoundStep :: refBoundC))) _ _).ordered (hearly he)

/-! ## Examples of the order -/

/-- A solver that answers `unsat` to every query. -/
def boundUnsatOracle : Oracle := fun _ => .answer .unsat

/-- A call on a flat net the enumeration route does not take: a reachability-safety property,
the phase on, one demand whose `sat` model passes the re-check, every other step entered and
stepping aside. -/
def bqFlat : BoundCall :=
  { safety := true, enabled := true, ignore := false, envPlaces := false, enumGate := false,
    drained := false, solverUp := true, checks := [("bound-0", true)], applies := fun _ => true,
    outcome := fun _ => .aside "steps aside" }

/-- The same call on an untimed net the enumeration route takes (Route B not entered). -/
def bqEnum : BoundCall :=
  { bqFlat with enumGate := true, applies := fun n => n != "Route B (ν name-partition graph)" }

/-- The untimed call where the enumeration decides `Violated`. -/
def bqEnumDecides : BoundCall :=
  { bqEnum with outcome := fun n =>
      if n = "state-space enumeration" then .decided .violated ["t1"] (some true)
      else .aside "steps aside" }

/-- A call on a ν-net: Route B steps aside, the flat state-equation and firing-bound phases and
the witness phase do not run, the fixpoint query decides `Proven`. -/
def bqNu : BoundCall :=
  { bqFlat with
    applies := fun n => !(n == "state-equation phase" || n == "firing-bound phase" ||
      n == "witness phase"),
    outcome := fun n =>
      if n = "IC3/PDR query" then .decided (.proven "IC3/PDR") [] none else .aside "steps aside" }

/-- ✓ **The bound's place, on four calls.** On an untimed net the enumeration route takes, the
bound runs first: when its one `bound` query is answered `sat` with a weighting that passes the
re-check, the call ends there with `Proven` (method `structural`) and the enumeration never
runs; when it is answered `unsat`, the enumeration runs next and decides, and the `bound` query
was sent once. When the solver cannot be started the bound sends nothing and the enumeration
still runs. On a ν-net the bound runs after Route B and before the colour-slot bound and the
fixpoint query. A quiescence property never enters the bound. -/
@[evidence nonvacuous VER_015_order]
theorem VER_015_order_nonvacuous :
    boundLog refBoundDispatch satOracle noStop {} bqEnum {} = ["linear bound"] ∧
    (runPipeline satOracle noStop {} bqEnum refBoundDispatch {}).1 =
      some (.structural, .decided (.proven "structural") [] none) ∧
    boundLog refBoundDispatch boundUnsatOracle noStop {} bqEnumDecides {} =
      ["linear bound", "state-space enumeration"] ∧
    (runPipeline boundUnsatOracle noStop {} bqEnumDecides refBoundDispatch {}).2.started =
      ["bound-0"] ∧
    (runPipeline boundUnsatOracle noStop {} bqEnumDecides refBoundDispatch {}).1 =
      some (.enumeration, .decided .violated ["t1"] (some true)) ∧
    boundLog refBoundDispatch satOracle noStop {} { bqEnumDecides with solverUp := false } {} =
      ["linear bound", "state-space enumeration"] ∧
    (runPipeline satOracle noStop {} { bqEnumDecides with solverUp := false } refBoundDispatch
      {}).2.started = [] ∧
    boundLog refBoundDispatch boundUnsatOracle noStop {} bqNu {} =
      ["Route B (ν name-partition graph)", "flattening", "structural pre-check",
       "P-invariant computation", "linear bound", "colour-slot bound", "IC3/PDR query"] ∧
    "linear bound" ∉ boundLog refBoundDispatch satOracle noStop {} { bqNu with safety := false } {} := by
  refine ⟨by decide, rfl, by decide, by decide, rfl, by decide, by decide, by decide, by decide⟩

/-! ## Wrong dispatches -/

/-- The bound's late slot as the runtimes had it before the early slot: gated on the phase only. -/
def lateBoundUngated : GStep BoundCall := { lateBoundStep with applies := fun _ q => q.phaseOk }

/-- A dispatch that runs the bound before Route B. -/
def mutBoundBeforeRouteB : BoundDispatch :=
  [lateBoundStep, otherBoundStep "Route B (ν name-partition graph)" .nuScg]

/-- ✗ **Route B comes first.** On a call where the bound steps aside, a dispatch that runs the
bound and then Route B enters them in the wrong order. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_beforeRouteB : ¬ VER_015_order mutBoundBeforeRouteB := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} bqFlat {} rfl).1
  revert this
  rw [ver015_ordered_iff]
  decide

/-- A dispatch that runs the bound after the fixpoint query. -/
def mutBoundAfterFixpoint : BoundDispatch := [otherBoundStep "IC3/PDR query" .smt, lateBoundStep]

/-- ✗ **The bound comes before the fixpoint query.** A dispatch that sends the fixpoint query
and only then tries the bound is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_afterFixpoint : ¬ VER_015_order mutBoundAfterFixpoint := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} bqFlat {} rfl).2.2.1
  revert this
  rw [ver015_ordered_iff]
  decide

/-- A dispatch that builds the coloured plan before the bound. -/
def mutBoundAfterSlot : BoundDispatch := [otherBoundStep "colour-slot bound" .smt, lateBoundStep]

/-- ✗ **The bound comes before the coloured plan.** A dispatch that builds the colour-slot bound
of the coloured encoding and only then tries the bound is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_afterSlot : ¬ VER_015_order mutBoundAfterSlot := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} bqFlat {} rfl).2.1
  revert this
  rw [ver015_ordered_iff]
  decide

/-- A dispatch whose bound ignores the kind of property. -/
def mutBoundOnQuiescence : BoundDispatch :=
  [{ lateBoundStep with applies := fun _ q => q.enabled && !(q.ignore && q.envPlaces) }]

/-- ✗ **No bound for a quiescence property.** A `DeadlockFree` property has no demand, so a
dispatch that enters the bound for it is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_quiescence : ¬ VER_015_order mutBoundOnQuiescence := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} { bqFlat with safety := false } {} rfl).2.2.2.1
  revert this
  decide

/-- A dispatch whose bound ignores `Ignore` with environment places. -/
def mutBoundUnderIgnore : BoundDispatch :=
  [{ lateBoundStep with applies := fun _ q => q.safety && q.enabled }]

/-- ✗ **No bound under `Ignore` with environment places**, where [VER-006] refuses every
`Proven`: a dispatch that enters the bound there is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_ignore : ¬ VER_015_order mutBoundUnderIgnore := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} { bqFlat with ignore := true, envPlaces := true } {}
    rfl).2.2.2.1
  revert this
  decide

/-- A dispatch that tries the bound ahead of the enumeration and again in its later slot. -/
def mutBoundTwice : BoundDispatch :=
  refBoundA ++ earlyBoundStep :: (refBoundB ++ lateBoundUngated :: refBoundC)

/-- ✗ **One bound per call.** When the bound ahead of the enumeration does not prove, a dispatch
that sends the `bound` query again before the fixpoint query enters the bound twice. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_twice : ¬ VER_015_order mutBoundTwice := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} bqEnum {} rfl).2.2.2.2.1
  revert this
  decide

/-- A dispatch with the bound ahead of the enumeration only. -/
def mutBoundEarlyOnly : BoundDispatch := refBoundA ++ earlyBoundStep :: (refBoundB ++ refBoundC)

/-- ✗ **The fixpoint query is not sent untried.** On a net the enumeration route does not take,
a dispatch whose only bound sits ahead of the enumeration reaches the fixpoint query without
the bound. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_earlyOnly : ¬ VER_015_order mutBoundEarlyOnly := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} bqFlat {} rfl).2.2.2.2.2.1 rfl (Or.inr (by decide))
  revert this
  decide

/-- A dispatch with the bound in its later slot only, as before the early slot existed. -/
def mutBoundLateOnly : BoundDispatch := refBoundA ++ (refBoundB ++ lateBoundUngated :: refBoundC)

/-- ✗ **On a net the enumeration route takes, the bound runs before it.** A dispatch that keeps
the bound in its later slot lets the enumeration spend its class budget first: the bound then
runs after the enumeration. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_lateOnly : ¬ VER_015_order mutBoundLateOnly := by
  intro h
  have := ((h.1 boundUnsatOracle noStop {} bqEnum {} rfl).2.2.2.2.2.2.1 rfl (by decide)).2
  revert this
  rw [ver015_ordered_iff]
  decide

/-- A dispatch whose early bound ignores a drained forward. -/
def mutBoundDrained : BoundDispatch :=
  refBoundA ++ { earlyBoundStep with applies := fun _ q => q.enumRoute && q.phaseOk } ::
    (refBoundB ++ lateBoundStep :: refBoundC)

/-- ✗ **Not ahead of the enumeration on a drained forward.** The flat net of a net with a
drained forward is not the net ([VER-001] AC5), so a dispatch that runs the bound ahead of the
enumeration there is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_drained : ¬ VER_015_order mutBoundDrained := by
  intro h
  have := (h.1 boundUnsatOracle noStop {} { bqEnum with drained := true } {} rfl).2.2.2.2.2.2.2 rfl
  revert this
  rw [ver015_ordered_iff]
  decide

/-- A bound that turns a solver failure into `Unknown`, as the later phases do. -/
def mutBoundStrict : BoundDispatch :=
  [{ lateBoundStep with run := fun _ _ => .ask "bound-0" fun r =>
      match r with
      | .answer .sat => .done (.decided (.proven "structural") [] none)
      | _ => .done (.decided (.unknown "solver failure") [] none) }]

/-- ✗ **A failure hands over.** A bound that answers a missing solver with `Unknown` would end
the call there, before the enumeration or the fixpoint query could decide. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_strict : ¬ VER_015_order mutBoundStrict := by
  intro h
  have := (h.2.1 _ List.mem_cons_self rfl {} bqFlat (fun _ _ => True) _
    (.ask (r := .failure .missing "z3 not found") trivial (.done _))).1
  rcases this with ⟨n, hn⟩ | hn <;> cases hn

/-- A bound that reads an `unsat` answer as a violation. -/
def mutBoundViolated : BoundDispatch :=
  [{ lateBoundStep with run := fun _ _ => .ask "bound-0" fun r =>
      match r with
      | .answer .sat => .done (.decided (.proven "structural") [] none)
      | _ => .done (.decided .violated [] none) }]

/-- ✗ **The bound never says `Violated`.** An `unsat` answer only means that no weighting
separates the violation; the violation may still be unreachable. A bound that reports
`Violated` on `unsat` is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_violated : ¬ VER_015_order mutBoundViolated := by
  intro h
  have := (h.2.1 _ List.mem_cons_self rfl {} bqFlat (fun _ _ => True) _
    (.ask (r := .answer .unsat) trivial (.done _))).1
  rcases this with ⟨n, hn⟩ | hn <;> cases hn

/-- A bound whose `Proven` claims a replayed counterexample. -/
def mutBoundConfirmed : BoundDispatch :=
  [{ lateBoundStep with run := fun _ _ => .ask "bound-0" fun r =>
      match r with
      | .answer .sat => .done (.decided (.proven "structural") [] (some true))
      | _ => .done (.aside "none separates the violation") }]

/-- ✗ **A structural `Proven` carries no replay flag.** The bound replays no run, so its
`Proven` has no `counterexampleConfirmed`. A bound that returns `Proven` with the flag set to
`true` is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_confirmed : ¬ VER_015_order mutBoundConfirmed := by
  intro h
  have := (h.2.1 _ List.mem_cons_self rfl {} bqFlat (fun _ _ => True) _
    (.ask (r := .answer .sat) trivial (.done _))).1
  rcases this with ⟨n, hn⟩ | hn <;> cases hn

/-- The bound as a `find_map`: `Proven` as soon as one demand's `sat` model passes the
re-check; any other answer moves on to the next demand. -/
def anyDemandProg : List (String × Bool) → PhaseProg PhaseOut
  | [] => .done (.aside "none separates the violation")
  | (s, ok) :: rest => .ask s fun r =>
    match r with
    | .answer .sat => if ok then .done (.decided (.proven "structural") [] none) else anyDemandProg rest
    | _ => anyDemandProg rest

/-- A bound that proves once one demand is separated. -/
def mutBoundAnyDemand : BoundDispatch :=
  [{ lateBoundStep with run := fun _ q => anyDemandProg q.checks }]

/-- A call with two demands: the first demand's model passes the re-check, the second one's
fails it. -/
def bqTwo : BoundCall := { bqFlat with checks := [("bound-0", true), ("bound-1", false)] }

/-- ✗ **Every demand must be separated.** A pairwise `MutualExclusion` over three places has one
demand per pair. Take two demands where the first model passes the re-check and the second
fails it: a bound that stops at the first separated demand returns `Proven`, though the second
pair may be marked together. It is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_anyDemand : ¬ VER_015_order mutBoundAnyDemand := by
  intro h
  have := (h.2.1 _ List.mem_cons_self rfl {} bqTwo (fun _ _ => True) _
    (.ask (r := .answer .sat) trivial (.done _))).2 rfl ("bound-1", false) (by simp [bqTwo])
  cases this.1

/-- The bound that believes a `sat` model without the exact re-check. -/
def noRecheckProg : List (String × Bool) → PhaseProg PhaseOut
  | [] => .done (.decided (.proven "structural") [] none)
  | (s, _) :: rest => .ask s fun r =>
    match r with
    | .answer .sat => noRecheckProg rest
    | _ => .done (.aside "none separates the violation")

/-- A bound without the exact re-check. -/
def mutBoundNoRecheck : BoundDispatch :=
  [{ lateBoundStep with run := fun _ q => noRecheckProg q.checks }]

/-- A call whose one `sat` model fails the exact re-check. -/
def bqBad : BoundCall := { bqFlat with checks := [("bound-0", false)] }

/-- ✗ **A `sat` model is checked before it is believed.** On a call where the solver answers
`sat` but the weighting fails the exact re-check, a bound that skips the re-check returns
`Proven`. It is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_noRecheck : ¬ VER_015_order mutBoundNoRecheck := by
  intro h
  have := (h.2.1 _ List.mem_cons_self rfl {} bqBad (fun _ _ => True) _
    (.ask (r := .answer .sat) trivial (.done _))).2 rfl ("bound-0", false) (by simp [bqBad])
  cases this.1

/-- A bound that never proves: it always hands over. -/
def mutBoundNeverProves : BoundDispatch :=
  [{ lateBoundStep with run := fun _ _ => .done (.aside "none separates the violation") }]

/-- ✗ **A separated demand is a proof.** On a call with one demand, a solver that answers `sat`
and a weighting that passes the re-check, the bound must return `Proven`. A bound that hands
over anyway is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_neverProves : ¬ VER_015_order mutBoundNeverProves := by
  intro h
  have := h.2.2.1 _ List.mem_cons_self rfl {} bqFlat (fun _ r => r = .answer .sat) _ rfl
    (by simp [bqFlat]) (.done _)
  cases this

/-- The enumeration gated on "the bound did not run ahead of it". -/
def enumSkipStep : GStep BoundCall :=
  { enumBoundStep with applies := fun _ q => q.enumRoute && !q.early }

/-- A dispatch that skips the enumeration once the bound ran ahead of it. -/
def mutBoundEnumSkip : BoundDispatch :=
  refBoundA ++ earlyBoundStep :: ((enumSkipStep :: refBoundB.drop 1) ++ lateBoundStep :: refBoundC)

/-- ✗ **What the bound does not prove falls through to the enumeration.** On an untimed net the
enumeration route takes, with a solver answering `unsat`, the reference enters the bound and
then the enumeration. A dispatch that skips the enumeration once the bound ran enters the
flattening next, and the call goes on to the flat SMT phases. It is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_enumSkip : ¬ VER_015_order mutBoundEnumSkip := by
  intro h
  have hl : boundLog mutBoundEnumSkip boundUnsatOracle noStop {} bqEnumDecides {} =
      [] ++ "linear bound" :: "flattening" ::
        ["structural pre-check", "P-invariant computation", "state-equation phase",
         "firing-bound phase", "colour-slot bound", "witness phase", "IC3/PDR query",
         "certificate check"] := by decide
  have := (h.2.2.2 boundUnsatOracle noStop {} bqEnumDecides {} rfl).1 rfl _ _ _ hl
  revert this
  decide

/-- Send every demand's script again, ignore the replies, then return `out`. -/
def resendProg : List (String × Bool) → PhaseOut → PhaseProg PhaseOut
  | [], out => .done out
  | (s, _) :: rest, out => .ask s fun _ => resendProg rest out

/-- A dispatch whose fixpoint query sends the demands' `bound` scripts again first. -/
def mutBoundResend : BoundDispatch :=
  refBoundA ++ earlyBoundStep :: (refBoundB ++ lateBoundStep ::
    [otherBoundStep "state-equation phase" .smt, otherBoundStep "firing-bound phase" .smt,
     otherBoundStep "colour-slot bound" .smt, otherBoundStep "witness phase" .smt,
     { otherBoundStep "IC3/PDR query" .smt with
       run := fun _ q => resendProg q.checks (q.outcome "IC3/PDR query") },
     otherBoundStep "certificate check" .smt])

/-- ✗ **The fixpoint query does not send the `bound` query again.** On a flat net with a solver
answering `unsat`, the reference starts `bound-0` once. A dispatch whose fixpoint query sends
it a second time starts it twice, though its step log is the reference's. It is rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_resend : ¬ VER_015_order mutBoundResend := by
  intro h
  have := (h.2.2.2 boundUnsatOracle noStop {} bqFlat {} rfl).2 rfl (by decide)
    ("bound-0", true) (by simp [bqFlat])
  revert this
  decide

/-- The reference bound program, asking a demand once more when the solver answers `unknown`. -/
def retryProg : List (String × Bool) → PhaseProg PhaseOut
  | [] => .done (.decided (.proven "structural") [] none)
  | (s, ok) :: rest => .ask s fun r =>
    match r with
    | .answer .unknown => .ask s fun r' =>
      match r' with
      | .answer .sat => if ok then retryProg rest else .done (.aside "inconclusive")
      | _ => .done (.aside "inconclusive")
    | .answer .sat => if ok then retryProg rest else .done (.aside "inconclusive")
    | _ => .done (.aside "none separates the violation")

/-- A dispatch whose later bound retries a demand on `unknown`. -/
def mutBoundRetry : BoundDispatch :=
  refBoundA ++ earlyBoundStep :: (refBoundB ++
    { lateBoundStep with run := fun _ q => retryProg q.checks } :: refBoundC)

/-- A solver that answers `unknown` to every query. -/
def boundUnknownOracle : Oracle := fun _ => .answer .unknown

/-- ✗ **One query per demand, also after `unknown`.** On a flat net with a solver answering
`unknown`, a bound that asks the same demand again starts `bound-0` twice in one call. It is
rejected. -/
@[evidence forbids VER_015_order]
theorem VER_015_order_forbids_retry : ¬ VER_015_order mutBoundRetry := by
  intro h
  have := (h.2.2.2 boundUnknownOracle noStop {} bqFlat {} rfl).2 rfl (by decide)
    ("bound-0", true) (by simp [bqFlat])
  revert this
  decide

/-! ## Coverage and the link to the phase -/

/-- **The offer the order block leaves to coverage**: the dispatch offers the bound phase, and on
some call the bound is entered and the call ends with its structural `Proven`. The block's lines
are safety lines and hold of a dispatch without a bound; this condition is the existence half
(the convention of `GlossaryExec`), for the consistency theorem. -/
def Ver015OrderCovers (D : BoundDispatch) : Prop :=
  ∃ (O : Oracle) (o : Options) (q : BoundCall),
    "linear bound" ∈ boundLog D O noStop o q {} ∧
    (runPipeline O noStop o q D {}).1 = some (.structural, .decided (.proven "structural") [] none)

/-- The reference dispatch offers the bound: on an untimed net the enumeration route takes, with
one demand that the solver separates, the bound runs and proves. -/
theorem ver015OrderCovers_reference : Ver015OrderCovers refBoundDispatch :=
  ⟨satOracle, {}, bqEnum, by decide, rfl⟩

/-- The checks of a call built from the first block's model: the `i`-th demand's script is
`scr i`, and its check passes when the `i`-th answer is `sat` with a weighting the re-check `C`
accepts. -/
noncomputable def ver015_checksOf (C : LinCheckRel) (rows : LinRows) (envs : List PlaceId)
    (a0 : AMarking) (n : Nat) (ans : Nat → BoundAnswer) (scr : Nat → String) :
    Nat → List AMarking → List (String × Bool)
  | _, [] => []
  | i, d :: ds =>
    (scr i, @decide (∃ y, ans i = .sat y ∧ C rows envs a0 d y n) (Classical.propDecidable _)) ::
      ver015_checksOf C rows envs a0 n ans scr (i + 1) ds

/-- Every check built from the first block's model passes exactly when every answer from `i` on
is `sat` with a weighting the re-check accepts for its demand. -/
theorem ver015_checksOf_ok (C : LinCheckRel) (rows : LinRows) (envs : List PlaceId)
    (a0 : AMarking) (n : Nat) (ans : Nat → BoundAnswer) (scr : Nat → String) :
    ∀ (ds : List AMarking) (i : Nat),
      (∀ c ∈ ver015_checksOf C rows envs a0 n ans scr i ds, c.2 = true) ↔
        ∀ j d, ds[j]? = some d → ∃ y, ans (i + j) = .sat y ∧ C rows envs a0 d y n
  | [], i => by simp [ver015_checksOf]
  | d :: ds, i => by
    simp only [ver015_checksOf, List.mem_cons, forall_eq_or_imp, decide_eq_true_eq]
    rw [ver015_checksOf_ok C rows envs a0 n ans scr ds (i + 1)]
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

/-- **The dispatched bound follows the phase.** Take any re-check, demands and phase that meet
the first block, and any dispatch that meets the order block. Build a call whose checks are the
re-check applied to the solver's answers for the property's demands, with the solver up. Then a
bound step of the dispatch can return `Proven` only when the phase proves, and when the phase
proves, a solver answering `sat` to every script makes the step return `Proven`. So the step a
dispatch runs and the phase of the first block agree on every call. -/
theorem VER_015_order_follows_phase {C : LinCheckRel} {Dm : LinDemandFn} {Ph : LinPhaseRel}
    (h15 : VER_015 C Dm Ph) {D : BoundDispatch} (hD : VER_015_order D) {s : GStep BoundCall}
    (hs : s ∈ D) (hn : s.name = "linear bound") (o : Options) (q : BoundCall) (rows : LinRows)
    (envs : List PlaceId) (a0 : AMarking) (n : Nat) (prop : BoundProp) (ans : Nat → BoundAnswer)
    (scr : Nat → String) (hq : q.checks = ver015_checksOf C rows envs a0 n ans scr 0 (Dm prop))
    (hup : q.solverUp = true) :
    (∀ R : String → SolverReply → Prop,
      Yields R (s.run o q) (.decided (.proven "structural") [] none) → Ph rows envs a0 n prop ans) ∧
    (Ph rows envs a0 n prop ans →
      Yields (fun _ r => r = .answer .sat) (s.run o q) (.decided (.proven "structural") [] none)) := by
  have hPh := h15.2.2.2.2.2 rows envs a0 n prop ans
  have hok := ver015_checksOf_ok C rows envs a0 n ans scr (Dm prop) 0
  simp only [Nat.zero_add] at hok
  refine ⟨fun R h => ?_, fun hp => ?_⟩
  · have := (hD.2.1 s hs hn o q R _ h).2 rfl
    rw [hPh, ← hok, ← hq]
    exact fun c hc => (this c hc).1
  · have hall : ∀ c ∈ q.checks, c.2 = true := by rw [hq, hok, ← hPh]; exact hp
    obtain ⟨out, hy⟩ := ver015_yields_exists (R := fun _ r => r = .answer .sat)
      (fun _ => ⟨_, rfl⟩) (s.run o q)
    have := hD.2.2.1 s hs hn o q _ out hup (fun c hc => ⟨hall c hc, fun r hr => hr⟩) hy
    rw [this] at hy
    exact hy

end Libpetri.Spec
