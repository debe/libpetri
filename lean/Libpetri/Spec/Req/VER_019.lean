import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Novel.FiringBound.Phase
import Libpetri.Novel.FiringBound.Witness
import Libpetri.Spec.Verifier.Pipeline

set_option linter.missingDocs true

/-!
# VER-019: Firing-bound phase (`spec/07-verification.md`)

After the state-equation phase and before the fixpoint query, the verifier asks for a
**ranking**: a weighting `r ≥ 0` of the places under which every flat transition that can fire
lowers `r·M` by at least one. Re-checked in exact arithmetic, it bounds every run by
`K = r·M0` firings. A bounded model check at depths up to `K` then decides the property: `unsat`
at a depth of at least `K` is a proof, `sat` is a run that is replayed before it is reported.

The requirement is a predicate over a triple `(C, D, P)`:

* `C : FBRankingCheck`, the exact re-check of a weighting, from the number of flat places, the
  flat net as deposit rows, `M0` and the weighting to the bound `K`, or to nothing when the
  weighting is not a ranking (the shape of `checkRankingExact`, `Novel/FiringBound/Ranking.lean`);
* `D : FBDepthLoop`, the depth loop, from the bound, the depth limit and the solver's answer per
  depth to an outcome (the shape of `phaseDepths`, `Novel/FiringBound/Phase.lean`);
* `P : FBPhaseFn`, the phase, from the injection flag, the flat net, `M0`, the violation, the
  depth limit, the ranking query's answer and the bounded model check's answer per depth to an
  outcome (`refFiringBoundPhase` below, which `run_firing_bound_phase` in `bounded_run.rs` is).

The witness triple is `checkRankingExact`, `phaseDepths` and `refFiringBoundPhase`. The statement
is checked against them (`VER_019_reference`), against two wrong re-checks (one that accepts a
column sum of 0, one that also demands the column sum of a transition that can never fire),
against two wrong depth loops (one that proves at its first `unsat`, one that jumps from the
first depth to the bound) and against wrong phases (one that runs on a net with injection, one
that proves a net without a ranking, one that reads an unanswered ranking query as no ranking,
one that skips the re-check, one without the largest bound, one that never proves, one that
proves at the depth limit, one that reports a run without replaying it, one that reads a model
defining no selector as the empty run, one that never reports a run). From the statement
alone: a `Proven` with bound `K` bounds every run by `K` firings (`VER_019_bound`), and, when the
solver's `unsat` answers are correct, no reachable marking violates (`VER_019_proven_sound`); a
reported run replays to a violating marking (`VER_019_violated_sound`). The schedule, the depth
limit, the largest bound and the report lines are pure functions, pinned with `#guard`.

A second block, `VER_019_order` at the end of the file, places the phase in the verifier's
pipeline (`Spec/Verifier/Pipeline.lean`): once, after the state-equation phase and before the
witness phase and the fixpoint query, entered where the state-equation phase would be entered whatever that phase's option,
never when disabled, and handing its outcome over as an aside or a decision.
-/

namespace Libpetri.Spec

open Libpetri (AMarking PlaceId Transition Card Weight dot)
open Libpetri.Novel.FiringBound
open Libpetri.Novel.ForwardDeposit (ReachAD)
open Libpetri.Novel.LinearBound (dotIncD)

/-! ## The model -/

/-- The answer of the ranking query (phase `ranking`). -/
inductive FBRank where
  /-- `sat`, with the weighting the model gives. -/
  | ranking (r : Weight)
  /-- `unsat`: no weighting is a ranking. -/
  | noRanking
  /-- No `sat` or `unsat` answer: `unknown`, a transport failure or a spent phase budget. -/
  | aside

/-- Why the phase ends inconclusive. -/
inductive FBReason where
  /-- The net has injected environment places. -/
  | injection
  /-- The ranking query got no `sat` or `unsat` answer. -/
  | rankingAside
  /-- The weighting failed the exact re-check. -/
  | recheck
  /-- The bound is larger than `2^53 − 1`. -/
  | tooLarge
  /-- The depth loop stepped aside: a depth without a `sat` or `unsat` answer, or `unsat` at the
  depth limit below the bound. -/
  | depthAside
  /-- The run read from a `sat` model does not replay to a violating marking, or the model
  defines no selector. -/
  | noReplay
  deriving DecidableEq, Repr

/-- What the phase ends with. -/
inductive FBOutcome where
  /-- `Proven` with method `bounded-model-check`, and the firing bound. -/
  | proven (K : Nat)
  /-- `Violated` with the replayed run (flat transition indices in firing order). -/
  | violated (run : List Nat)
  /-- No ranking exists; the pipeline continues. -/
  | unbounded
  /-- The phase steps aside; the pipeline continues. -/
  | inconclusive (why : FBReason)
  deriving DecidableEq, Repr

/-- An exact ranking re-check: `C n rows a0 r` is the bound `K` the weighting `r` gives on the
flat net `rows` with `n` places from `M0 = a0`, or `none` when `r` is not accepted. The shape of
`checkRankingExact`. -/
abbrev FBRankingCheck : Type :=
  Nat → List Novel.FiringBound.Row → AMarking → Weight → Option Int

/-- A depth loop: `D k L ask` is the outcome for the bound `k`, the depth limit `L` and the
solver's answers `ask d` (`some true` = `sat`, `some false` = `unsat`, `none` = no answer). The
shape of `phaseDepths`. -/
abbrev FBDepthLoop : Type := Nat → Nat → (Nat → Option Bool) → DepthOutcome

/-- A firing-bound phase: `P inj n rows a0 isBad L rank bmc` is the outcome on the flat net
`rows` with `n` places, `M0 = a0` and the violation `isBad`, with the injection flag `inj` (the
net declares environment places for injection), the depth limit `L`, the ranking query's answer
`rank` and the bounded model check's answer `bmc d` at each depth `d`. -/
abbrev FBPhaseFn : Type :=
  Bool → Nat → List Novel.FiringBound.Row → AMarking → (AMarking → Bool) → Nat → FBRank →
    (Nat → Witness.Answer) → FBOutcome

/-- The bounded model check's answer at a depth, as the depth loop reads it: `sat` is
`some true`, `unsat` is `some false`, and `unknown`, a transport failure or a spent budget is no
answer. -/
def ver019_ask (bmc : Nat → Witness.Answer) (d : Nat) : Option Bool :=
  match bmc d with
  | .sat _ => some true
  | .unsat => some false
  | _ => none

/-- The largest bound the phase accepts, `2^53 − 1`: the ports count depths in a type that holds
it exactly, so they refuse the same bounds. -/
def ver019_largestBound : Int := 2 ^ 53 - 1

/-- The depth loop read along a list of depths: the first depth without an answer ends it, a
`sat` depth is reported, an `unsat` depth of at least `k` is a proof, and an `unsat` depth below
`k` goes on to the next; running out of depths is stepping aside. -/
def ver019_scan (k : Nat) (ask : Nat → Option Bool) : List Nat → DepthOutcome
  | [] => .stop
  | d :: ds =>
    match ask d with
    | none => .stop
    | some true => .sat d
    | some false => if k ≤ d then .proven else ver019_scan k ask ds

/-- The depths from `d` on: `d`, then, while `d` is below both `k` and `L`,
`min(2d, k, L)`. -/
def ver019_scheduleFrom (k L : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, d =>
    d :: if k ≤ d ∨ L ≤ d then [] else ver019_scheduleFrom k L fuel (min (min (2 * d) k) L)

/-- **The depth schedule** for the bound `k` and the depth limit `L`: first `min(k, 8, L)`, then
each time twice the previous depth, capped at `k` and at `L`, until a depth reaches `k` or `L`.
The fuel `k + 1` never runs out first: a first depth of 0 means `k = 0` or `L = 0`, where the list
ends at once, and from a positive depth every step grows by at least one up to `min(k, L)`. -/
def ver019_schedule (k L : Nat) : List Nat :=
  ver019_scheduleFrom k L (k + 1) (min (min k 8) L)

/-- **The reference phase**, `run_firing_bound_phase` (`bounded_run.rs`): no query on a net with
injection; the ranking query; the exact re-check (`checkRankingExact`); the largest bound; the
depth loop (`phaseDepths`); on a `sat` depth, the run read from the model (`decodeModel`, with no
injection step) and replayed under the exact abstract semantics (`replays` with no injection). -/
def refFiringBoundPhase : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  if inj = true then .inconclusive .injection
  else
    match rank with
    | .noRanking => .unbounded
    | .aside => .inconclusive .rankingAside
    | .ranking r =>
      match checkRankingExact n rows a0 r with
      | none => .inconclusive .recheck
      | some K =>
        if ver019_largestBound < K then .inconclusive .tooLarge
        else
          match phaseDepths K.toNat L (ver019_ask bmc) with
          | .proven => .proven K.toNat
          | .stop => .inconclusive .depthAside
          | .sat d =>
            match bmc d with
            | .sat s =>
              match decodeModel rows.length s d with
              | none => .inconclusive .noReplay
              | some run =>
                if replays rows [] isBad a0 run = true then .violated run
                else .inconclusive .noReplay
            | _ => .inconclusive .depthAside

/- The exact re-check, the depth loop and the composite phase are the witness triple of
VER-019's `holds` theorem. -/
#spec_witness checkRankingExact
#spec_witness phaseDepths
#spec_witness refFiringBoundPhase

/-! ## VER-019: Firing-bound phase -/

requirement VER_019
  id "VER-019"
  title "Firing-Bound Phase"
  kind B
  scope "the SMT verifier, all implementations"
  source verbatim "spec/07-verification.md"
  quote "*When* the ranking query answers with a weighting `r`, the phase *shall* re-check in exact integer arithmetic that every weight is at least 0 and that `r·C_t ≤ −1` for every flat transition `t` that can fire, and *shall* take the bound `K = r·M0` only when the re-check passes."
        "*If* the re-check fails or `K` is larger than `2^53 − 1`, *then* the phase *shall* end inconclusive without a bounded model check, and the pipeline *shall* continue."
        "*When* the phase has the bound `K`, it *shall* ask the bounded model check first at depth `min(K, 8, L)`, where `L` is the depth limit, and after an `unsat` answer at a depth `d` below both `K` and `L` it *shall* ask next at depth `min(2d, K, L)`."
        "The depth limit `L` *shall* be 512 in every implementation."
        "*If* the bounded model check answers `unsat` at a depth of at least `K`, *then* the phase *shall* return `Proven` with method `bounded-model-check` and the bound `K`."
        "*If* the bounded model check answers `unsat` at the depth limit while `K` is larger, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue."
        "*When* the bounded model check answers `sat` at a depth, the phase *shall* read the run from the model's selectors as the bounded witness phase ([VER-025]) reads it with no injection step, replay it under the exact abstract semantics, and return `Violated` with that run, untrimmed and confirmed, when every step is enabled and the last marking violates the property."
        "*If* the depth is positive and the model defines none of the step selectors, or the run does not replay to a violating marking, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue."
        "*If* the ranking query answers `unsat`, *then* the phase *shall* report that the net has no firing bound, whatever the second query answers, and the pipeline *shall* continue to the fixpoint query."
        "*If* the ranking query or a bounded model check fails in the transport or answers `unknown`, or the phase budget is spent before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue."
        "*If* environment places are declared for injection, *then* the phase *shall* send no query and *shall* end inconclusive, also when no arc touches such a place."
        "Every implementation *shall* turn this phase on by default, as it turns on the phase of [VER-018]."
  reading "The re-check C accepts a weighting r on a flat net (rows, n places) from a0, with the bound K, exactly when r is a ranking (every weight below n is at least 0, and every row that can fire has a column sum r·C_t of at most −1: IsRanking) and K = r·a0."
          "The depth loop D for the bound k and the limit L is the scan of the schedule: the depths min(k, 8, L), then min(2d, k, L) while d is below k and L; at each depth in turn, no answer ends it (stop), sat reports that depth, unsat at a depth of at least k is proven, unsat below k goes on, and running out of depths is stop."
          "With the injection flag set, the phase P ends inconclusive (injection), whatever the solver would answer."
          "Without injection, a ranking query answered unsat gives unbounded (no firing bound)."
          "Without injection, a ranking query without a sat or unsat answer gives inconclusive (rankingAside)."
          "Without injection, a weighting C rejects gives inconclusive (recheck)."
          "Without injection, a bound K that C accepts and that is larger than 2^53 − 1 gives inconclusive (tooLarge)."
          "Without injection, with a bound K that C accepts and that is at most 2^53 − 1: when D at K and L, over the bounded model check's answers, is proven, P is proven with the bound K."
          "In the same case, when D stops, P is inconclusive (depthAside)."
          "In the same case, when D reports a sat depth d whose model s is given: a model decodeModel reads as no run (d is positive and s defines none of the selectors below d) gives inconclusive (noReplay); a model whose decoded run (decodeModel at T, no injection) replays to a violating marking gives violated with that run; one whose run does not replay gives inconclusive (noReplay)."
  assumes "The model is the triple (C, D, P) of FBRankingCheck, FBDepthLoop and FBPhaseFn. C is the re-check from the number n of flat places, the flat net as deposit rows (Row = transition and deposit, the exact abstract semantics of VER-004: enabledA, fireAD), M0 and the weighting (Weight, an integer per place) to the bound K or none. D is the depth loop from the bound, the depth limit and the solver's answer per depth (some true = sat, some false = unsat, none = no answer). P is the phase from the injection flag, n, the rows, M0, the violation isBad (the property's violation predicate as replay_run reads it), the depth limit L, the ranking query's answer (FBRank) and the bounded model check's answer per depth (Witness.Answer, as for VER-025: sat with the selector values the model defines, unsat, unknown, a transport failure, a spent budget). The witness triple is checkRankingExact, phaseDepths and refFiringBoundPhase."
          "The first quoted sentence is line 1. 'Can fire' is canFire (bounded_run.rs can_fire): every inhibited place has pre 0 and is not read; a transition that inhibits a place it needs is enabled at no marking (not_canFire_never_enabled), so its column does not count. 'Exact integer arithmetic' is Lean's Int: the model has no overflow. A port whose i128 re-check overflows refuses the weighting, which is the recheck outcome; z3's weights keep it far from that. A sat reply whose weights do not decode is reported by the ports as a failed re-check; the model's FBRank.ranking carries decoded weights only, and both cases end inconclusive. That a ranking bounds every run by K is a consequence, not a line: VER_019_bound, from line 1 through ranking_bounds_length."
          "The second quoted sentence is lines 6 and 7: P ends inconclusive and D is never consulted. 'The pipeline shall continue' is the pipeline around the phase, the second block VER_019_order (line 7): its hand-over turns P's inconclusive and unbounded outcomes into an aside, after which the pipeline enters its next step (VER_019_order_continues)."
          "The third quoted sentence is line 2 (ver019_schedule, pinned with #guard below: bound 5 gives the depths [5], bound 25 [8, 16, 25], bound 600 at the limit 512 [8, 16, 32, 64, 128, 256, 512]). The fourth (the limit 512) is the constant ver019_depthLimit, pinned below; the model is parametric in L, so the statement holds at every limit."
          "The fifth quoted sentence is line 2 (unsat at a depth of at least K is proven) with line 8 (P is proven with the bound K, the outcome proven K; VER_019_forbids_neverProves kills a phase that steps aside there). 'Method bounded-model-check' is the verdict's method ver019_method, which the hand-over of VER_019_order (line 8) puts on the Proven it returns, with no counterexample and no counterexampleConfirmed, and the bound reaches the report as the Bound line of AC1. That the proof is sound is VER_019_proven_sound, from the statement alone, under the premises it names: well-formed rows (P1, P2), an integer violation that agrees with isBad (P5), and correct unsat answers (P4: the depth-d script has no model, BmcSat, when the solver says unsat). These premises are about the solver and the encoder, which the statement does not model, so they are hypotheses of the derived theorem, not of the requirement."
          "The sixth quoted sentence is line 2 (unsat at the last depth of the schedule, the limit, below K ends the scan with stop) and line 9."
          "The seventh and eighth quoted sentences are line 10. The run is read as VER-025 reads it (decodeModel at T = the number of rows, J = 0: a selector in [0, T) is a transition step, anything else ends the run, an undefined selector is idle, a model that defines none of the selectors below a positive depth gives no run, and depth 0 gives the empty run whatever the model, as decode_bounded_run does with seen = depth == 0) and replayed by replays with no injection (replayEnv at [] is replay: replayEnv_nil). So at depth 0, which the schedule asks only when K = 0 (or L = 0), a sat answer is the empty run, reported when isBad a0 holds; the prose after the eighth sentence says so. The run is reported as decoded, untrimmed, as the seventh sentence says (the trim is VER-025's). Each branch of line 10 has its own mutant: VER_019_forbids_silentAsEmpty (a model that defines no selector at a positive depth read as the empty run), VER_019_forbids_neverViolated (a replaying run not reported) and VER_019_forbids_noReplay (a run reported without replay). 'Confirmed' (counterexampleConfirmed true) and the run's transitions as the counterexample are VER_019_order line 9; the result text is outside the model. That a reported run reaches a violating marking is VER_019_violated_sound, from the statement alone. A sat answer comes only at a depth the loop asked (line 2: scan reports sat only where ask answered sat), so the model given is that depth's."
          "The ninth quoted sentence is line 4. The second query that names the transitions of a repeatable firing vector is not an input of P: line 4 fixes unbounded for every answer the phase gets after the ranking query's unsat, so whatever the second query answers (a vector, unsat, unknown, a transport failure or a spent budget, as bounded_run.rs reads every reply but a decodable sat as no vector) the outcome is unbounded. Its report line, with the vector or the fallback, is report text (ver019_noBoundLine and ver019_noBoundFallback, pinned below); which transitions z3 names is not modelled. 'Continue to the fixpoint query' is the pipeline, as in the second quoted sentence."
          "The tenth quoted sentence names the ranking query and the bounded model checks only; the second query is the ninth sentence's. It is line 5 for the ranking query and lines 2 and 9 for a depth (no answer ends the scan with stop). A transport failure, unknown and a spent phase budget are one answer each in Witness.Answer and one FBRank.aside; the model does not tell them apart, as the outcome does not; only the reason text of the report does, and it is not modelled. The budget, half the timeout rounded down to whole milliseconds and at least 1 ms as the prose says (max(1, floor(timeout_ms / 2)) in smt_verifier.rs, smt-verifier.ts and SmtVerifier.java), is the pure function ver019_budgetMs, pinned below; the wall clock is not modelled."
          "The eleventh quoted sentence is line 3. The flag is the declared injection list being non-empty (smt_verifier.rs gates on cx.env_injection before resolution), so a declared environment place no arc touches sets it too. 'Send no query' is not expressible, as for VER-025: the answers are inputs of P; line 3 fixes the outcome for every answer, so it depends on none. Under Ignore the phase is not entered at all (it runs on the queries VER-018 runs on), which is the pipeline's gate (VER_019_order line 6), not this model's."
          "The twelfth quoted sentence (on by default, as VER-018) is configuration (N): the constant ver019_defaultOn, pinned below; that the two phases default alike is checked by the verdict-parity fixtures, and the order 'after VER-018 and before the witness phase and the fixpoint query' and 'runs on the queries VER-018 runs on' are VER_019_order lines 1 to 4 and line 6, not this model."
          "The sentence on a disabled phase (not run, and the verdicts and reports those of the pipeline without it) is quoted by VER_019_order, line 5, the pipeline's gate: P is the phase when it runs, so a disabled phase is not an input of P and the equality with the pipeline without the phase is a statement about the pipeline (VER_019_order_disabled). The prose 'Disabling the phase leaves the query to the later steps, up to the fixpoint query' is the same gate seen from the pipeline."
          "The kept prose that the ranking with the least K is found by one optimisation query names the ranking script's objective, the line (minimize r·M0) that encode_ranking_query writes in every port (bounded_run.rs, bounded-run.ts, BoundedRun.java). The model takes the solver's weighting as an input of P, and every line holds for every weighting, so the statement neither needs nor checks that it is least. Least matters across ports, since K sets the depth schedule and the tooLarge cut, but the least K is one number for a given net and M0, so ports that send the same objective and get a correct optimum agree on it. The objective is pinned by the Rust and Java script tests (bounded_run.rs, BoundedRunTest.java); the cross-language goldens of VER-013 hold the state-equation, horn, certificate and witness scripts, not the ranking script."
          "A name-alignment property (NU-055) is refused by the phase before any query and before the injection check (bounded_run.rs and bounded-run.ts return the NU-055 reason first; the prose says so); that refusal is NU-055's line, and isBad here is a violation over counts. The quiescence reading inside isBad (reap-aware unless assumeNoReaping, VER-002) is VER-002's subject: the model takes the violation as given. Reaping.firing_bound_proves_reaped_net is a retrodiction of the phase before the reaping fix and is not evidence here."
          "AC1 (the ranking re-checked before its bound is used; the Bound report line) is line 1 and lines 6 to 10 (no bound is used unless C accepts), with VER_019_nonvacuous (the queue-and-bundle ranking budget + s + 2*src accepted with the bound 5) and the report line ver019_boundLine, pinned below."
          "AC2 (a violating run replayed and reported violated, confirmed) is line 10 and VER_019_violated_sound; VER_019_nonvacuous replays the run produce, produce, produce, cancel on the cancelled queue."
          "AC3 (unsat at depth K is Proven with method bounded-model-check; the certificate line) is lines 2 and 8, with ver019_method and ver019_certLine pinned below. That the certificate check does not apply is the pipeline's: the hand-over of VER_019_order returns a decision, which ends the run before the certificate check step."
          "AC4 (a net without a ranking, with the repeatable-vector line or its fallback, then the fixpoint query) is line 4, VER_019_ring_no_ranking (no weighting is accepted on the ring t0, t1, t2) and the report lines pinned below."
          "AC5 (with the phase disabled, verdicts and reports are those of the pipeline without it) is VER_019_order line 5 with VER_019_order_disabled: the model here is the phase when it runs."
          "The Encoding paragraph (the script's selectors, idle steps, the empty post-caps) is the constraint system BmcModel of Bmc.lean, whose exactness at the bound (bmc_exact_at_bound) VER_019_proven_sound uses; the SMT-LIB text and its goldens are VER-013's (P4). The measurements are not requirements. The test derivation is AC1 to AC4 as above, under the options it names (enumeration budget 0, VER-018 off, assumeAtomicFiring for the queue, the linear bound off for the ring), which the pipeline sets outside the model."
  signoff "pending"
  statement : FBRankingCheck → FBDepthLoop → FBPhaseFn → Prop :=
    fun C D P =>
      (∀ (n : Nat) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (r : Weight) (K : Int),
        C n rows a0 r = some K ↔ IsRanking n rows r ∧ K = dot r a0 n) ∧
      (∀ (k L : Nat) (ask : Nat → Option Bool),
        D k L ask = ver019_scan k ask (ver019_schedule k L)) ∧
      (∀ n rows a0 isBad L rank bmc,
        P true n rows a0 isBad L rank bmc = .inconclusive .injection) ∧
      (∀ n rows a0 isBad L bmc, P false n rows a0 isBad L .noRanking bmc = .unbounded) ∧
      (∀ n rows a0 isBad L bmc,
        P false n rows a0 isBad L .aside bmc = .inconclusive .rankingAside) ∧
      (∀ n rows a0 isBad L r bmc, C n rows a0 r = none →
        P false n rows a0 isBad L (.ranking r) bmc = .inconclusive .recheck) ∧
      (∀ n rows a0 isBad L r K bmc, C n rows a0 r = some K → ver019_largestBound < K →
        P false n rows a0 isBad L (.ranking r) bmc = .inconclusive .tooLarge) ∧
      (∀ n rows a0 isBad L r K bmc, C n rows a0 r = some K → K ≤ ver019_largestBound →
        D K.toNat L (ver019_ask bmc) = .proven →
        P false n rows a0 isBad L (.ranking r) bmc = .proven K.toNat) ∧
      (∀ n rows a0 isBad L r K bmc, C n rows a0 r = some K → K ≤ ver019_largestBound →
        D K.toNat L (ver019_ask bmc) = .stop →
        P false n rows a0 isBad L (.ranking r) bmc = .inconclusive .depthAside) ∧
      (∀ n rows a0 isBad L r K bmc d s, C n rows a0 r = some K → K ≤ ver019_largestBound →
        D K.toNat L (ver019_ask bmc) = .sat d → bmc d = .sat s →
        (decodeModel rows.length s d = none →
          P false n rows a0 isBad L (.ranking r) bmc = .inconclusive .noReplay) ∧
        ∀ run, decodeModel rows.length s d = some run →
          (replays rows [] isBad a0 run = true →
            P false n rows a0 isBad L (.ranking r) bmc = .violated run) ∧
          (replays rows [] isBad a0 run = false →
            P false n rows a0 isBad L (.ranking r) bmc = .inconclusive .noReplay))

/- The pinned readable form of VER-019: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_019 : FBRankingCheck → FBDepthLoop → FBPhaseFn → Prop :=
fun C D P =>
  (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (r : Weight) (K : ℤ),
      C n rows a0 r = some K ↔ IsRanking n rows r ∧ K = dot r a0 n) ∧
    (∀ (k L : ℕ) (ask : ℕ → Option Bool), D k L ask = ver019_scan k ask (ver019_schedule k L)) ∧
      (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ) (rank : FBRank)
          (bmc : ℕ → Witness.Answer), P true n rows a0 isBad L rank bmc = FBOutcome.inconclusive FBReason.injection) ∧
        (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
            (bmc : ℕ → Witness.Answer), P false n rows a0 isBad L FBRank.noRanking bmc = FBOutcome.unbounded) ∧
          (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
              (bmc : ℕ → Witness.Answer),
              P false n rows a0 isBad L FBRank.aside bmc = FBOutcome.inconclusive FBReason.rankingAside) ∧
            (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
                (r : Weight) (bmc : ℕ → Witness.Answer),
                C n rows a0 r = none →
                  P false n rows a0 isBad L (FBRank.ranking r) bmc = FBOutcome.inconclusive FBReason.recheck) ∧
              (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
                  (r : Weight) (K : ℤ) (bmc : ℕ → Witness.Answer),
                  C n rows a0 r = some K →
                    ver019_largestBound < K →
                      P false n rows a0 isBad L (FBRank.ranking r) bmc = FBOutcome.inconclusive FBReason.tooLarge) ∧
                (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
                    (r : Weight) (K : ℤ) (bmc : ℕ → Witness.Answer),
                    C n rows a0 r = some K →
                      K ≤ ver019_largestBound →
                        D K.toNat L (ver019_ask bmc) = DepthOutcome.proven →
                          P false n rows a0 isBad L (FBRank.ranking r) bmc = FBOutcome.proven K.toNat) ∧
                  (∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
                      (r : Weight) (K : ℤ) (bmc : ℕ → Witness.Answer),
                      C n rows a0 r = some K →
                        K ≤ ver019_largestBound →
                          D K.toNat L (ver019_ask bmc) = DepthOutcome.stop →
                            P false n rows a0 isBad L (FBRank.ranking r) bmc =
                              FBOutcome.inconclusive FBReason.depthAside) ∧
                    ∀ (n : ℕ) (rows : List Novel.FiringBound.Row) (a0 : AMarking) (isBad : AMarking → Bool) (L : ℕ)
                      (r : Weight) (K : ℤ) (bmc : ℕ → Witness.Answer) (d : ℕ) (s : ℕ → Option ℤ),
                      C n rows a0 r = some K →
                        K ≤ ver019_largestBound →
                          D K.toNat L (ver019_ask bmc) = DepthOutcome.sat d →
                            bmc d = Witness.Answer.sat s →
                              (decodeModel rows.length s d = none →
                                  P false n rows a0 isBad L (FBRank.ranking r) bmc =
                                    FBOutcome.inconclusive FBReason.noReplay) ∧
                                ∀ (run : List ℕ),
                                  decodeModel rows.length s d = some run →
                                    (replays rows [] isBad a0 run = true →
                                        P false n rows a0 isBad L (FBRank.ranking r) bmc = FBOutcome.violated run) ∧
                                      (replays rows [] isBad a0 run = false →
                                        P false n rows a0 isBad L (FBRank.ranking r) bmc =
                                          FBOutcome.inconclusive FBReason.noReplay)
-/
#guard_msgs in #print VER_019

/-! ### The reference -/

/-- The exact re-check accepts a weighting with the bound `K` exactly when it is a ranking and
`K = r·M0`: `checkRankingExact_sound` one way, the definition the other. -/
theorem ver019_check_iff (n : Nat) (rows : List Novel.FiringBound.Row) (a0 : AMarking)
    (r : Weight) (K : Int) :
    checkRankingExact n rows a0 r = some K ↔ IsRanking n rows r ∧ K = dot r a0 n := by
  constructor
  · exact checkRankingExact_sound
  · rintro ⟨⟨hpos, hrows⟩, rfl⟩
    unfold checkRankingExact
    rw [if_pos]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
      Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨hpos, fun tr hmem => ?_⟩
    cases h : canFire tr.1
    · exact Or.inl rfl
    · exact Or.inr (hrows tr hmem h)

/-- The fuelled depth loop is the scan of the schedule from the same depth with the same fuel. -/
theorem ver019_depthLoop_eq (k L : Nat) (ask : Nat → Option Bool) :
    ∀ fuel d, depthLoop k L ask fuel d = ver019_scan k ask (ver019_scheduleFrom k L fuel d)
  | 0, _ => rfl
  | fuel + 1, d => by
    simp only [depthLoop, ver019_scheduleFrom, ver019_scan]
    cases ask d with
    | none => rfl
    | some b =>
      cases b with
      | true => rfl
      | false =>
        simp only
        by_cases hk : k ≤ d
        · simp [hk]
        · by_cases hL : L ≤ d
          · simp [hk, hL, ver019_scan]
          · simp only [hk, hL, if_false, false_or]
            exact ver019_depthLoop_eq k L ask fuel _

/-- **The reference depth loop is the scan of the schedule.** -/
theorem ver019_phaseDepths_eq (k L : Nat) (ask : Nat → Option Bool) :
    phaseDepths k L ask = ver019_scan k ask (ver019_schedule k L) :=
  ver019_depthLoop_eq k L ask (k + 1) _

/-- The reference triple satisfies VER-019: the re-check is exact (`ver019_check_iff`), the
depth loop is the scan of the schedule (`ver019_phaseDepths_eq`), and the phase's cases are those
of `refFiringBoundPhase`. -/
@[evidence holds VER_019]
theorem VER_019_reference : VER_019 checkRankingExact phaseDepths refFiringBoundPhase := by
  refine ⟨ver019_check_iff, ver019_phaseDepths_eq,
    fun _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun n rows a0 isBad L r bmc hC => by simp [refFiringBoundPhase, hC],
    fun n rows a0 isBad L r K bmc hC hK => by simp [refFiringBoundPhase, hC, hK],
    fun n rows a0 isBad L r K bmc hC hK hD => by
      simp [refFiringBoundPhase, hC, not_lt.mpr hK, hD],
    fun n rows a0 isBad L r K bmc hC hK hD => by
      simp [refFiringBoundPhase, hC, not_lt.mpr hK, hD],
    fun n rows a0 isBad L r K bmc d s hC hK hD hs => ⟨fun hdec => by
      simp [refFiringBoundPhase, hC, not_lt.mpr hK, hD, hs, hdec],
      fun run hdec => ⟨fun hr => by simp [refFiringBoundPhase, hC, not_lt.mpr hK, hD, hs, hdec, hr],
        fun hr => by simp [refFiringBoundPhase, hC, not_lt.mpr hK, hD, hs, hdec, hr]⟩⟩⟩

/-- ✓ VER-019 is consistent: the reference re-check, depth loop and phase satisfy it. -/
@[evidence consistent VER_019]
theorem VER_019_consistent :
    ∃ (C : FBRankingCheck) (D : FBDepthLoop) (P : FBPhaseFn), VER_019 C D P :=
  ⟨_, _, _, VER_019_reference⟩

/-! ### What the statement says on its own -/

/-- The scan proves only at a depth of the list that is at least `k` and was answered `unsat`. -/
theorem ver019_scan_proven {k : Nat} {ask : Nat → Option Bool} :
    ∀ {ds : List Nat}, ver019_scan k ask ds = .proven → ∃ d ∈ ds, k ≤ d ∧ ask d = some false
  | [], h => by simp [ver019_scan] at h
  | d :: ds, h => by
    simp only [ver019_scan] at h
    cases hq : ask d with
    | none => rw [hq] at h; cases h
    | some b =>
      rw [hq] at h
      cases b with
      | true => cases h
      | false =>
        simp only at h
        split at h
        · exact ⟨d, List.mem_cons_self .., by assumption, hq⟩
        · obtain ⟨e, he, hk, hq'⟩ := ver019_scan_proven h
          exact ⟨e, List.mem_cons_of_mem _ he, hk, hq'⟩

/-- The scan reports `sat` only at a depth answered `sat`. -/
theorem ver019_scan_sat {k : Nat} {ask : Nat → Option Bool} :
    ∀ {ds : List Nat} {d : Nat}, ver019_scan k ask ds = .sat d → ask d = some true
  | [], _, h => by simp [ver019_scan] at h
  | e :: ds, d, h => by
    simp only [ver019_scan] at h
    cases hq : ask e with
    | none => rw [hq] at h; cases h
    | some b =>
      rw [hq] at h
      cases b with
      | true => simp only [DepthOutcome.sat.injEq] at h; subst h; exact hq
      | false =>
        simp only at h
        split at h
        · cases h
        · exact ver019_scan_sat h

/-- `unsat` at a depth is the answer `unsat`. -/
theorem ver019_ask_false {bmc : Nat → Witness.Answer} {d : Nat}
    (h : ver019_ask bmc d = some false) : bmc d = .unsat := by
  cases hb : bmc d <;> simp [ver019_ask, hb] at h ⊢

/-- `sat` at a depth is a `sat` answer with a model. -/
theorem ver019_ask_true {bmc : Nat → Witness.Answer} {d : Nat}
    (h : ver019_ask bmc d = some true) : ∃ s, bmc d = .sat s := by
  cases hb : bmc d <;> simp [ver019_ask, hb] at h ⊢

/-- **Where a `Proven` and a run come from**, from the statement alone: without injection, a
`Proven` with bound `K` comes from a ranking query answered with a weighting that `C` accepts with
a bound `K'` within the largest bound, a depth loop that proves at `K'`, and `K = K'`; a reported
run replays to a violating marking. -/
theorem VER_019_outcome {C : FBRankingCheck} {D : FBDepthLoop} {P : FBPhaseFn}
    (h : VER_019 C D P) {n : Nat} {rows : List Novel.FiringBound.Row} {a0 : AMarking}
    {isBad : AMarking → Bool} {L : Nat} {rank : FBRank} {bmc : Nat → Witness.Answer} :
    (∀ K, P false n rows a0 isBad L rank bmc = .proven K →
      ∃ r K', rank = .ranking r ∧ C n rows a0 r = some K' ∧ K' ≤ ver019_largestBound ∧
        D K'.toNat L (ver019_ask bmc) = .proven ∧ K = K'.toNat) ∧
    (∀ run, P false n rows a0 isBad L rank bmc = .violated run →
      replays rows [] isBad a0 run = true) := by
  obtain ⟨-, h2, -, h4, h5, h6, h7, h8, h9, h10⟩ := h
  cases rank with
  | noRanking =>
    rw [h4]; exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
  | aside =>
    rw [h5]; exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
  | ranking r =>
    cases hC : C n rows a0 r with
    | none =>
      rw [h6 n rows a0 isBad L r bmc hC]
      exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
    | some K' =>
      by_cases hL : ver019_largestBound < K'
      · rw [h7 n rows a0 isBad L r K' bmc hC hL]
        exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
      · have hL' : K' ≤ ver019_largestBound := not_lt.mp hL
        cases hD : D K'.toNat L (ver019_ask bmc) with
        | proven =>
          rw [h8 n rows a0 isBad L r K' bmc hC hL' hD]
          refine ⟨fun K hp => ?_, fun _ hp => (by cases hp)⟩
          cases hp
          exact ⟨r, K', rfl, hC, hL', hD, rfl⟩
        | stop =>
          rw [h9 n rows a0 isBad L r K' bmc hC hL' hD]
          exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
        | sat d =>
          have hq := ver019_scan_sat ((h2 _ _ _).symm.trans hD)
          obtain ⟨s, hs⟩ := ver019_ask_true hq
          have h10' := h10 n rows a0 isBad L r K' bmc d s hC hL' hD hs
          cases hdec : decodeModel rows.length s d with
          | none =>
            rw [h10'.1 hdec]
            exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩
          | some run =>
            cases hr : replays rows [] isBad a0 run with
            | true =>
              rw [((h10'.2 run hdec).1 hr)]
              refine ⟨fun _ hp => (by cases hp), fun run' hp => ?_⟩
              cases hp
              exact hr
            | false =>
              rw [((h10'.2 run hdec).2 hr)]
              exact ⟨fun _ hp => (by cases hp), fun _ hp => (by cases hp)⟩

/-- **A `Proven` bounds every run**, from the statement alone: when the phase proves with the
bound `K`, no replayable run from `M0` has more than `K` firings. -/
theorem VER_019_bound {C : FBRankingCheck} {D : FBDepthLoop} {P : FBPhaseFn}
    (h : VER_019 C D P) {n : Nat} {rows : List Novel.FiringBound.Row} {a0 : AMarking}
    {isBad : AMarking → Bool} {L : Nat} {rank : FBRank} {bmc : Nat → Witness.Answer} {K : Nat}
    (hP : P false n rows a0 isBad L rank bmc = .proven K) :
    ∀ ts a, replay rows a0 ts = some a → ts.length ≤ K := by
  obtain ⟨r, K', -, hC, -, -, rfl⟩ := (VER_019_outcome h).1 K hP
  obtain ⟨hr, rfl⟩ := (h.1 n rows a0 r K').mp hC
  intro ts a hrep
  have h1 := ranking_bounds_length hr hrep
  have h2 := Int.self_le_toNat (dot r a0 n)
  omega

/-- **A `Proven` is sound**, from the statement alone, under the premises about the encoder and
the solver: with well-formed rows (P1, P2), an integer violation `badI` that agrees with `isBad`
(P5), and `unsat` answers that are correct for the depth-`d` script (P4, `BmcSat`), a `Proven`
leaves no reachable marking that violates. -/
theorem VER_019_proven_sound {C : FBRankingCheck} {D : FBDepthLoop} {P : FBPhaseFn}
    (h : VER_019 C D P) {n : Nat} {rows : List Novel.FiringBound.Row} {a0 : AMarking}
    {isBad : AMarking → Bool} {badI : (PlaceId → Int) → Prop} {L : Nat} {rank : FBRank}
    {bmc : Nat → Witness.Answer} {K : Nat}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI fun a => isBad a = true)
    (hAsk : ∀ d, bmc d = .unsat → ¬ BmcSat rows n a0 badI d)
    (hP : P false n rows a0 isBad L rank bmc = .proven K) :
    ∀ a, ReachAD rows a0 a → isBad a = false := by
  obtain ⟨r, K', -, hC, -, hD, -⟩ := (VER_019_outcome h).1 K hP
  have hCk : checkRankingExact n rows a0 r = some K' :=
    (ver019_check_iff n rows a0 r K').mpr ((h.1 n rows a0 r K').mp hC)
  obtain ⟨d, -, hkd, hq⟩ := ver019_scan_proven ((h.2.1 _ _ _).symm.trans hD)
  have hKd : K' ≤ d := le_trans (Int.self_le_toNat K') (by exact_mod_cast hkd)
  intro a hreach
  cases hb : isBad a with
  | false => rfl
  | true =>
    exact absurd ((bmc_exact_at_bound hWF hBad hCk hKd).mpr ⟨a, hreach, hb⟩)
      (hAsk d (ver019_ask_false hq))

/-- **A reported run is a run to a violating marking**, from the statement alone. -/
theorem VER_019_violated_sound {C : FBRankingCheck} {D : FBDepthLoop} {P : FBPhaseFn}
    (h : VER_019 C D P) {n : Nat} {rows : List Novel.FiringBound.Row} {a0 : AMarking}
    {isBad : AMarking → Bool} {L : Nat} {rank : FBRank} {bmc : Nat → Witness.Answer}
    {run : List Nat} (hP : P false n rows a0 isBad L rank bmc = .violated run) :
    ∃ a, replay rows a0 run = some a ∧ isBad a = true ∧ ReachAD rows a0 a := by
  obtain ⟨a, hrep, hbad⟩ := replays_iff.mp ((VER_019_outcome h).2 run hP)
  rw [replayEnv_nil] at hrep
  exact ⟨a, hrep, hbad, replay_sound hrep⟩

/-! ### Examples -/

/-- A flat transition with `one`/`all` inputs and inhibitor arcs, no read or reset arc. -/
def ver019_tr (name : String) (ins : List (PlaceId × Card)) (inh : List PlaceId) : Transition :=
  { name, inputs := ins.map fun (p, c) => ⟨p, c, none⟩, inhibitors := inh, reads := [],
    resets := [] }

/-- The queue-and-bundle net of [VER-018] with the `cancel` alternative, as flat rows over the
places `budget` (0), `q` (1), `s` (2), `src` (3), `out` (4) and `cancelled` (5):
`produce: budget → q` inhibited by `s` and `out`, `signal: src → s`, `bundle: all(q) + s → out`,
`bundleEmpty: s, inhibitor(q) → out`, `cancel: src → cancelled`. -/
def ver019_queueCancel : List Novel.FiringBound.Row :=
  [(ver019_tr "produce" [(0, .one)] [2, 4], [1]),
   (ver019_tr "signal" [(3, .one)] [], [2]),
   (ver019_tr "bundle" [(1, .all), (2, .one)] [], [4]),
   (ver019_tr "bundleEmpty" [(2, .one)] [1], [4]),
   (ver019_tr "cancel" [(3, .one)] [], [5])]

/-- The queue-and-bundle net without `cancel`. -/
def ver019_queue : List Novel.FiringBound.Row := ver019_queueCancel.take 4

/-- `M0 = {budget: 3, src: 1}`. -/
def ver019_queueA0 : AMarking := fun p => if p = 0 then 3 else if p = 3 then 1 else 0

/-- The ranking `budget + s + 2*src`. -/
def ver019_queueRank : Weight := fun p => if p = 0 then 1 else if p = 2 then 1 else if p = 3 then 2 else 0

/-- `DeadlockFree` with the sinks `sinks` over the rows: no row is enabled and some place below
`n` that is not a sink holds a token. -/
def ver019_deadlock (rows : List Novel.FiringBound.Row) (n : Nat) (sinks : List PlaceId) :
    AMarking → Bool := fun a =>
  rows.all (fun tr => !enabledA a tr.1) && (List.range n).any fun p => a p != 0 && !sinks.contains p

/-- A solver model that defines every selector: the listed values, then `idle`. -/
def ver019_model (idle : Int) (xs : List Int) : Nat → Option Int :=
  Witness.defined fun i => xs.getD i idle

/-- ✓ **AC1, AC2, AC3 on the queue-and-bundle net** (the test derivation): the ranking
`budget + s + 2*src` passes the exact re-check with the bound 5; the schedule asks depth 5 alone;
with `unsat` there the phase proves `DeadlockFree` (sinks `out`, `budget`) with the bound 5. With
the `cancel` alternative (`cancelled` a sink) the ranking still gives 5, and a depth-5 model
`produce, produce, produce, cancel`, then idle, is replayed and reported as that run. -/
@[evidence nonvacuous VER_019]
theorem VER_019_nonvacuous :
    checkRankingExact 6 ver019_queue ver019_queueA0 ver019_queueRank = some 5 ∧
    ver019_schedule 5 512 = [5] ∧
    refFiringBoundPhase false 6 ver019_queue ver019_queueA0 (ver019_deadlock ver019_queue 6 [4, 0])
      512 (.ranking ver019_queueRank) (fun _ => .unsat) = .proven 5 ∧
    checkRankingExact 6 ver019_queueCancel ver019_queueA0 ver019_queueRank = some 5 ∧
    refFiringBoundPhase false 6 ver019_queueCancel ver019_queueA0
      (ver019_deadlock ver019_queueCancel 6 [4, 0, 5]) 512 (.ranking ver019_queueRank)
      (fun _ => .sat (ver019_model 5 [0, 0, 0, 4])) = .violated [0, 0, 0, 4] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The ring `t0: p0 → p1`, `t1: p1 → p2`, `t2: p2 → p0`. -/
def ver019_ring : List Novel.FiringBound.Row :=
  [(ver019_tr "t0" [(0, .one)] [], [1]),
   (ver019_tr "t1" [(1, .one)] [], [2]),
   (ver019_tr "t2" [(2, .one)] [], [0])]

/-- ✓ **AC4**: the ring has no ranking, so the exact re-check accepts no weighting at all (the
three column sums add up to 0, not to at most −3), and the phase reports no firing bound when
the ranking query answers `unsat`. -/
theorem VER_019_ring_no_ranking (a0 : AMarking) (r : Weight) :
    checkRankingExact 3 ver019_ring a0 r = none ∧
    refFiringBoundPhase false 3 ver019_ring a0 (fun _ => false) 512 .noRanking
      (fun _ => .unsat) = .unbounded := by
  refine ⟨?_, rfl⟩
  cases hc : checkRankingExact 3 ver019_ring a0 r with
  | none => rfl
  | some K =>
    obtain ⟨⟨-, hr⟩, -⟩ := checkRankingExact_sound hc
    have h0 := hr (ver019_tr "t0" [(0, .one)] [], [1]) (by simp [ver019_ring]) (by decide)
    have h1 := hr (ver019_tr "t1" [(1, .one)] [], [2]) (by simp [ver019_ring]) (by decide)
    have h2 := hr (ver019_tr "t2" [(2, .one)] [], [0]) (by simp [ver019_ring]) (by decide)
    simp [dotIncD, Libpetri.isum, Finset.sum_range_succ, ver019_tr, Libpetri.pre,
      Libpetri.specAt, Libpetri.Card.required] at h0 h1 h2
    omega

/-! ### Violations -/

/-- A re-check that accepts a column sum of 0: a loop gets a finite bound. -/
def ver019_rankLoose : FBRankingCheck := fun n rows a0 r =>
  if ((List.range n).all fun p => decide (0 ≤ r p))
      && (rows.all fun tr => !canFire tr.1 || decide (dotIncD r tr n ≤ 0)) then
    some (dot r a0 n)
  else none

/-- A transition with no arc at all: its column is 0. -/
def ver019_idleRow : Novel.FiringBound.Row := (ver019_tr "idle" [] [], [])

/-- ✗ A re-check that accepts a column sum of 0 violates VER-019 (line 1): it accepts the
weighting 0 on a transition with no arc, which every marking enables over and over. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_rankLoose :
    ¬ VER_019 ver019_rankLoose phaseDepths refFiringBoundPhase := by
  intro h
  obtain ⟨⟨-, hr⟩, -⟩ := (h.1 0 [ver019_idleRow] (fun _ => 0) (fun _ => 0) 0).mp (by decide)
  have := hr ver019_idleRow (by simp) (by decide)
  simp [dotIncD, Libpetri.isum] at this

/-- A re-check without the `can fire` filter: it demands the column sum of every row. -/
def ver019_rankAllRows : FBRankingCheck := fun n rows a0 r =>
  if ((List.range n).all fun p => decide (0 ≤ r p))
      && (rows.all fun tr => decide (dotIncD r tr n ≤ -1)) then
    some (dot r a0 n)
  else none

/-- A transition that inhibits and reads `p0`: it can never fire. -/
def ver019_deadRow : Novel.FiringBound.Row :=
  ({ name := "dead", inputs := [], inhibitors := [0], reads := [0], resets := [] }, [])

/-- ✗ A re-check without the `can fire` filter violates VER-019 (line 1): it rejects the
weighting 0 on a net whose one transition can never fire, which is a ranking. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_rankAllRows :
    ¬ VER_019 ver019_rankAllRows phaseDepths refFiringBoundPhase := by
  intro h
  have := (h.1 1 [ver019_deadRow] (fun _ => 0) (fun _ => 0) 0).mpr
    ⟨⟨fun _ _ => le_refl _, fun tr htr hcf => by
      simp only [List.mem_singleton] at htr; subst htr; revert hcf; decide⟩,
     by simp [dot, dotProduct]⟩
  revert this
  decide

/-- A depth loop that proves at its first `unsat`, whatever the bound. -/
def ver019_firstUnsat : FBDepthLoop := fun k L ask =>
  match ask (min (min k 8) L) with
  | some false => .proven
  | some true => .sat (min (min k 8) L)
  | none => .stop

/-- ✗ A depth loop that proves below the bound violates VER-019 (line 2): with the bound 9, an
`unsat` at depth 8 and a `sat` at depth 9, it proves where the schedule finds the run at 9. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_firstUnsat :
    ¬ VER_019 checkRankingExact ver019_firstUnsat refFiringBoundPhase := by
  intro h
  have := h.2.1 9 512 (fun d => if d = 8 then some false else some true)
  revert this
  decide

/-- A depth loop that goes from the first depth straight to the bound. -/
def ver019_noDoubling : FBDepthLoop := fun k L ask =>
  ver019_scan k ask [min (min k 8) L, min k L]

/-- ✗ A depth loop without the doubling violates VER-019 (line 2): with the bound 25 and a run at
depth 16, the schedule `8, 16, 25` reports `sat` at 16, while the loop that jumps to 25 proves
when the solver answers `unsat` there. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_noDoubling :
    ¬ VER_019 checkRankingExact ver019_noDoubling refFiringBoundPhase := by
  intro h
  have := h.2.1 25 512 (fun d => if d = 16 then some true else some false)
  revert this
  decide

/-- A phase that runs on a net with injection as on any other. -/
def ver019_ignoresInjection : FBPhaseFn := fun _ n rows a0 isBad L rank bmc =>
  refFiringBoundPhase false n rows a0 isBad L rank bmc

/-- ✗ A phase that runs under injection violates VER-019 (line 3): it proves the empty net with
injection, where no weighting bounds the injected runs. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_ignoresInjection :
    ¬ VER_019 checkRankingExact phaseDepths ver019_ignoresInjection := by
  intro h
  have := h.2.2.1 0 [] (fun _ => 0) (fun _ => false) 512 (.ranking fun _ => 0) (fun _ => .unsat)
  revert this
  decide

/-- A phase that, with no ranking, still runs the bounded model check at the depth limit and
proves on `unsat`. -/
def ver019_noRankingProves : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match inj, rank with
  | false, .noRanking => if ver019_ask bmc L = some false then .proven L else .unbounded
  | _, _ => refFiringBoundPhase inj n rows a0 isBad L rank bmc

/-- ✗ A phase that proves a net without a ranking violates VER-019 (line 4): the run it did not
search can be longer than the depth limit. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_noRankingProves :
    ¬ VER_019 checkRankingExact phaseDepths ver019_noRankingProves := by
  intro h
  have := h.2.2.2.1 3 ver019_ring (fun _ => 0) (fun _ => false) 512 (fun _ => .unsat)
  revert this
  decide

/-- A phase that reads an unanswered ranking query as no ranking. -/
def ver019_asideAsNoRanking : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match inj, rank with
  | false, .aside => .unbounded
  | _, _ => refFiringBoundPhase inj n rows a0 isBad L rank bmc

/-- ✗ A phase that reads `unknown` from the ranking query as `unsat` violates VER-019 (line 5):
it reports that the net has no firing bound, which no query showed. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_asideAsNoRanking :
    ¬ VER_019 checkRankingExact phaseDepths ver019_asideAsNoRanking := by
  intro h
  have := h.2.2.2.2.1 0 [] (fun _ => 0) (fun _ => false) 512 (fun _ => .unsat)
  revert this
  decide

/-- A phase that skips the re-check and takes `r·M0` as the bound of the solver's weighting. -/
def ver019_noRecheck : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match inj, rank with
  | false, .ranking r =>
    if phaseDepths (dot r a0 n).toNat L (ver019_ask bmc) = .proven then .proven (dot r a0 n).toNat
    else refFiringBoundPhase inj n rows a0 isBad L rank bmc
  | _, _ => refFiringBoundPhase inj n rows a0 isBad L rank bmc

/-- ✗ A phase without the re-check violates VER-019 (line 6): it proves with the bound 0 the net
whose one transition fires forever, from the weighting 0 the solver returned. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_noRecheck :
    ¬ VER_019 checkRankingExact phaseDepths ver019_noRecheck := by
  intro h
  have := h.2.2.2.2.2.1 0 [ver019_idleRow] (fun _ => 0) (fun _ => false) 512 (fun _ => 0)
    (fun _ => .unsat) (by decide)
  revert this
  decide

/-- A phase without the largest bound. -/
def ver019_noLargest : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match inj, rank with
  | false, .ranking r =>
    match checkRankingExact n rows a0 r with
    | some K =>
      if phaseDepths K.toNat L (ver019_ask bmc) = .proven then .proven K.toNat
      else refFiringBoundPhase inj n rows a0 isBad L rank bmc
    | none => .inconclusive .recheck
  | _, _ => refFiringBoundPhase inj n rows a0 isBad L rank bmc

/-- ✗ A phase without the largest bound violates VER-019 (line 7): with `2^53` tokens weighted 1
it runs the depth loop to a bound the ports cannot count exactly. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_noLargest :
    ¬ VER_019 checkRankingExact phaseDepths ver019_noLargest := by
  intro h
  have := h.2.2.2.2.2.2.1 1 [] (fun _ => 2 ^ 53) (fun _ => false) (2 ^ 53 + 1) (fun _ => 1)
    (2 ^ 53) (fun _ => .unsat) (by decide) (by decide)
  revert this
  decide

/-- A phase that never proves: it steps aside where the depth loop proves. -/
def ver019_neverProves : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match refFiringBoundPhase inj n rows a0 isBad L rank bmc with
  | .proven _ => .inconclusive .depthAside
  | o => o

/-- ✗ A phase that never proves violates VER-019 (line 8): on the empty net with the bound 0 and
`unsat` at depth 0 it steps aside. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_neverProves :
    ¬ VER_019 checkRankingExact phaseDepths ver019_neverProves := by
  intro h
  have := h.2.2.2.2.2.2.2.1 0 [] (fun _ => 0) (fun _ => false) 512 (fun _ => 0) 0
    (fun _ => .unsat) (by decide) (by decide) (by decide)
  revert this
  decide

/-- A phase that proves when the depth loop stops at the depth limit. -/
def ver019_limitProves : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match refFiringBoundPhase inj n rows a0 isBad L rank bmc with
  | .inconclusive .depthAside =>
    match rank with
    | .ranking r => .proven (dot r a0 n).toNat
    | _ => .inconclusive .depthAside
  | o => o

/-- `M0` with 9 tokens on `p0`. -/
def ver019_nine : AMarking := fun p => if p = 0 then 9 else 0

/-- ✗ A phase that proves at the depth limit violates VER-019 (line 9): with the bound 9 and the
limit 8, `unsat` at depth 8 says nothing about runs of 9 firings. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_limitProves :
    ¬ VER_019 checkRankingExact phaseDepths ver019_limitProves := by
  intro h
  have := h.2.2.2.2.2.2.2.2.1 1 [] ver019_nine (fun _ => false) 8 (fun _ => 1) 9
    (fun _ => .unsat) (by decide) (by decide) (by decide)
  revert this
  decide

/-- A phase that reports the run of a `sat` model without replaying it. -/
def ver019_noReplay : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match refFiringBoundPhase inj n rows a0 isBad L rank bmc with
  | .inconclusive .noReplay =>
    match rank with
    | .ranking r =>
      match phaseDepths (dot r a0 n).toNat L (ver019_ask bmc) with
      | .sat d =>
        match bmc d with
        | .sat s => .violated ((decodeModel rows.length s d).getD [])
        | _ => .inconclusive .noReplay
      | _ => .inconclusive .noReplay
    | _ => .inconclusive .noReplay
  | o => o

/-- ✗ A phase that does not replay violates VER-019 (line 10): on the empty net with a violation
no marking meets, a `sat` model at depth 0 is reported as the run of 0 steps. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_noReplay :
    ¬ VER_019 checkRankingExact phaseDepths ver019_noReplay := by
  intro h
  have := ((h.2.2.2.2.2.2.2.2.2 0 [] (fun _ => 0) (fun _ => false) 512 (fun _ => 0) 0
    (fun _ => .sat (ver019_model 0 [])) 0 (ver019_model 0 []) (by decide) (by decide)
    (by decide) rfl).2 [] (by decide)).2 (by decide)
  revert this
  decide

/-- A phase that reads a model defining no selector as the empty run: it decodes every
selector the model is silent on as idle, at every depth. -/
def ver019_silentAsEmpty : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match refFiringBoundPhase inj n rows a0 isBad L rank bmc with
  | .inconclusive .noReplay =>
    match rank with
    | .ranking r =>
      match phaseDepths (dot r a0 n).toNat L (ver019_ask bmc) with
      | .sat d =>
        match bmc d with
        | .sat s =>
          let run := decodeRust rows.length (fun i => (s i).getD (rows.length : Int)) d
          if replays rows [] isBad a0 run = true then .violated run else .inconclusive .noReplay
        | _ => .inconclusive .noReplay
      | _ => .inconclusive .noReplay
    | _ => .inconclusive .noReplay
  | o => o

/-- `M0` with one token on `p0`. -/
def ver019_one : AMarking := fun p => if p = 0 then 1 else 0

/-- ✗ A phase that reads a model defining no selector as the empty run violates VER-019 (line 10,
the `none` branch): on the net with one place, no transition and one token, the bound is 1, and a
`sat` model at depth 1 that defines no selector is reported as the run of 0 steps, since `M0`
violates; the statement wants `noReplay`. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_silentAsEmpty :
    ¬ VER_019 checkRankingExact phaseDepths ver019_silentAsEmpty := by
  intro h
  have := (h.2.2.2.2.2.2.2.2.2 1 [] ver019_one (fun _ => true) 512 (fun _ => 1) 1
    (fun _ => .sat fun _ => none) 1 (fun _ => none) (by decide) (by decide)
    (by decide) rfl).1 (by decide)
  revert this
  decide

/-- A phase that never reports a run: it steps aside where a run replays. -/
def ver019_neverViolated : FBPhaseFn := fun inj n rows a0 isBad L rank bmc =>
  match refFiringBoundPhase inj n rows a0 isBad L rank bmc with
  | .violated _ => .inconclusive .noReplay
  | o => o

/-- ✗ A phase that never reports a run violates VER-019 (line 10, the replaying branch): on the
same net, a `sat` model at depth 1 whose one selector is idle decodes to the run of 0 steps, which
replays to `M0`, a violating marking; the statement wants that run reported. -/
@[evidence forbids VER_019]
theorem VER_019_forbids_neverViolated :
    ¬ VER_019 checkRankingExact phaseDepths ver019_neverViolated := by
  intro h
  have := ((h.2.2.2.2.2.2.2.2.2 1 [] ver019_one (fun _ => true) 512 (fun _ => 1) 1
    (fun _ => .sat (ver019_model 0 [])) 1 (ver019_model 0 []) (by decide) (by decide)
    (by decide) rfl).2 [] (by decide)).1 (by decide)
  revert this
  decide

/-! ## Pure functions: the limits, the default, the budget and the report

Kind-N and report lines of the quoted sentences and the acceptance criteria, as functions,
pinned with `#guard`. They are not part of the statement. -/

/-- The depth limit `L` (fourth quoted sentence). -/
def ver019_depthLimit : Nat := 512

/-- The phase is on by default (twelfth quoted sentence). -/
def ver019_defaultOn : Bool := true

/-- The phase budget in milliseconds: half the timeout, rounded down to whole milliseconds and at
least 1 ms, as the prose of VER-019 says. -/
def ver019_budgetMs (timeoutMs : Nat) : Nat := max 1 (timeoutMs / 2)

/-- The method of a `Proven` from this phase. -/
def ver019_method : String := "bounded-model-check"

/-- The report header of the phase. -/
def ver019_header : String := "  Firing bound (VER-019):"

/-- AC1: the bound line, with the ranking as the report prints it. -/
def ver019_boundLine (K : Int) (ranking : String) : String :=
  s!"    Bound: {K} firings ({ranking} drops on every firing)"

/-- AC3: the certificate line. -/
def ver019_certLine : String :=
  "  Certificate check: not applicable (bounded model check to the firing bound)"

/-- AC4: the line for a net without a ranking, with the transitions of a repeatable vector. -/
def ver019_noBoundLine (names : List String) : String :=
  s!"    Status: no firing bound — the marking equation lets {", ".intercalate names} repeat; not attempted"

/-- AC4: the line when the second query finds no repeatable vector. -/
def ver019_noBoundFallback : String :=
  "    Status: no firing bound (no weights decrease on every firing); not attempted"

-- The third and fourth quoted sentences: the schedule and the limit.
#guard ver019_depthLimit == 512
#guard ver019_schedule 5 ver019_depthLimit == [5]
#guard ver019_schedule 25 ver019_depthLimit == [8, 16, 25]
#guard ver019_schedule 600 ver019_depthLimit == [8, 16, 32, 64, 128, 256, 512]
#guard ver019_schedule 0 ver019_depthLimit == [0]
#guard ver019_schedule 9 0 == [0]
-- The second quoted sentence: the largest bound.
#guard ver019_largestBound == 9007199254740991
-- The twelfth quoted sentence and the budget.
#guard ver019_defaultOn == true
#guard ver019_budgetMs 60000 == 30000
#guard ver019_budgetMs 1 == 1
-- AC1, AC3, AC4: the report lines of the test derivation.
#guard ver019_method == "bounded-model-check"
#guard ver019_header == "  Firing bound (VER-019):"
#guard ver019_boundLine 5 "budget + s + 2*src" ==
  "    Bound: 5 firings (budget + s + 2*src drops on every firing)"
#guard ver019_certLine ==
  "  Certificate check: not applicable (bounded model check to the firing bound)"
#guard ver019_noBoundLine ["t0", "t1", "t2"] ==
  "    Status: no firing bound — the marking equation lets t0, t1, t2 repeat; not attempted"
#guard ver019_noBoundFallback ==
  "    Status: no firing bound (no weights decrease on every firing); not attempted"

/-! ## VER-019, the second block: where the phase sits in the pipeline

The block above is the phase when it runs. This block is the pipeline around it
(`Spec/Verifier/Pipeline.lean`): where the phase sits in the list of steps (once, after the
state-equation phase, before the witness phase of [VER-025] and the fixpoint query), when its step
is entered, and how its outcome is handed over. It reads three things:

* the names of the pipeline's steps (`GStep`), in order;
* two gates over `FBCtx` (the net has a ν match transition, the policy is `Ignore` with environment
  places declared, the option of [VER-018], the option of this phase): `seG`, where the
  state-equation phase is entered, and `fbG`, where this phase is entered;
* the hand-over `W` (`FBWrap`), from the phase's outcome to what the step returns to the
  pipeline: a decision, which ends the run, or an aside, after which the pipeline enters its next
  step.

The witness is the runtimes' step names `rtStepNames` (the names of `rtPipeline`), the gates of the three runtimes (both phases
on the flat path only, not on a ν-net and not under `Ignore` with environment places, each behind
its own option: `smt_verifier.rs` `flat_phases && self.firing_bound`, `SmtVerifier.java`
`flatPhases && firingBound`, `smt-verifier.ts` `!hasMatch && !this.ignoresEnvironment` then
`this._firingBound`), and the hand-over of `firing_bound_decision`. -/

/-- What the gates of the two pre-fixpoint phases read. -/
structure FBCtx where
  /-- The verified net has a ν match transition ([NU-001]). -/
  nuNet : Bool
  /-- The environment policy is `Ignore` and environment places are declared ([VER-006]). -/
  ignoreEnv : Bool
  /-- The option of the state-equation phase ([VER-018]). -/
  seOn : Bool
  /-- The option of the firing-bound phase. -/
  fbOn : Bool
  deriving DecidableEq, Repr

/-- A gate: whether a phase's step is entered when the pipeline reaches it. -/
abbrev FBGate : Type := FBCtx → Bool

/-- A hand-over: from the names of the flat transitions and the phase's outcome to what the step
returns to the pipeline. -/
abbrev FBWrap : Type := (Nat → String) → FBOutcome → Verifier.PhaseOut

/-- The step name of the state-equation phase in all three runtimes. -/
def ver019_seStep : String := "state-equation phase"

/-- The step name of the firing-bound phase in all three runtimes. -/
def ver019_fbStep : String := "firing-bound phase"

/-- The step name of the fixpoint query in all three runtimes. -/
def ver019_fixStep : String := "IC3/PDR query"

/-- The step name of the bounded witness phase ([VER-025]) in all three runtimes. -/
def ver019_witStep : String := "witness phase"

/-- The runtimes' gate of the state-equation phase: the flat path (no ν match transition, not
`Ignore` with environment places) and its option. -/
def refSeGate : FBGate := fun c => !c.nuNet && !c.ignoreEnv && c.seOn

/-- The runtimes' gate of the firing-bound phase: the same flat path and its own option. -/
def refFbGate : FBGate := fun c => !c.nuNet && !c.ignoreEnv && c.fbOn

/-- The runtimes' hand-over (`firing_bound_decision`, `smt_verifier.rs`): a proof is `Proven` with
the method `bounded-model-check`, no trace and no `counterexampleConfirmed`; a replayed run is `Violated` with the run's
transitions and `counterexampleConfirmed` `true`; no firing bound and an inconclusive end are an
aside, with a short note (the report's reason text is not modelled). -/
def refFbWrap : FBWrap := fun nm o =>
  match o with
  | .proven _ => .decided (.proven ver019_method) [] none
  | .violated run => .decided .violated (run.map nm) (some true)
  | .unbounded => .aside "no firing bound"
  | .inconclusive _ => .aside "firing bound inconclusive"

#spec_witness Verifier.rtStepNames
#spec_witness refSeGate
#spec_witness refFbGate
#spec_witness refFbWrap

requirement VER_019_order
  id "VER-019"
  title "Firing-Bound Phase: its place in the pipeline"
  kind B
  scope "the SMT verifier's pipeline, all implementations"
  source verbatim "spec/07-verification.md"
  quote "The pipeline *shall* place the firing-bound phase at one point, after the state-equation phase of [VER-018] and before the bounded witness phase of [VER-025] and the fixpoint query."
        "*While* the phase is enabled, the pipeline *shall* run it on exactly the queries that the state-equation phase of [VER-018] runs on when that phase is enabled, whether [VER-018] is enabled or not, unless an earlier step has decided the query or the run has stopped."
        "*If* the phase is disabled, *then* the verifier *shall not* run it, and the verdicts and reports *shall* be those of the pipeline without the phase."
        "*When* the phase ends inconclusive or reports that the net has no firing bound, the pipeline *shall* go on to its next step."
        "*When* the phase returns `Proven` or `Violated`, the verifier *shall* return that result: `Proven` with the method `bounded-model-check` and neither a counterexample nor `counterexampleConfirmed`; `Violated` with the transitions of the replayed run, in firing order, as the counterexample and `counterexampleConfirmed` `true`."
  reading "In the pipeline's step names, the state-equation phase comes before the firing-bound phase: the list splits so that every state-equation step is in the first part and every firing-bound step in the second, and each part holds one of them."
          "In the same sense, the firing-bound phase comes before the fixpoint query (the IC3/PDR query)."
          "Where the step names include the bounded witness phase, the firing-bound phase comes before it in the same sense."
          "The firing-bound phase occurs exactly once in the step names."
          "With the phase's option off, the gate fbG is false."
          "With the phase's option on, fbG is the gate seG of the state-equation phase read with that phase's option on, whatever that option is."
          "The hand-over W returns an aside exactly for the outcomes unbounded (no firing bound) and inconclusive."
          "W hands a proof with any bound over as a decision Proven with the method bounded-model-check, an empty trace and no counterexampleConfirmed."
          "W hands a replayed run over as a decision Violated whose trace is the run's transitions, by name, in firing order, with counterexampleConfirmed true."
  assumes "The model is the triple (names, gates, W). names is the list of the pipeline's step names, in order (the names of the GStep list of Spec/Verifier/Pipeline.lean); runPipeline gives the order its meaning in a run (VER_019_order_runs). The gates read FBCtx: a ν match transition in the verified net, the Ignore policy with environment places declared, and the two options. W reads the flat transitions' names and the outcome FBOutcome of the first block. The witness is rtStepNames (the runtimes' thirteen step names, the names of rtPipeline), refSeGate, refFbGate and refFbWrap."
          "That the pipeline's firing-bound step is entered under fbG and runs W over the first block's phase is the wiring this block assumes and does not state: in rtPipeline the step is still idle, and the integrator ties it when the phase's slice replaces the idle step (open item). VER_019_order_disabled and VER_019_order_continues take the wiring as a premise, and VER_019_order_runs holds of a step list whose names are the given list."
          "The first quoted sentence is lines 1 to 4. 'Place' is the order of the step names (Before); in every run the steps are entered in that order, and the firing-bound phase at most once (VER_019_order_runs, from runPipeline_ordered and runPipeline_entered), so no run enters the state-equation phase after this phase, this phase after the witness phase or the fixpoint query, or this phase twice. 'At one point' is line 4. 'Before the bounded witness phase' is line 3: it binds a pipeline that has the witness phase, since VER-025 is a SHOULD of its own; that the witness phase sits directly before the fixpoint query is VER-025's line. The colour-slot bound between this phase and the witness phase, and the linear bound, the structural pre-check and the P-invariants before the phase, are other requirements' order lines."
          "The second quoted sentence is line 6. 'Exactly the queries that the state-equation phase runs on' is the gate seG read with VER-018's option on: the three runtimes test the same flat-path condition for both phases (no ν match transition, not Ignore with environment places declared) and then each phase's own option, so disabling VER-018 does not change where this phase runs (VER_019_order_se_free, from the statement alone). 'Unless an earlier step has decided the query or the run has stopped' is the pipeline: a decision ends the run, and so does the stop poll before each step on a timeout or a cancellation, with no decision; in both cases no later step is entered (runPipeline). That the phase steps aside under declared injection is the first block's line 3."
          "What seG itself contains is line 4 of VER_018_order, which fixes it to the flat path. This block alone does not pin where the phase runs: a pair of gates wrong in the same way (both false everywhere, or both entered on ν-nets only) passes it. With VER_018_order on the same names and seG, as the consistency theorem has them, line 6 pins fbG to the runtimes' gate (VER_018_order_fb_gate, from VER_019_order_flat_gate). The runtimes' gate of VER-018 does not read this phase's option."
          "The third quoted sentence is line 5: a step whose gate is false is skipped without a poll, so the run, its decision and its trail are those of the step list without the step (VER_019_order_disabled, from the statement alone, through ver019_runPipeline_skip). The reports are not modelled; that they agree is checked by the runtimes' tests with the phase off. It is AC5."
          "The fourth quoted sentence is line 7: an aside goes on to the next step (VER_019_order_continues). It is the 'the pipeline shall continue' of the first block's quoted sentences, and the 'continue to the fixpoint query' of its sentence on a net without a ranking, through lines 2 and 3."
          "The fifth quoted sentence is lines 8 and 9. 'Neither a counterexample nor counterexampleConfirmed' is the empty trace and the absent flag of line 8, as the result record of VER-003 has them where no replay applies. That the proof skips the certificate check, which the prose says, is the hand-over itself: the step returns a decision, which ends the run before the certificate check step. The route a decision reports (the SMT pipeline) is the step's route in the list, not a line here. The bound K is not part of the verdict: it reaches the report, which is not modelled."
          "The order of the runtimes' list is pinned by rtStepNames_order, and the step names are the same in Rust (step!), Java (enter) and TypeScript (enter)."
  signoff "pending"
  statement : List String → FBGate → FBGate → FBWrap → Prop :=
    fun names seG fbG W =>
      Verifier.Before names ver019_seStep ver019_fbStep ∧
      Verifier.Before names ver019_fbStep ver019_fixStep ∧
      (ver019_witStep ∈ names → Verifier.Before names ver019_fbStep ver019_witStep) ∧
      names.count ver019_fbStep = 1 ∧
      (∀ c : FBCtx, c.fbOn = false → fbG c = false) ∧
      (∀ c : FBCtx, c.fbOn = true → fbG c = seG { c with seOn := true }) ∧
      (∀ nm o, (∃ n, W nm o = .aside n) ↔ (o = .unbounded ∨ ∃ why, o = .inconclusive why)) ∧
      (∀ nm K, W nm (.proven K) = .decided (.proven ver019_method) [] none) ∧
      (∀ nm run, W nm (.violated run) = .decided .violated (run.map nm) (some true))

/- The pinned readable form of VER-019's pipeline block. -/
/--
info: def Libpetri.Spec.VER_019_order : List String → FBGate → FBGate → FBWrap → Prop :=
fun names seG fbG W =>
  Verifier.Before names ver019_seStep ver019_fbStep ∧
    Verifier.Before names ver019_fbStep ver019_fixStep ∧
      (ver019_witStep ∈ names → Verifier.Before names ver019_fbStep ver019_witStep) ∧
        List.count ver019_fbStep names = 1 ∧
          (∀ (c : FBCtx), c.fbOn = false → fbG c = false) ∧
            (∀ (c : FBCtx),
                c.fbOn = true →
                  fbG c = seG { nuNet := c.nuNet, ignoreEnv := c.ignoreEnv, seOn := true, fbOn := c.fbOn }) ∧
              (∀ (nm : ℕ → String) (o : FBOutcome),
                  (∃ n, W nm o = Verifier.PhaseOut.aside n) ↔
                    o = FBOutcome.unbounded ∨ ∃ why, o = FBOutcome.inconclusive why) ∧
                (∀ (nm : ℕ → String) (K : ℕ),
                    W nm (FBOutcome.proven K) =
                      Verifier.PhaseOut.decided (Verifier.Verdict.proven ver019_method) [] none) ∧
                  ∀ (nm : ℕ → String) (run : List ℕ),
                    W nm (FBOutcome.violated run) =
                      Verifier.PhaseOut.decided Verifier.Verdict.violated (List.map nm run) (some true)
-/
#guard_msgs in #print VER_019_order

/-! ### The reference -/

/-- The reference hand-over steps aside exactly on no firing bound and on an inconclusive end. -/
theorem ver019_refFbWrap_aside (nm : Nat → String) (o : FBOutcome) :
    (∃ n, refFbWrap nm o = .aside n) ↔ (o = .unbounded ∨ ∃ why, o = .inconclusive why) := by
  cases o <;> simp [refFbWrap]

/-- ✓ **The runtimes satisfy the pipeline block.** In their step list the state-equation phase
comes eighth, the firing-bound phase ninth and only there, the witness phase eleventh and the
IC3/PDR query twelfth; both phases are entered on the flat path only, each behind its own option;
and the phase's outcome is handed over as `firing_bound_decision` hands it over. -/
@[evidence holds VER_019_order]
theorem VER_019_order_reference :
    VER_019_order Verifier.rtStepNames refSeGate refFbGate refFbWrap := by
  refine ⟨by decide, by decide, fun _ => by decide, by decide, fun c h => by simp [refFbGate, h],
    fun c h => by simp [refFbGate, refSeGate, h], ver019_refFbWrap_aside, fun _ _ => rfl,
    fun _ _ => rfl⟩

/-- ✓ The pipeline block is consistent: the runtimes' step list, gates and hand-over satisfy it. -/
@[evidence consistent VER_019_order]
theorem VER_019_order_consistent :
    ∃ (names : List String) (seG fbG : FBGate) (W : FBWrap), VER_019_order names seG fbG W :=
  ⟨_, _, _, _, VER_019_order_reference⟩

/-! ### What the statement says on its own -/

/-- **In every run the phase is entered in its place, and at most once**, from the statement
alone: starting from an empty log, no run of the pipeline enters the state-equation phase after
the firing-bound phase, the firing-bound phase after the witness phase or the IC3/PDR query, or
the firing-bound phase twice. Example: a run that enters the state-equation phase, the
firing-bound phase, the witness phase and the IC3/PDR query logs them in that order, each once. -/
@[evidence cites "VER-019" "after the state-equation phase of [VER-018] and before the bounded witness phase of [VER-025] and the fixpoint query"]
theorem VER_019_order_runs {Q : Type} {steps : List (Verifier.GStep Q)} {seG fbG : FBGate}
    {W : FBWrap} (h : VER_019_order (steps.map Verifier.GStep.name) seG fbG W) {O : Verifier.Oracle} {stop : Verifier.Stop}
    {o : Verifier.Options} {q : Q} {t : Verifier.Trail} (ht : t.entered = []) :
    Verifier.Ordered (Verifier.runPipeline O stop o q steps t).2.entered ver019_seStep
        ver019_fbStep ∧
      Verifier.Ordered (Verifier.runPipeline O stop o q steps t).2.entered ver019_fbStep
        ver019_fixStep ∧
      (ver019_witStep ∈ steps.map Verifier.GStep.name →
        Verifier.Ordered (Verifier.runPipeline O stop o q steps t).2.entered ver019_fbStep
          ver019_witStep) ∧
      (Verifier.runPipeline O stop o q steps t).2.entered.count ver019_fbStep ≤ 1 := by
  refine ⟨Verifier.runPipeline_ordered ht h.1, Verifier.runPipeline_ordered ht h.2.1,
    fun hw => Verifier.runPipeline_ordered ht (h.2.2.1 hw), ?_⟩
  obtain ⟨l, hl, hs⟩ := Verifier.runPipeline_entered (O := O) (stop := stop) (o := o) (q := q)
    steps t
  rw [hl, ht, List.nil_append, ← h.2.2.2.1]
  exact hs.count_le _

/-- **Disabling the state-equation phase does not move this phase**, from the statement alone:
whatever the option of [VER-018], the gate of this phase gives the same answer. Example: with the
option of [VER-018] off and this phase's option on, on a flat net, the phase is still entered. -/
@[evidence cites "VER-019" "whether [VER-018] is enabled or not"]
theorem VER_019_order_se_free {names : List String} {seG fbG : FBGate}
    {W : FBWrap} (h : VER_019_order names seG fbG W) (c : FBCtx) (a b : Bool) :
    fbG { c with seOn := a } = fbG { c with seOn := b } := by
  obtain ⟨-, -, -, -, hoff, hon, -⟩ := h
  cases c.fbOn
  · exact (hoff _ rfl).trans (hoff _ rfl).symm
  · rw [hon ⟨c.nuNet, c.ignoreEnv, a, true⟩ rfl, hon ⟨c.nuNet, c.ignoreEnv, b, true⟩ rfl]

/-- **Once the state-equation phase's gate is the flat path, so is this phase's**, from the
statement alone: when [VER-018] is entered exactly on a net without a ν match transition, not
under `Ignore` with environment places, with its option on, this phase is entered exactly there
with its own option on, which is the runtimes' gate. Example: with [VER-018] off and this phase
on, a flat net enters it and a ν-net does not. -/
@[evidence cites "VER-019" "on exactly the queries that the state-equation phase of [VER-018] runs on"]
theorem VER_019_order_flat_gate {names : List String} {seG fbG : FBGate}
    {W : FBWrap} (h : VER_019_order names seG fbG W)
    (hse : ∀ c : FBCtx, seG c = (!c.nuNet && !c.ignoreEnv && c.seOn)) : fbG = refFbGate := by
  obtain ⟨-, -, -, -, hoff, hon, -⟩ := h
  funext c
  cases hc : c.fbOn
  · rw [hoff c hc]; simp [refFbGate, hc]
  · rw [hon c hc, hse]; simp [refFbGate, hc]

/-- A step whose gate is false leaves the run as if it were not in the list: the same decision
and the same trail, polls and log included. -/
theorem ver019_runPipeline_skip {Q : Type} {O : Verifier.Oracle} {stop : Verifier.Stop}
    {o : Verifier.Options} {q : Q} {s : Verifier.GStep Q} (hs : s.applies o q = false)
    (post : List (Verifier.GStep Q)) :
    ∀ (pre : List (Verifier.GStep Q)) (t : Verifier.Trail),
      Verifier.runPipeline O stop o q (pre ++ s :: post) t =
        Verifier.runPipeline O stop o q (pre ++ post) t := by
  intro pre
  induction pre with
  | nil => intro t; simp [Verifier.runPipeline, hs]
  | cons p pre ih => intro t; simp only [List.cons_append, Verifier.runPipeline, ih]

/-- **A disabled phase changes nothing**, from the statement alone: when the firing-bound step is
entered under the gate `fbG` and the phase's option is off, a run of the pipeline is the run of
the list without that step, with the same decision and the same trail. Example: on the
queue-and-bundle net with the phase off, the verdict and the steps entered are those of the
pipeline that never had the phase. -/
@[evidence cites "VER-019" "the verdicts and reports *shall* be those of the pipeline without the phase"]
theorem VER_019_order_disabled {Q : Type} {names : List String} {seG fbG : FBGate}
    {W : FBWrap} (h : VER_019_order names seG fbG W) {O : Verifier.Oracle} {stop : Verifier.Stop}
    {o : Verifier.Options} {q : Q} {s : Verifier.GStep Q} {c : FBCtx}
    (hw : s.applies o q = fbG c) (hoff : c.fbOn = false)
    (pre post : List (Verifier.GStep Q)) (t : Verifier.Trail) :
    Verifier.runPipeline O stop o q (pre ++ s :: post) t =
      Verifier.runPipeline O stop o q (pre ++ post) t :=
  ver019_runPipeline_skip (by rw [hw, h.2.2.2.2.1 c hoff]) post pre t

/-- **No firing bound, or an inconclusive end, goes on to the next step**, from the statement
alone: when the firing-bound step is entered and runs the hand-over `W` of such an outcome, the
run continues with the rest of the list from the trail the step left. Example: on the ring
`t0, t1, t2`, which has no ranking, the pipeline goes on and the IC3/PDR query decides. -/
@[evidence cites "VER-019" "the pipeline *shall* go on to its next step"]
theorem VER_019_order_continues {Q : Type} {names : List String} {seG fbG : FBGate}
    {W : FBWrap} (h : VER_019_order names seG fbG W) {O : Verifier.Oracle} {stop : Verifier.Stop}
    {o : Verifier.Options} {q : Q} {s : Verifier.GStep Q} {nm : Nat → String} {out : FBOutcome}
    {t : Verifier.Trail} (happ : s.applies o q = true)
    (hpoll : (Verifier.pollStop stop t).1 = false) (hrun : s.run o q = .done (W nm out))
    (hout : out = .unbounded ∨ ∃ why, out = .inconclusive why) (ss : List (Verifier.GStep Q)) :
    Verifier.runPipeline O stop o q (s :: ss) t =
      Verifier.runPipeline O stop o q ss ((Verifier.pollStop stop t).2.enter s) := by
  obtain ⟨n, hn⟩ := ((h.2.2.2.2.2.2.1 nm out).mpr hout)
  simp only [Verifier.runPipeline, happ, hpoll, if_true, Bool.false_eq_true, if_false, hrun,
    Verifier.execProg_done, hn]

/-! ### Examples -/

/-- The names of the flat transitions of the queue-and-bundle net with `cancel`. -/
def ver019_names (i : Nat) : String :=
  ["produce", "signal", "bundle", "bundleEmpty", "cancel"].getD i "?"

/-- A demo pipeline over the trivial query: the state-equation phase steps aside, the
firing-bound phase hands over the outcome `out`, then the fixpoint query asks the solver. -/
def ver019_demoSteps (out : FBOutcome) : List (Verifier.GStep Unit) :=
  [{ name := ver019_seStep, route := .smt, run := fun _ _ => .done (.aside "no refinement") },
   { name := ver019_fbStep, route := .smt, run := fun _ _ => .done (refFbWrap ver019_names out) },
   { name := ver019_fixStep, route := .smt, run := fun _ _ => Verifier.demoQuery "horn" }]

/-- A run of the demo pipeline with no stop and a solver that answers `sat`. -/
def ver019_demoRun (out : FBOutcome) : Option (Verifier.Route × Verifier.PhaseOut) × Verifier.Trail :=
  Verifier.runPipeline Verifier.satOracle Verifier.noStop {} () (ver019_demoSteps out) {}

/-- ✓ **The pipeline block on worked examples.** In the runtimes' list the firing-bound phase
sits once, after the state-equation phase and before the witness phase and the IC3/PDR query.
With the option of [VER-018] off and this phase on, on a flat net, this phase is entered and
[VER-018] is not; on a ν-net neither is. In a demo pipeline, a phase that finds no firing bound
lets the IC3/PDR query run and decide, after three steps; a phase that proves with the bound 5
ends the run after two steps with `Proven` by `bounded-model-check`, no counterexample and no
solver script started by the query; a phase that replays `produce, produce, produce, cancel` ends
it with that run as a confirmed `Violated`. -/
@[evidence nonvacuous VER_019_order]
theorem VER_019_order_nonvacuous :
    Verifier.Before Verifier.rtStepNames ver019_seStep ver019_fbStep ∧
    Verifier.Before Verifier.rtStepNames ver019_fbStep ver019_fixStep ∧
    Verifier.Before Verifier.rtStepNames ver019_fbStep ver019_witStep ∧
    Verifier.rtStepNames.count ver019_fbStep = 1 ∧
    refFbGate ⟨false, false, false, true⟩ = true ∧ refSeGate ⟨false, false, false, true⟩ = false ∧
    refFbGate ⟨true, false, true, true⟩ = false ∧
    (ver019_demoRun .unbounded).2.entered = [ver019_seStep, ver019_fbStep, ver019_fixStep] ∧
    (ver019_demoRun .unbounded).1 = some (.smt, .decided (.proven "IC3/PDR") [] none) ∧
    (ver019_demoRun (.proven 5)).2.entered = [ver019_seStep, ver019_fbStep] ∧
    (ver019_demoRun (.proven 5)).2.started = [] ∧
    (ver019_demoRun (.proven 5)).1 = some (.smt, .decided (.proven "bounded-model-check") [] none) ∧
    (ver019_demoRun (.violated [0, 0, 0, 4])).1 =
      some (.smt, .decided .violated ["produce", "produce", "produce", "cancel"] (some true)) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
    by decide, by decide, rfl, rfl⟩

/-! ### Violations -/

/-- The runtimes' step list with the two pre-fixpoint phases swapped. -/
def ver019_swapped : List String :=
  ["linear bound", ver019_fbStep, ver019_seStep, ver019_witStep, ver019_fixStep]

/-- ✗ A pipeline that runs the firing bound before the state-equation phase violates VER-019's
pipeline block (line 1): in its list the state-equation phase comes third, after the firing
bound. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_swapped :
    ¬ VER_019_order ver019_swapped refSeGate refFbGate refFbWrap := by
  intro h
  exact absurd h.1 (by decide)

/-- A step list with the firing bound after the fixpoint query. -/
def ver019_late : List String :=
  [ver019_seStep, ver019_fixStep, ver019_fbStep, ver019_witStep]

/-- ✗ A pipeline that runs the firing bound after the fixpoint query violates VER-019's pipeline
block (line 2): the IC3/PDR query comes second, the firing bound third. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_late :
    ¬ VER_019_order ver019_late refSeGate refFbGate refFbWrap := by
  intro h
  exact absurd h.2.1 (by decide)

/-- The runtimes' list with the witness phase moved up before the firing-bound phase. -/
def ver019_witnessFirst : List String :=
  ["Route B (ν name-partition graph)", "linear bound", "state-space enumeration", "flattening",
   "structural pre-check", "P-invariant computation", "linear bound", ver019_seStep,
   ver019_witStep, ver019_fbStep, "colour-slot bound", ver019_fixStep, "certificate check"]

/-- ✗ A pipeline that runs the witness phase of [VER-025] before the firing bound violates
VER-019's pipeline block (line 3). On the queue-and-bundle net with `cancel`, the witness phase
would then report its trimmed run where the runtimes report the firing bound's untrimmed
`produce, produce, produce, cancel`. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_witnessFirst :
    ¬ VER_019_order ver019_witnessFirst refSeGate refFbGate refFbWrap := by
  intro h
  exact absurd (h.2.2.1 (by decide)) (by decide)

/-- A step list that runs the firing bound twice, before and after the colour-slot bound. -/
def ver019_twice : List String :=
  [ver019_seStep, ver019_fbStep, "colour-slot bound", ver019_fbStep, ver019_witStep,
   ver019_fixStep]

/-- ✗ A pipeline that runs the firing bound a second time violates VER-019's pipeline block
(line 4): the order is kept, but the phase sits at two points of the list, and a run that steps
aside the first time spends a second phase budget on the same question. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_twice :
    ¬ VER_019_order ver019_twice refSeGate refFbGate refFbWrap := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

/-- A gate that ignores the phase's own option. -/
def ver019_gateNoOption : FBGate := fun c => !c.nuNet && !c.ignoreEnv

/-- ✗ A phase that runs although it is disabled violates VER-019's pipeline block (line 5): on a
flat net with the option off it is still entered. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_gateNoOption :
    ¬ VER_019_order Verifier.rtStepNames refSeGate ver019_gateNoOption refFbWrap := by
  intro h
  exact absurd (h.2.2.2.2.1 ⟨false, false, false, false⟩ rfl) (by decide)

/-- A gate that runs the phase only where the state-equation phase runs with its own option. -/
def ver019_gateFollowsSe : FBGate := fun c => refSeGate c && c.fbOn

/-- ✗ A phase that runs only when [VER-018] is enabled violates VER-019's pipeline block (line 6):
with [VER-018] off and this phase on, on a flat net, it is not entered, though the test
derivation runs it with [VER-018] off. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_gateFollowsSe :
    ¬ VER_019_order Verifier.rtStepNames refSeGate ver019_gateFollowsSe refFbWrap := by
  intro h
  exact absurd (h.2.2.2.2.2.1 ⟨false, false, false, true⟩ rfl) (by decide)

/-- A gate that also runs the phase under `Ignore` with environment places. -/
def ver019_gateUnderIgnore : FBGate := fun c => !c.nuNet && c.fbOn

/-- ✗ A phase that runs under `Ignore` with environment places, where [VER-018] does not, violates
VER-019's pipeline block (line 6). -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_gateUnderIgnore :
    ¬ VER_019_order Verifier.rtStepNames refSeGate ver019_gateUnderIgnore refFbWrap := by
  intro h
  exact absurd (h.2.2.2.2.2.1 ⟨false, true, true, true⟩ rfl) (by decide)

/-- A hand-over that ends the run with `Unknown` when the phase is inconclusive. -/
def ver019_wrapStops : FBWrap := fun nm o =>
  match o with
  | .inconclusive _ => .decided (.unknown "firing bound inconclusive") [] none
  | o => refFbWrap nm o

/-- ✗ A phase whose inconclusive end stops the pipeline violates VER-019's pipeline block (line 7):
the fixpoint query, which could still prove the property, is never asked. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_wrapStops :
    ¬ VER_019_order Verifier.rtStepNames refSeGate refFbGate ver019_wrapStops := by
  intro h
  obtain ⟨n, hn⟩ := (h.2.2.2.2.2.2.1 ver019_names (.inconclusive .depthAside)).mpr
    (Or.inr ⟨_, rfl⟩)
  simp [ver019_wrapStops] at hn

/-- A hand-over that reports a proof under the fixpoint query's method. -/
def ver019_wrapMethod : FBWrap := fun nm o =>
  match o with
  | .proven _ => .decided (.proven "IC3/PDR") [] none
  | o => refFbWrap nm o

/-- ✗ A proof reported with another method violates VER-019's pipeline block (line 8): the
verdict-parity fixtures read `bounded-model-check`. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_wrapMethod :
    ¬ VER_019_order Verifier.rtStepNames refSeGate refFbGate ver019_wrapMethod := by
  intro h
  have := h.2.2.2.2.2.2.2.1 ver019_names 5
  simp [ver019_wrapMethod, ver019_method] at this

/-- A hand-over that builds both decisions with one helper and so puts the first transition and
the confirmed flag on a proof as well. -/
def ver019_wrapProvenTrace : FBWrap := fun nm o =>
  match o with
  | .proven _ => .decided (.proven ver019_method) [nm 0] (some true)
  | o => refFbWrap nm o

/-- ✗ A proof reported with a counterexample violates VER-019's pipeline block (line 8): on the
queue-and-bundle net it would read `Proven` by `bounded-model-check` with the trace `produce`
and `counterexampleConfirmed` `true`, where the runtimes report no trace and no flag. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_wrapProvenTrace :
    ¬ VER_019_order Verifier.rtStepNames refSeGate refFbGate ver019_wrapProvenTrace := by
  intro h
  have := h.2.2.2.2.2.2.2.1 ver019_names 5
  simp [ver019_wrapProvenTrace] at this

/-- A hand-over that reports a replayed run as unconfirmed. -/
def ver019_wrapUnconfirmed : FBWrap := fun nm o =>
  match o with
  | .violated run => .decided .violated (run.map nm) none
  | o => refFbWrap nm o

/-- ✗ A replayed run reported without `counterexampleConfirmed` `true` violates VER-019's pipeline
block (line 9). -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_wrapUnconfirmed :
    ¬ VER_019_order Verifier.rtStepNames refSeGate refFbGate ver019_wrapUnconfirmed := by
  intro h
  have := h.2.2.2.2.2.2.2.2 ver019_names [0]
  simp [ver019_wrapUnconfirmed] at this

/-- A hand-over that trims the run to its last step. -/
def ver019_wrapTrimmed : FBWrap := fun nm o =>
  match o with
  | .violated run => .decided .violated ((run.drop (run.length - 1)).map nm) (some true)
  | o => refFbWrap nm o

/-- ✗ A trimmed run violates VER-019's pipeline block (line 9): the run
`produce, produce, produce, cancel` is reported as `cancel` alone. -/
@[evidence forbids VER_019_order]
theorem VER_019_order_forbids_wrapTrimmed :
    ¬ VER_019_order Verifier.rtStepNames refSeGate refFbGate ver019_wrapTrimmed := by
  intro h
  have := h.2.2.2.2.2.2.2.2 ver019_names [0, 0, 0, 4]
  revert this
  simp [ver019_wrapTrimmed, ver019_names]

end Libpetri.Spec
