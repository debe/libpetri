import Libpetri.Spec.Registry
import Libpetri.Novel.RouteA.SlotBound
import Libpetri.Novel.RouteA.Shipped

set_option linter.missingDocs true

/-!
# NU-053: EXTENDED-coloured quiescence in the Route A SMT encoder (`spec/12-nu-nets.md`)

Route A encodes a bounded ν-net with `k` colours per coloured place. This block states what the
coloured encoding computes, as a predicate over four models:

* `B : ColourSlotBound`, the colour-slot bound: from the place count, the coloured places, the
  flat rows and the initial marking, a bound `k` or no plan. The witness `refColourSlotBound` is
  the least `k` some covering weighting certifies (`Novel.RouteA.ScaledCover`), refused above the
  cap `slotCap`. It is a specification-level definition by classical choice: the simplex that
  computes it (pivots, Bland's rule, the work and coefficient limits) is checked by the shared
  fixture, not modelled. On a net small enough that the solve reaches no limit (`Nu053Fits`) a
  bound must be set whenever a covering weighting is within the cap.
* `K : SlotReCheck`, the exact re-check of a scaled weighting `Y / D`. The witness is
  `refSlotReCheck`, the shipped `check_cover` (`Novel.RouteA.checkCover`).
* `U : ConsumerRule`, the colour rule the encoding emits for a coloured consumer, guard and
  update. The witness is `refConsumerRule`, the join rule on the consumer's one input
  (`Novel.RouteA.sJoin`) under the consumer's guard, which is what the shipped encoder emits
  (`Novel.RouteA.Cls.shipped`).
* `V : ColouredViolation`, the violation term of a quiescence property in the coloured encoding,
  the property's own clause a parameter. The witness is `refColouredViolation`, the shipped
  reap-aware predicate `Novel.RouteA.DeadERs` conjoined with the clause over the all-colour
  counts.

The verdict lines (a `Proven` of the coloured plan holds of every marking the ν executor reaches;
the dispatch after Route B and after the [VER-015] bound) are not stated here: they need the
reference ν executor and the verifier pipeline.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteA Libpetri.Novel.ForwardDeposit Libpetri.Novel.LinearBound

/-! ## The models -/

/-- A colour-slot bound: from the place count `n`, the coloured places `C`, the flat rows and the
initial marking, the bound `k`, or `none` when no plan is built. -/
abbrev ColourSlotBound : Type :=
  Nat → List PlaceId → List (Transition × Deposit) → AMarking → Option Nat

/-- An exact re-check: from the place count, the coloured places, the flat rows, the initial
marking and a weighting scaled to integers (a denominator `D` and a vector `Y`, standing for
`y = Y / D`), the bound it gives, or `none` when it refuses the weighting. -/
abbrev SlotReCheck : Type :=
  Nat → List PlaceId → List (Transition × Deposit) → AMarking → Nat → Weight → Option Nat

/-- The colour rule of a coloured consumer: from its input place, its coloured output places, the
slot count `k` and the colour columns before and after (place, colour), whether one rule of the
consumer (there is one per colour below `k`) takes the first columns to the second. -/
abbrev ConsumerRule : Type :=
  PlaceId → List PlaceId → Nat → (PlaceId → Nat → Nat) → (PlaceId → Nat → Nat) → Prop

/-- The violation term of a quiescence property in the coloured encoding: from the encoding, the
names of the reapable transitions, the property's own clause over token counts and an encoding
state, whether the state violates the property. -/
abbrev ColouredViolation : Type :=
  Enc → List String → (AMarking → Prop) → EState → Prop

/-- The largest entry the initial tableau of the slot-bound program can have on a flat net with
`n` places: `1`, every initial count below `n`, and `n` times every `pre + post` of a row at a
place below `n` (an objective entry sums at most `n` such terms). -/
def nu053Entry (n : Nat) (rows : List (Transition × Deposit)) (a0 : AMarking) : Nat :=
  ((List.range n).map a0 ++
    rows.map fun tr =>
      n * ((List.range n).map fun p => pre tr.1 p + tr.2.count p).foldr max 0).foldr max 1

/-- A flat net small enough that the normative solve reaches none of its limits: at most 4096
places and 16384 rows; fewer pivots than bases (`C(n+m, n)`, Bland's rule never returns to a
basis) times the most work one pivot can do (`(2n+1)·(n+m+1)`) within the work limit; and every
minor of the initial tableau (`(n+1)!·E^(n+1)` bounds one of order at most `n + 1`) within the
coefficient limit, a tableau entry in lowest terms being a ratio of two such minors. -/
def Nu053Fits (n : Nat) (rows : List (Transition × Deposit)) (a0 : AMarking) : Prop :=
  n ≤ 4096 ∧ rows.length ≤ 16384 ∧
    Nat.choose (n + rows.length) n * ((2 * n + 1) * (n + rows.length + 1)) ≤ 4000000 ∧
    Nat.factorial (n + 1) * nu053Entry n rows a0 ^ (n + 1) ≤ 2 ^ 63 - 1

instance (n : Nat) (rows : List (Transition × Deposit)) (a0 : AMarking) :
    Decidable (Nu053Fits n rows a0) := by
  unfold Nu053Fits; infer_instance

open Classical in
/-- The reference colour-slot bound: the least `k` that some covering weighting certifies, when
one exists and `k` is within `slotCap`; no plan otherwise. -/
noncomputable def refColourSlotBound : ColourSlotBound := fun n C rows a0 =>
  if h : ∃ k, ScaledCover n C rows a0 k then
    (if Nat.find h ≤ slotCap then some (Nat.find h) else none)
  else none

/-- The reference re-check: the shipped `check_cover` (`slot_bound_lp.rs`). -/
def refSlotReCheck : SlotReCheck := checkCover

/-- The reference consumer rule: for some colour `c < k` resident in the input, the join rule on
the consumer's one input with its coloured outputs as relay targets. A self-loop column is
carried over. -/
def refConsumerRule : ConsumerRule := fun inp outs k s s' =>
  ∃ c, c < k ∧ 1 ≤ s inp c ∧ s' = sJoin [inp] outs c s

/-- The reference violation term: the shipped reap-aware colour-aware quiescence (`DeadERs`,
`encode_coloured_quiescent`) and the property's own clause over the all-colour counts. -/
def refColouredViolation : ColouredViolation :=
  fun E R Q e => DeadERs E R e ∧ Q (agg E.C E.k e)

#spec_witness refColourSlotBound
#spec_witness refSlotReCheck
#spec_witness refConsumerRule
#spec_witness refColouredViolation

/-! ## NU-053 -/

requirement NU_053
  id "NU-053"
  title "EXTENDED-Coloured Quiescence in the Route A SMT Encoder"
  kind F
  scope "the colour-slot bound, its exact re-check and the coloured consumer and quiescence terms of the Route A coloured encoding, where offered"
  source verbatim "spec/12-nu-nets.md"
  quote "*If* the verifier sets the colour-slot bound to `k`, *then* some covering weighting `y` *shall* have `⌊y·M0⌋ = k`, and no covering weighting *shall* have `⌊y·M0⌋ < k`, a covering weighting being one with `y ≥ 0`, `y_p ≥ 1` on every coloured place and `y·C_t ≤ 0` on every flat transition."
        "*When* the verifier solves the colour-slot program of a flat net with `n` places and `m` transitions that has a covering weighting `y` with `⌊y·M0⌋ ≤ 2^31 − 1`, and `n ≤ 4096`, `m ≤ 16384`, `C(n+m, n)·(2n+1)·(n+m+1) ≤ 4000000` and `(n+1)!·E^(n+1) ≤ 2^63 − 1`, where `E` is the largest of 1, every initial count and `n` times every `pre + post` of a flat transition at a place, it *shall* set a colour-slot bound unless the solve is stopped ([VER-013])."
        "*If* the verifier sets the colour-slot bound to `k`, *then* the exact re-check *shall* have accepted a weighting and given it the bound `k`."
        "The exact re-check *shall* accept a weighting `y` exactly when `y ≥ 0`, `y_p ≥ 1` on every coloured place, `y·C_t ≤ 0` on every flat transition and `⌊y·M0⌋ ≤ 2^31 − 1`, and *shall* give an accepted weighting the bound `⌊y·M0⌋`."
        "*When* the coloured encoding emits the rule of a coloured consumer for a colour `c` below `k`, the rule *shall* be enabled only when colour `c` of the input holds a token, and *shall* subtract one from colour `c` of the input, add one to colour `c` of each coloured output, and leave unchanged colour `c` of a place that is both the input and an output and every other colour column."
        "*When* the coloured encoding decides a quiescence property, it *shall* treat an encoding state as violating exactly when every flat row (each XOR branch is its own row) whose transition is not reapable ([VER-002]) is disabled in the state for an uncoloured reason or, when the row touches a coloured place, for every colour below `k`, and the property's own clause holds of the state's all-colour token counts."
  reading "For every colour-slot bound B, re-check K, consumer rule U and violation term V:"
          "for every place count n, coloured places C, flat rows and initial marking a0: if B answers k, there is a scaled cover at k (some D > 0 and Y with Y ≥ 0 below n, Y ≥ D on every place of C, Y not increasing along any row and Y·a0 < D·(k + 1)), and there is none at any j < k;"
          "if the flat net meets Nu053Fits (at most 4096 places and 16384 rows, C(n+m, n)·(2n+1)·(n+m+1) ≤ 4000000 and (n+1)!·E^(n+1) ≤ 2^63 − 1 with E = nu053Entry) and there is a scaled cover at some k ≤ slotCap, then B answers some bound;"
          "if B answers k, K accepts some scaled weighting (D, Y) with the bound k;"
          "K accepts (D, Y) with the bound k exactly when D > 0, Y ≥ 0 below n, Y ≥ D on every place of C, Y·C_r ≤ 0 on every row r, k = ⌊Y·a0 / D⌋ and k ≤ slotCap;"
          "U relates the colour columns s and s' of the consumer with input inp, outputs outs and k slots exactly when some colour c < k has s(inp, c) ≥ 1 and s' is s with, on colour c, one less at inp when inp is not an output, one more at an output that is not inp, and every other place unchanged, and every column of another colour unchanged;"
          "V marks an encoding state e of the encoding E with the reapable names R and the clause Q exactly when every row whose transition is not named in R is disabled at e for an uncoloured reason (uDisabled) or for every colour below k (colDisabled, which is False for a row of class untouched), and Q holds of the all-colour counts of e."
  assumes "The model is the tuple (B, K, U, V). B is a function of the flat net as the shipped build_plan sees it: the place count, the coloured places (sorted, duplicate-free flat indices below the place count), the flat rows (Transition × Deposit, Novel.ForwardDeposit) and the initial count marking. A weighting is handled scaled to integers, a vector Y and a denominator D standing for y = Y / D, as check_cover takes it (slot_bound_lp.rs; Novel.RouteA.checkCover); 'y_p ≥ 1' is Y_p ≥ D and '⌊y·M0⌋' is ⌊Y·M0 / D⌋. A covering weighting at k is Novel.RouteA.ScaledCover at k. The column C_t of a flat transition is post − pre with pre the required count and a timeout outcome counting its deposit (dotIncD), and a reset or consume-all place may carry weight (no H1; SlotBound.lean, 'No H1'); the token-sum bound holds anyway (coloured_tokens_le). U is a relation between the colour columns before and after one rule, so it carries the rule's guard as well as its update; V is the violation term on one encoding state."
          "Line 1 is the first quoted sentence and the body's '`k` is `⌊opt⌋`, where `opt` is the least `y·M0` over all such weightings' (ruling D80 (d)): k is certified by a covering weighting and no smaller bound is. 'The optimum is unique, so every implementation computes the same `k`' is NU_053_unique: two bounds that meet NU-053 agree wherever both answer. 'When no weighting exists (the program is infeasible) ... the plan is refused' is NU_053_infeasible. The simplex itself is not modelled: the witness is the least certified bound by classical choice (refColourSlotBound), not an execution of the solve."
          "Line 2 is the second quoted sentence, which this migration adds so that a bound that never answers does not conform: on a net that meets Nu053Fits a bound is set whenever a covering weighting is within the cap, and by line 1 it is then the least one (NU_053_answers_least). The sentence after it in the markdown gives the reason the normative solve meets it: Bland's rule never returns to a basis, so it makes fewer than C(n+m, n) pivots of work at most (2n+1)·(n+m+1) each, and a tableau entry in lowest terms is a ratio of two minors of the initial tableau, each at most (n+1)!·E^(n+1) by the Leibniz expansion; the optimal weighting the solve reads off is an exact optimum, which passes the re-check below the cap. Every case of spec/verification-fixtures/slot-bound-lp.json that meets Nu053Fits is optimal or infeasible, and the coefficient-limit and work-limit cases do not meet it. Line 2 kills a bound that never answers (NU_053_forbids_never), one that treats k = 0 as a fallback (NU_053_forbids_zeroFallback), one with a narrower cap (NU_053_forbids_byteCap) and one that answers only integer optima (NU_053_forbids_integerOnly). On a net that does not meet Nu053Fits, whether the solve reaches a limit is the normative solve's, kind Q. A stopped solve ([VER-013]) ends the query with the stop, so B reads a solve that is not stopped."
          "Lines 3 and 4 are the third and fourth quoted sentences and the body's 'uses its weighting only after an exact re-check in arbitrary-precision arithmetic' with ruling D80 (a) (clash nu-c#6): the re-check also refuses a bound above 2^31 − 1 (slotCap), as every runtime does (slot_bound_lp.rs SLOT_CAP, SlotBoundLp.java, slot-bound-lp.ts). 'A weighting that fails the re-check is discarded and the plan is refused; it never sets `k`' is line 3 for the bound: no k is set without a weighting the re-check accepts with that bound. That the accepted weighting is the one the solve returned (the shipped colourSlotBoundLP binds the solve's answer to checkCover) is not stated, because B does not expose the weighting it read: a refusal of the solve's own weighting while another weighting would pass is the normative solve's and the fixture's (kind Q), and on a net that meets Nu053Fits line 2 already forbids refusing the plan. The re-check's shape guard on the length of Y (one entry per place) has no counterpart, Weight being total; it only refuses more. Each condition of line 4 is load-bearing: a re-check without the cap (NU_053_forbids_noCap), without the coloured condition (NU_053_forbids_noColouredCheck), without non-negativity (NU_053_forbids_noNegCheck), without the row condition (NU_053_forbids_noRowCheck), without D > 0 (NU_053_forbids_noPosDCheck) or with the ceiling for the floor (NU_053_forbids_ceilCheck) is killed."
          "Line 5 is the fifth quoted sentence and the paragraph on the update of a coloured consumer: the rule for colour c is enabled only with colour c resident in the input (its '>= 1' guard), emits '(- x 1)' for the input column and '(+ x 1)' for each coloured output column, and has no update term for a self-loop column, which keeps its guard and is carried over unchanged, as a join's key that is also a relay target is ([NU-054]). U ranges over the colour columns only: the uncoloured columns of the rule (AC7's tick and tock) are the uncoloured update uFire, not this line. Natural subtraction at a zero column does not arise under the guard. The shipped encoder emits exactly this rule (NU_053_consumer_shipped, Novel.RouteA.colourStep_consume_shipped). The old write order, in which the output's '+ 1' overwrote the input's '− 1' on a self-loop, is killed (NU_053_forbids_oldConsumer) and was a live wrong Proven (Novel.RouteA.self_loop_consume_false_proven); a rule without the guard is killed too (NU_053_forbids_noGuard)."
          "Line 6 is the sixth quoted sentence and the quiescence bullet as reworded by ruling D80 (a) (clash nu-c#5): the quiescence of [VER-002], read colour-aware, for each quiescence property (DeadlockFree, TerminatesAtSink, JoinedOrDeadLettered, QuiescentCount), each conjoining its own clause Q over the all-colour counts (agg). Q is a parameter: NU-053 fixes the colour-aware quiescence term and that the clause is read over the all-colour counts, not which clause each property has. The clauses of DeadlockFree, TerminatesAtSink and QuiescentCount are VER-002's lines 1, 2 and 6 without their quiescence conjunct; JoinedOrDeadLettered and its clause, which has no sink clause ([NU-040] AC4), are NU-040's, and the NU-040 block (wave W9) adds the line that ties the coloured violation of each property to its clause. Until then 'so `JoinedOrDeadLettered` carries no sink clause' has no Lean line. A transition is reapable when its name is in R, the set the verifier hands the encoders (VER-002's reap-aware reading; empty under assumeNoReaping). Disabled 'for an uncoloured reason' is uDisabled: an uncoloured input below its demand, a marked inhibitor or an empty read place; 'for every colour' is colDisabled: a mint finds no globally-fresh colour, a join no colour on every key, a consumer no colour on its input. A row that touches no coloured place has no colour reason (colDisabled of class untouched is False), so it is disabled only for an uncoloured reason, also at k = 0. A strict quiescence that ignores R (NU_053_forbids_strict; Novel.RouteA.ReapW.reaping_breaks_routeA_quiescence) and a count-level quiescence that reads the all-colour counts instead of the colours (NU_053_forbids_countLevel) are killed."
          "The bullet on the EXTENDED fragment ([NU-051]: coloured consumers, relay or drain, and declared carrier places, each consuming exactly one coloured input at count one) is the fragment classifier of NU-051 (refClassify, the NU_051 block). The bullet 'classifies each XOR output branch independently by its own incidence' is build_plan's classification of each flat row (Novel.RouteA.ClassShape, buildPlan in Plan.lean), a pipeline line with the verifier slice of wave W10. 'The encoding has no environment-injection rule, so it does not answer when injection is modelled ([VER-006] AC7)' is the pipeline's decline under injection (wave W10)."
          "The bullet on the structural bound restates line 1 and its soundness: 'every reachable marking has Σ_{coloured} M ≤ y·M ≤ y·M0' is NU_053_tokens_le (Novel.RouteA.coloured_tokens_le), and its dual reading (the largest coloured token count of the state equation M = M0 + C·σ over the reals) is LP duality, not encoded. The examples of the bullet (a budget place that gates minting yields a weighting, a refund to a non-minting place keeps the minting budget covering, a leaky co-mint fan-out yields none) are instances of line 1. 'A relay threads its colour onward and still MUST NOT refund' is not a check of its own: a relay that refunds the minting budget leaves the program infeasible, so by line 1 no plan is built (NU_053_relayRefund, mint: budget → a and relay: a → a2, budget), while a relay that refunds to a place that does not mint keeps the program feasible and the plan built (NU_053_otherRefund, k = 1). '`k = 0` is a bound like any other ... the zero-slot plan is exact rather than a fallback' is NU_053_zero_exact (Novel.RouteA.vacuous_colour_layer_lp) with line 2: a bound of 0 is set, not refused (NU_053_ac6)."
          "The paragraph 'The solve is normative' (the presolve, the tableau, Bland's rule, the weighting read off the slacks, the limits of 4096 places and 16384 rows, the work limit 'it MUST NOT exceed 4000000', the coefficient limit 'MUST have numerator and denominator in lowest terms at most `2^63 − 1` in absolute value' and the order of each round) fixes which nets every implementation refuses and with which pivots. It is kind Q: the shared fixture spec/verification-fixtures/slot-bound-lp.json pins each case's status, pivots, work, presolved sizes, optimum, k and weighting for every implementation (ruling D80 (d)). Line 2 is the one consequence of it stated here. The six report lines, 'colour-slot bound k=<k>' and the stop that prints no line are report text (kind N)."
          "The paragraph on the dispatch (Route B first, deferral to the coloured plan on a Route B Unknown, a verdict of the coloured plan not downgraded, its Proven sound while the declared mints and coloured consumers keep their contracts) and the paragraph on the [VER-015] linear bound running before the coloured query are verdict and pipeline lines. They need the reference ν executor and the verifier pipeline: the soundness line is stated over RefNuReach (design ruling S7 (a)) with wave W9, the dispatch order with wave W10. The current evidence for the soundness is Novel.RouteA.routeA_safety_sound_plan and routeA_quiescence_sound_reaping, relative to the Route A ν step (RouteA.NuStep)."
          "AC1 (a budget-bounded EXTENDED ν-net whose only quiescent marking holds sink tokens is Proven deadlock-free via the coloured Route A encoding) and AC2 (removing the drain turns it Violated) are verdicts of the coloured plan: the quiescence term they read is line 6, the verdicts come with the soundness line (wave W9) and the test fixtures (kind Q)."
          "AC3 (Route A and Route B agree on every small fixture both decide) is differential testing, kind Q."
          "AC4 (a net with no covering weighting falls back rather than a false Proven; a refund to a non-minting place stays bounded) and AC5 (a leaky co-mint fan-out falls back) are line 1: with no scaled cover at any k the bound answers nothing (NU_053_infeasible). The relay that refunds the minting budget is NU_053_relayRefund (no plan) and the refund to a place that does not mint is NU_053_otherRefund (lines 1 and 2: every bound that meets NU-053 answers 1). The fallback itself is the pipeline's (wave W10)."
          "AC6 (an optimum below one yields the exact plan with k = 0) is lines 1 and 2: on the fork that consumes exactly(3) budget tokens from one budget token, optimum 2/3, every bound that meets NU-053 answers 0 (NU_053_ac6), and the zero-slot plan is exact (NU_053_zero_exact). That quiescence is then decided and the emitted encoding is well-formed with zero colour slots is the pipeline's and the scripts' (wave W10, kind Q). The remark that an exactly(2) fork refunded by a join has optimum 1 and that an infeasible program is still refused are instances of line 1."
          "AC7 (the self-loop consumer `spin: a, tick → a, tock` lets placeBound(tock, 0) be Violated) is line 5: the consumer's self-loop column is carried over under its guard, so `spin` can fire; the old update that kept only the '+ 1' is killed (NU_053_forbids_oldConsumer). The verdict itself comes with the soundness line (wave W9)."
          "AC8 (k is the floor of the optimum, identical in every implementation, never larger than the bound of any covering non-negative P-semiflow) is lines 1 and 2 with NU_053_unique and NU_053_le_semiflow: on the exactly(3) fork with a budget of 7, optimum 14/3, every bound that meets NU-053 answers 4 (NU_053_ac8), where every integer cover gives at least 7 (NU_053_forbids_semiflow, NU_053_forbids_integerOnly). The scatter-gather numbers (k = 4 against 10) and that encodeScripts() emits k without a solver ([VER-013] AC1) are fixture checks, kind Q."
          "AC9 (a weighting is used only after the exact re-check; a negative weight, a weight below one on a coloured place, an increasing transition or a bound above 2^31 − 1 refuses the plan with the re-check report line; a reset or consume-all arc on an uncoloured place does not refuse the plan by itself) is lines 3 and 4 with their mutants. Its example (mint: budget → a, b, join: a, b → budget and cancel: r → r2 with a reset arc on budget, from {budget: 2, r: 1}) has k = 4 in every bound that meets NU-053 (NU_053_ac9_reset, lines 1 and 2; the reset place carries weight, no H1). The report line text is kind N."
          "The test derivation (a co-mint to join net Proven deadlock-free via Route A while its name-partition graph truncates; an EXTENDED drain-steal net Violated; the routes agreeing on the no-stall net) is AC1 to AC3 with the dispatch, wave W10; its scatter-gather k = 4 is a fixture check (kind Q), its exactly(3) fork with k = 0 is NU_053_ac6 and its reset arc that keeps the plan is NU_053_ac9_reset."
  signoff "pending"
  statement : ColourSlotBound → SlotReCheck → ConsumerRule → ColouredViolation → Prop :=
    fun B K U V =>
      (∀ n C rows a0 k, B n C rows a0 = some k →
        ScaledCover n C rows a0 k ∧ ∀ j, j < k → ¬ ScaledCover n C rows a0 j) ∧
      (∀ n C rows a0 k, Nu053Fits n rows a0 → ScaledCover n C rows a0 k → k ≤ slotCap →
        ∃ j, B n C rows a0 = some j) ∧
      (∀ n C rows a0 k, B n C rows a0 = some k → ∃ D y, K n C rows a0 D y = some k) ∧
      (∀ n C rows a0 D y k, K n C rows a0 D y = some k ↔
        0 < D ∧ (∀ p, p < n → 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
          (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ k = (dot y a0 n).toNat / D ∧ k ≤ slotCap) ∧
      (∀ inp outs k s s', U inp outs k s s' ↔
        ∃ c, c < k ∧ 1 ≤ s inp c ∧ ∀ p c', s' p c' =
          if c' = c then
            (if p = inp ∧ p ∉ outs then s p c' - 1
             else if p ∈ outs ∧ p ≠ inp then s p c' + 1 else s p c')
          else s p c') ∧
      (∀ E R Q e, V E R Q e ↔
        (∀ r ∈ E.rows, reapT R r.t = false →
          uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s) ∧ Q (agg E.C E.k e))

/- The pinned readable form of NU-053: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_053 : ColourSlotBound → SlotReCheck → ConsumerRule → ColouredViolation → Prop :=
fun B K U V =>
  (∀ (n : ℕ) (C : List PlaceId) (rows : List (Transition × Deposit)) (a0 : AMarking) (k : ℕ),
      B n C rows a0 = some k → ScaledCover n C rows a0 k ∧ ∀ j < k, ¬ScaledCover n C rows a0 j) ∧
    (∀ (n : ℕ) (C : List PlaceId) (rows : List (Transition × Deposit)) (a0 : AMarking) (k : ℕ),
        Nu053Fits n rows a0 → ScaledCover n C rows a0 k → k ≤ slotCap → ∃ j, B n C rows a0 = some j) ∧
      (∀ (n : ℕ) (C : List PlaceId) (rows : List (Transition × Deposit)) (a0 : AMarking) (k : ℕ),
          B n C rows a0 = some k → ∃ D y, K n C rows a0 D y = some k) ∧
        (∀ (n : ℕ) (C : List PlaceId) (rows : List (Transition × Deposit)) (a0 : AMarking) (D : ℕ) (y : Weight) (k : ℕ),
            K n C rows a0 D y = some k ↔
              0 < D ∧
                (∀ p < n, 0 ≤ y p) ∧
                  (∀ p ∈ C, ↑D ≤ y p) ∧ (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ k = (dot y a0 n).toNat / D ∧ k ≤ slotCap) ∧
          (∀ (inp : PlaceId) (outs : List PlaceId) (k : ℕ) (s s' : PlaceId → ℕ → ℕ),
              U inp outs k s s' ↔
                ∃ c < k,
                  1 ≤ s inp c ∧
                    ∀ (p : PlaceId) (c' : ℕ),
                      s' p c' =
                        if c' = c then
                          if p = inp ∧ p ∉ outs then s p c' - 1 else if p ∈ outs ∧ p ≠ inp then s p c' + 1 else s p c'
                        else s p c') ∧
            ∀ (E : Enc) (R : List String) (Q : AMarking → Prop) (e : EState),
              V E R Q e ↔
                (∀ r ∈ E.rows, reapT R r.t = false → uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s) ∧
                  Q (agg E.C E.k e)
-/
#guard_msgs in #print NU_053

/-! ## The reference -/

/-- Under a scaled weighting that covers at `k` while no scaled cover exists below `k`, the
weighting's own floor is `k`. -/
theorem nu053_floor_eq {n : Nat} {C : List PlaceId} {rows : List (Transition × Deposit)}
    {a0 : AMarking} {k D : Nat} {y : Weight} (hD : 0 < D) (hpos : ∀ p, p < n → 0 ≤ y p)
    (hcov : ∀ p ∈ C, (D : Int) ≤ y p) (hdec : ∀ tr ∈ rows, dotIncD y tr n ≤ 0)
    (hk : dot y a0 n < (D : Int) * ((k : Int) + 1))
    (hmin : ∀ j, j < k → ¬ ScaledCover n C rows a0 j) :
    (dot y a0 n).toNat / D = k := by
  have hv : ((dot y a0 n).toNat : Int) = dot y a0 n := Int.toNat_of_nonneg (dot_nonneg_of hpos)
  have hlt : (dot y a0 n).toNat < D * (k + 1) := by
    have : ((dot y a0 n).toNat : Int) < ((D * (k + 1) : Nat) : Int) := by
      rw [hv]; push_cast; exact hk
    exact_mod_cast this
  have hle : (dot y a0 n).toNat / D ≤ k := by
    have := (Nat.div_lt_iff_lt_mul hD).mpr (by rw [Nat.mul_comm]; exact hlt)
    omega
  refine le_antisymm hle (Nat.not_lt.mp fun hq => hmin _ hq ⟨D, y, hD, hpos, hcov, hdec, ?_⟩)
  have h2 := Nat.lt_mul_div_succ (dot y a0 n).toNat hD
  rw [← hv]
  exact_mod_cast h2

/-- The re-check accepts exactly the weightings line 4 names. -/
theorem nu053_checkCover_iff (n : Nat) (C : List PlaceId) (rows : List (Transition × Deposit))
    (a0 : AMarking) (D : Nat) (y : Weight) (k : Nat) :
    checkCover n C rows a0 D y = some k ↔
      0 < D ∧ (∀ p, p < n → 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
        (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ k = (dot y a0 n).toNat / D ∧ k ≤ slotCap := by
  unfold checkCover
  split
  · rename_i hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    constructor
    · intro h
      obtain rfl := (Option.some.inj h).symm
      exact ⟨h1, fun p hp => h2 p (List.mem_range.mpr hp), h3, h4, rfl, h5⟩
    · rintro ⟨-, -, -, -, rfl, -⟩
      rfl
  · rename_i hc
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨h1, h2, h3, h4, rfl, h5⟩
      exact absurd ⟨h1, fun p hp => h2 p (List.mem_range.mp hp), h3, h4, h5⟩ hc

/-- The reference satisfies NU-053. Line 1 is `Nat.find`'s specification and minimality; line 2
holds on every net, since the least certified bound is at most any certified one; line 3 is
`nu053_floor_eq` on the cover the least bound comes with, within the cap; line 4 is
`check_cover` unfolded; line 5 is the join rule on one key under the consumer's guard; line 6 is
the shipped reap-aware predicate with its filter read as an implication. -/
@[evidence holds NU_053]
theorem NU_053_reference :
    NU_053 refColourSlotBound refSlotReCheck refConsumerRule refColouredViolation := by
  classical
  refine ⟨fun n C rows a0 k h => ?_, fun n C rows a0 k _ hc hk => ?_, fun n C rows a0 k h => ?_,
    fun n C rows a0 D y k => ?_, fun inp outs k s s' => ?_, fun E R Q e => ?_⟩
  · unfold refColourSlotBound at h
    split_ifs at h with hex hcap
    cases h
    exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  · unfold refColourSlotBound
    split_ifs with hex hcap
    · exact ⟨_, rfl⟩
    · exact absurd (le_trans (Nat.find_min' hex hc) hk) hcap
    · exact absurd ⟨k, hc⟩ hex
  · unfold refColourSlotBound at h
    split_ifs at h with hex hcap
    cases h
    obtain ⟨D, y, hD, hpos, hcov, hdec, hk⟩ := Nat.find_spec hex
    have hfl := nu053_floor_eq hD hpos hcov hdec hk (fun j hj => Nat.find_min hex hj)
    refine ⟨D, y, (nu053_checkCover_iff _ _ _ _ _ _ _).mpr
      ⟨hD, hpos, hcov, hdec, hfl.symm, hcap⟩⟩
  · exact nu053_checkCover_iff n C rows a0 D y k
  · simp only [refConsumerRule]
    refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · rintro rfl p c'
      simp only [sJoin, List.mem_singleton]
    · intro h
      funext p c'
      rw [h p c']
      simp only [sJoin, List.mem_singleton]
  · simp only [refColouredViolation, DeadERs, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    constructor
    · rintro ⟨h, hq⟩
      exact ⟨fun r hr hn => h r ⟨hr, hn⟩, hq⟩
    · rintro ⟨h, hq⟩
      exact ⟨fun r ⟨hr, hn⟩ => h r hr hn, hq⟩

/-! ## Consequences of lines 1 and 2 -/

/-- **The bound is the same in every implementation.** Two colour-slot bounds that meet NU-053
agree wherever both answer. -/
@[evidence cites "NU-053" "the optimum is unique, so every implementation computes the same k (AC8): two colour-slot bounds that are certified by a covering weighting and undercut by none agree wherever both answer"]
theorem NU_053_unique {B B' : ColourSlotBound} {K K' : SlotReCheck} {U U' : ConsumerRule}
    {V V' : ColouredViolation} (h : NU_053 B K U V) (h' : NU_053 B' K' U' V')
    {n : Nat} {C : List PlaceId} {rows : List (Transition × Deposit)} {a0 : AMarking}
    {k k' : Nat} (hk : B n C rows a0 = some k) (hk' : B' n C rows a0 = some k') : k = k' := by
  obtain ⟨c, m⟩ := h.1 n C rows a0 k hk
  obtain ⟨c', m'⟩ := h'.1 n C rows a0 k' hk'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd c (m' k hlt)
  · exact heq
  · exact absurd c' (m k' hgt)

/-- **An infeasible program builds no plan.** With no covering weighting at any bound, a
colour-slot bound that meets NU-053 answers nothing. -/
@[evidence cites "NU-053" "when no weighting exists (the program is infeasible) the plan is refused (AC4, AC5): a colour-slot bound certified by a covering weighting answers nothing when no scaled cover exists at any k; the fallback itself is the pipeline's"]
theorem NU_053_infeasible {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking}
    (hno : ∀ k, ¬ ScaledCover n C rows a0 k) : B n C rows a0 = none := by
  cases hB : B n C rows a0 with
  | none => rfl
  | some k => exact absurd (h.1 n C rows a0 k hB).1 (hno k)

/-- **On a net that fits, the bound is the least certified one.** If the net meets `Nu053Fits`,
some scaled cover exists at `k`, none below `k`, and `k` is within the cap, a colour-slot bound
that meets NU-053 answers `k`. -/
@[evidence cites "NU-053" "k is the floor of the optimum and is set: on a flat net small enough that the normative solve reaches no limit, a colour-slot bound that meets NU-053 answers the least certified k whenever it is within 2^31 - 1"]
theorem NU_053_answers_least {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {k : Nat}
    (hfit : Nu053Fits n rows a0) (hc : ScaledCover n C rows a0 k)
    (hmin : ∀ j, j < k → ¬ ScaledCover n C rows a0 j) (hk : k ≤ slotCap) :
    B n C rows a0 = some k := by
  obtain ⟨j, hj⟩ := h.2.1 n C rows a0 k hfit hc hk
  obtain ⟨hcj, hmj⟩ := h.1 n C rows a0 j hj
  rcases Nat.lt_trichotomy j k with hlt | rfl | hgt
  · exact absurd hcj (hmin j hlt)
  · exact hj
  · exact absurd hc (hmj k hgt)

/-- **The bound bounds the coloured tokens.** If the colour-slot bound answers `k`, every marking
the flat rows reach holds at most `k` tokens on the coloured places. -/
@[evidence cites "NU-053" "every reachable marking has the coloured token sum at most y.M0, so at most k live colours: under a bound that meets NU-053 line 1, every marking the flat deposit rows reach holds at most k tokens on the coloured places"]
theorem NU_053_tokens_le {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {k : Nat}
    (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n) (hk : B n C rows a0 = some k) :
    ∀ a, ReachAD rows a0 a → (C.map a).sum ≤ k :=
  fun _ ha => coloured_tokens_le hnd hCn (h.1 n C rows a0 k hk).1 ha

/-- **`k = 0` is exact.** If the colour-slot bound answers `0`, dropping every row that touches a
coloured place changes no reachable marking. -/
@[evidence cites "NU-053" "AC6: a bound of k = 0 from a bound that meets NU-053 line 1 gives the exact zero-slot plan: any sub-net keeping the rows that touch no coloured place reaches exactly the markings the full flat net reaches"]
theorem NU_053_zero_exact {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) {n : Nat} {C : List PlaceId}
    {rows rows' : List (Transition × Deposit)} {a0 : AMarking}
    (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n) (h0 : B n C rows a0 = some 0)
    (hsub : ∀ tr ∈ rows', tr ∈ rows)
    (hkeep : ∀ tr ∈ rows, (∀ p ∈ C, pre tr.1 p = 0 ∧ tr.2.count p = 0) → tr ∈ rows') :
    ∀ a, ReachAD rows a0 a ↔ ReachAD rows' a0 a :=
  vacuous_colour_layer_lp hnd hCn (h.1 n C rows a0 0 h0).1 hsub hkeep

/-- **Never above a semiflow bound.** If the colour-slot bound answers `k` and an integer
covering weighting (a covering non-negative P-semiflow bound) has `y·M0 ≤ m`, then `k ≤ m`. -/
@[evidence cites "NU-053" "AC8: k is never larger than the bound of any covering non-negative P-semiflow: an integer covering weighting with y.M0 <= m is a scaled cover at m, so a bound that no cover undercuts is at most m"]
theorem NU_053_le_semiflow {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {k m : Nat} {y : Weight}
    (hk : B n C rows a0 = some k) (hpos : ∀ p, p < n → 0 ≤ y p) (hcov : ∀ p ∈ C, 1 ≤ y p)
    (hdec : ∀ tr ∈ rows, dotIncD y tr n ≤ 0) (hm : dot y a0 n ≤ m) : k ≤ m :=
  Nat.not_lt.mp fun hlt =>
    (h.1 n C rows a0 k hk).2 m hlt (scaledCover_of_cover hpos hcov hdec hm)

/-! ## The reference against the shipped encoder -/

/-- The shipped consumer rule is line 5's rule. -/
theorem NU_053_consumer_shipped {C : List PlaceId} {k : Nat} {inp : PlaceId}
    {outs : List PlaceId} {s s' : PlaceId → Nat → Nat} :
    ColourStep C k (Cls.consume inp outs).shipped s s' ↔ refConsumerRule inp outs k s s' :=
  colourStep_consume_shipped

/-- The reference violation term is the reap-aware predicate `DeadER` with the rows `R` names
marked reapable, and with no reapable name it is the strict `DeadE`. -/
theorem NU_053_violation_deadER (E : Enc) (R : List String) (Q : AMarking → Prop) (e : EState) :
    (refColouredViolation E R Q e ↔
      DeadER E (fun r => reapT R r.t = true) e ∧ Q (agg E.C E.k e)) ∧
    (refColouredViolation E [] Q e ↔ DeadE E e ∧ Q (agg E.C E.k e)) := by
  simp only [refColouredViolation]
  exact ⟨and_congr_left fun _ => deadERs_iff, and_congr_left fun _ => deadERs_nil⟩

/-! ## Examples

Places of the slot-bound nets: `0 = budget`, `1 = a`, `2 = b`, with `a` and `b` coloured
(`Novel.RouteA.Frac`: `fork : exactly(3) budget → a, b`, `join : a, b → budget`). -/

/-- One budget token: the optimum is `2/3` (AC6). -/
def nu053_a0One : AMarking := fun p => if p = 0 then 1 else 0

/-- A coloured place `0` holding `2^31` tokens, with no row: every cover gives a bound of at
least `2^31`, one past the cap. -/
def nu053_a0Big : AMarking := fun p => if p = 0 then 2147483648 else 0

/-- A coloured place `0` holding 256 tokens, with no row: the bound is 256. -/
def nu053_a0Byte : AMarking := fun p => if p = 0 then 256 else 0

/-- The reference answers `k` exactly when `k` is certified, no smaller bound is, and `k` is within
the cap. -/
theorem refColourSlotBound_eq_some {n : Nat} {C : List PlaceId}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {k : Nat} :
    refColourSlotBound n C rows a0 = some k ↔
      ScaledCover n C rows a0 k ∧ (∀ j, j < k → ¬ ScaledCover n C rows a0 j) ∧ k ≤ slotCap := by
  classical
  unfold refColourSlotBound
  split_ifs with hex hcap
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj, hcap⟩
    · rintro ⟨hc, hm, -⟩
      exact (Nat.find_eq_iff hex).mpr ⟨hc, hm⟩
  · simp only [false_iff, not_and]
    intro hc hm hk
    exact hcap ((Nat.find_eq_iff hex).mpr ⟨hc, hm⟩ ▸ hk)
  · simp only [false_iff, not_and]
    exact fun hc => absurd ⟨k, hc⟩ hex

/-- On the exactly(3) fork from a budget of 7 no scaled cover exists below 4: the fork forces
`3·y_budget ≥ y_a + y_b ≥ 2·D`, so `3·y·M0 = 21·y_budget ≥ 14·D`. -/
theorem nu053_frac_noCover :
    ∀ j, j < 4 → ¬ ScaledCover 3 [1, 2] Frac.rowsFrac Frac.a0Frac j := by
  rintro j hj ⟨D, y, hD, -, hcov, hdec, hk⟩
  have hf := hdec (Frac.tFork, [1, 2]) (by simp [Frac.rowsFrac])
  have h1 := hcov 1 (by simp)
  have h2 := hcov 2 (by simp)
  have hp0 : pre Frac.tFork 0 = 3 := rfl
  have hp1 : pre Frac.tFork 1 = 0 := rfl
  have hp2 : pre Frac.tFork 2 = 0 := rfl
  simp [dotIncD, isum, Finset.sum_range_succ, hp0, hp1, hp2] at hf
  simp [dot_eq_isum, isum, Frac.a0Frac] at hk
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    norm_num at hk <;> omega

/-- The reference answers 4 on the exactly(3) fork from a budget of 7. -/
theorem nu053_frac_four : refColourSlotBound 3 [1, 2] Frac.rowsFrac Frac.a0Frac = some 4 :=
  refColourSlotBound_eq_some.mpr
    ⟨checkCover_sound Frac.checked_fractional, nu053_frac_noCover, by decide⟩

/-- The reference answers 0 on the exactly(3) fork from one budget token. -/
theorem nu053_frac_zero : refColourSlotBound 3 [1, 2] Frac.rowsFrac nu053_a0One = some 0 := by
  have hc : ScaledCover 3 [1, 2] Frac.rowsFrac nu053_a0One 0 :=
    checkCover_sound (show checkCover 3 [1, 2] Frac.rowsFrac nu053_a0One 3 Frac.yFrac = some 0 by
      decide)
  exact refColourSlotBound_eq_some.mpr ⟨hc, fun _ hj => absurd hj (Nat.not_lt_zero _), by decide⟩

/-- On one coloured place holding 256 tokens no scaled cover exists below 256. -/
theorem nu053_byte_noCover : ∀ j, j < 256 → ¬ ScaledCover 1 [0] [] nu053_a0Byte j := by
  rintro j hj ⟨D, y, hD, -, hcov, -, hk⟩
  have h0 := hcov 0 (by simp)
  simp [dot_eq_isum, isum, nu053_a0Byte] at hk
  have hm : (D : Int) * 256 < (D : Int) * ((j : Int) + 1) :=
    lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right h0 (by decide)) hk
  have := Int.lt_of_mul_lt_mul_left hm (Int.natCast_nonneg D)
  omega

/-- The reference answers 256 on one coloured place holding 256 tokens. -/
theorem nu053_byte_ref : refColourSlotBound 1 [0] [] nu053_a0Byte = some 256 := by
  have hc : checkCover 1 [0] [] nu053_a0Byte 1 (fun _ => 1) = some 256 := by decide
  exact refColourSlotBound_eq_some.mpr ⟨checkCover_sound hc, nu053_byte_noCover, by decide⟩

/-- `mint : budget → a, b` (places `0 → 1, 2`), and `relay`'s input `a` alone. -/
def nu053_tMint : Transition :=
  { name := "mint", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- `cancel : r → r2` (places `3 → 4`) with a reset arc on the budget `0`. -/
def nu053_tCancel : Transition :=
  { name := "cancel", inputs := [⟨3, .one, none⟩], inhibitors := [], reads := [], resets := [0] }

/-- `relay : a → a2, …` (input place `1`). -/
def nu053_tRelay : Transition :=
  { name := "relay", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- AC9's net: `mint : budget → a, b`, `join : a, b → budget` and `cancel : r → r2` with a reset
arc on `budget`; places `0 = budget`, `1 = a`, `2 = b`, `3 = r`, `4 = r2`. -/
def nu053_rowsReset : List (Transition × Deposit) :=
  [(nu053_tMint, [1, 2]), (Frac.tJoin, [0]), (nu053_tCancel, [4])]

/-- AC9's initial marking `{budget: 2, r: 1}`. -/
def nu053_a0Reset : AMarking := fun p => if p = 0 then 2 else if p = 3 then 1 else 0

/-- The weighting `budget 2, a 1, b 1` of AC9's net. -/
def nu053_yReset : Weight := fun p => if p = 0 then 2 else if p = 1 ∨ p = 2 then 1 else 0

/-- On AC9's net no scaled cover exists below 4: the mint forces `y_budget ≥ y_a + y_b ≥ 2·D`,
so `y·M0 ≥ 2·y_budget ≥ 4·D`. -/
theorem nu053_reset_noCover :
    ∀ j, j < 4 → ¬ ScaledCover 5 [1, 2] nu053_rowsReset nu053_a0Reset j := by
  rintro j hj ⟨D, y, hD, hpos, hcov, hdec, hk⟩
  have hf := hdec (nu053_tMint, [1, 2]) (by simp [nu053_rowsReset])
  have h1 := hcov 1 (by simp)
  have h2 := hcov 2 (by simp)
  have h3 := hpos 3 (by decide)
  have hp0 : pre nu053_tMint 0 = 1 := rfl
  have hp1 : pre nu053_tMint 1 = 0 := rfl
  have hp2 : pre nu053_tMint 2 = 0 := rfl
  have hp3 : pre nu053_tMint 3 = 0 := rfl
  have hp4 : pre nu053_tMint 4 = 0 := rfl
  simp [dotIncD, isum, Finset.sum_range_succ, hp0, hp1, hp2, hp3, hp4] at hf
  simp [dot_eq_isum, isum, Finset.sum_range_succ, nu053_a0Reset] at hk
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    norm_num at hk <;> omega

/-- The reference answers 4 on AC9's net. -/
theorem nu053_reset_four : refColourSlotBound 5 [1, 2] nu053_rowsReset nu053_a0Reset = some 4 := by
  have hc : checkCover 5 [1, 2] nu053_rowsReset nu053_a0Reset 1 nu053_yReset = some 4 := by
    decide
  exact refColourSlotBound_eq_some.mpr ⟨checkCover_sound hc, nu053_reset_noCover, by decide⟩

/-- AC4's relay that refunds the minting budget: `mint : budget → a`, `relay : a → a2, budget`;
places `0 = budget`, `1 = a`, `2 = a2`, with `a` and `a2` coloured. -/
def nu053_rowsRefund : List (Transition × Deposit) :=
  [(nu053_tMint, [1]), (nu053_tRelay, [2, 0])]

/-- AC4's relay that refunds a place that does not mint: `mint : budget → a`,
`relay : a → a2, r`; places `0 = budget`, `1 = a`, `2 = a2`, `3 = r`. -/
def nu053_rowsOther : List (Transition × Deposit) :=
  [(nu053_tMint, [1]), (nu053_tRelay, [2, 3])]

/-- The weighting `1` on `budget`, `a` and `a2`. -/
def nu053_yOther : Weight := fun p => if p ≤ 2 then 1 else 0

/-- A relay that refunds the minting budget leaves the program infeasible: the mint gives
`y_a ≤ y_budget`, the relay `y_a2 + y_budget ≤ y_a`, so `y_a2 ≤ 0 < D`. -/
theorem nu053_refund_noCover : ∀ k, ¬ ScaledCover 3 [1, 2] nu053_rowsRefund nu053_a0One k := by
  rintro k ⟨D, y, hD, -, hcov, hdec, -⟩
  have hm := hdec (nu053_tMint, [1]) (by simp [nu053_rowsRefund])
  have hr := hdec (nu053_tRelay, [2, 0]) (by simp [nu053_rowsRefund])
  have h2 := hcov 2 (by simp)
  have hm0 : pre nu053_tMint 0 = 1 := rfl
  have hm1 : pre nu053_tMint 1 = 0 := rfl
  have hm2 : pre nu053_tMint 2 = 0 := rfl
  have hr0 : pre nu053_tRelay 0 = 0 := rfl
  have hr1 : pre nu053_tRelay 1 = 1 := rfl
  have hr2 : pre nu053_tRelay 2 = 0 := rfl
  simp [dotIncD, isum, Finset.sum_range_succ, hm0, hm1, hm2] at hm
  simp [dotIncD, isum, Finset.sum_range_succ, hr0, hr1, hr2] at hr
  omega

/-- A relay that refunds a place that does not mint keeps the program feasible: no cover at 0
(the mint gives `D ≤ y_a ≤ y_budget = y·M0`), a cover at 1. -/
theorem nu053_other_one : refColourSlotBound 4 [1, 2] nu053_rowsOther nu053_a0One = some 1 := by
  have hc : checkCover 4 [1, 2] nu053_rowsOther nu053_a0One 1 nu053_yOther = some 1 := by decide
  refine refColourSlotBound_eq_some.mpr ⟨checkCover_sound hc, ?_, by decide⟩
  rintro j hj ⟨D, y, hD, -, hcov, hdec, hk⟩
  obtain rfl : j = 0 := by omega
  have hm := hdec (nu053_tMint, [1]) (by simp [nu053_rowsOther])
  have h1 := hcov 1 (by simp)
  have hm0 : pre nu053_tMint 0 = 1 := rfl
  have hm1 : pre nu053_tMint 1 = 0 := rfl
  have hm2 : pre nu053_tMint 2 = 0 := rfl
  have hm3 : pre nu053_tMint 3 = 0 := rfl
  simp [dotIncD, isum, Finset.sum_range_succ, hm0, hm1, hm2, hm3] at hm
  simp [dot_eq_isum, isum, nu053_a0One] at hk
  omega

/-- A join `join : 0, 1 → 2` keyed on the coloured places `0` and `1`. -/
def nu053_tJ : Transition :=
  { name := "join", inputs := [⟨0, .one, none⟩, ⟨1, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }

/-- The encoding of the join alone, with two colours. -/
def nu053_encJ : Enc :=
  { C := [0, 1], k := 2, n := 3, rows := [⟨nu053_tJ, [2], .join [0, 1] []⟩], invs := [],
    a0 := fun _ => 0 }

/-- Colour 0 on key `0` and colour 1 on key `1`: the keys hold one token each, of different
colours, so the join is count-enabled but disabled for every colour. -/
def nu053_eJ : EState :=
  ⟨fun _ => 0, fun p c => if (p = 0 ∧ c = 0) ∨ (p = 1 ∧ c = 1) then 1 else 0⟩

theorem nu053_pre_tJ (p : PlaceId) : pre nu053_tJ p = if p = 0 ∨ p = 1 then 1 else 0 := by
  by_cases h0 : p = 0
  · subst h0; rfl
  by_cases h1 : p = 1
  · subst h1; rfl
  have e0 : (0 == p) = false := by simpa using Ne.symm h0
  have e1 : (1 == p) = false := by simpa using Ne.symm h1
  simp [pre, specAt, nu053_tJ, List.find?, e0, e1, h0, h1]

/-- The colour-aware quiescence holds at `nu053_eJ`. -/
theorem nu053_eJ_quiescent : refColouredViolation nu053_encJ [] (fun _ => True) nu053_eJ := by
  refine ⟨fun r hr => Or.inr ?_, trivial⟩
  simp only [nu053_encJ, List.mem_filter, List.mem_singleton] at hr
  obtain ⟨rfl, -⟩ := hr
  show ∀ c, c < 2 → ∃ p ∈ [0, 1], nu053_eJ.s p c = 0
  intro c hc
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · exact ⟨1, by simp, by simp [nu053_eJ]⟩
  · exact ⟨0, by simp, by simp [nu053_eJ]⟩

/-- The join is not disabled for an uncoloured reason at `nu053_eJ`, and its keys hold one token
each in all colours together. -/
theorem nu053_eJ_counts :
    ¬ uDisabled [0, 1] nu053_eJ nu053_tJ ∧ ¬ ∃ p ∈ [0, 1], agg [0, 1] 2 nu053_eJ p < pre nu053_tJ p := by
  constructor
  · rintro (⟨p, hp, hlt⟩ | ⟨p, hp, -⟩ | ⟨p, hp, -⟩)
    · rw [nu053_pre_tJ] at hlt
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
      simp [hp.1, hp.2] at hlt
    · simp [nu053_tJ] at hp
    · simp [nu053_tJ] at hp
  · rintro ⟨p, hp, hlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      simp [agg, nu053_eJ, nu053_pre_tJ] at hlt

/-- NU-053's reference on the examples: the bound 4 on the exactly(3) fork from a budget of 7
(optimum `14/3`, AC8), the bound 0 from one budget token (optimum `2/3`, AC6), the bound 4 on
AC9's reset net, the re-check giving 4 for the weighting `(2, 3, 3) / 3`, a self-loop consumer
rule that carries its column over (AC7) and the join of `nu053_encJ` quiescent although
count-enabled. -/
@[evidence nonvacuous NU_053]
theorem NU_053_nonvacuous :
    refColourSlotBound 3 [1, 2] Frac.rowsFrac Frac.a0Frac = some 4 ∧
    refColourSlotBound 3 [1, 2] Frac.rowsFrac nu053_a0One = some 0 ∧
    refColourSlotBound 5 [1, 2] nu053_rowsReset nu053_a0Reset = some 4 ∧
    refSlotReCheck 3 [1, 2] Frac.rowsFrac Frac.a0Frac 3 Frac.yFrac = some 4 ∧
    refConsumerRule 0 [0] 1 (fun _ _ => 1) (fun _ _ => 1) ∧
    refColouredViolation nu053_encJ [] (fun _ => True) nu053_eJ := by
  refine ⟨nu053_frac_four, nu053_frac_zero, nu053_reset_four, Frac.checked_fractional,
    ⟨0, by decide, le_refl _, ?_⟩, nu053_eJ_quiescent⟩
  funext p c
  simp [sJoin]

/-! ## Consequences on the examples

Every bound that meets NU-053 answers what the reference answers on these nets: each fits, so
line 2 makes it answer, and line 1 makes the answer the least certified one. -/

/-- **AC6.** On the exactly(3) fork from one budget token (optimum `2/3`) every bound that meets
NU-053 answers 0: the zero-slot plan is built, not refused. -/
@[evidence cites "NU-053" "AC6: a slot-bound optimum below one yields the plan with k = 0: on the exactly(3) fork from one budget token every colour-slot bound that meets NU-053 answers 0"]
theorem NU_053_ac6 {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 3 [1, 2] Frac.rowsFrac nu053_a0One = some 0 := by
  obtain ⟨hc, hm, hk⟩ := refColourSlotBound_eq_some.mp nu053_frac_zero
  exact NU_053_answers_least h (by decide) hc hm hk

/-- **AC8.** On the exactly(3) fork from a budget of 7 (optimum `14/3`) every bound that meets
NU-053 answers 4. -/
@[evidence cites "NU-053" "AC8: with a fork that consumes exactly(3) budget tokens into the two keys, a join that refunds one, and a budget of 7, the optimum is 14/3 and every colour-slot bound that meets NU-053 answers k = 4"]
theorem NU_053_ac8 {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 3 [1, 2] Frac.rowsFrac Frac.a0Frac = some 4 := by
  obtain ⟨hc, hm, hk⟩ := refColourSlotBound_eq_some.mp nu053_frac_four
  exact NU_053_answers_least h (by decide) hc hm hk

/-- **AC9.** A reset arc on the uncoloured budget does not refuse the plan: on AC9's net every
bound that meets NU-053 answers 4. -/
@[evidence cites "NU-053" "AC9: a reset or consume-all arc on an uncoloured place does not refuse the plan by itself: on mint: budget -> a, b, join: a, b -> budget and cancel: r -> r2 with a reset arc on budget, from {budget: 2, r: 1}, every colour-slot bound that meets NU-053 answers k = 4"]
theorem NU_053_ac9_reset {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 5 [1, 2] nu053_rowsReset nu053_a0Reset = some 4 := by
  obtain ⟨hc, hm, hk⟩ := refColourSlotBound_eq_some.mp nu053_reset_four
  exact NU_053_answers_least h (by decide) hc hm hk

/-- **AC4, a relay that refunds the minting budget.** Every bound that meets NU-053 builds no
plan: the program is infeasible. -/
@[evidence cites "NU-053" "AC4: a relay that refunds and frees a budget token for a (k+1)-th colour leaves the slot-bound program infeasible, so every colour-slot bound that meets NU-053 builds no plan"]
theorem NU_053_relayRefund {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 3 [1, 2] nu053_rowsRefund nu053_a0One = none :=
  NU_053_infeasible h nu053_refund_noCover

/-- **AC4, a refund to a place that does not mint.** Every bound that meets NU-053 answers 1:
the minting budget still covers. -/
@[evidence cites "NU-053" "AC4: a refund to a non-minting place keeps the minting budget a covering weighting, so it stays bounded: every colour-slot bound that meets NU-053 answers k = 1 on mint: budget -> a, relay: a -> a2, r from one budget token"]
theorem NU_053_otherRefund {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 4 [1, 2] nu053_rowsOther nu053_a0One = some 1 := by
  obtain ⟨hc, hm, hk⟩ := refColourSlotBound_eq_some.mp nu053_other_one
  exact NU_053_answers_least h (by decide) hc hm hk

/-- On one coloured place holding 256 tokens every bound that meets NU-053 answers 256. -/
theorem NU_053_byte {B : ColourSlotBound} {K : SlotReCheck} {U : ConsumerRule}
    {V : ColouredViolation} (h : NU_053 B K U V) :
    B 1 [0] [] nu053_a0Byte = some 256 := by
  obtain ⟨hc, hm, hk⟩ := refColourSlotBound_eq_some.mp nu053_byte_ref
  exact NU_053_answers_least h (by decide) hc hm hk

/-! ## Wrong models -/

/-- An integer covering weighting bounding the coloured tokens by `k`: the bound of a covering
non-negative P-semiflow. -/
def Nu053IntCover (n : Nat) (C : List PlaceId) (rows : List (Transition × Deposit))
    (a0 : AMarking) (k : Nat) : Prop :=
  ∃ y : Weight, (∀ p, p < n → 0 ≤ y p) ∧ (∀ p ∈ C, 1 ≤ y p) ∧
    (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ dot y a0 n ≤ k

open Classical in
/-- The semiflow bound: the least `k` an integer covering weighting gives (sound, not optimal). -/
noncomputable def nu053_semiflowBound : ColourSlotBound := fun n C rows a0 =>
  if h : ∃ k, Nu053IntCover n C rows a0 k then some (Nat.find h) else none

open Classical in
/-- The optimal bound without the cap. -/
noncomputable def nu053_uncappedBound : ColourSlotBound := fun n C rows a0 =>
  if h : ∃ k, ScaledCover n C rows a0 k then some (Nat.find h) else none

/-- A bound that never builds a plan. -/
def nu053_never : ColourSlotBound := fun _ _ _ _ => none

/-- The zero-slot plan treated as a fallback: the reference, refusing whenever it answers 0. -/
noncomputable def nu053_zeroFallback : ColourSlotBound := fun n C rows a0 =>
  match refColourSlotBound n C rows a0 with
  | some 0 => none
  | x => x

/-- A narrower cap: the reference, refusing any bound above 255 (a colour index held in a byte). -/
noncomputable def nu053_byteCap : ColourSlotBound := fun n C rows a0 =>
  match refColourSlotBound n C rows a0 with
  | some k => if k ≤ 255 then some k else none
  | none => none

open Classical in
/-- An integer-only solve: the reference, refusing when no integer covering weighting attains its
bound (a strictly fractional optimum). -/
noncomputable def nu053_integerOnly : ColourSlotBound := fun n C rows a0 =>
  match refColourSlotBound n C rows a0 with
  | some k => if Nu053IntCover n C rows a0 k then some k else none
  | none => none

/-- A re-check without the cap. -/
def nu053_noCapCheck : SlotReCheck := fun n C rows a0 D y =>
  if 0 < D ∧ (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
      (∀ tr ∈ rows, dotIncD y tr n ≤ 0)
  then some ((dot y a0 n).toNat / D) else none

/-- A re-check that does not check the coloured places. -/
def nu053_noColouredCheck : SlotReCheck := fun n _ rows a0 D y =>
  if 0 < D ∧ (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
      (dot y a0 n).toNat / D ≤ slotCap
  then some ((dot y a0 n).toNat / D) else none

/-- A re-check that does not check that the weighting is non-negative. -/
def nu053_noNegCheck : SlotReCheck := fun n C rows a0 D y =>
  if 0 < D ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧ (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧
      (dot y a0 n).toNat / D ≤ slotCap
  then some ((dot y a0 n).toNat / D) else none

/-- A re-check that does not check the flat rows. -/
def nu053_noRowCheck : SlotReCheck := fun n C _ a0 D y =>
  if 0 < D ∧ (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
      (dot y a0 n).toNat / D ≤ slotCap
  then some ((dot y a0 n).toNat / D) else none

/-- A re-check that does not check that the denominator is positive. -/
def nu053_noPosDCheck : SlotReCheck := fun n C rows a0 D y =>
  if (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
      (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ (dot y a0 n).toNat / D ≤ slotCap
  then some ((dot y a0 n).toNat / D) else none

/-- A re-check that gives the ceiling of `y·M0` instead of its floor. -/
def nu053_ceilCheck : SlotReCheck := fun n C rows a0 D y =>
  if 0 < D ∧ (∀ p ∈ List.range n, 0 ≤ y p) ∧ (∀ p ∈ C, (D : Int) ≤ y p) ∧
      (∀ tr ∈ rows, dotIncD y tr n ≤ 0) ∧ ((dot y a0 n).toNat + D - 1) / D ≤ slotCap
  then some (((dot y a0 n).toNat + D - 1) / D) else none

/-- The weighting `0` on the budget and `1` on every other place: it increases along the fork. -/
def nu053_yKeys : Weight := fun p => if p = 0 then 0 else 1

/-- The consumer rule in the old write order (`Novel.RouteA.sConsume`): the output's `+ 1` wins
over the input's `− 1` on a self-loop column. -/
def nu053_oldConsumer : ConsumerRule := fun inp outs k s s' =>
  ∃ c, c < k ∧ 1 ≤ s inp c ∧ s' = sConsume inp outs c s

/-- A consumer rule without its guard: it fires for a colour the input does not hold. -/
def nu053_noGuardConsumer : ConsumerRule := fun inp outs k s s' =>
  ∃ c, c < k ∧ s' = sJoin [inp] outs c s

/-- A violation term with the strict quiescence, which ignores the reapable names. -/
def nu053_strictViolation : ColouredViolation := fun E _ Q e => DeadE E e ∧ Q (agg E.C E.k e)

/-- A violation term with a count-level quiescence: a coloured row is read as disabled when some
coloured input's all-colour count is below its demand, not colour by colour. -/
def nu053_countViolation : ColouredViolation := fun E R Q e =>
  (∀ r ∈ E.rows, reapT R r.t = false →
    uDisabled E.C e r.t ∨ ∃ p ∈ E.C, agg E.C E.k e p < pre r.t p) ∧ Q (agg E.C E.k e)

/-- Line 1 forbids the semiflow bound: on the exactly(3) fork from a budget of 7 it gives at
least 7, while a scaled cover exists at 4. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_semiflow :
    ¬ NU_053 nu053_semiflowBound refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have hex : ∃ k, Nu053IntCover 3 [1, 2] Frac.rowsFrac Frac.a0Frac k :=
    ⟨7, fun _ => 1, fun _ _ => by simp, fun _ _ => le_refl _, by decide, by decide⟩
  obtain ⟨k, hB, y, -, hcov, hdec, hle⟩ : ∃ k,
      nu053_semiflowBound 3 [1, 2] Frac.rowsFrac Frac.a0Frac = some k ∧
        Nu053IntCover 3 [1, 2] Frac.rowsFrac Frac.a0Frac k := by
    classical
    unfold nu053_semiflowBound
    rw [dif_pos hex]
    exact ⟨_, rfl, Nat.find_spec hex⟩
  have h7 := Frac.integer_cover_ge_seven hcov hdec
  have hge : 7 ≤ k := by omega
  exact (h.1 _ _ _ _ _ hB).2 4 (by omega) (checkCover_sound Frac.checked_fractional)

/-- Line 2 forbids a bound that never builds a plan: on AC6's net it must answer. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_never :
    ¬ NU_053 nu053_never refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have := NU_053_ac6 h
  simp [nu053_never] at this

/-- Line 2 forbids the zero-slot plan as a fallback: on AC6's net the bound must be 0, and the
mutant refuses it. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_zeroFallback :
    ¬ NU_053 nu053_zeroFallback refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have h6 := NU_053_ac6 h
  have hn : nu053_zeroFallback 3 [1, 2] Frac.rowsFrac nu053_a0One = none := by
    unfold nu053_zeroFallback; rw [nu053_frac_zero]; rfl
  simp [hn] at h6

/-- Line 2 forbids a narrower cap: on one coloured place holding 256 tokens the bound must be
256, and the mutant refuses it. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_byteCap :
    ¬ NU_053 nu053_byteCap refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have hb := NU_053_byte h
  have hn : nu053_byteCap 1 [0] [] nu053_a0Byte = none := by
    unfold nu053_byteCap; rw [nu053_byte_ref]; decide
  simp [hn] at hb

/-- Line 2 forbids an integer-only solve: on the exactly(3) fork from a budget of 7 the bound
must be 4, and every integer cover gives at least 7. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_integerOnly :
    ¬ NU_053 nu053_integerOnly refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have h8 := NU_053_ac8 h
  have hn : nu053_integerOnly 3 [1, 2] Frac.rowsFrac Frac.a0Frac = none := by
    unfold nu053_integerOnly; rw [nu053_frac_four]
    simp only
    rw [if_neg]
    rintro ⟨y, -, hcov, hdec, hle⟩
    have := Frac.integer_cover_ge_seven hcov hdec
    omega
  simp [hn] at h8

/-- Lines 3 and 4 forbid the bound without the cap: on a coloured place holding `2^31` tokens it
answers at least `2^31`, which no accepted weighting gives. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_uncapped :
    ¬ NU_053 nu053_uncappedBound refSlotReCheck refConsumerRule refColouredViolation := by
  intro h
  have hex : ∃ k, ScaledCover 1 [0] [] nu053_a0Big k :=
    ⟨2147483648, 1, fun _ => 1, by decide, fun _ _ => by simp, fun _ _ => le_refl _,
      fun _ h => absurd h List.not_mem_nil, by decide⟩
  obtain ⟨k, hB, D', y', hD', -, hcov, -, hk⟩ : ∃ k,
      nu053_uncappedBound 1 [0] [] nu053_a0Big = some k ∧ ScaledCover 1 [0] [] nu053_a0Big k := by
    classical
    unfold nu053_uncappedBound
    rw [dif_pos hex]
    exact ⟨_, rfl, Nat.find_spec hex⟩
  obtain ⟨D, y, hck⟩ := h.2.2.1 _ _ _ _ _ hB
  have hcap := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hck).2.2.2.2.2
  have h0 := hcov 0 (by simp)
  simp [dot_eq_isum, isum, nu053_a0Big] at hk
  have hm : (D' : Int) * 2147483648 < (D' : Int) * ((k : Int) + 1) :=
    lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right h0 (by decide)) hk
  have := Int.lt_of_mul_lt_mul_left hm (Int.natCast_nonneg D')
  simp [slotCap] at hcap
  omega

/-- Line 4 forbids a re-check without the cap: it accepts a weighting with the bound `2^31`. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noCap :
    ¬ NU_053 refColourSlotBound nu053_noCapCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_noCapCheck 1 [0] [] nu053_a0Big 1 (fun _ => 1) = some 2147483648 := by decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).2.2.2.2.2
  simp [slotCap] at this

/-- Line 4 forbids a re-check that does not check the coloured places: it accepts the zero
weighting, below one on the coloured place `0`. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noColouredCheck :
    ¬ NU_053 refColourSlotBound nu053_noColouredCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_noColouredCheck 1 [0] [] (fun _ => 1) 1 (fun _ => 0) = some 0 := by decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).2.2.1 0 (by simp)
  simp at this

/-- Line 4 forbids a re-check that does not check non-negativity: it accepts a weighting that is
`−1` on the place `1`. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noNegCheck :
    ¬ NU_053 refColourSlotBound nu053_noNegCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_noNegCheck 2 [0] [] (fun _ => 0) 1 (fun p => if p = 0 then 1 else -1) =
      some 0 := by decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).2.1 1 (by decide)
  exact absurd this (by decide)

/-- Line 4 forbids a re-check that does not check the flat rows: it accepts a weighting that
increases along the fork. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noRowCheck :
    ¬ NU_053 refColourSlotBound nu053_noRowCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_noRowCheck 3 [1, 2] Frac.rowsFrac Frac.a0Frac 1 nu053_yKeys = some 0 := by
    decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).2.2.2.1 (Frac.tFork, [1, 2]) (by simp [Frac.rowsFrac])
  exact absurd this (by decide)

/-- Line 4 forbids a re-check that does not check the denominator: it accepts `D = 0`. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noPosDCheck :
    ¬ NU_053 refColourSlotBound nu053_noPosDCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_noPosDCheck 1 [] [] (fun _ => 0) 0 (fun _ => 0) = some 0 := by decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).1
  exact absurd this (by decide)

/-- Line 4 forbids a re-check that gives the ceiling: on the weighting `(2, 3, 3) / 3` it gives 5,
where `⌊14/3⌋ = 4`. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_ceilCheck :
    ¬ NU_053 refColourSlotBound nu053_ceilCheck refConsumerRule refColouredViolation := by
  intro h
  have hv : nu053_ceilCheck 3 [1, 2] Frac.rowsFrac Frac.a0Frac 3 Frac.yFrac = some 5 := by decide
  have := ((h.2.2.2.1 _ _ _ _ _ _ _).mp hv).2.2.2.2.1
  exact absurd this (by decide)

/-- Line 5 forbids the old consumer write order: on a self-loop it adds one to the input. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_oldConsumer :
    ¬ NU_053 refColourSlotBound refSlotReCheck nu053_oldConsumer refColouredViolation := by
  intro h
  have hr : nu053_oldConsumer 0 [0] 1 (fun _ _ => 1) (sConsume 0 [0] 0 fun _ _ => 1) :=
    ⟨0, by decide, le_refl _, rfl⟩
  obtain ⟨c, hc, -, hs⟩ := (h.2.2.2.2.1 _ _ _ _ _).mp hr
  obtain rfl : c = 0 := by omega
  have := hs 0 0
  simp [sConsume] at this

/-- Line 5 forbids a consumer rule without its guard: it fires for colour 0 on an empty input. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_noGuard :
    ¬ NU_053 refColourSlotBound refSlotReCheck nu053_noGuardConsumer refColouredViolation := by
  intro h
  have hr : nu053_noGuardConsumer 0 [1] 1 (fun _ _ => 0) (sJoin [0] [1] 0 fun _ _ => 0) :=
    ⟨0, by decide, rfl⟩
  obtain ⟨c, -, hg, -⟩ := (h.2.2.2.2.1 _ _ _ _ _).mp hr
  simp at hg

/-- Line 6 forbids the strict quiescence: a reapable transition `t` that is still enabled. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_strict :
    ¬ NU_053 refColourSlotBound refSlotReCheck refConsumerRule nu053_strictViolation := by
  intro h
  let tR : Transition :=
    { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }
  let E : Enc :=
    { C := [], k := 0, n := 1, rows := [⟨tR, [], .untouched⟩], invs := [], a0 := fun _ => 1 }
  let e : EState := ⟨fun _ => 1, fun _ _ => 0⟩
  have hiff := h.2.2.2.2.2 E ["t"] (fun _ => True) e
  have hR : (∀ r ∈ E.rows, reapT ["t"] r.t = false →
      uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s) := by
    intro r hr hn
    simp only [E, List.mem_singleton] at hr
    subst hr
    exact absurd hn (by decide)
  obtain ⟨hdead, -⟩ := hiff.mpr ⟨hR, trivial⟩
  rcases hdead ⟨tR, [], .untouched⟩ (by simp [E]) with hu | hc
  · rcases hu with ⟨p, -, hlt⟩ | ⟨p, hp, -⟩ | ⟨p, hp, -⟩
    · have : pre tR p ≤ 1 := by
        by_cases h0 : p = 0
        · subst h0; decide
        · have e0 : (0 == p) = false := by simpa using Ne.symm h0
          simp [pre, specAt, tR, List.find?, e0]
      simp only [e] at hlt
      omega
    · simp [tR] at hp
    · simp [tR] at hp
  · exact hc

/-- Line 6 forbids a count-level quiescence: at `nu053_eJ` the join is disabled for every colour
but count-enabled. -/
@[evidence forbids NU_053]
theorem NU_053_forbids_countLevel :
    ¬ NU_053 refColourSlotBound refSlotReCheck refConsumerRule nu053_countViolation := by
  intro h
  have href := (NU_053_reference.2.2.2.2.2 nu053_encJ [] (fun _ => True) nu053_eJ).mp
    nu053_eJ_quiescent
  obtain ⟨hm, -⟩ := (h.2.2.2.2.2 nu053_encJ [] (fun _ => True) nu053_eJ).mpr href
  rcases hm ⟨nu053_tJ, [2], .join [0, 1] []⟩ (by simp [nu053_encJ]) rfl with hu | hc
  · exact nu053_eJ_counts.1 hu
  · exact nu053_eJ_counts.2 hc

end Libpetri.Spec
