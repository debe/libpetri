import Libpetri.Spec.Registry
import Libpetri.Spec.Req.NU_055
import Libpetri.Reference.NuLink
import Libpetri.Reference.NuLinkA
import Libpetri.Spec.Text.NU_050

set_option linter.missingDocs true

/-!
# NU-050: Exact verification of matched transitions (`spec/12-nu-nets.md`)

Three blocks, one per claim the section makes about a verdict of the two ν routes. The timed
lines (a join's clock on a timed net, AC3 and AC4, and the name-layer reading of the
[TIME-012] restart) are the fourth block, `NU_050_timed` (`NU_050_timed.lean`), over the timed
semantics Route B's classes stand for; the executor side of the ν-join clock is `TIME_012_nu`.

* `NU_050_prefix` (kind F): the verdict Route B reads off a built graph, for every property.
  A stopped build answers `Unknown`; a build that was not stopped answers `Violated` when some
  class violates the property, also when the graph did not close (the prefix rule, ruling D59
  (a)); a `Violated` names a violating class; with no violating class the answer is `Proven` on a
  closed graph and `Unknown` otherwise. It is a predicate over an abstract verdict function
  (`ClassVerdict`, the model of the NU-055 truncation block), witness `refClassVerdict`, the
  shipped `Decide.verdict`. That a graph that did not close never gives `Proven` is a theorem of
  the lines (`NU_050_prefix_never_proven`).
* `NU_050_soundB` (kind B): a Route B `Proven` holds of every marking the reference ν executor
  reaches (and, for a quiescence property, rests at), while the actions keep their contracts and
  the projections read the names their writers put there. It is a predicate over an abstract
  Route B decider; witness `refRouteB`, the build and verdict on the untimed graph. Holds evidence
  is bridge B1 (`Reference/NuLink.lean`) composed with `routeB_untimed_safety_sound` and
  `routeB_untimed_quiescence_sound`.
* `NU_050_soundA` (kind B): the same for Route A, with the colour-slot plan of [NU-053]. It is a
  predicate over an abstract plan builder; witness `refRouteAPlan`, the shipped `build_plan`.
  Holds evidence is bridge B2 (`Reference/NuLinkA.lean`) composed with `routeA_safety_sound_plan`
  and `routeA_quiescence_sound_plan`.

The soundness lines run the reference executor under the contracts: a run is a sequence of
reference ν firings (`RefNuFire`) in which every firing's action keeps the contract of its role,
as the spec's "while the declared mints and the coloured consumers keep their contracts" says.
The runs are the bridges' headline forms: `NuLink.RefNuRunB` for Route B and `NuLinkA.RefNuRunA`
for Route A. Route A's run and its rows premise read the SOURCE rows `build_plan` receives
(`NuLinkA.srcClass`, `NuLinkA.SrcCovers`), not the plan the planner returns, so a planner that
leaves a row out is judged against the firings of that row too (`NU_050_soundA_forbids_dropRow`).
The bridges' strong forms (`refNuReach_names_reach`'s `hok`, `NuLinkA.FiringsHaveRows`) ask the
contract of every firing the reference offers, including one whose action writes a stale name,
which no net with a mint that can fire twice meets (`nu050_hok_fails`,
`nu050_firingsHaveRows_fails`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.ForwardDeposit

/-! ## NU-050 (F): the verdict on a built graph -/

requirement NU_050_prefix
  id "NU-050"
  title "Exact Verification of Matched Transitions: the verdict on a built graph"
  kind F
  scope "every verifier that offers the Route B name-partition graph (MAY); the verdict it reads off a built graph, for every property"
  source verbatim "spec/12-nu-nets.md"
  covers NU_050.s2, NU_050.s3, NU_050.s4, NU_050.s5
  reading "For every explorer E over classes, every build outcome o (the stored classes in discovery order, the number expanded, whether the build closed and whether it stopped) and every property p, where a class violates p as Decide.violatesAt reads it (for a safety property a stored class at which the predicate holds; for a quiescence property an expanded class at which the predicate holds and every successor is a firing of a reapable transition):"
          "if the build stopped, V answers Unknown;"
          "if the build did not stop and some class violates p, V answers Violated (at some class);"
          "if V answers Violated at the class index i, class i violates p;"
          "if the build did not stop and no class violates p, V answers Proven when the graph closed and Unknown when it did not."
  assumes "The model is a verdict function on a built graph (ClassVerdict, the model of NU_055_truncation, shared so that one verdict function serves NU-050 and NU-055): from the explorer, the build's outcome (Decide.Out: the stored classes, the number expanded, complete, stopped) and the property (Decide.Prop': a safety predicate on classes, or a quiescence predicate with its reapable set), the verdict. How the build stores and expands classes, and that a stored class is reachable in the graph (Decide.prefix_safety_sound, Decide.prefix_quiescence_sound), is Decide.build's and VER-012's; the graph itself (its key, the name-permutation quotient) is VER-012's block. 'Does not close' is o.complete = false: the class bound reached (truncated, o.stopped = false), or the total budget or a cancellation (o.stopped = true), or the fuel of the Lean model run out (also a stop)."
          "Ruling D59 (a) (clashes nu-b#1, ver-d#1): a truncated graph answers Violated when a stored class violates (the prefix rule of VER-012 AC3), as Rust, Java and TypeScript do (verify_name_scg in nu_scg_verifier.rs, NuScgVerifier.verify in NuScgVerifier.java, verifyNameScg in nu-scg-verifier.ts). AC2 is reworded accordingly (NUB-1 (a)); the old 'not Proven/Violated' reading is NU_050_prefix_mutant_unknownOnTruncation, met by nu050_unknownOnTruncation and killed by line 2. A build stopped by the total budget or a cancellation answers Unknown whatever its prefix holds (the is_stopped check of verify_name_scg in nu_scg_verifier.rs, VER-013's rule): line 1, killed in nu050_stoppedPrefix."
          "The sentence 'If the Route B graph does not close, then Route B shall not answer `Proven`.' is a consequence of the lines, not a line, so it is not quoted here: a stopped build answers Unknown (line 1), and a build that was not stopped answers Violated (line 2) or, with no violating class, Proven only on a closed graph (line 4). NU_050_prefix_open_never_proven carries it as cited evidence (the same fact as Decide.truncated_never_proven for the shipped verdict). The paragraph on an unbounded name pool ('the verifier MUST NOT return an unsound verdict', reworded under ruling D59 (a) from 'MUST return Unknown rather than an unsound verdict') is this rule together with the soundness blocks NU_050_soundB and NU_050_soundA: a graph that does not close never answers Proven, and a Violated names a class the graph reaches. AC2 is that paragraph's criterion #2 (NUB-1 (a)); its sentence '(NU-050 #2) An unbounded-fresh-name net without a budget place never yields Proven' is not quoted either, since it also says that the graph of every such net does not close, which no line states: the lines give that a graph that does not close answers Unknown or, by the prefix rule, Violated, never Proven, and NU_050_soundB_nonvacuous shows a graph that does not close on one such net at one class bound."
          "Line 3 does not say which violating class a Violated names. The shipped verdict names the first in discovery order, which the spec calls the shortest witness; that and the report line naming the truncation are VER-003's and VER-012's report shape (ruling D40, clash ver-a#11), kind Q here. A Violated is sound for the graph: the class it names is reachable in the graph, not necessarily in the executor, since the graph lets a join fire on any shared name and a consumer take any resident one (clash nu-b#3); completeness against that free-choice name semantics is VER-012's (VD-1 (a)). AC1 (a counterexample that needs two different names to be equal is not reported on the exact path) is this: the graph's classes keep names apart, so a Violated names a class whose names are those of a graph path (line 3 and Decide.prefix_safety_sound); its run against the value-blind encoding is a fixture test (kind Q)."
          "The exactness paragraph's Route B sentence is reworded under ruling D59 (a) and VD-1 (a) from 'exact (sound and complete) whenever the symbolic graph closes' to 'sound for every executor run, and complete for the free-choice name semantics the graph explores': soundness is NU_050_soundB, completeness VER-012's block. Under modelled injection ([VER-006]) Route B declines when a verdict would depend on an environment place: VER-006 AC8 (VER_006_routeB_env, cited by VER-006's block: env_count_frozen and the decline cases of route_b_env_observation), not this block."
  signoff "2026-11-13 27bf729786cbfe08 ai"
  statement : ClassVerdict → Prop :=
    fun V => ∀ (S K L : Type) (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S)
      (p : Novel.RouteB.Decide.Prop' S L),
      (o.stopped = true → V S K L E o p = .unknown) ∧
      (o.stopped = false → (∃ i, Novel.RouteB.Decide.violatesAt E o p i = true) →
        ∃ i, V S K L E o p = .violated i) ∧
      (∀ i, V S K L E o p = .violated i → Novel.RouteB.Decide.violatesAt E o p i = true) ∧
      (o.stopped = false → (∀ i, Novel.RouteB.Decide.violatesAt E o p i = false) →
        V S K L E o p = if o.complete then .proven else .unknown)

/- The pinned readable form of NU_050_prefix: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_050_prefix : ClassVerdict → Prop :=
fun V =>
  ∀ (S K L : Type) (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S) (p : Novel.RouteB.Decide.Prop' S L),
    (o.stopped = true → V S K L E o p = Novel.RouteB.Decide.Verdict.unknown) ∧
      (o.stopped = false →
          (∃ i, Novel.RouteB.Decide.violatesAt E o p i = true) →
            ∃ i, V S K L E o p = Novel.RouteB.Decide.Verdict.violated i) ∧
        (∀ (i : ℕ),
            V S K L E o p = Novel.RouteB.Decide.Verdict.violated i → Novel.RouteB.Decide.violatesAt E o p i = true) ∧
          (o.stopped = false →
            (∀ (i : ℕ), Novel.RouteB.Decide.violatesAt E o p i = false) →
              V S K L E o p =
                if o.complete = true then Novel.RouteB.Decide.Verdict.proven else Novel.RouteB.Decide.Verdict.unknown)
-/
#guard_msgs in #print NU_050_prefix

/-! ### The reference -/

/-- The shipped verdict function satisfies the four lines: a stopped build gives `Unknown`
before any class is read; otherwise the search for the first violating class decides, and with
none the build's `complete` flag chooses between `Proven` and `Unknown` (`Decide.verdict`). -/
@[evidence holds NU_050_prefix]
theorem NU_050_prefix_reference : NU_050_prefix refClassVerdict := by
  intro S K L E o p
  refine ⟨fun hs => ?_, fun hs ⟨j, hj⟩ => ?_, fun i h => ?_, fun hs hv => ?_⟩
  · simp [refClassVerdict, Novel.RouteB.Decide.verdict, hs]
  · simp only [refClassVerdict, Novel.RouteB.Decide.verdict, hs, Bool.false_eq_true, if_false]
    cases hf : (List.range o.cls.length).find? (Novel.RouteB.Decide.violatesAt E o p) with
    | some i => exact ⟨i, rfl⟩
    | none =>
      have := (nu055_find_none_iff E o p).1 hf j
      rw [hj] at this; cases this
  · simp only [refClassVerdict, Novel.RouteB.Decide.verdict] at h
    split at h
    · cases h
    · cases hf : (List.range o.cls.length).find? (Novel.RouteB.Decide.violatesAt E o p) with
      | none =>
        rw [hf] at h
        by_cases hc : o.complete = true <;> simp [hc] at h
      | some j =>
        rw [hf] at h
        cases h
        exact List.find?_some hf
  · simp only [refClassVerdict, Novel.RouteB.Decide.verdict, hs, Bool.false_eq_true, if_false]
    rw [(nu055_find_none_iff E o p).2 hv]

/-! ### A consequence of the lines -/

/-- "*If* the Route B graph does not close, *then* Route B *shall not* answer `Proven`": a verdict
function that meets the lines answers `Proven` only on a build that closed and was not stopped.
A stopped build answers `Unknown` (line 1); a build that was not stopped answers `Violated` when
some class violates (line 2) and, when none does, `Proven` only if it closed (line 4). -/
@[evidence cites "VER-012" "A truncated graph never yields `Proven`"]
theorem NU_050_prefix_never_proven {V : ClassVerdict} (h : NU_050_prefix V) {S K L : Type}
    (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S) (p : Novel.RouteB.Decide.Prop' S L)
    (hP : V S K L E o p = .proven) : o.complete = true ∧ o.stopped = false := by
  obtain ⟨h1, h2, -, h4⟩ := h S K L E o p
  cases hs : o.stopped
  · refine ⟨?_, rfl⟩
    by_cases hv : ∀ i, Novel.RouteB.Decide.violatesAt E o p i = false
    · have := h4 hs hv
      rw [hP] at this
      cases hc : o.complete
      · rw [hc] at this; cases this
      · rfl
    · simp only [not_forall, Bool.not_eq_false] at hv
      obtain ⟨j, hj⟩ := h2 hs hv
      rw [hP] at hj; cases hj
  · have := h1 hs
    rw [hP] at this; cases this

/-- A graph that does not close never answers `Proven`, for every verdict function that meets
the lines. For instance, a build that stored the good class `0` and then reached the class bound
answers `Unknown`, not `Proven`, although no stored class is bad: the classes it never stored may
be. -/
@[evidence cites "NU-050" "If the Route B graph does not close, then Route B shall not answer `Proven` (a consequence of the four lines of NU_050_prefix)", evidence cites "NU-050" "AC2 (NU-050 #2): on a net whose Route B graph does not close, as an unbounded-fresh-name net without a budget place has, the verdict is never Proven; it is Unknown unless a stored class violates the property, and then Violated by the prefix rule. That the graph of every such net does not close is not proven here; NU_050_soundB_nonvacuous shows it for one net at one class bound."]
theorem NU_050_prefix_open_never_proven {V : ClassVerdict} (h : NU_050_prefix V) {S K L : Type}
    (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S) (p : Novel.RouteB.Decide.Prop' S L)
    (hc : o.complete = false) : V S K L E o p ≠ .proven := fun hP => by
  have := (NU_050_prefix_never_proven h E o p hP).1
  rw [hc] at this; cases this

/-! ### Examples: classes are numbers -/

/-- An explorer over number-named classes with no successor: every expanded class is one at
which the net rests. -/
def nu050_E : Explorer ℕ ℕ String := ⟨id, fun _ => 0, fun _ _ => []⟩

/-- The safety property "class `2` is bad". -/
def nu050_pSafe : Novel.RouteB.Decide.Prop' ℕ String := .safety (fun x => x == 2)

/-- The quiescence property "class `2` is bad where the net rests", nothing reapable. -/
def nu050_pQuiet : Novel.RouteB.Decide.Prop' ℕ String := .quiescence (fun x => x == 2) (fun _ => false)

/-- A build that stored the good class `0` and the bad class `2`, expanded neither and stopped
at the class bound: a truncated graph, not stopped. -/
def nu050_trunc : Novel.RouteB.Decide.Out ℕ := ⟨[0, 2], 0, false, false, false⟩

/-- The same stored classes, but the build ran out of budget: a stopped build. -/
def nu050_stopped : Novel.RouteB.Decide.Out ℕ := ⟨[0, 2], 0, false, true, false⟩

/-- A build that stored and expanded the good class `0` only, then reached the class bound. -/
def nu050_truncGood : Novel.RouteB.Decide.Out ℕ := ⟨[0], 1, false, false, false⟩

/-- A build that stored and expanded the classes `0` and `2` and closed. -/
def nu050_closed : Novel.RouteB.Decide.Out ℕ := ⟨[0, 2], 2, true, false, false⟩

/-- A build that stored and expanded the good class `0` only and closed. -/
def nu050_closedGood : Novel.RouteB.Decide.Out ℕ := ⟨[0], 1, true, false, false⟩

/-! ### Violation: a stopped build read for a prefix (line 1) -/

/-- A verdict function that reads a violating class even off a stopped build. -/
def nu050_stoppedPrefix : ClassVerdict := fun _ _ _ E o p =>
  match (List.range o.cls.length).find? (Novel.RouteB.Decide.violatesAt E o p) with
  | some i => .violated i
  | none => if o.complete && !o.stopped then .proven else .unknown

/-- ✗ Reading a stopped build violates NU-050 (line 1): the build that ran out of budget with the
bad class `2` stored is answered `Violated`, where a stopped build must answer `Unknown`,
whatever it stored (VER-013). -/
@[evidence forbids NU_050_prefix]
theorem NU_050_prefix_forbids_stoppedPrefix : ¬ NU_050_prefix nu050_stoppedPrefix := by
  intro h
  have := (h ℕ ℕ String nu050_E nu050_stopped nu050_pSafe).1 rfl
  revert this
  decide

/-! ### Violation: Unknown on every truncated graph (line 2, ruling D59) -/

/-- A verdict function that answers `Unknown` on every graph that did not close: the reading of
the old AC2, "`Unknown`, not `Proven`/`Violated`" (ruling D59 (b)). -/
def nu050_unknownOnTruncation : ClassVerdict := fun _ _ _ E o p =>
  if o.stopped || !o.complete then .unknown else Novel.RouteB.Decide.verdict E o p

/-- ✗ Answering `Unknown` on every truncated graph violates NU-050 (line 2): the truncated build
that stored the bad class `2` is answered `Unknown`, where the prefix rule answers `Violated`. -/
@[evidence forbids NU_050_prefix]
theorem NU_050_prefix_forbids_unknownOnTruncation : ¬ NU_050_prefix nu050_unknownOnTruncation := by
  intro h
  obtain ⟨i, hi⟩ := (h ℕ ℕ String nu050_E nu050_trunc nu050_pSafe).2.1 rfl ⟨1, by decide⟩
  simp [nu050_unknownOnTruncation, nu050_trunc] at hi

/-- Mutant reading of NU-050 under ruling D59 (b): a stopped or truncated build answers
`Unknown`, a `Violated` names a violating class, and a closed build that was not stopped answers
`Violated` when a class violates and `Proven` when none does. -/
def NU_050_prefix_mutant_unknownOnTruncation (V : ClassVerdict) : Prop :=
  ∀ (S K L : Type) (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S)
    (p : Novel.RouteB.Decide.Prop' S L),
    (o.stopped = true ∨ o.complete = false → V S K L E o p = .unknown) ∧
    (∀ i, V S K L E o p = .violated i → Novel.RouteB.Decide.violatesAt E o p i = true) ∧
    (o.stopped = false → o.complete = true →
      ((∃ i, Novel.RouteB.Decide.violatesAt E o p i = true) → ∃ i, V S K L E o p = .violated i) ∧
      ((∀ i, Novel.RouteB.Decide.violatesAt E o p i = false) → V S K L E o p = .proven))

/-- The verdict function that answers `Unknown` on every truncated graph kills the reading of
ruling D59 (b): it meets that reading, but NU-050's prefix rule (line 2) rejects it on a truncated
build that stored a violating class (clash nu-b#1). -/
@[evidence mutant NU_050_prefix]
theorem NU_050_prefix_mutant_unknownOnTruncation_killed :
    NU_050_prefix_mutant_unknownOnTruncation nu050_unknownOnTruncation ∧
      ¬ NU_050_prefix nu050_unknownOnTruncation := by
  refine ⟨fun S K L E o p => ?_, NU_050_prefix_forbids_unknownOnTruncation⟩
  have href := NU_050_prefix_reference S K L E o p
  refine ⟨fun h => ?_, fun i h => ?_, fun hs hc => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rcases h with h | h <;> simp [nu050_unknownOnTruncation, h]
  · simp only [nu050_unknownOnTruncation] at h
    split at h
    · cases h
    · exact href.2.2.1 i h
  · simp only [nu050_unknownOnTruncation, hs, hc, Bool.false_or]
    exact href.2.1 hs hv
  · simp only [nu050_unknownOnTruncation, hs, hc, Bool.false_or]
    have := href.2.2.2 hs hv
    rw [hc] at this
    exact this

/-! ### Violation: a quiescence property read on an unexpanded class (line 3) -/

/-- A verdict function that reads a quiescence property on every stored class, expanded or not,
as if a class whose successors were never computed rested. -/
def nu050_storedQuiescence : ClassVerdict := fun _ _ _ _ o p =>
  let viol : ℕ → Bool := fun i => match p, o.cls[i]? with
    | .safety bad, some x => bad x
    | .quiescence bad _, some x => bad x
    | _, none => false
  if o.stopped then .unknown
  else match (List.range o.cls.length).find? viol with
    | some i => .violated i
    | none => if o.complete then .proven else .unknown

/-- ✗ Reading quiescence on an unexpanded class violates NU-050 (line 3): the truncated build
stored the bad class `2` without expanding it, so nothing is known about its successors; the
verdict function answers `Violated` at class `2`, which does not violate the quiescence property
(design correction S4: only an expanded class witnesses a quiescence violation). -/
@[evidence forbids NU_050_prefix]
theorem NU_050_prefix_forbids_storedQuiescence : ¬ NU_050_prefix nu050_storedQuiescence := by
  intro h
  have := (h ℕ ℕ String nu050_E nu050_trunc nu050_pQuiet).2.2.1 1 (by decide)
  revert this
  decide

/-! ### Violation: a truncated graph read as closed (line 4) -/

/-- A verdict function that reads a graph that did not close as closed: `Proven` when no class
violates. -/
def nu050_closedReading : ClassVerdict := fun _ _ _ E o p =>
  if o.stopped then .unknown
  else match (List.range o.cls.length).find? (Novel.RouteB.Decide.violatesAt E o p) with
    | some i => .violated i
    | none => .proven

/-- ✗ Reading a truncated graph as closed violates NU-050 (line 4): the build that expanded the
good class `0` and then reached the class bound is answered `Proven`, although the classes it
never stored may violate the property. -/
@[evidence forbids NU_050_prefix]
theorem NU_050_prefix_forbids_closedReading : ¬ NU_050_prefix nu050_closedReading := by
  intro h
  have := (h ℕ ℕ String nu050_E nu050_truncGood nu050_pSafe).2.2.2 rfl (by
    intro i; match i with
    | 0 => decide
    | _ + 1 => simp [Novel.RouteB.Decide.violatesAt, nu050_truncGood, nu050_pSafe])
  revert this
  decide

/-! ### The lines exercised -/

/-- ✓ Worked example. Classes are numbers and class `2` is bad. The shipped verdict answers:
`Unknown` for a build that ran out of budget, although it stored class `2`; `Violated` at class
`2` for a build that reached the class bound with class `2` stored, under the safety reading (the
prefix rule), and `Unknown` under the quiescence reading, since class `2` was never expanded;
`Unknown` for a cut build of good classes and `Proven` for a closed one; and `Violated` at class
`2` for a closed build that expanded class `2`, under both readings. -/
@[evidence nonvacuous NU_050_prefix]
theorem NU_050_prefix_nonvacuous :
    refClassVerdict _ _ _ nu050_E nu050_stopped nu050_pSafe = .unknown ∧
      refClassVerdict _ _ _ nu050_E nu050_trunc nu050_pSafe = .violated 1 ∧
      refClassVerdict _ _ _ nu050_E nu050_trunc nu050_pQuiet = .unknown ∧
      refClassVerdict _ _ _ nu050_E nu050_truncGood nu050_pSafe = .unknown ∧
      refClassVerdict _ _ _ nu050_E nu050_closedGood nu050_pSafe = .proven ∧
      refClassVerdict _ _ _ nu050_E nu050_closed nu050_pSafe = .violated 1 ∧
      refClassVerdict _ _ _ nu050_E nu050_closed nu050_pQuiet = .violated 1 := by
  decide

/-! ## NU-050 (B): Route B is sound against the reference executor -/

/-- A ν transition of the reference over the places, values and names Route B reads: places
`PlaceId`, token values `Colour`, names `ℕ`. -/
abbrev NuTransR := NuTrans PlaceId (KeyFn Colour ℕ)

/-- A queue marking of stamped tokens over those places and values. -/
abbrev QMarkR := QMarking PlaceId (Stamped Colour)

/-- One Route B call on a reference ν net: the transitions, the coloured set and the roles the
classifier gave, the class bound, the total-budget oracle and the fuel of the build, and the
initial queue marking. -/
structure RouteBQuery where
  /-- The transitions of the net. -/
  X : List NuTransR
  /-- The coloured set, in the classifier's order. -/
  co : List PlaceId
  /-- The role of each transition. -/
  role : Novel.RouteB.NuTrans → Novel.RouteB.Role
  /-- The class bound. -/
  maxClasses : ℕ
  /-- The total budget or a cancellation: `cut f` stops the build when `f` fuel is left. -/
  cut : ℕ → Bool
  /-- The fuel of the Lean build. -/
  fuel : ℕ
  /-- The initial marking. -/
  M0 : QMarkR

/-- A property read on token counts: a safety property (no reachable marking is bad) or a
quiescence property (no marking at which the net rests is bad). -/
inductive CountProp where
  /-- No reachable marking is bad. -/
  | safety (bad : AMarking → Bool)
  /-- No reachable marking at which the net rests is bad. -/
  | quiescence (bad : AMarking → Bool)

/-- A Route B decider: a verdict for each call and property. -/
abbrev RouteBDecider := RouteBQuery → CountProp → RouteBVerdict

/-- The reapable set Route B is given, by transition name: the names of the reapable
transitions of `X` ([TIME-013], [VER-002]). -/
def reapNames (X : List NuTransR) (s : String) : Bool :=
  X.any fun t => t.base.core.name == s && t.base.reapable

/-- The Route B explorer of a call: the untimed graph of the translated net, conflict priority
off. -/
noncomputable def routeBE (q : RouteBQuery) :=
  Novel.RouteB.routeB (co := q.co) Novel.RouteB.untimedBase (q.X.map NuLink.toNuTransB) q.role false

/-- **The reference Route B decider**: the build from the initial class (with the early stop of
[VER-012] AC5 for a safety property), then `Decide.verdict` for the property. Registered as a
witness model. -/
noncomputable def refRouteB : RouteBDecider := fun q p =>
  match p with
  | .safety bad => Novel.RouteB.Decide.verdict (routeBE q)
      (Novel.RouteB.Decide.build (routeBE q) q.maxClasses q.cut (fun S => bad S.b) true q.fuel
        (Novel.RouteB.initState q.co (qCount q.M0)))
      (.safety fun S => bad S.b)
  | .quiescence bad => Novel.RouteB.Decide.verdict (routeBE q)
      (Novel.RouteB.Decide.build (routeBE q) q.maxClasses q.cut (fun S => bad S.b) false q.fuel
        (Novel.RouteB.initState q.co (qCount q.M0)))
      (.quiescence (fun S => bad S.b) (reapNames q.X))

#spec_witness refRouteB

requirement NU_050_soundB
  id "NU-050"
  title "Exact Verification of Matched Transitions: Route B is sound"
  kind B
  scope "every verifier that offers the Route B name-partition graph (MAY), judged against the reference ν executor, untimed and environment-free"
  source verbatim "spec/12-nu-nets.md"
  covers NU_050.s17, NU_050.s18, NU_050.s14, NU_050.s15, NU_050.s16
  reading "For every call q (a net X of reference ν transitions, its coloured set co, its roles, the build limits and the initial marking M0), every property over token counts and every projection nameOf, where every coloured place of co is empty in M0, co lists each place once, every translated transition is in Route B's fragment for its role (InFragment) and every transition has the shape B1 needs (B1Shape: distinct input places, correlated inputs taking a fixed count, correlated inputs coloured), and where at every marking a contract-keeping run reaches, every key and relay projection of every transition gives each token of its place the name nameOf gives it (NuProj):"
          "if D answers Proven for the safety property bad, then bad is false at the counts of every marking a contract-keeping reference run from M0 reaches;"
          "if, in addition, every correlated input takes at least one token (PosKeys), and D answers Proven for the quiescence property bad, then bad is false at the counts of every marking a contract-keeping reference run from M0 reaches and at which every ν-enabled transition is reapable (NuRests)."
  assumes "The executor is the reference ν firing RefNuFire (Reference/Nu.lean), untimed and environment-free, one atomic firing per step: a run is NuLink.RefNuRunB, a sequence of firings of transitions of X each of whose actions keeps the contract of its role (NuLink.NuContract), the kind A premise 'while the declared mints and the coloured consumers keep their contracts' of the Route A bullet, which the quoted paragraph on coloured writes says holds of both routes, and the mint contract of NU-010 under ruling D78 (a): one fresh name per firing, the same in every coloured place it writes. That NuLink.NuContract at the mint role is that contract is NuLink.nuContract_mint_iff: it is Reference.MintContract with holds = the names the coloured places of the marking hold and wr = the names the firing writes per coloured place, the contract nu010_contract_fresh derives from NU_010_contract with the reference minter (and nu050_mintContracts_agree: Route A's mint contract is the same). A firing whose action breaks the contract is not a step of the run; the spec makes no claim about it (copyingMint_breaks_simulation, cited by NU-010). The projection premise is the paragraph on the one name of a coloured token, read at every marking the run reaches. The timed lines (the join clock, the name-layer restart, the latest-bound relaxation of TIME-013) are the block NU_050_timed, over the timed semantics the graph's classes stand for (RefRouteBT); that the shipped timed graph is sound against it, and so the name x time claim, is still gap R6 of Novel/RouteB/Sound.lean. Environment places and modelled injection are VER-006 AC8's."
          "The decider is Route B alone from the initial class (refRouteB: Decide.build of the untimed graph of the translated net, then Decide.verdict), with no refusal step and no routing: the routing order, the name-blind guard (a verdict of the name-blind encoders on a net with a matched transition is Unknown without a declared budget place or for a quiescence property, apply_nu_guard in smt_verifier.rs) and the declines are the verifier pipeline's. The routing order and part of the guard are the block NU_053_dispatch (no Route B after the colour-slot bound; no Proven of a quiescence property on a ν-net without the coloured plan); the Route B decline under environment injection is cited by VER_006 (VER_006_routeB_env) and test evidence; the refusal order of the name-alignment properties is NU_055_refusal; the rest of the guard (Unknown without a declared budget place) is stated by no block. Conflict-only priority (NU-052) is off: the priority pass is the executor's (RefExec), not one firing's, so the translated net is explored with conflict false (nu.md 1.5)."
          "The premises are hypotheses, one per clause of the EARS sentence: the coloured places start empty (Route B refuses otherwise, nu_scg_verifier.rs, refusal step 7 of NU-055); InFragment, the conditions the classifier establishes (Novel.RouteB.classifyS_inFragment); B1Shape, which every transition that builds and that the classifier accepts as a join meets (CORE-030 AC3, Route B accepts only One and Exactly keys); the projection premise and the contracts (kind A, unchecked by every runtime); PosKeys for quiescence (every join key takes at least one token, which TransitionBuilder::build enforces). co.Nodup says the coloured set is a set. Every input arc is unguarded (IO-006 removed guards: NuLink.guardFree_toNuTransB), so no premise is needed for it."
          "The lines are soundness only: a decider that never answers Proven meets them. That a closed graph none of whose classes violates answers Proven is NU_050_prefix line 4; that the Proven is complete against the free-choice name semantics of the graph is VER-012's block (ruling D59 (a), VD-1 (a)). The holds proof is bridge B1 on contract-keeping runs (NuLink.refNuRunB_names_reach, from NuLink.refNuFire_names_step: every contract-keeping reference firing is a NuStepC step of the translated net) composed with routeB_untimed_safety_sound and routeB_untimed_quiescence_sound; for quiescence a reference rest is an executor rest of the translated net (nu050_execRests_of_nuRests), resting read with the names of the reapable transitions. The lines cover the properties over token counts; the name-layer properties NameAligned and QuiescentNameAligned (NU-055) read the name layer, not the counts, and their soundness against the untimed executor is NU_055_sound's (routeB_untimed_nameAligned_sound, routeB_untimed_quiescentNameAligned_sound)."
          "AC2 (an unbounded-fresh-name net without a budget place never yields Proven; Unknown unless a stored class violates) is NU_050_prefix with these lines: the Route B graph of such a net does not close (refRouteB answers Unknown on it at a class bound, NU_050_soundB_nonvacuous), and a decider that read the cut graph as closed answers Proven where the reference run reaches a violating marking (NU_050_soundB_forbids_truncAsClosed)."
          "AC3 and AC4 (a join on a timed net has a clock only while a name is shared, Route B's earliest firing time) are timed lines, the block NU_050_timed over Route B's timed semantics (RefRouteBT); the shipped Route B timed graph is not modelled in Lean (gap R6), so its graph side is a fixture test (kind Q)."
  signoff "2026-11-13 4939a2769a438e36 ai"
  statement : RouteBDecider → Prop :=
    fun D =>
      (∀ (q : RouteBQuery) (bad : AMarking → Bool) (nameOf : Colour → ℕ),
        q.co.Nodup → (∀ T ∈ q.X.map NuLink.toNuTransB, Novel.RouteB.InFragment q.co T (q.role T)) →
        (∀ t ∈ q.X, NuLink.B1Shape q.co t) → (∀ p ∈ q.co, q.M0 p = []) →
        (∀ M, NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → ∀ t ∈ q.X, NuLink.NuProj nameOf t M) →
        D q (.safety bad) = .proven →
        ∀ M, NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → bad (qCount M) = false) ∧
      (∀ (q : RouteBQuery) (bad : AMarking → Bool) (nameOf : Colour → ℕ),
        q.co.Nodup → (∀ T ∈ q.X.map NuLink.toNuTransB, Novel.RouteB.InFragment q.co T (q.role T)) →
        (∀ T ∈ q.X.map NuLink.toNuTransB, Novel.RouteB.PosKeys (q.role T)) →
        (∀ t ∈ q.X, NuLink.B1Shape q.co t) → (∀ p ∈ q.co, q.M0 p = []) →
        (∀ M, NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → ∀ t ∈ q.X, NuLink.NuProj nameOf t M) →
        D q (.quiescence bad) = .proven →
        ∀ M, NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → NuRests q.X M → bad (qCount M) = false)

/- The pinned readable form of NU_050_soundB: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_050_soundB : RouteBDecider → Prop :=
fun D =>
  (∀ (q : RouteBQuery) (bad : AMarking → Bool) (nameOf : Colour → ℕ),
      q.co.Nodup →
        (∀ T ∈ List.map NuLink.toNuTransB q.X, Novel.RouteB.InFragment q.co T (q.role T)) →
          (∀ t ∈ q.X, NuLink.B1Shape q.co t) →
            (∀ p ∈ q.co, q.M0 p = []) →
              (∀ (M : QMarking PlaceId (Stamped Colour)),
                  NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → ∀ t ∈ q.X, NuLink.NuProj nameOf t M) →
                D q (CountProp.safety bad) = Novel.RouteB.Decide.Verdict.proven →
                  ∀ (M : QMarking PlaceId (Stamped Colour)),
                    NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → bad (qCount M) = false) ∧
    ∀ (q : RouteBQuery) (bad : AMarking → Bool) (nameOf : Colour → ℕ),
      q.co.Nodup →
        (∀ T ∈ List.map NuLink.toNuTransB q.X, Novel.RouteB.InFragment q.co T (q.role T)) →
          (∀ T ∈ List.map NuLink.toNuTransB q.X, Novel.RouteB.PosKeys (q.role T)) →
            (∀ t ∈ q.X, NuLink.B1Shape q.co t) →
              (∀ p ∈ q.co, q.M0 p = []) →
                (∀ (M : QMarking PlaceId (Stamped Colour)),
                    NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → ∀ t ∈ q.X, NuLink.NuProj nameOf t M) →
                  D q (CountProp.quiescence bad) = Novel.RouteB.Decide.Verdict.proven →
                    ∀ (M : QMarking PlaceId (Stamped Colour)),
                      NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → NuRests q.X M → bad (qCount M) = false
-/
#guard_msgs in #print NU_050_soundB

/-! ### The reference -/

/-- A name Route B's executor accepts for a translated matched transition is eligible for the
reference selection: the converse of `NuLink.selectable_of_eligible`. -/
theorem nu050_eligible_of_selectable {co : List PlaceId} {nameOf : Colour → ℕ} {t : NuTransR}
    {ms : MatchSpec PlaceId (KeyFn Colour ℕ)} {M : QMarkR} {n : ℕ} (hm : t.mspec = some ms)
    (hsh : NuLink.B1Shape co t) (hproj : NuLink.NuProj nameOf t M)
    (hsel : Novel.RouteB.Selectable co (NuLink.toNuTransB t)
      (Novel.RouteB.nameLayer co nameOf (NuLink.vals M)) n) :
    eligible (matchIn ms t M) n = true := by
  have hmo : NuLink.msOf t = ms := by simp [NuLink.msOf, hm]
  obtain ⟨hne, hall⟩ := hsel ms.keyPlaces (by simp [NuLink.toNuTransB, hm])
  unfold eligible matchIn
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_eq_false_iff, List.mem_map]
  refine ⟨fun he => hne (by simpa [MatchSpec.keyPlaces] using he), ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hp : k.1 ∈ ms.keyPlaces := List.mem_map.2 ⟨k, hk, rfl⟩
  have hcol := hsh.keysColoured k.1 (by rw [hmo]; exact hp)
  have hpr := hproj k (by rw [hmo]; exact List.mem_append_left _ hk)
  obtain ⟨h1, h2⟩ := hall k.1 hp
  rw [NuLink.cnt_vals_mem hcol, ← NuLink.named_length_eq_count hpr] at h1 h2
  rw [NuLink.keyReq_toNuTransB] at h2
  simp only [NuLink.stamps_length]
  exact ⟨h1, h2⟩

/-- **A reference rest is an executor rest of the translated net**: where every ν-enabled
transition of `X` is reapable, every transition Route B's executor model can fire is reapable by
name. -/
theorem nu050_execRests_of_nuRests {co : List PlaceId} {nameOf : Colour → ℕ}
    {X : List NuTransR} {M : QMarkR} (hsh : ∀ t ∈ X, NuLink.B1Shape co t)
    (hproj : ∀ t ∈ X, NuLink.NuProj nameOf t M) (h : NuRests X M) :
    Novel.RouteB.ExecRests (co := co) (nameOf := nameOf) (net := X.map NuLink.toNuTransB)
      (reapNames X) (NuLink.vals M) := by
  intro T hT hen
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
  have hnu : NuEnabled t M := by
    refine ⟨?_, fun ms hm => ?_⟩
    · have h1 := hen.1
      show Enabled t.base (qCount M)
      unfold Enabled
      rw [NuLink.qCount_eq_alpha, ← Link.enabledC_toTransition]
      exact h1
    · obtain ⟨n, hn⟩ := hen.2 ms.keyPlaces (by simp [NuLink.toNuTransB, hm])
      exact ⟨n, nu050_eligible_of_selectable hm (hsh t ht) (hproj t ht) hn⟩
  have hr := h t ht hnu
  show reapNames X t.base.core.name = true
  exact List.any_eq_true.2 ⟨t, ht, by simp [hr]⟩

/-- The reference Route B decider satisfies NU-050's soundness lines: B1 makes every
contract-keeping reference run a run of Route B's executor model on the translated net, and Route
B's untimed soundness theorems then carry a `Proven` to every marking that run reaches (and, for
quiescence, rests at). -/
@[evidence holds NU_050_soundB]
theorem NU_050_soundB_reference : NU_050_soundB refRouteB := by
  refine ⟨fun q bad nameOf hco hfr hsh hempty hproj hP M hM => ?_,
    fun q bad nameOf hco hfr hpos hsh hempty hproj hP M hM hrest => ?_⟩
  · have hR := NuLink.refNuRunB_names_reach hsh hproj hM
    have he : ∀ i : Fin q.co.length, NuLink.vals q.M0 q.co[i.1] = [] := by
      intro i; simp [NuLink.vals, hempty _ (List.getElem_mem i.2)]
    simp only [refRouteB, routeBE, NuLink.qCount_eq_alpha] at hP
    rw [NuLink.qCount_eq_alpha]
    exact Novel.RouteB.routeB_untimed_safety_sound hco hfr (NuLink.guardFree_toNuTransB q.X) he
      hP hR
  · have hR := NuLink.refNuRunB_names_reach hsh hproj hM
    have he : ∀ i : Fin q.co.length, NuLink.vals q.M0 q.co[i.1] = [] := by
      intro i; simp [NuLink.vals, hempty _ (List.getElem_mem i.2)]
    simp only [refRouteB, routeBE, NuLink.qCount_eq_alpha] at hP
    rw [NuLink.qCount_eq_alpha]
    exact Novel.RouteB.routeB_untimed_quiescence_sound hco hfr hpos
      (NuLink.guardFree_toNuTransB q.X) he hP hR
      (nu050_execRests_of_nuRests hsh (hproj M hM) hrest)

/-! ### Examples: a mint drawing on a budget of two -/

/-- The example transition: a mint that takes one token from the budget place `1` and writes one
token to the coloured place `0`; no match, not reapable. -/
def nu050_tM : NuTransR where
  base :=
    { core := { name := "mint", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] }
      out := some (.place 0) }
  mspec := none

/-- The initial marking: two budget tokens in place `1`, nothing else. -/
def nu050_M0 : QMarkR := fun p => if p = 1 then [⟨7, 0⟩, ⟨8, 1⟩] else []

/-- The first mint writes the name `10`. -/
def nu050_e1 : List (PlaceId × Stamped Colour) := [(0, ⟨10, 2⟩)]

/-- The second mint writes the name `11`. -/
def nu050_e2 : List (PlaceId × Stamped Colour) := [(0, ⟨11, 3⟩)]

/-- The marking after the first mint. -/
def nu050_M1 : QMarkR := qFire nu050_M0 nu050_tM.base nu050_e1

/-- The marking after the second mint. -/
def nu050_M2 : QMarkR := qFire nu050_M1 nu050_tM.base nu050_e2

theorem nu050_fire1 :
    RefNuFire nu050_tM nu050_M0 none (qDelivered nu050_M0 nu050_tM.base) nu050_e1 nu050_M1 :=
  (refNuFire_restrictsTo nu050_tM rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

theorem nu050_fire2 :
    RefNuFire nu050_tM nu050_M1 none (qDelivered nu050_M1 nu050_tM.base) nu050_e2 nu050_M2 :=
  (refNuFire_restrictsTo nu050_tM rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- The run of the example under Route B's mint contract: both mints write a name no coloured
place holds. -/
theorem nu050_runB1 :
    NuLink.RefNuRunB [0] id (fun _ => .mint) [nu050_tM] nu050_M0 nu050_M1 :=
  Relation.ReflTransGen.single ⟨nu050_tM, List.mem_singleton_self _, none, _, _, nu050_fire1,
    ⟨10, by decide, by decide⟩⟩

theorem nu050_runB2 :
    NuLink.RefNuRunB [0] id (fun _ => .mint) [nu050_tM] nu050_M0 nu050_M2 :=
  nu050_runB1.tail ⟨nu050_tM, List.mem_singleton_self _, none, _, _, nu050_fire2,
    ⟨11, by decide, by decide⟩⟩

theorem nu050_M1_count : qCount nu050_M1 0 = 1 := by decide

theorem nu050_M2_count : qCount nu050_M2 0 = 2 := by decide

/-- After the two mints the budget is spent and the mint is not ν-enabled: the net rests. -/
theorem nu050_M2_rests : NuRests [nu050_tM] nu050_M2 := by
  intro t ht hen
  simp only [List.mem_singleton] at ht
  subst ht
  have := hen.1
  revert this
  decide

/-- The Route B call on the example: coloured set `[0]`, the mint role, a class bound of one
class. -/
def nu050_qB : RouteBQuery :=
  ⟨[nu050_tM], [0], fun _ => .mint, 1, fun _ => false, 3, nu050_M0⟩

theorem nu050_qB_fragment :
    ∀ T ∈ nu050_qB.X.map NuLink.toNuTransB, Novel.RouteB.InFragment nu050_qB.co T (nu050_qB.role T) := by
  intro T hT
  simp only [nu050_qB, List.map_cons, List.map_nil, List.mem_singleton] at hT
  subst hT
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩ <;>
    simp [NuLink.toNuTransB, NuLink.outRows, nu050_tM, Link.toTransition, Link.toInSpec,
      Out.branches, Out.findTimeout, Novel.RouteB.idx]
  decide

theorem nu050_qB_shape : ∀ t ∈ nu050_qB.X, NuLink.B1Shape nu050_qB.co t := by
  intro t ht
  simp only [nu050_qB, List.mem_singleton] at ht
  subst ht
  exact ⟨by decide, by simp [NuLink.msOf, nu050_tM, MatchSpec.keyPlaces],
    by simp [NuLink.msOf, nu050_tM, MatchSpec.keyPlaces]⟩

theorem nu050_qB_proj (nameOf : Colour → ℕ) :
    ∀ M, NuLink.RefNuRunB nu050_qB.co nameOf nu050_qB.role nu050_qB.X nu050_qB.M0 M →
      ∀ t ∈ nu050_qB.X, NuLink.NuProj nameOf t M := by
  intro M _ t ht k hk
  simp only [nu050_qB, List.mem_singleton] at ht
  subst ht
  simp [NuLink.msOf, nu050_tM] at hk

theorem nu050_qB_empty : ∀ p ∈ nu050_qB.co, nu050_qB.M0 p = [] := by decide

/-- "At least one name in place `0`", as a property over counts. -/
def nu050_bad1 : AMarking → Bool := fun a => decide (1 ≤ a 0)

/-- "Two names in place `0`", as a property over counts. -/
def nu050_bad2 : AMarking → Bool := fun a => decide (2 ≤ a 0)

/-! ### Violation: a cut graph read as closed -/

/-- A Route B decider that reads a graph that did not close as closed: the reference build, then
the verdict function `nu050_closedReading`. -/
noncomputable def nu050_truncAsClosed : RouteBDecider := fun q p =>
  match p with
  | .safety bad => nu050_closedReading _ _ _ (routeBE q)
      (Novel.RouteB.Decide.build (routeBE q) q.maxClasses q.cut (fun S => bad S.b) true q.fuel
        (Novel.RouteB.initState q.co (qCount q.M0)))
      (.safety fun S => bad S.b)
  | .quiescence bad => nu050_closedReading _ _ _ (routeBE q)
      (Novel.RouteB.Decide.build (routeBE q) q.maxClasses q.cut (fun S => bad S.b) false q.fuel
        (Novel.RouteB.initState q.co (qCount q.M0)))
      (.quiescence (fun S => bad S.b) (reapNames q.X))

theorem nu050_truncAsClosed_safety : nu050_truncAsClosed nu050_qB (.safety nu050_bad1) = .proven := by
  decide

theorem nu050_truncAsClosed_quiescence :
    nu050_truncAsClosed nu050_qB (.quiescence nu050_bad2) = .proven := by
  decide

/-- ✗ Reading a cut graph as closed violates NU-050's Route B safety line. With a class bound of
one class, the graph of the example stops after the initial class, where place `0` is empty;
the decider answers `Proven` for "place `0` never holds a name", yet the first mint puts a name
there. -/
@[evidence forbids NU_050_soundB]
theorem NU_050_soundB_forbids_truncAsClosed : ¬ NU_050_soundB nu050_truncAsClosed := by
  intro h
  have := h.1 nu050_qB nu050_bad1 id (by decide) nu050_qB_fragment nu050_qB_shape nu050_qB_empty
    (nu050_qB_proj id) nu050_truncAsClosed_safety nu050_M1 nu050_runB1
  revert this
  decide

/-- ✗ Reading a cut graph as closed violates NU-050's Route B quiescence line too. The decider
answers `Proven` for "where the net rests, place `0` holds fewer than two names", yet after the
two mints the budget is spent, the net rests, and place `0` holds the names `10` and `11`. -/
@[evidence forbids NU_050_soundB]
theorem NU_050_soundB_forbids_truncAsClosed_quiescence : ¬ NU_050_soundB nu050_truncAsClosed := by
  intro h
  have := h.2 nu050_qB nu050_bad2 id (by decide) nu050_qB_fragment
    (fun T _ cin rel hr => by simp [nu050_qB] at hr) nu050_qB_shape nu050_qB_empty
    (nu050_qB_proj id) nu050_truncAsClosed_quiescence nu050_M2 nu050_runB2 nu050_M2_rests
  revert this
  decide

/-- The Route B call on the empty net over the coloured set `[0]`, class bound two. -/
def nu050_qEmpty : RouteBQuery := ⟨[], [0], fun _ => .ordinary, 2, fun _ => false, 3, fun _ => []⟩

/-- ✓ Worked example. On the empty net the Route B graph closes with one class, and Route B
answers `Proven` for "place `0` never holds a name", for both readings. On a mint that draws on a
budget of two, with a class bound of one class, the graph does not close and Route B answers
`Unknown` (AC2's case: the graph is cut before it finds the names). The safety line rules out
`Proven` there, because a run in which each mint writes a fresh name reaches a marking with a
name in place `0`. -/
@[evidence nonvacuous NU_050_soundB]
theorem NU_050_soundB_nonvacuous :
    refRouteB nu050_qEmpty (.safety nu050_bad1) = .proven ∧
      refRouteB nu050_qEmpty (.quiescence nu050_bad1) = .proven ∧
      refRouteB nu050_qB (.safety nu050_bad1) = .unknown ∧
      refRouteB nu050_qB (.safety nu050_bad1) ≠ .proven := by
  refine ⟨by decide, by decide, by decide, fun hP => ?_⟩
  have := NU_050_soundB_reference.1 nu050_qB nu050_bad1 id (by decide) nu050_qB_fragment
    nu050_qB_shape nu050_qB_empty (nu050_qB_proj id) hP nu050_M1 nu050_runB1
  revert this
  decide

/-! ## NU-050 (B): Route A is sound against the reference executor -/

/-- A Route A plan builder (`build_plan`): from the place count, the coloured places, the fragment
mode (EXTENDED or not), the initial count marking, the simplex's answer and the flat rows with
their match information, the colour-slot bound `k` and the classified rows, or no plan. -/
abbrev RouteAPlanner : Type :=
  ℕ → List PlaceId → Bool → AMarking → Option (ℕ × Weight) → List Novel.RouteA.SrcRow →
    Option (ℕ × List Novel.RouteA.CRow)

/-- **The reference plan builder**: the shipped `build_plan` (`Novel.RouteA.buildPlan`), with the
checked colour-slot bound of [NU-053] whatever the simplex answers. Registered as a witness
model. -/
def refRouteAPlan : RouteAPlanner := fun n C ext a0 ans src => Novel.RouteA.buildPlan n C ext a0 ans src

#spec_witness refRouteAPlan

requirement NU_050_soundA
  id "NU-050"
  title "Exact Verification of Matched Transitions: Route A is sound"
  kind B
  scope "every verifier that offers the Route A coloured encoding (MAY), judged against the reference ν executor, untimed and environment-free"
  source verbatim "spec/12-nu-nets.md"
  covers NU_050.s1, NU_050.s19, NU_050.s20
  reading "For every plan builder P, and for every place count n, coloured places C, mode ext, simplex answer ans, flat source rows src (as build_plan receives them), invariants invs, projection nameOf, net X of reference ν transitions and initial marking M0, where P answers the plan (k, rows) for the counts of M0, C lists each place once and below n, every consume-all input arc of src is unguarded, every invariant is zero on the nonlinear places of src and conserved by every source row, every firing of a transition of X from a marking a contract-keeping run reaches has a source row (SrcCovers: a row of src that is the row of the firing's transition and deposit, whose class under build_plan's rule fits the match), and at every such marking every key and relay projection gives each token of its place the name nameOf gives it (ProjCoherent); a contract-keeping run (NuLinkA.RefNuRunA) is a sequence of reference firings each of whose actions keeps the contract of the class build_plan's rule gives its source rows (srcClass), so the run and the premises read src and not the plan P returns:"
          "if no state the shipped coloured encoding of the plan reaches has its all-colour counts in Bad (a Proven of the encoding), then no marking a contract-keeping reference run from M0 reaches has its counts in Bad;"
          "if, in addition, the input places of every source row are distinct, every source row comes from a transition of X whose match its class fits (SrcFrom), no transition of X is reapable, and no state the shipped coloured encoding reaches is quiescent (DeadE) with its all-colour counts in Q, then no marking a contract-keeping reference run reaches and rests at (NuRests) has its counts in Q."
  assumes "The model is the plan builder P (build_plan: the coloured set, the classification of every flat row, the checked colour-slot bound of NU-053, the refusals), with the shipped coloured encoding (Novel.RouteA.Enc.shipped, encode_coloured) fixed: a Proven of the encoding is read as its meaning, that no state the encoding's Reachable relation holds is bad (the solver is outside Lean), as in Novel.RouteA.routeA_safety_sound_plan. The executor is the reference ν firing RefNuFire, untimed and environment-free; a run is NuLinkA.RefNuRunA, a sequence of firings each of whose actions keeps the contract of the class build_plan's classification rule gives its source row (NuLinkA.srcClass: classifyRowG under the shipped gates; NuLinkA.NuContract; NU-010's mint contract under ruling D78 (a), NU-051's consumer contract), the premise 'while the declared mints and the coloured consumers keep their contracts' of the quoted sentence. That NuLinkA.NuContract at a mint class is NU-010's contract is NuLinkA.nuContract_mint_iff: it is Reference.MintContract, the contract nu010_contract_fresh derives from NU_010_contract with the reference minter, and Route B's mint contract is the same (nu050_mintContracts_agree). A source row the rule refuses carries no contract, since no declared mint or coloured consumer is read there; the shipped build_plan then refuses the plan."
          "Ruling D59 (a) and NUB-2 (a) (clash nu-b#2): the fragment of Route A is 'a colour-slot bound exists' ([NU-053]), not budget conservation; the bullet is reworded so, and 'the initial budget k' and the refund example are dropped. The budget count is not a sound bound (Novel.RouteA.Retro.budget_k_false_proven): a planner with a fixed bound of one slot, the bound a budget of one would give, is killed here (NU_050_soundA_forbids_slotOne) on a mint drawing on a budget of two, which reaches two live names."
          "The premises are hypotheses, and none reads the plan P returns. The rows premise (SrcCovers: every firing of the run has a source row) stands for the computation of the flat rows and the coloured set from the net (net_flattener, the coloured-set computation), which the Lean model takes as given, as Novel/RouteA/Plan.lean does; the guard, invariant and coloured-set premises are what the verifier checks before the encoding (buildPlan_premisesS). That the plan carries a classified row for every source row, with the class the rule gives, is a property of the shipped build_plan (NuLinkA.buildPlan_src), not a premise: a planner that leaves out a row (for instance an undeclared mint skipped where build_plan refuses the plan) still faces that row's firings in the premises and the run, and its Proven of the encoding without the row is unsound there (NU_050_soundA_forbids_dropRow). The projection premise is the paragraph on the one name of a coloured token, which the quoted paragraph on coloured writes applies to both routes."
          "The quiescence line is stated for a net with no reapable transition, the strict quiescence DeadE of the shipped build_plan path (Novel.RouteA.routeA_quiescence_sound_plan). The reaping-aware form (DeadER over the reapable rows, NuLinkA.refNu_routeA_quiescence_sound_reaping) reads the reapable rows by transition, where the shipped encoder reads them by name (DeadERs, NU-053 line 6); the tie between the two waits for row names (open item of bridge B2) and is not a line here."
          "The lines are soundness only: a planner that never answers meets them (the fallback to the over-approximation is the pipeline's: NU_053_dispatch says that without the coloured plan a quiescence property is never Proven, and no block states the rest of the fallback). That a plan is built whenever a colour-slot bound exists is NU-053 line 2. Completeness of Route A (NU-053 AC3, agreement with Route B on the fixtures) is kind Q."
          "AC1 (a counterexample that needs two different names to be equal is not reported on the exact path) is the colour discipline of the encoding: a join consumes the same colour from every correlated input (sJoin), so the coloured encoding has no step that equates two names; NU_053 line 5 and the join rule of Novel.RouteA.ColourStep. Its run against the value-blind encoding is a fixture test (kind Q)."
  signoff "2026-11-13 28d84939f14ecd69 ai"
  statement : RouteAPlanner → Prop :=
    fun P =>
      (∀ (n : ℕ) (C : List PlaceId) (ext : Bool) (ans : Option (ℕ × Weight))
        (src : List Novel.RouteA.SrcRow) (k : ℕ) (rows : List Novel.RouteA.CRow)
        (invs : List Weight) (nameOf : Colour → ℕ) (X : List NuTransR) (M0 : QMarkR)
        (Bad : AMarking → Prop),
        P n C ext (qCount M0) ans src = some (k, rows) → C.Nodup → (∀ p ∈ C, p < n) →
        (∀ s ∈ src, GuardFreeConsumeAll s.t) →
        (∀ y ∈ invs, ∀ s ∈ src,
          ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0) →
        NuLinkA.SrcCovers C ext nameOf X src M0 →
        (∀ M, NuLinkA.RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, NuLinkA.ProjCoherent nameOf t M) →
        (∀ e, Novel.RouteA.ReachE (Novel.RouteA.Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e →
          ¬ Bad (Novel.RouteA.agg C k e)) →
        ∀ M, NuLinkA.RefNuRunA C ext nameOf X src M0 M → ¬ Bad (qCount M)) ∧
      (∀ (n : ℕ) (C : List PlaceId) (ext : Bool) (ans : Option (ℕ × Weight))
        (src : List Novel.RouteA.SrcRow) (k : ℕ) (rows : List Novel.RouteA.CRow)
        (invs : List Weight) (nameOf : Colour → ℕ) (X : List NuTransR) (M0 : QMarkR)
        (Q : AMarking → Prop),
        P n C ext (qCount M0) ans src = some (k, rows) → C.Nodup → (∀ p ∈ C, p < n) →
        (∀ s ∈ src, GuardFreeConsumeAll s.t) →
        (∀ y ∈ invs, ∀ s ∈ src,
          ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0) →
        NuLinkA.SrcCovers C ext nameOf X src M0 →
        (∀ M, NuLinkA.RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, NuLinkA.ProjCoherent nameOf t M) →
        (∀ s ∈ src, InputsDistinctPlaces s.t) → NuLinkA.SrcFrom C ext X src →
        (∀ t ∈ X, t.base.reapable = false) →
        (∀ e, Novel.RouteA.ReachE (Novel.RouteA.Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e →
          ¬ (Novel.RouteA.DeadE (Novel.RouteA.Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e ∧
            Q (Novel.RouteA.agg C k e))) →
        ∀ M, NuLinkA.RefNuRunA C ext nameOf X src M0 M → NuRests X M → ¬ Q (qCount M))

/- The pinned readable form of NU_050_soundA: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_050_soundA : RouteAPlanner → Prop :=
fun P =>
  (∀ (n : ℕ) (C : List PlaceId) (ext : Bool) (ans : Option (ℕ × Weight)) (src : List Novel.RouteA.SrcRow) (k : ℕ)
      (rows : List Novel.RouteA.CRow) (invs : List Weight) (nameOf : Colour → ℕ) (X : List NuTransR) (M0 : QMarkR)
      (Bad : AMarking → Prop),
      P n C ext (qCount M0) ans src = some (k, rows) →
        C.Nodup →
          (∀ p ∈ C, p < n) →
            (∀ s ∈ src, GuardFreeConsumeAll s.t) →
              (∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0) →
                NuLinkA.SrcCovers C ext nameOf X src M0 →
                  (∀ (M : QMarking PlaceId (Stamped Colour)),
                      NuLinkA.RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, NuLinkA.ProjCoherent nameOf t M) →
                    (∀ (e : Novel.RouteA.EState),
                        Novel.RouteA.ReachE
                            { C := C, k := k, n := n, rows := rows, invs := invs, a0 := qCount M0 }.shipped e →
                          ¬Bad (Novel.RouteA.agg C k e)) →
                      ∀ (M : QMarking PlaceId (Stamped Colour)),
                        NuLinkA.RefNuRunA C ext nameOf X src M0 M → ¬Bad (qCount M)) ∧
    ∀ (n : ℕ) (C : List PlaceId) (ext : Bool) (ans : Option (ℕ × Weight)) (src : List Novel.RouteA.SrcRow) (k : ℕ)
      (rows : List Novel.RouteA.CRow) (invs : List Weight) (nameOf : Colour → ℕ) (X : List NuTransR) (M0 : QMarkR)
      (Q : AMarking → Prop),
      P n C ext (qCount M0) ans src = some (k, rows) →
        C.Nodup →
          (∀ p ∈ C, p < n) →
            (∀ s ∈ src, GuardFreeConsumeAll s.t) →
              (∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0) →
                NuLinkA.SrcCovers C ext nameOf X src M0 →
                  (∀ (M : QMarking PlaceId (Stamped Colour)),
                      NuLinkA.RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, NuLinkA.ProjCoherent nameOf t M) →
                    (∀ s ∈ src, InputsDistinctPlaces s.t) →
                      NuLinkA.SrcFrom C ext X src →
                        (∀ t ∈ X, t.base.reapable = false) →
                          (∀ (e : Novel.RouteA.EState),
                              Novel.RouteA.ReachE
                                  { C := C, k := k, n := n, rows := rows, invs := invs, a0 := qCount M0 }.shipped e →
                                ¬(Novel.RouteA.DeadE
                                      { C := C, k := k, n := n, rows := rows, invs := invs, a0 := qCount M0 }.shipped
                                      e ∧
                                    Q (Novel.RouteA.agg C k e))) →
                            ∀ (M : QMarking PlaceId (Stamped Colour)),
                              NuLinkA.RefNuRunA C ext nameOf X src M0 M → NuRests X M → ¬Q (qCount M)
-/
#guard_msgs in #print NU_050_soundA

/-! ### The reference -/

/-- The reference plan builder satisfies NU-050's Route A soundness lines: B2 on contract-keeping
runs (`NuLinkA.refNuRunA_routeA_reach`) makes every run read off the source rows a Route A ν run
over the rows of the shipped plan, which carries a classified row for every source row
(`NuLinkA.buildPlan_src`), and Route A's soundness from the shipped `build_plan` carries a
`Proven` of the encoding to every marking that run reaches (and, for quiescence, rests at). -/
@[evidence holds NU_050_soundA]
theorem NU_050_soundA_reference : NU_050_soundA refRouteAPlan :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hP hnd hC hG hinv hcov hcoh hpr =>
      NuLinkA.refNuRunA_routeA_safety_sound_plan hP hnd hC hG hinv hcov hcoh hpr,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hP hnd hC hG hinv hcov hcoh hd hsrc hnr hpr =>
      NuLinkA.refNuRunA_routeA_quiescence_sound_plan hP hnd hC hG hinv hcov hcoh hd hsrc hnr hpr⟩

/-- Both routes read one mint contract: Route B's at the mint role (`NuLink.NuContract`) and
Route A's at a mint class (`NuLinkA.NuContract`) are both `Reference.MintContract`, the contract
of [NU-010] under ruling D78 (a). For instance, a mint that writes the name `10` into place `0`
while no coloured place holds `10` keeps both, and one that writes `10` while place `0` already
holds it keeps neither. -/
theorem nu050_mintContracts_agree (co : List PlaceId) (nameOf : Colour → ℕ) (t : NuTransR)
    (outs : List PlaceId) (M : QMarkR) (δ : QDelivered PlaceId (Stamped Colour))
    (e : List (PlaceId × Stamped Colour)) :
    NuLink.NuContract co nameOf .mint t M δ e ↔ NuLinkA.NuContract co nameOf (.mint outs) M δ e :=
  (NuLink.nuContract_mint_iff co nameOf t M δ e).trans
    (NuLinkA.nuContract_mint_iff co nameOf outs M δ e).symm

/-! ### Examples: the mint drawing on a budget of two, read by Route A -/

/-- The flat row of the example mint as `build_plan` receives it: no match, a declared mint, no
timeout write. -/
def nu050_s : Novel.RouteA.SrcRow := ⟨Link.toTransition nu050_tM.base.core, [0], none, true, []⟩

/-- The source rows of the example: the declared mint's row. -/
def nu050_src : List Novel.RouteA.SrcRow := [nu050_s]

/-- The classified row of the example mint: a mint into the coloured place `0`. -/
def nu050_rM : Novel.RouteA.CRow := ⟨Link.toTransition nu050_tM.base.core, [0], .mint [0]⟩

/-- The same flat row from a transition that is NOT declared a mint. -/
def nu050_sU : Novel.RouteA.SrcRow := ⟨Link.toTransition nu050_tM.base.core, [0], none, false, []⟩

/-- The source rows of the undeclared example. -/
def nu050_srcU : List Novel.RouteA.SrcRow := [nu050_sU]

/-- Every source row that is the example mint's flat row has no unguarded consume-all arc. -/
theorem nu050_guard {src : List Novel.RouteA.SrcRow}
    (h : ∀ s ∈ src, s.t = Link.toTransition nu050_tM.base.core) :
    ∀ s ∈ src, GuardFreeConsumeAll s.t := by
  intro s hs x hx _
  rw [h s hs] at hx
  exact Link.guardNone_toTransition _ x hx

theorem nu050_rM_ok : Novel.RouteA.ClassOK [0] nu050_rM := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [List.mem_singleton] at hp
    subst hp
    simp [nu050_rM, Link.toTransition, Link.toInSpec, nu050_tM, consumeAllAt, specAt]
  · refine ⟨by simp, by simp, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp
    subst hp
    simp [nu050_rM, Link.toTransition, Link.toInSpec, nu050_tM, pre, specAt]

theorem nu050_conA1 : NuLinkA.NuContract [0] id nu050_rM.cls nu050_M0
    (qDelivered nu050_M0 nu050_tM.base) nu050_e1 := ⟨10, by decide, by decide⟩

theorem nu050_conA2 : NuLinkA.NuContract [0] id nu050_rM.cls nu050_M1
    (qDelivered nu050_M1 nu050_tM.base) nu050_e2 := ⟨11, by decide, by decide⟩

/-- Every firing of the example mint deposits into place `0` only: its one output branch. -/
theorem nu050_dep {M : QMarkR} {c δ e M'} (hf : RefNuFire nu050_tM M c δ e M') :
    e.map Prod.fst = [0] := by
  obtain ⟨-, -, ⟨ch, hch⟩, -, -⟩ := (refNuFire_restrictsTo nu050_tM rfl M c δ e M').1 hf
  cases ch with
  | action i =>
    match i, hch with
    | 0, hch => simpa [Reference.deposit, nu050_tM, Out.branches] using hch.symm
    | _ + 1, hch => simp [Reference.deposit, nu050_tM, Out.branches] at hch
  | timedOut j => simp [Reference.deposit, nu050_tM, Out.findTimeout] at hch

/-- The rule classifies the declared mint's source row as a mint into place `0`. -/
theorem nu050_src_class : NuLinkA.srcClass [0] false nu050_s = some (.mint [0]) := by
  decide

/-- The rule refuses the undeclared row: it writes a coloured place and is not declared. -/
theorem nu050_srcU_class : NuLinkA.srcClass [0] false nu050_sU = none := by
  decide

/-- The source row is a source row of every firing of the example mint (when the rule gives it a
class, a mint class, which fits a transition without a match). -/
theorem nu050_srcRowOf {s : Novel.RouteA.SrcRow} (hs : s.t = Link.toTransition nu050_tM.base.core)
    (hd : s.d = [0]) (hfit : ∀ cls, NuLinkA.srcClass [0] false s = some cls → cls = .mint [0])
    {M : QMarkR} {c δ e M'} (hf : RefNuFire nu050_tM M c δ e M') :
    NuLinkA.SrcRowOf [0] false nu050_tM (e.map Prod.fst) s :=
  ⟨hs, fun p => by rw [hd, nu050_dep hf], fun cls hc => by rw [hfit cls hc]; rfl⟩

/-- Every firing of the example mint, from any marking, has a source row in `src`, for both
example source lists. -/
theorem nu050_covers {src : List Novel.RouteA.SrcRow} (hne : src ≠ [])
    (h : ∀ s ∈ src, s.t = Link.toTransition nu050_tM.base.core ∧ s.d = [0] ∧
      ∀ cls, NuLinkA.srcClass [0] false s = some cls → cls = .mint [0]) :
    NuLinkA.SrcCovers [0] false id [nu050_tM] src nu050_M0 := by
  intro M _ t ht c δ e M' hf
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil src hne
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨s, hs, nu050_srcRowOf h1 h2 h3 hf⟩

theorem nu050_src_props : ∀ s ∈ nu050_src, s.t = Link.toTransition nu050_tM.base.core ∧
    s.d = [0] ∧ ∀ cls, NuLinkA.srcClass [0] false s = some cls → cls = .mint [0] := by
  intro s hs
  simp only [nu050_src, List.mem_singleton] at hs
  subst hs
  refine ⟨rfl, rfl, fun cls hc => ?_⟩
  rw [nu050_src_class] at hc
  exact (Option.some.inj hc).symm

theorem nu050_srcU_props : ∀ s ∈ nu050_srcU, s.t = Link.toTransition nu050_tM.base.core ∧
    s.d = [0] ∧ ∀ cls, NuLinkA.srcClass [0] false s = some cls → cls = .mint [0] := by
  intro s hs
  simp only [nu050_srcU, List.mem_singleton] at hs
  subst hs
  refine ⟨rfl, rfl, fun cls hc => ?_⟩
  rw [nu050_srcU_class] at hc
  cases hc

theorem nu050_coherent (M : QMarkR) : ∀ t ∈ [nu050_tM], NuLinkA.ProjCoherent id t M := by
  intro t ht ms hms
  simp only [List.mem_singleton] at ht
  subst ht
  cases hms

/-- The run of the example under Route A's mint contract, read off the declared mint's source
row: both mints write a name no coloured place holds. -/
theorem nu050_runA2 : NuLinkA.RefNuRunA [0] false id [nu050_tM] nu050_src nu050_M0 nu050_M2 := by
  have hK : ∀ {M δ e}, NuLinkA.NuContract [0] id nu050_rM.cls M δ e →
      ∀ s ∈ nu050_src, NuLinkA.SrcRowOf [0] false nu050_tM (e.map Prod.fst) s →
        ∀ cls, NuLinkA.srcClass [0] false s = some cls → NuLinkA.NuContract [0] id cls M δ e := by
    intro M δ e hc s hs _ cls hcls
    rw [(nu050_src_props s hs).2.2 cls hcls]
    exact hc
  have h1 : NuLinkA.RefNuRunA [0] false id [nu050_tM] nu050_src nu050_M0 nu050_M1 :=
    Relation.ReflTransGen.single ⟨nu050_tM, List.mem_singleton_self _, none, _, _,
      nu050_fire1, hK nu050_conA1⟩
  exact h1.tail ⟨nu050_tM, List.mem_singleton_self _, none, _, _, nu050_fire2, hK nu050_conA2⟩

/-- The run of one undeclared mint: the rule gives its source row no class, so no contract
restricts the firing; it writes the name `10`. -/
theorem nu050_runU1 : NuLinkA.RefNuRunA [0] false id [nu050_tM] nu050_srcU nu050_M0 nu050_M1 :=
  Relation.ReflTransGen.single ⟨nu050_tM, List.mem_singleton_self _, none, _, _, nu050_fire1,
    fun s hs _ cls hcls => absurd ((nu050_srcU_props s hs).2.2 cls hcls) (by
      rintro rfl
      simp only [nu050_srcU, List.mem_singleton] at hs
      subst hs
      rw [nu050_srcU_class] at hcls
      cases hcls)⟩

/-! ### Violation: a fixed colour-slot bound of one -/

/-- A plan builder that classifies the rows as `build_plan` does but takes one colour slot
whatever the net, the bound a budget of one would give, instead of the checked colour-slot bound
of [NU-053]. -/
def nu050_slotOne : RouteAPlanner := fun n C ext a0 _ src =>
  Novel.RouteA.buildPlanG n C ext (Novel.RouteA.shippedGate C) a0 (some 1) src

theorem nu050_slotOne_plan :
    nu050_slotOne 2 [0] false (qCount nu050_M0) none nu050_src = some (1, [nu050_rM]) := by
  rfl

/-- With one colour slot the coloured encoding of the example never holds more than one name in
place `0`: the mint needs a colour no coloured place holds, and after the first mint the only
colour is taken. -/
theorem nu050_slotOne_enc :
    ∀ e, Novel.RouteA.ReachE
        (Novel.RouteA.Enc.shipped ⟨[0], 1, 2, [nu050_rM], [], qCount nu050_M0⟩) e →
      e.s 0 0 ≤ 1 := by
  intro e h
  induction h with
  | refl => simp [Novel.RouteA.e0]
  | tail _ hs ih =>
    obtain ⟨r, hr, hst⟩ := hs
    simp only [Novel.RouteA.Enc.shipped, List.map_cons, List.map_nil, List.mem_singleton] at hr
    subst hr
    obtain ⟨c, hc, h0, hs'⟩ := hst.s
    simp only [Novel.RouteA.Enc.shipped] at hc h0
    have hc0 : c = 0 := by omega
    subst hc0
    rw [hs']
    simp [Novel.RouteA.sMint, h0 0 (by simp)]

/-- ✗ A fixed bound of one colour slot violates NU-050's Route A safety line. The example mint
draws on a budget of two and so can hold two live names; with one slot the coloured encoding
proves "place `0` never holds two names", yet the reference runs the mint twice under its
contract and place `0` holds the names `10` and `11` (the retrodiction
`Novel.RouteA.Retro.budget_k_false_proven`). -/
@[evidence forbids NU_050_soundA]
theorem NU_050_soundA_forbids_slotOne : ¬ NU_050_soundA nu050_slotOne := by
  intro h
  have := h.1 2 [0] false none nu050_src 1 [nu050_rM] [] id [nu050_tM] nu050_M0
    (fun a => 2 ≤ a 0) nu050_slotOne_plan (by decide) (by decide)
    (nu050_guard fun s hs => (nu050_src_props s hs).1)
    (by simp) (nu050_covers (List.cons_ne_nil _ _) nu050_src_props) (fun M _ => nu050_coherent M)
    (fun e he hb => by
      have h1 := nu050_slotOne_enc e he
      simp [Novel.RouteA.agg] at hb
      omega)
    nu050_M2 nu050_runA2
  exact this (by rw [nu050_M2_count])

/-- The source row of the example mint comes from the example mint, and its class fits it. -/
theorem nu050_srcFrom : NuLinkA.SrcFrom [0] false [nu050_tM] nu050_src := by
  intro s hs
  refine ⟨nu050_tM, List.mem_singleton_self _, (nu050_src_props s hs).1, fun cls hc => ?_⟩
  rw [(nu050_src_props s hs).2.2 cls hc]
  rfl

/-- ✗ The same planner violates NU-050's Route A quiescence line. The coloured encoding with one
slot proves "where the net rests, place `0` holds fewer than two names", yet after the two mints
the budget is spent, the net rests, and place `0` holds two names. -/
@[evidence forbids NU_050_soundA]
theorem NU_050_soundA_forbids_slotOne_quiescence : ¬ NU_050_soundA nu050_slotOne := by
  intro h
  have := h.2 2 [0] false none nu050_src 1 [nu050_rM] [] id [nu050_tM] nu050_M0
    (fun a => 2 ≤ a 0) nu050_slotOne_plan (by decide) (by decide)
    (nu050_guard fun s hs => (nu050_src_props s hs).1)
    (by simp) (nu050_covers (List.cons_ne_nil _ _) nu050_src_props) (fun M _ => nu050_coherent M)
    (fun s hs => by
      simp only [nu050_src, List.mem_singleton] at hs
      subst hs
      intro x hx
      simp only [nu050_s, Link.toTransition, nu050_tM, List.map_cons, List.map_nil,
        List.mem_singleton] at hx
      subst hx
      rfl)
    nu050_srcFrom
    (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; rfl)
    (fun e he hb => by
      have h1 := nu050_slotOne_enc e he
      have h2 := hb.2
      simp [Novel.RouteA.agg] at h2
      omega)
    nu050_M2 nu050_runA2 nu050_M2_rests
  exact this (by rw [nu050_M2_count])

/-! ### Violation: a row left out of the plan -/

/-- A source row the minting branch of `build_plan` reaches (no match, a coloured output, no
coloured input) whose transition is not a declared mint. -/
def nu050_undecl (C : List PlaceId) (s : Novel.RouteA.SrcRow) : Bool :=
  s.ms.isNone && !s.declared && C.all (fun p => pre s.t p == 0) &&
    C.any (fun p => decide (0 < s.d.count p))

/-- A plan builder with the slip `continue` for `return None` in the classification loop of
`build_plan` (`rust/libpetri-verification/src/name_coloured_encoder.rs`, the minting branch,
`if !mints.contains(t.name())`): an undeclared mint's row is left out of the plan, and the other
rows are encoded as if its transition did not exist. The colour-slot bound is still checked over
every flat row. -/
def nu050_dropRow : RouteAPlanner := fun n C ext a0 ans src =>
  Novel.RouteA.buildPlanG n C ext (Novel.RouteA.shippedGate C) a0
    (Novel.RouteA.colourSlotBoundLP n C (src.map Novel.RouteA.SrcRow.flat) a0 ans)
    (src.filter fun s => !nu050_undecl C s)

/-- The checked simplex answer for the example: denominator one, weight one on both places. -/
def nu050_ans : Option (ℕ × Weight) := some (1, fun p => if p < 2 then 1 else 0)

/-- The shipped `build_plan` refuses the undeclared row; the slipped planner builds a plan with
the checked bound `k = 2` and no row at all. -/
theorem nu050_dropRow_plan :
    refRouteAPlan 2 [0] false (qCount nu050_M0) nu050_ans nu050_srcU = none ∧
      nu050_dropRow 2 [0] false (qCount nu050_M0) nu050_ans nu050_srcU = some (2, []) :=
  ⟨rfl, rfl⟩

/-- With no row the coloured encoding reaches its seed only, which holds no name: it proves
"place `0` never holds a name". -/
theorem nu050_emptyEnc : ∀ e, Novel.RouteA.ReachE
    (Novel.RouteA.Enc.shipped ⟨[0], 2, 2, [], [], qCount nu050_M0⟩) e →
    ¬ 1 ≤ Novel.RouteA.agg [0] 2 e 0 := by
  intro e h
  induction h with
  | refl => simp [Novel.RouteA.agg, Novel.RouteA.e0, Novel.RouteA.Enc.shipped]
  | tail _ hs _ =>
    obtain ⟨r, hr, -⟩ := hs
    simp [Novel.RouteA.Enc.shipped] at hr

/-- ✗ A planner that leaves an undeclared mint's row out of its plan, where `build_plan` refuses
the plan, violates NU-050's Route A safety line. The transition writes a name into place `0`
without being declared a mint. The slipped planner builds a plan with no row, whose encoding
proves "place `0` never holds a name", yet the reference fires the transition once and place `0`
holds the name `10`. The rows premise and the run read the source rows, so the left-out row's
firing is still judged. -/
@[evidence forbids NU_050_soundA]
theorem NU_050_soundA_forbids_dropRow : ¬ NU_050_soundA nu050_dropRow := by
  intro h
  have := h.1 2 [0] false nu050_ans nu050_srcU 2 [] [] id [nu050_tM] nu050_M0
    (fun a => 1 ≤ a 0) nu050_dropRow_plan.2 (by decide) (by decide)
    (nu050_guard fun s hs => (nu050_srcU_props s hs).1)
    (by simp) (nu050_covers (List.cons_ne_nil _ _) nu050_srcU_props)
    (fun M _ => nu050_coherent M) nu050_emptyEnc nu050_M1 nu050_runU1
  exact this (by rw [nu050_M1_count])

/-- ✓ Worked example. On a mint that draws on a budget of two, the shipped plan builder builds the
plan with two colour slots: the weighting one on both places covers the coloured place and gives
`⌊y·M0⌋ = 2`. The safety line then rules out a `Proven` of "place `0` never holds two names" for
that plan: the reference runs the mint twice, each time writing a fresh name, and place `0` ends
with the names `10` and `11`. -/
@[evidence nonvacuous NU_050_soundA]
theorem NU_050_soundA_nonvacuous :
    refRouteAPlan 2 [0] false (qCount nu050_M0) nu050_ans nu050_src = some (2, [nu050_rM]) ∧
      ¬ (∀ e, Novel.RouteA.ReachE
          (Novel.RouteA.Enc.shipped ⟨[0], 2, 2, [nu050_rM], [], qCount nu050_M0⟩) e →
        ¬ 2 ≤ Novel.RouteA.agg [0] 2 e 0) := by
  have hplan : refRouteAPlan 2 [0] false (qCount nu050_M0) nu050_ans nu050_src =
      some (2, [nu050_rM]) := by rfl
  refine ⟨hplan, fun hpr => ?_⟩
  have := NU_050_soundA_reference.1 2 [0] false nu050_ans nu050_src 2 [nu050_rM] [] id
    [nu050_tM] nu050_M0 (fun a => 2 ≤ a 0) hplan (by decide) (by decide)
    (nu050_guard fun s hs => (nu050_src_props s hs).1)
    (by simp) (nu050_covers (List.cons_ne_nil _ _) nu050_src_props) (fun M _ => nu050_coherent M) hpr
    nu050_M2 nu050_runA2
  exact this (by rw [nu050_M2_count])

/-! ### Why the runs restrict the actions

The bridges' own run premises ask the action contract of every firing the reference offers from
a reachable marking. The reference leaves the emitted values free (an action may emit anything
its output specification allows), so a mint that can fire from a marking holding a name has a
firing that writes that name again, and the premise fails. The two theorems below show it on the
example: after the first mint, a second mint that writes the name `10` again is a reference
firing, so neither premise holds of this net, and the corollaries that take them say nothing
about it. The blocks above restrict the run to firings whose actions keep their contracts
instead. -/

/-- The second mint of the example, writing the name `10` that place `0` already holds. -/
def nu050_eStale : List (PlaceId × Stamped Colour) := [(0, ⟨10, 3⟩)]

theorem nu050_fireStale : RefNuFire nu050_tM nu050_M1 none (qDelivered nu050_M1 nu050_tM.base)
    nu050_eStale (qFire nu050_M1 nu050_tM.base nu050_eStale) :=
  (refNuFire_restrictsTo nu050_tM rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

theorem nu050_reach1 : RefNuReach [nu050_tM] nu050_M0 nu050_M1 :=
  Relation.ReflTransGen.single ⟨nu050_tM, List.mem_singleton_self _, none, _, _, nu050_fire1⟩

/-- Bridge B2's run premise (`NuLinkA.FiringsHaveRows`) fails on the example: the stale second
mint is a reference firing from a reachable marking, and its only row is a mint whose contract
asks for a name no coloured place holds. -/
theorem nu050_firingsHaveRows_fails :
    ¬ NuLinkA.FiringsHaveRows [0] id [nu050_tM] [nu050_rM] nu050_M0 := by
  intro h
  obtain ⟨r, hr, -, hK⟩ := h nu050_M1 nu050_reach1 nu050_tM (List.mem_singleton_self _) none _ _ _
    nu050_fireStale
  simp only [List.mem_singleton] at hr
  subst hr
  obtain ⟨v, hfresh, hall⟩ := hK
  have hv : v = 10 := (hall 0 (by simp) ⟨10, 3⟩ (by decide)).symm
  subst hv
  exact hfresh 0 (by simp) ⟨10, 2⟩ (by decide) rfl

/-- Bridge B1's run premise (the `hok` of `NuLink.refNuReach_names_reach`) fails on the example
for the same reason: the stale second mint breaks the mint contract. -/
theorem nu050_hok_fails :
    ¬ (∀ M₁ M₂, RefNuReach [nu050_tM] nu050_M0 M₁ → ∀ t ∈ [nu050_tM], ∀ c δ e,
        RefNuFire t M₁ c δ e M₂ →
        NuLink.NuProj id t M₁ ∧ NuLink.NuProj id t M₂ ∧
          NuLink.NuContract [0] id ((fun _ => Novel.RouteB.Role.mint) (NuLink.toNuTransB t)) t M₁
            δ e) := by
  intro h
  obtain ⟨-, -, f, hfresh, hall⟩ := h nu050_M1 _ nu050_reach1 nu050_tM
    (List.mem_singleton_self _) none _ _ nu050_fireStale
  have hf : (10 : ℕ) = f := hall (0, ⟨10, 3⟩) (by decide) (by decide)
  subst hf
  exact hfresh 0 (by simp) ⟨10, 2⟩ (by decide) rfl

end Libpetri.Spec
