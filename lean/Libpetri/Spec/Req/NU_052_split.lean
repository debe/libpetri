import Libpetri.Spec.Req.VER_004
import Libpetri.Spec.Req.NU_052

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# NU-052, companion: which calls prune, the split and the in-flight test (`spec/12-nu-nets.md`)

The block `NU_052` states the Route B step for a given mode. This companion states how the
verifier picks the mode for a call and what it hands the in-flight split ([VER-004]) with it
(ruling D97 (a), clash nu-c#4), and how the base layer reads "a firing of `H` in flight". It is a
predicate over a pair of models:

* `M : NuSetupFn K`, the verifier's setup of a call: from the options, the selected mode
  (`true`: `CONFLICT`), the call's shape (`NuSplitCall`), the priorities by name, the property, the
  base split configuration and the net, the split configuration handed to the in-flight split,
  whether Route B prunes, and the transition the report names when the pruning was turned off.
  The witness is `refNuSetup`: `conflict_pruning_applies` (smt_verifier.rs, `SmtVerifier.java`,
  `smt-verifier.ts`) feeding the [VER-004] plan `refSplitPlan` (`with_in_flight`).
* `B : InFlightBase`, the untimed base layer of a Route B call given the in-flight place of each
  transition name. The witness is `refInFlightBase`, the untimed base whose `idle` reads the
  in-flight place (`priority_dominated`: `marking.count(in_flight_place(h)) == 0`) and whose
  `compete` is the competition test of `NU_052` (`shares_consumed_input`).

The seven lines: under `NONE` nothing prunes and the split gets the `QuiescentCount` demand
alone (1); conflict priority applies only to a call whose net has no transition read as reapable
and whose property Route B decides, a name-alignment call included, and every other call is the
`NONE` call (2); under `assumeAtomicFiring` the pruning stays on (3); otherwise every pruner and
every transition feeding one is split and the pruning stays on (4), unless one of them cannot be
split, when the call is the `NONE` call and the report names that transition, if the call is not
refused under `NONE` as well (5); a transition has a firing in flight exactly when its in-flight
place is marked (6); and two transitions compete by the required counts of `NU_052` line 2 (7).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB
open Libpetri.Spec.Verifier (Options)
open Libpetri.Spec.Verifier.Split (SplitCfg splits)

/-! ## The models -/

/-- **A call, as conflict priority reads it**: whether the property is a name-alignment one
([NU-055]), whether the net has a ν-join (a transition with a match specification), whether the
property is a reachability-safety one, and whether a budget place is declared ([NU-050]). -/
structure NuSplitCall where
  /-- The property is `NameAligned` or `QuiescentNameAligned`. -/
  nameAlign : Bool
  /-- The net has a ν-join. -/
  join      : Bool
  /-- The property is a reachability-safety one. -/
  safety    : Bool
  /-- A budget place is declared to the verifier. -/
  budget    : Bool
  deriving DecidableEq, Repr

/-- **Route B reads the mode of the call**: a name-alignment property, on any net; on a net with
a ν-join, every property except a reachability-safety one with a declared budget place, which
stays on Route A ([NU-050]). -/
def NuSplitCall.routeB (k : NuSplitCall) : Bool :=
  k.nameAlign || (k.join && !(k.safety && k.budget))

/-- **Read as reapable** ([VER-002]): some transition of the net has a `Deadline` or `Window`
timing, and `assumeNoReaping` is not set (`reapable_set`). -/
def nu052sReapable {K : Type} (o : Options) (X : Reference.TimedNet K) : Bool :=
  !o.assumeNoReaping && X.net.transitions.any fun t => (X.timing t).reapable

/-- **Conflict priority applies to a call** (`conflict_pruning_applies`): `CONFLICT` is selected,
Route B reads the mode of the call, and no transition is read as reapable. -/
def nu052sApplies {K : Type} (o : Options) (sel : Bool) (k : NuSplitCall) (X : Reference.TimedNet K) :
    Bool :=
  sel && k.routeB && !nu052sReapable o X

/-- **The setup of a call**: the split configuration handed to the in-flight split, whether
Route B prunes, and the transition the report names when the pruning was turned off. -/
structure NuSetup (K : Type) where
  /-- The configuration handed to the in-flight split ([VER-004]). -/
  cfg   : SplitCfg K
  /-- Route B prunes (`CONFLICT` after every switch-off). -/
  prune : Bool
  /-- The transition named by the conflict-off note, if the pruning was turned off. -/
  off   : Option String

/-- **The verifier's setup of a call**: from the options, the selected mode (`true`:
`CONFLICT`), the call, the priorities by transition name, the property, the base split
configuration and the net. -/
abbrev NuSetupFn (K : Type) : Type :=
  Options → Bool → NuSplitCall → (String → Int) → VerProp K → SplitCfg K → Reference.TimedNet K →
    NuSetup K

/-- **The untimed Route B base layer of a call, given the in-flight place of each transition
name.** -/
abbrev InFlightBase : Type := (String → PlaceId) → BaseLayer AMarking

section Ref

variable {K : Type} [DecidableEq K]

/-- The first transition, in net order, that the split under the conflict demand added to `cfg`
cannot split (`first_unsplittable` over `in_flight_transitions_for` with `conflict_demand`). -/
def nu052sConflictRefused (prio : String → Int) (cfg : SplitCfg K) (X : Reference.TimedNet K) :
    Option String :=
  ver004FirstRefused (ver004WithConflict prio cfg X.net) X.net
    (splits (ver004WithConflict prio cfg X.net) X.net)

/-- The first transition, in net order, that the split under `cfg` itself cannot split: the
refusal of [VER-004] when `cfg` is what the verifier hands the split. -/
def nu052sRefused (cfg : SplitCfg K) (X : Reference.TimedNet K) : Option String :=
  ver004FirstRefused cfg X.net (splits cfg X.net)

/-- **The reference setup** (`with_in_flight` with `conflict_pruning_applies`): the [VER-004]
plan, told whether conflict priority applies; when the plan turns the pruning off, the first
transition the split under the conflict demand refuses is named, unless the split under the
configuration handed on is refused as well, when the call answers `Unknown` with that refusal
and the note is dropped (`InFlight::Refused => f(verifier, None)`). -/
def refNuSetup : NuSetupFn K := fun o sel k prio φ cfg X =>
  let c := nu052sApplies o sel k X
  let p := refSplitPlan o c prio φ cfg X
  { cfg := p.1, prune := p.2,
    off := if c && !p.2 && (nu052sRefused p.1 X).isNone then
        nu052sConflictRefused prio (ver004WithCount cfg φ) X else none }

end Ref

#spec_witness refNuSetup

/-- **The reference base layer**: the untimed base, whose `idle` reads the in-flight place. -/
def refInFlightBase : InFlightBase := fun ifl =>
  { untimedBase with idle := fun a H => decide (a (ifl H.name) = 0) }

#spec_witness refInFlightBase

/-- The reference setup hands on exactly what the [VER-004] plan hands on, told whether conflict
priority applies: the two blocks share one plan. -/
theorem refNuSetup_plan {K : Type} [DecidableEq K] (o : Options) (sel : Bool) (k : NuSplitCall)
    (prio : String → Int) (φ : VerProp K) (cfg : SplitCfg K) (X : Reference.TimedNet K) :
    ((refNuSetup o sel k prio φ cfg X).cfg, (refNuSetup o sel k prio φ cfg X).prune) =
      refSplitPlan o (nu052sApplies o sel k X) prio φ cfg X := rfl

/-- The reference base layer reads competition through `refCompete` on the count marking itself,
so it is one of the base layers line 1 of `NU_052` speaks of. -/
theorem refInFlightBase_compete (ifl : String → PlaceId) :
    (refInFlightBase ifl).compete = refCompete := rfl

/-! ## NU-052, the companion block -/

requirement NU_052_split
  id "NU-052"
  title "Conflict-Only Priority for the Route B Name-SCG (which calls prune, the split, the in-flight test)"
  kind F
  scope "the verifier's setup of a call under CONFLICT and NONE (MAY; the shall sentences bind an implementation that offers CONFLICT), and the in-flight test of the Route B base layer"
  source verbatim "spec/12-nu-nets.md"
  quote "*While* the mode is `NONE`, conflict priority *shall not* apply to any call, and the verifier *shall* hand the in-flight split ([VER-004]) the `QuiescentCount` demand alone."
        "*While* the mode is `CONFLICT`, conflict priority *shall* apply to a call exactly when no transition of the net is read as reapable ([VER-002]) and either the property is a name-alignment one ([NU-055]) or the net has a ν-join and the property is not a reachability-safety one with a declared budget place ([NU-050]), and the verifier *shall* verify every other call as under `NONE`."
        "*While* conflict priority applies to a call and `assumeAtomicFiring` is set, the verifier *shall* keep conflict priority on."
        "*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net has no pruner or every transition the verifier would split under conflict priority can be split, *then* the verifier *shall* split every pruner and every transition that deposits into an input or read place of a pruner, except a transition that models an environment or is a completion step ([VER-004]), and *shall* keep conflict priority on."
        "*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net has a pruner and a transition the verifier would split under conflict priority cannot be split, *then* the verifier *shall* hand the in-flight split and Route B what it hands them under `NONE`, so the verdict is the `NONE` verdict, and *shall* name the first such transition, in the transition order, in the report, unless the split under `NONE` is refused too, when the call answers `Unknown` with that refusal ([VER-004])."
        "*While* the mode is `CONFLICT`, the Route B graph *shall* take a transition `H` to have a firing in flight in a class exactly when the class marking holds a token on the place `inflight:<H>`."
        "*While* the mode is `CONFLICT`, the Route B graph *shall* take two transitions `H` and `L` to compete in a class exactly when some place is a consumed input of both and its token count in the class marking is less than the sum of their demands on it, where a transition's demand on a place is the sum of the required counts ([IO-007]) of its input arcs on that place."
  reading "Let M be the verifier's setup of a call and B the base layer given the in-flight places. For every options o, call k, priorities prio, property φ, split configuration cfg and timed net X, write M sel for M o sel k prio φ cfg X (sel true for CONFLICT) and N for M false, the NONE setup."
          "N hands on cfg with the QuiescentCount demand added (ver004WithCount), prunes nothing and names no transition."
          "If conflict priority does not apply (nu052sApplies o true k X is false: a transition is read as reapable, or k.routeB is false), M true is N."
          "If it applies and o sets assumeAtomicFiring, M true prunes and names no transition."
          "If it applies, o does not set assumeAtomicFiring, and the net has no pruner (ver004Pruners) or the split under N's configuration with the conflict demand added refuses no transition, M true hands on N's configuration with the conflict demand added (ver004WithConflict: every pruner forced, its input and read places tested), prunes, and names no transition."
          "If it applies, o does not set assumeAtomicFiring, the net has a pruner, and the first transition that the split under N's configuration with the conflict demand added refuses is t, M true hands on N's configuration and N's pruning, and names t when the split under N's configuration refuses nothing (nu052sRefused) and no transition when it refuses one."
          "For every in-flight place naming ifl, count marking a and transition H: H is idle in B ifl at a exactly when a holds no token on ifl H's name."
          "For every in-flight place naming ifl, count marking a and transitions H and L: H and L compete in B ifl at a exactly when some input arc of H is on a place that is also the place of an input arc of L and holds fewer tokens in a than the sum of H's and L's demands on it (demandOn, as line 2 of NU_052)."
  assumes "The model is the pair (M, B). M : NuSetupFn K is with_in_flight with conflict_pruning_applies (rust/libpetri-verification/src/smt_verifier.rs, SmtVerifier.applyInFlight and conflictPruningApplies in java/src/main/java/org/libpetri/smt/SmtVerifier.java, the same pair in typescript/src/verification/smt-verifier.ts; Python rides Rust). Its result is what the rest of the pipeline reads of the mode: the split configuration handed to the in-flight split of [VER-004], whether Route B prunes, and the transition the conflict-off note names. The witness refNuSetup is the [VER-004] plan refSplitPlan told whether conflict priority applies (nu052sApplies), so VER_004_split decides what the configuration does to the net, and this block decides when conflict priority applies, what the call hands on and what it reports. B : InFlightBase is the untimed base layer of Novel.RouteB with the in-flight place of each name given (ifl); the witness refInFlightBase is untimedBase with idle reading ifl and compete the test refCompete of NU_052."
          "The call's shape is NuSplitCall: the four booleans conflict_pruning_applies reads (is_name_alignment, a transition with a match spec, is_reachability_safety, a declared budget place). Read as reapable is nu052sReapable: some transition has a Deadline or Window timing and assumeNoReaping is not set, as Verifier.refNet reads the reapable flags ([VER-002], reapable_set). Two overrides of that set are not modelled: a caller that passes its own reapable set to the Route B reaping entry (verify_via_name_scg_reaping, NuScgVerifier.verifyReaping, verifyViaNameScgReaping), and the verifier-level set the open-net route of [VER-022] names for a net whose timing a rewrite is about to drop (reapable_transitions at smt_verifier.rs:4383, set at open_net/smt_route.rs:120; reapableOverride at SmtVerifier.java:905; _reapable at smt-verifier.ts:202). On that route the transitions read as reapable are the named ones, not the Deadline and Window transitions of the net handed on."
          "The first quoted sentence is line 1. 'The QuiescentCount demand alone' is what VER_004_split line 5 hands on without conflict priority: cfg with the places of a QuiescentCount property counted as tested, and no pruner forced. A NONE setup that forces the pruners would make the NONE call refuse the split of the AC2 shape and answer Unknown instead of the NONE verdict, against AC1 (NU_052_split_forbids_noneDemand). With line 1, 'what it hands them under NONE' in line 5 is ver004WithCount cfg φ with the pruning off. The second sentence is lines 2 and 4 with 3 and 5: 'exactly when' is line 2 for the calls it does not apply to, which are the NONE call, and lines 3 to 5 for those it applies to. 'Conflict priority applies' is the condition (nu052sApplies), not the outcome: line 5 verifies an applying call as under NONE, as VER-004's 'While conflict priority applies' reads it. Ruling D97 (a) widens the body's 'whenever it applies CONFLICT on a net with a ν-join' to every call conflict priority applies to: a name-alignment call on a net without a ν-join is split too, as all three runtimes do (NU_052_split_forbids_joinOnly). The reapable exception is [VER-002]'s 'It does not prune by priority ([NU-052]) on a net with a reapable transition.', which NU-052 now states as well (clash nu-c#4; NU_052_split_forbids_reapBlind). Route B also turns CONFLICT into NONE itself when it is handed a non-empty reapable set (nu_scg_verifier.rs verify_via_name_scg_reaping, NuScgVerifier.java pruningOff, nu-scg-verifier.ts pruningOff), so the verifier's test and Route B's agree; that inner switch-off is not a separate line. A direct call to Route B passes it an empty set and prunes on any net, which is NU_052 line 1."
          "The third quoted sentence is line 3. Which net is verified under assumeAtomicFiring (the net itself) is VER_004_split line 1; the report line stating the atomic assumption (atomic_assumption_note_for) is report text, kind N. Lines 3 and 4 also say that no transition is named: keeping conflict priority on writes no conflict-off note, since the runtimes write it only when they turn the pruning off (conflict_off in smt_verifier.rs with_in_flight, off in SmtVerifier.applyInFlight, conflictOff in smt-verifier.ts applyInFlight)."
          "The fourth quoted sentence is line 4. 'Split every pruner and every transition that deposits into an input or read place of a pruner' is the configuration handed on: ver004WithConflict forces every pruner (ver004Pruners, conflict_pruners: strictly higher priority than another transition that shares an input place with it) and counts its input and read places as tested, and VER_004_split lines 2 to 4 split exactly the forced transitions and those with an output place that is tested, except the environment steps and the completion steps, which Split.splitB leaves atomic even when forced; that is the sentence's 'except a transition that models an environment or is a completion step'. A pruner is read by input places, whatever the cardinality and the token count, as the body's parenthesis has it; line 7 then decides which pruners compete in a class. 'The net has no pruner' covers a net with no conflict at all, where the demand adds nothing and the pruning stays on (Rust's reasons.conflict is false, so nothing is switched off)."
          "The fifth quoted sentence is line 5. 'What it hands them under NONE' is the NONE setup N, configuration and mode, so every route reads what it reads under NONE and the verdict is the NONE verdict (nu052s_verdict_none); a setup that hands on the bare configuration instead forgets the QuiescentCount demand (NU_052_split_forbids_bareOff). The note names the first transition, in net order, that the split under the conflict demand refuses (first_unsplittable; conflict_off_note). 'Unless the split under NONE is refused too' is the case where a transition the split under N's configuration splits for another reason is a ν-join or a coloured writer: the call then answers Unknown with the refusal of [VER-004], whose reason opens with the first transition that split refuses, and all three runtimes drop the conflict-off note (smt_verifier.rs with_in_flight, InFlight::Refused calls f(verifier, None); SmtVerifier.java applyInFlight, Outcome.Refused sets only inFlightRefusal; smt-verifier.ts applyInFlight, the refused branch sets only _inFlightRefusal), so line 5 names no transition there (NU_052_split_forbids_noteKept, NU_052_split_ac2). That report is VER_004_split's line 3 and VER-003's line 4. The text of the note is kind N."
          "The sixth quoted sentence is line 6, the in-flight bullet of the body's 'MUST NOT let H pre-empt anything while inflight:<H> is marked': with line 1 of NU_052 (Pre-empt reads idle), a transition whose in-flight place holds a token pre-empts nothing (NU_052_split_nonvacuous, the reference keeps L expanded while H is in flight). All three runtimes read it on the class marking (priority_dominated in name_state_class_graph.rs, NameStateClassGraph.java, name-state-class-graph.ts). Line 6 is stated for every naming ifl, so it holds for the naming the split uses: the place inflight:<H> is SplitCfg.inflight of the configuration line 4 hands on (in_flight_place), and that the Route B call is given that naming is how the runtimes build the call, not a further line. On a net without in-flight places the place holds nothing and the guard has no effect, which is the body's last sentence. B is the untimed base; the timed base reads the same count on the timed class's marking, and its readyLe is the open timed base of NU_052 (gap R6)."
          "The seventh quoted sentence is NU_052's second, read here as line 7 on the base layer of a call. NU_052 line 2 states it of the competition test C, and NU_052 line 1 speaks only of base layers whose compete is C; line 7 says the base layer of a Route B call is such a layer, with C the required-count test, so a base layer whose competition reads a demand as the tokens one firing consumes (consumed_demand through the firing count instead of required_count) breaks this block although it meets NU_052 (NU_052_split_forbids_consumedBase). B is untimed; that the timed base reads the same test on the timed class's marking is gap R6."
          "The body's 'A direct call to Route B (Rust verify_via_name_scg, TypeScript verifyViaNameScg) applies no split and prunes as before' is NU_052 line 1: the step prunes by Pre-empt on whatever net and mode it is given. 'Two cases break the pruning' (a feeder of H in flight leaves H disabled; H in flight is not started again by Java and TypeScript) is why the split is needed; that the split net over-approximates the executor with actions in flight is VER-004 block B (wave W11), and whether a transition starts again while in flight is ruling D8 (b), implementation-defined, under which the split is sound either way."
          "AC1's 'NONE MUST leave every existing Route B verdict unchanged' is, for the setup, line 1: under NONE the split gets what it got before conflict priority existed. AC2's pipeline half (through verify() with the split on, the join cannot be split, the verdict equals the NONE verdict and the report says conflict priority is off) is line 5 (NU_052_split_ac2); its verdicts are Route B's (NU_052, VER-012). AC7's split half (H and its feeder t are split, and under assumeAtomicFiring nothing is and the pruning stays on) is line 4 and line 3 (NU_052_split_ac2, VER_004_split_ac7); a pruner in flight pre-empting nothing is line 6. AC3 to AC6 and the test derivation are NU_052's; AC6 on the base layer of a call is line 7."
  signoff "pending"
  statement : ∀ {K : Type} [DecidableEq K], NuSetupFn K → InFlightBase → Prop :=
    fun M B =>
      (∀ o k prio φ cfg X, (M o false k prio φ cfg X).cfg = ver004WithCount cfg φ ∧
        (M o false k prio φ cfg X).prune = false ∧ (M o false k prio φ cfg X).off = none) ∧
      (∀ o k prio φ cfg X, nu052sApplies o true k X = false →
        M o true k prio φ cfg X = M o false k prio φ cfg X) ∧
      (∀ o k prio φ cfg X, nu052sApplies o true k X = true → o.assumeAtomicFiring = true →
        (M o true k prio φ cfg X).prune = true ∧ (M o true k prio φ cfg X).off = none) ∧
      (∀ o k prio φ cfg X, nu052sApplies o true k X = true → o.assumeAtomicFiring = false →
        (ver004Pruners prio X.net = [] ∨
          nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = none) →
        M o true k prio φ cfg X =
          ⟨ver004WithConflict prio (M o false k prio φ cfg X).cfg X.net, true, none⟩) ∧
      (∀ o k prio φ cfg X t, nu052sApplies o true k X = true → o.assumeAtomicFiring = false →
        ver004Pruners prio X.net ≠ [] →
        nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = some t →
        M o true k prio φ cfg X =
          ⟨(M o false k prio φ cfg X).cfg, (M o false k prio φ cfg X).prune,
            if nu052sRefused (M o false k prio φ cfg X).cfg X = none then some t else none⟩) ∧
      (∀ ifl (a : AMarking) (H : Transition), (B ifl).idle a H = true ↔ a (ifl H.name) = 0) ∧
      (∀ ifl (a : AMarking) (H L : Transition),
        (B ifl).compete a H L = true ↔ ∃ sh ∈ H.inputs, (∃ sl ∈ L.inputs, sl.place = sh.place) ∧
          a sh.place < demandOn H sh.place + demandOn L sh.place)

/- The pinned readable form of the companion block: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.NU_052_split : {K : Type} → [DecidableEq K] → NuSetupFn K → InFlightBase → Prop :=
fun {K} [DecidableEq K] M B =>
  (∀ (o : Options) (k : NuSplitCall) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K) (X : Reference.TimedNet K),
      (M o false k prio φ cfg X).cfg = ver004WithCount cfg φ ∧
        (M o false k prio φ cfg X).prune = false ∧ (M o false k prio φ cfg X).off = none) ∧
    (∀ (o : Options) (k : NuSplitCall) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K)
        (X : Reference.TimedNet K),
        nu052sApplies o true k X = false → M o true k prio φ cfg X = M o false k prio φ cfg X) ∧
      (∀ (o : Options) (k : NuSplitCall) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K)
          (X : Reference.TimedNet K),
          nu052sApplies o true k X = true →
            o.assumeAtomicFiring = true →
              (M o true k prio φ cfg X).prune = true ∧ (M o true k prio φ cfg X).off = none) ∧
        (∀ (o : Options) (k : NuSplitCall) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K)
            (X : Reference.TimedNet K),
            nu052sApplies o true k X = true →
              o.assumeAtomicFiring = false →
                ver004Pruners prio X.net = [] ∨ nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = none →
                  M o true k prio φ cfg X =
                    { cfg := ver004WithConflict prio (M o false k prio φ cfg X).cfg X.net, prune := true,
                      off := none }) ∧
          (∀ (o : Options) (k : NuSplitCall) (prio : String → ℤ) (φ : VerProp K) (cfg : SplitCfg K)
              (X : Reference.TimedNet K) (t : String),
              nu052sApplies o true k X = true →
                o.assumeAtomicFiring = false →
                  ver004Pruners prio X.net ≠ [] →
                    nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = some t →
                      M o true k prio φ cfg X =
                        { cfg := (M o false k prio φ cfg X).cfg, prune := (M o false k prio φ cfg X).prune,
                          off := if nu052sRefused (M o false k prio φ cfg X).cfg X = none then some t else none }) ∧
            (∀ (ifl : String → PlaceId) (a : AMarking) (H : Transition), (B ifl).idle a H = true ↔ a (ifl H.name) = 0) ∧
              ∀ (ifl : String → PlaceId) (a : AMarking) (H L : Transition),
                (B ifl).compete a H L = true ↔
                  ∃ sh ∈ H.inputs,
                    (∃ sl ∈ L.inputs, sl.place = sh.place) ∧ a sh.place < demandOn H sh.place + demandOn L sh.place
-/
#guard_msgs in #print NU_052_split

/-! ## The reference -/

/-- The reference meets the companion block. Worked example of why: under `NONE`,
`refNuSetup` tells the [VER-004] plan that conflict priority does not apply, so the plan hands on
the `QuiescentCount` demand alone, prunes nothing and the setup names nothing (line 1); when
conflict priority does not apply, `CONFLICT` tells the plan the same thing (line 2); otherwise the
plan adds the conflict demand and keeps the pruning on (lines 3 and 4) unless the split under it
refuses a transition, when the plan hands on the `NONE` configuration with the pruning off and the
setup names that transition, or nothing if the `NONE` split is refused too (line 5). The base
layer's `idle` is the test `a (ifl H.name) = 0` itself (line 6), and its `compete` is the test of
`NU_052`, which counts required counts (line 7). -/
@[evidence holds NU_052_split]
theorem NU_052_split_reference {K : Type} [DecidableEq K] :
    NU_052_split (refNuSetup (K := K)) refInFlightBase := by
  refine ⟨fun o k prio φ cfg X => ?_, fun o k prio φ cfg X h => ?_,
    fun o k prio φ cfg X h hat => ?_, fun o k prio φ cfg X h hat hp => ?_,
    fun o k prio φ cfg X t h hat hp ht => ?_, fun ifl a H => ?_, fun ifl a H L => ?_⟩
  · simp [refNuSetup, nu052sApplies, refSplitPlan]
  · have h0 : nu052sApplies o false k X = false := by simp [nu052sApplies]
    simp only [refNuSetup, h, h0]
  · simp [refNuSetup, h, refSplitPlan, hat]
  · have hN : (refNuSetup o false k prio φ cfg X).cfg = ver004WithCount cfg φ := by
      simp [refNuSetup, nu052sApplies, refSplitPlan]
    rw [hN] at hp ⊢
    unfold nu052sConflictRefused at hp
    rcases hp with hp | hp
    · simp [refNuSetup, h, refSplitPlan, hp]
    · simp [refNuSetup, h, refSplitPlan, hp]
  · have hN : (refNuSetup o false k prio φ cfg X).cfg = ver004WithCount cfg φ := by
      simp [refNuSetup, nu052sApplies, refSplitPlan]
    rw [hN] at ht
    have ht' := ht
    unfold nu052sConflictRefused at ht'
    have h2 : k.routeB = true ∧ nu052sReapable o X = false := by simpa [nu052sApplies] using h
    by_cases hn : nu052sRefused (ver004WithCount cfg φ) X = none
    · simp [refNuSetup, refSplitPlan, hat, hp, ht', ht, nu052sApplies, h2, hn]
    · simp [refNuSetup, refSplitPlan, hat, hp, ht', nu052sApplies, h2, hn]
  · simp [refInFlightBase]
  · exact (NU_052_reference (β := Unit)).2.1 a H L

/-- **The `NONE` verdict.** Worked example of line 5's "so the verdict is the `NONE` verdict":
whatever a verifier computes from the configuration it hands the split and the mode it hands
Route B, it computes the same under `CONFLICT` as under `NONE` once the split under conflict
priority is refused, because the two setups agree on both. -/
theorem nu052s_verdict_none {K : Type} [DecidableEq K] {M : NuSetupFn K} {B : InFlightBase}
    (h : NU_052_split M B) {α : Type} (V : SplitCfg K → Bool → α) {o : Options} {k : NuSplitCall}
    {prio : String → Int} {φ : VerProp K} {cfg : SplitCfg K} {X : Reference.TimedNet K}
    {t : String} (ha : nu052sApplies o true k X = true) (hat : o.assumeAtomicFiring = false)
    (hp : ver004Pruners prio X.net ≠ [])
    (ht : nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = some t) :
    V (M o true k prio φ cfg X).cfg (M o true k prio φ cfg X).prune =
      V (M o false k prio φ cfg X).cfg (M o false k prio φ cfg X).prune := by
  rw [h.2.2.2.2.1 o k prio φ cfg X t ha hat hp ht]

/-! ## Examples -/

/-- A call on a net with a ν-join and a property that is not a reachability-safety one. -/
def nu052s_joinCall : NuSplitCall := ⟨false, true, false, false⟩

/-- A name-alignment call on a net without a ν-join. -/
def nu052s_alignCall : NuSplitCall := ⟨true, false, false, false⟩

/-- The AC7 net of [VER-004] with `L` given a `deadline(5)` timing, so it is read as reapable. -/
def nu052s_reapNet : Reference.TimedNet String :=
  { ver004_ac7 with timing := fun t => if t.core.name = "L" then .deadline 5 else .immediate }

/-- The forced transitions a setup hands on. -/
def nu052sForced {K : Type} (s : NuSetup K) : List String := s.cfg.forced

/-- ✓ **The setup on the AC7 and AC2 shapes** (AC2, AC7, lines 1 to 5). Worked example: in the
AC7 net `H : one(p) + one(b) → ok` at priority 10 shares `b` with `L` at priority 0, so `H` is a
pruner. Under `NONE` nothing is forced. On a ν-join call conflict priority applies: `H` is forced
into the split and the pruning stays on; under `assumeAtomicFiring` the pruning stays on too. When
`H` is a ν-join it cannot be split, so the call is set up as under `NONE`, nothing forced, the
pruning off, and `H` is named (AC2). If `ok` is tested as well, the split under `NONE` has to
split `H` too and refuses it, so the call ends `Unknown` and nothing is named. With `L` timed
`deadline(5)` the net has a reapable transition and the call is the `NONE` call; under
`assumeNoReaping` it is not. -/
@[evidence nonvacuous NU_052_split]
theorem NU_052_split_ac2 :
    nu052sForced (refNuSetup {} false nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7)
      = [] ∧
    nu052sForced (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7)
      = ["H"] ∧
    (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7).prune = true ∧
    (refNuSetup { assumeAtomicFiring := true } true nu052s_joinCall ver004_prio7 ver004_bad
      ver004_cfg ver004_ac7).prune = true ∧
    nu052sForced (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"] } ver004_ac7) = [] ∧
    (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"] } ver004_ac7).prune = false ∧
    (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"] } ver004_ac7).off = some "H" ∧
    (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"], tested := ["ok"] } ver004_ac7).off = none ∧
    (refNuSetup {} true nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg nu052s_reapNet).prune
      = false ∧
    (refNuSetup { assumeNoReaping := true } true nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg
      nu052s_reapNet).prune = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The count marking with one token on place `0` and `k` on place `10`, the in-flight place of
the examples. -/
def nu052s_a (k : ℕ) : AMarking := fun p => if p = 0 then 1 else if p = 10 then k else 0

/-- ✓ **A pruner in flight pre-empts nothing** (line 6, AC7). Worked example: `hi : one(0)` at
priority 10 and `lo : one(0)` at priority 0 compete for the one token on place `0`. With the
in-flight place of `hi` empty, `CONFLICT` expands `hi` only; with a token on it, `hi` has a firing
in flight and pre-empts nothing, so `lo` is expanded too. -/
@[evidence nonvacuous NU_052_split]
theorem NU_052_split_nonvacuous :
    (refExpand [] (refInFlightBase fun _ => 10) [nu052_hi, nu052_lo] nu052_ord true 0
        (initState [] (nu052s_a 0))).map Prod.fst = ["hi"] ∧
      (refExpand [] (refInFlightBase fun _ => 10) [nu052_hi, nu052_lo] nu052_ord true 0
        (initState [] (nu052s_a 1))).map Prod.fst = ["hi", "lo"] := by
  refine ⟨by decide, by decide⟩

/-! ## Violations -/

/-- A setup that ignores the selected mode: it prunes under `NONE` as under `CONFLICT`. -/
def nu052s_selBlind {K : Type} [DecidableEq K] : NuSetupFn K := fun o _ k prio φ cfg X =>
  refNuSetup o true k prio φ cfg X

/-- ✗ Pruning under `NONE` violates the companion block (line 1). Worked example: on the AC7
net, a ν-join call under `NONE` must not prune, but a setup that ignores the mode prunes. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_selBlind :
    ¬ NU_052_split (nu052s_selBlind (K := String)) refInFlightBase := by
  intro h
  have := (h.1 {} nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7).2.1
  revert this
  decide +kernel

/-- A setup that applies conflict priority whatever the reapable transitions (no [VER-002]
exception). -/
def nu052s_reapBlind {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  refNuSetup { o with assumeNoReaping := true } sel k prio φ cfg X

/-- ✗ Pruning on a net with a reapable transition violates the companion block (line 2, ruling
D97 (a)). Worked example: with `L` timed `deadline(5)` a late executor reaps `H` and fires `L`, so
the call must be the `NONE` call; a setup without the exception prunes. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_reapBlind :
    ¬ NU_052_split (nu052s_reapBlind (K := String)) refInFlightBase := by
  intro h
  have := congrArg NuSetup.prune
    (h.2.1 {} nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg nu052s_reapNet (by decide +kernel))
  revert this
  decide +kernel

/-- A setup that applies conflict priority only on a net with a ν-join (the body's scope before
ruling D97 (a)). -/
def nu052s_joinOnly {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  refNuSetup o (sel && k.join) k prio φ cfg X

/-- ✗ Leaving a name-alignment call without a ν-join unsplit violates the companion block (line
4, ruling D97 (a)). Worked example: a `NameAligned` call on the AC7 net, which has no ν-join,
reads `CONFLICT` on Route B, so `H` must be split; a setup scoped to ν-join nets splits nothing
and prunes nothing. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_joinOnly :
    ¬ NU_052_split (nu052s_joinOnly (K := String)) refInFlightBase := by
  intro h
  have := congrArg NuSetup.prune
    (h.2.2.2.1 {} nu052s_alignCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7 (by decide +kernel)
      rfl (Or.inr (by decide +kernel)))
  revert this
  decide +kernel

/-- A setup that turns the pruning off under `assumeAtomicFiring`. -/
def nu052s_atomicOff {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  refNuSetup o (sel && !o.assumeAtomicFiring) k prio φ cfg X

/-- ✗ Turning the pruning off under `assumeAtomicFiring` violates the companion block (line 3).
Worked example: on the AC7 net under `assumeAtomicFiring` nothing is split, and the pruning must
stay on, as AC2 asks of `verify()` under the atomic assumption. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_atomicOff :
    ¬ NU_052_split (nu052s_atomicOff (K := String)) refInFlightBase := by
  intro h
  have := (h.2.2.1 { assumeAtomicFiring := true } nu052s_joinCall ver004_prio7 ver004_bad
    ver004_cfg ver004_ac7 (by decide +kernel) rfl).1
  revert this
  decide +kernel

/-- A setup that prunes without the conflict demand: it hands on the `NONE` configuration. -/
def nu052s_noDemand {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  { refNuSetup o sel k prio φ cfg X with cfg := (refNuSetup o false k prio φ cfg X).cfg }

/-- ✗ Pruning without splitting the pruners violates the companion block (line 4). Worked
example: on the AC7 net the pruner `H` must be forced into the split; a setup that keeps the
`NONE` configuration forces nothing. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_noDemand :
    ¬ NU_052_split (nu052s_noDemand (K := String)) refInFlightBase := by
  intro h
  have := congrArg nu052sForced
    (h.2.2.2.1 {} nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7 (by decide +kernel)
      rfl (Or.inr (by decide +kernel)))
  revert this
  decide +kernel

/-- A setup that never turns the pruning off: a refused split under conflict priority stays
refused. -/
def nu052s_neverOff {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  if nu052sApplies o sel k X then
    ⟨ver004WithConflict prio (ver004WithCount cfg φ) X.net, true, none⟩
  else refNuSetup o sel k prio φ cfg X

/-- ✗ Keeping the pruning on when a pruner cannot be split violates the companion block (line 5,
AC2). Worked example: when the pruner `H` of the AC7 net is a ν-join it cannot be split, so the
call must be verified as under `NONE`; a setup that keeps the conflict demand makes the split
refuse the net and the call answer `Unknown`. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_neverOff :
    ¬ NU_052_split (nu052s_neverOff (K := String)) refInFlightBase := by
  intro h
  have := congrArg NuSetup.prune
    (h.2.2.2.2.1 {} nu052s_joinCall ver004_prio7 ver004_bad { ver004_cfg with joins := ["H"] }
      ver004_ac7 "H" (by decide +kernel) rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- A setup that turns the pruning off without naming the transition. -/
def nu052s_silentOff {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  { refNuSetup o sel k prio φ cfg X with off := none }

/-- ✗ Turning the pruning off without naming the transition violates the companion block (line
5). Worked example: the report of the AC2 call must name the join `H` that could not be split. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_silentOff :
    ¬ NU_052_split (nu052s_silentOff (K := String)) refInFlightBase := by
  intro h
  have := congrArg NuSetup.off
    (h.2.2.2.2.1 {} nu052s_joinCall ver004_prio7 ver004_bad { ver004_cfg with joins := ["H"] }
      ver004_ac7 "H" (by decide +kernel) rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- A setup that adds the conflict demand under `NONE` too: it hands the split the base
configuration with every pruner forced, whatever the mode. -/
def nu052s_noneDemand {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  refNuSetup o sel k prio φ (ver004WithConflict prio cfg X.net) X

/-- ✗ Splitting the pruners under `NONE` violates the companion block (line 1, AC1). Worked
example: under `NONE` the AC7 net is handed to the split with the `QuiescentCount` demand alone,
so nothing is forced. A setup that adds the conflict demand under `NONE` forces the pruner `H`,
and on the AC2 shape, where `H` is a ν-join, the `NONE` call would then answer `Unknown` instead
of the `NONE` verdict. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_noneDemand :
    ¬ NU_052_split (nu052s_noneDemand (K := String)) refInFlightBase := by
  intro h
  have := congrArg SplitCfg.forced
    (h.1 {} nu052s_joinCall ver004_prio7 ver004_bad ver004_cfg ver004_ac7).1
  revert this
  decide +kernel

/-- A setup that keeps the conflict-off note even when the split under `NONE` is refused too. -/
def nu052s_noteKept {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  let c := nu052sApplies o sel k X
  let p := refSplitPlan o c prio φ cfg X
  { cfg := p.1, prune := p.2,
    off := if c && !p.2 then nu052sConflictRefused prio (ver004WithCount cfg φ) X else none }

/-- ✗ Naming the transition when the call ends refused violates the companion block (line 5).
Worked example: on the AC7 net with `H` a ν-join and `ok` tested, the split under `NONE` also
has to split `H` (it deposits into `ok`) and refuses it, so the call answers `Unknown` with that
refusal and every runtime drops the conflict-off note. A setup that still names `H` reports a
line no runtime prints. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_noteKept :
    ¬ NU_052_split (nu052s_noteKept (K := String)) refInFlightBase := by
  intro h
  have := congrArg NuSetup.off
    (h.2.2.2.2.1 {} nu052s_joinCall ver004_prio7 ver004_bad
      { ver004_cfg with joins := ["H"], tested := ["ok"] } ver004_ac7 "H"
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- The property `QuiescentCount([p], min 1)`: with a terminal place it counts `p` as tested. -/
def nu052s_countPhi : VerProp String := .quiescentCount ["p"] 1 none []

/-- A setup that, when it turns the pruning off, hands the split the bare configuration instead
of the `NONE` one, so it forgets the `QuiescentCount` demand. -/
def nu052s_bareOff {K : Type} [DecidableEq K] : NuSetupFn K := fun o sel k prio φ cfg X =>
  let s := refNuSetup o sel k prio φ cfg X
  if s.off.isSome then { s with cfg := cfg } else s

/-- ✗ Forgetting the `QuiescentCount` demand when the pruning is turned off violates the companion
block (line 5). Worked example: on the AC7 net with `bad` terminal, `H` a ν-join and the property
`QuiescentCount([p], min 1)`, the split under conflict priority refuses `H`, so the call is the
`NONE` call, which counts `p` as tested and splits its feeder `t`. A setup that hands on the bare
configuration leaves `p` untested. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_bareOff :
    ¬ NU_052_split (nu052s_bareOff (K := String)) refInFlightBase := by
  intro h
  have := congrArg (fun s => s.cfg.tested)
    (h.2.2.2.2.1 {} nu052s_joinCall ver004_prio7 nu052s_countPhi
      { ver004_cfg with terminals := ["bad"], joins := ["H"] } ver004_ac7 "H"
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel))
  revert this
  decide +kernel

/-- The base layer of a call whose in-flight test is right but whose competition test reads a
demand as the tokens one firing consumes (`consumed_demand` through the firing count). -/
def nu052s_consumedBase : InFlightBase := fun ifl =>
  { refInFlightBase ifl with compete := nu052_consumed }

/-- ✗ A base layer that reads a demand as the tokens consumed violates the companion block
(line 7, ruling D97 (a)). Worked example: `hiDrain : all(0)` and `lo : one(0)` share place `0`,
which holds two tokens. Their required counts are 1 and 1, so they do not compete and `lo` stays
expanded. Read as tokens consumed, `hiDrain` demands both tokens, the two compete, and the graph
over that base layer prunes `lo`. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_consumedBase :
    ¬ NU_052_split (refNuSetup (K := String)) nu052s_consumedBase := by
  intro h
  have := (h.2.2.2.2.2.2 (fun _ => 10) (nu052_a 2) nu052_hiDrain nu052_lo.base).1 rfl
  revert this
  decide

/-- ✗ A base layer that never sees a firing in flight violates the companion block (line 6).
Worked example: the untimed base calls `hi` idle although its in-flight place holds a token, so
`hi` would still pre-empt `lo`. -/
@[evidence forbids NU_052_split]
theorem NU_052_split_forbids_idleTrue :
    ¬ NU_052_split (refNuSetup (K := String)) (fun _ => untimedBase) := by
  intro h
  have := (h.2.2.2.2.2.1 (fun _ => 10) (nu052s_a 1) nu052_hi.base).1 rfl
  revert this
  decide

/-! ## Mutant: no reapable exception -/

/-- Mutant reading of the companion block whose line 2 drops the reapable exception: conflict
priority applies whenever `CONFLICT` is selected and Route B reads the mode of the call (the body
before ruling D97 (a), with the name-alignment scope). Lines 1 and 3 to 7 are as in the block,
with the same reading of 'applies'. -/
def NU_052_split_mutant_reapBlind {K : Type} [DecidableEq K] (M : NuSetupFn K)
    (B : InFlightBase) : Prop :=
  let ap : Options → NuSplitCall → Reference.TimedNet K → Bool := fun _ k _ => k.routeB
  (∀ o k prio φ cfg X, (M o false k prio φ cfg X).cfg = ver004WithCount cfg φ ∧
    (M o false k prio φ cfg X).prune = false ∧ (M o false k prio φ cfg X).off = none) ∧
  (∀ o k prio φ cfg X, ap o k X = false →
    M o true k prio φ cfg X = M o false k prio φ cfg X) ∧
  (∀ o k prio φ cfg X, ap o k X = true → o.assumeAtomicFiring = true →
    (M o true k prio φ cfg X).prune = true ∧ (M o true k prio φ cfg X).off = none) ∧
  (∀ o k prio φ cfg X, ap o k X = true → o.assumeAtomicFiring = false →
    (ver004Pruners prio X.net = [] ∨
      nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = none) →
    M o true k prio φ cfg X =
      ⟨ver004WithConflict prio (M o false k prio φ cfg X).cfg X.net, true, none⟩) ∧
  (∀ o k prio φ cfg X t, ap o k X = true → o.assumeAtomicFiring = false →
    ver004Pruners prio X.net ≠ [] →
    nu052sConflictRefused prio (M o false k prio φ cfg X).cfg X = some t →
    M o true k prio φ cfg X =
      ⟨(M o false k prio φ cfg X).cfg, (M o false k prio φ cfg X).prune,
        if nu052sRefused (M o false k prio φ cfg X).cfg X = none then some t else none⟩) ∧
  (∀ ifl (a : AMarking) (H : Transition), (B ifl).idle a H = true ↔ a (ifl H.name) = 0) ∧
  (∀ ifl (a : AMarking) (H L : Transition),
    (B ifl).compete a H L = true ↔ ∃ sh ∈ H.inputs, (∃ sl ∈ L.inputs, sl.place = sh.place) ∧
      a sh.place < demandOn H sh.place + demandOn L sh.place)

/-- The setup without the reapable exception kills the mutant. Worked example: it is the
reference read with `assumeNoReaping` always set, so it meets the mutant reading (the reference's
lines with no transition ever read as reapable), but the companion block asks that the call on
the AC7 net with `L` timed `deadline(5)` be the `NONE` call, and it prunes there. -/
@[evidence mutant NU_052_split]
theorem NU_052_split_mutant_reapBlind_killed :
    NU_052_split_mutant_reapBlind (nu052s_reapBlind (K := String)) refInFlightBase ∧
      ¬ NU_052_split (nu052s_reapBlind (K := String)) refInFlightBase := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := NU_052_split_reference (K := String)
  have hap : ∀ (o : Options) sel k (X : Reference.TimedNet String),
      nu052sApplies { o with assumeNoReaping := true } sel k X = (sel && k.routeB) := by
    intro o sel k X; simp [nu052sApplies, nu052sReapable]
  refine ⟨⟨fun o k prio φ cfg X => r1 _ k prio φ cfg X,
      fun o k prio φ cfg X h => r2 _ k prio φ cfg X (by rw [hap]; simpa using h),
      fun o k prio φ cfg X h hat => r3 _ k prio φ cfg X (by rw [hap]; simpa using h) hat,
      fun o k prio φ cfg X h hat hp => r4 _ k prio φ cfg X (by rw [hap]; simpa using h) hat hp,
      fun o k prio φ cfg X t h hat hp ht =>
        r5 _ k prio φ cfg X t (by rw [hap]; simpa using h) hat hp ht, r6, r7⟩,
    NU_052_split_forbids_reapBlind⟩

end Libpetri.Spec
