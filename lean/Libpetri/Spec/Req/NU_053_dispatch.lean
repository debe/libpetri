import Libpetri.Spec.Registry
import Libpetri.Spec.Verifier.Pipeline
import Libpetri.Spec.Req.VER_015

set_option linter.missingDocs true

/-!
# NU-053 (B): the coloured plan's place in the dispatch (`spec/12-nu-nets.md`)

The first NU-053 block (`Spec/Req/NU_053.lean`) states what the coloured encoding of Route A
computes: the colour-slot bound, its exact re-check, the consumer rule and the colour-aware
quiescence term. This block states where that encoding sits in the verifier's dispatch, as a
predicate over a dispatch: a list of pipeline steps (`GStep` of `Spec/Verifier/Pipeline.lean`)
over a `NuCall`, the facts of one verification call that the runtimes' guards read.

Six lines: Route B never runs after the colour-slot bound; on a quiescence query the colour-slot
bound runs only in a call that ran Route B; the colour-slot bound runs only on a budgeted net
with a ν-join and without injection; a Route B `Unknown` on a bounded quiescence query hands over
instead of ending the call; the fixpoint query of a coloured plan decides with the coloured
verdict, not downgraded; and without a coloured plan the fixpoint query never proves a
quiescence property of a net with a ν-join. The witness `refNuDispatch` is the runtimes'
thirteen steps, with Route B, the colour-slot bound and the fixpoint query modelled and every
other step left free. `Nu053DispatchCovers` is the offer the block leaves to coverage: a bounded
quiescence query runs Route B, and when its graph truncates the call ends with the coloured
verdict.
-/

namespace Libpetri.Spec

open Libpetri.Spec.Verifier

/-! ## The model -/

/-- **What the coloured plan's place in the dispatch reads of one verification call.** -/
structure NuCall where
  /-- The property is a quiescence property: `DeadlockFree`, `TerminatesAtSink`,
  `JoinedOrDeadLettered` or `QuiescentCount`. -/
  quiescence : Bool
  /-- The property is a name-alignment property of [NU-055], which Route B alone decides. -/
  nameAlign : Bool
  /-- The net has a ν-join: a transition with a match specification. -/
  join : Bool
  /-- A budget place is declared. -/
  budget : Bool
  /-- Route A declines the call for injection: environment injection is modelled on the flat
  net, or an arrival transition feeds a coloured place ([VER-006] AC10). -/
  injection : Bool
  /-- Route B declines under environment injection before it builds its graph ([VER-006]
  AC8). -/
  envDecline : Bool
  /-- What Route B's name-partition graph returns: `none` outside its fragment, else its
  verdict (an `Unknown` when it truncates). -/
  graph : Option Verdict
  /-- The structural checks of the coloured plan pass, so the colour-slot program is solved. -/
  fragment : Bool
  /-- The colour-slot program sets a bound and the coloured plan is built. -/
  plan : Bool
  /-- The call is under `Ignore` with environment places registered ([VER-006]). -/
  ignoreEnv : Bool
  /-- The verdict of the coloured fixpoint query, when there is a plan. -/
  coloured : Verdict
  /-- The verdict of the flat fixpoint query, when there is no plan. -/
  flat : Verdict
  /-- Whether each other step of the pipeline runs on this call. -/
  applies : String → Bool
  /-- What each other step of the pipeline returns on this call. -/
  outcome : String → PhaseOut

namespace NuCall

/-- Route B's `Unknown` hands over rather than ends the call: a quiescence property that is
not a name-alignment property, on a net with a declared budget place. -/
def defers (q : NuCall) : Bool := q.quiescence && q.budget && !q.nameAlign

/-- Route B runs: a name-alignment property, or a net with a ν-join and a quiescence property
or no declared budget place. -/
def routeB (q : NuCall) : Bool := q.nameAlign || (q.join && (q.quiescence || !q.budget))

/-- The colour-slot bound runs: a ν-join, a declared budget place, no injection, and the plan's
structural checks pass. -/
def slotOk (q : NuCall) : Bool := q.join && q.budget && !q.injection && q.fragment

/-- The coloured plan is built. -/
def planOk (q : NuCall) : Bool := q.slotOk && q.plan

end NuCall

/-- **A ν dispatch**: the pipeline's steps over a verification call. -/
abbrev NuDispatch : Type := List (GStep NuCall)

/-- The steps a run of the dispatch `D` enters, in order, from a trail `t`. -/
def nuLog (D : NuDispatch) (O : Oracle) (stop : Stop) (o : Options) (q : NuCall)
    (t : Trail) : List String :=
  (runPipeline O stop o q D t).2.entered

/-! ## The reference dispatch -/

/-- **Route B's step**: under environment injection it declines with `Unknown`; outside its
fragment it hands over, except for a name-alignment property; a truncated graph hands over on a
bounded quiescence query and ends the call otherwise; every other verdict ends the call. -/
def nuRouteBStep : GStep NuCall :=
  { name := "Route B (ν name-partition graph)", route := .nuScg,
    applies := fun _ q => q.routeB,
    run := fun _ q =>
      if q.envDecline then .done (.decided (.unknown "Declined under environment injection") [] none)
      else match q.graph with
        | none =>
          if q.nameAlign then .done (.decided (.unknown "outside the fragment") [] none)
          else .done (.aside "Route B declined")
        | some (.unknown w) =>
          if q.defers then .done (.aside "Route B inconclusive; deferring to Route A")
          else .done (.decided (.unknown w) [] none)
        | some v => .done (.decided v [] none) }

/-- **The colour-slot bound**: entered when the coloured plan is attempted; it never decides. -/
def nuSlotStep : GStep NuCall :=
  { name := "colour-slot bound", route := .smt, applies := fun _ q => q.slotOk,
    run := fun _ _ => .done (.aside "colour-slot bound") }

/-- The downgrade of [VER-006] under `Ignore` with environment places: a `Proven` becomes
`Unknown`. -/
def nuIgnoreDown : Verdict → Verdict
  | .proven _ => .unknown "Ignore mode: a proof that holds only without injection"
  | v => v

/-- The name-blind guard of the flat fixpoint query (`apply_nu_guard` with no coloured plan): on
a net with a ν-join, a quiescence verdict becomes `Unknown`, and so does any verdict without a
declared budget place. -/
def nuNameBlind (q : NuCall) : Verdict → Verdict
  | .unknown w => .unknown w
  | v =>
    if q.join then
      if q.quiescence then .unknown "quiescence on a ν-net needs the exact ν-analysis"
      else if q.budget then v else .unknown "unbounded fresh names"
    else v

/-- The verdict the reference fixpoint query decides with: the coloured verdict with a plan, the
guarded flat verdict without one, each after the `Ignore` downgrade. -/
def nuIc3Verdict (q : NuCall) : Verdict :=
  if q.planOk then (if q.ignoreEnv then nuIgnoreDown q.coloured else q.coloured)
  else nuNameBlind q (if q.ignoreEnv then nuIgnoreDown q.flat else q.flat)

/-- **The fixpoint query**: entered whenever it is reached, and always decides. -/
def nuIc3Step : GStep NuCall :=
  { name := "IC3/PDR query", route := .smt,
    run := fun _ q => .done (.decided (nuIc3Verdict q) [] none) }

/-- Any other step: entered and answered as the call says. -/
def otherNuStep (name : String) (route : Route) : GStep NuCall :=
  { name, route, applies := fun _ q => q.applies name, run := fun _ q => .done (q.outcome name) }

/-- **The reference dispatch**: the runtimes' thirteen steps, with Route B, the colour-slot bound
and the fixpoint query modelled and every other step left free. -/
def refNuDispatch : NuDispatch :=
  [nuRouteBStep, otherNuStep "linear bound" .structural,
   otherNuStep "state-space enumeration" .enumeration, otherNuStep "flattening" .smt,
   otherNuStep "structural pre-check" .structural, otherNuStep "P-invariant computation" .smt,
   otherNuStep "linear bound" .structural, otherNuStep "state-equation phase" .smt,
   otherNuStep "firing-bound phase" .smt, nuSlotStep, otherNuStep "witness phase" .smt,
   nuIc3Step, otherNuStep "certificate check" .smt]

/- The reference dispatch is the witness of `NU_053_dispatch`'s `holds` theorem. -/
#spec_witness refNuDispatch

/-- The reference dispatch carries the runtimes' step names. -/
theorem refNuDispatch_names : refNuDispatch.map GStep.name = rtStepNames := rfl

/-- The only step of the reference dispatch with a given modelled name is the modelled step. -/
theorem refNu_steps {s : GStep NuCall} (hs : s ∈ refNuDispatch) :
    (s.name = "Route B (ν name-partition graph)" → s = nuRouteBStep) ∧
    (s.name = "colour-slot bound" → s = nuSlotStep) ∧
    (s.name = "IC3/PDR query" → s = nuIc3Step) := by
  simp only [refNuDispatch, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [otherNuStep, nuRouteBStep, nuSlotStep, nuIc3Step]

/-! ## NU-053 (B) -/

requirement NU_053_dispatch
  id "NU-053"
  title "EXTENDED-Coloured Quiescence in the Route A SMT Encoder: Place in the Dispatch"
  kind B
  scope "the dispatch of the SMT verifier on ν-nets, where the coloured encoding of Route A is offered (MAY; the shall sentences bind an implementation that offers it)"
  source verbatim "spec/12-nu-nets.md"
  quote "The verifier routes a bounded quiescence query to Route B first; when Route B truncates (`Unknown`), it **defers** to this scalable Route A encoding rather than returning `Unknown`."
        "A verdict from the coloured plan is not downgraded as a name-blind verdict would be (the colour-aware deadlock does not over-fire joins); only the `Ignore` downgrade of [VER-006] applies to it."
        "The verifier *shall not* run Route B ([VER-012]) after the colour-slot bound in one verification call."
        "*When* the verifier runs the colour-slot bound for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property, it *shall* have run Route B ([VER-012]) in the same verification call."
        "The verifier *shall not* run the colour-slot bound on a net without a ν-join or without a declared budget place, or when environment injection is modelled or an arrival feeds a coloured place ([VER-006])."
        "*When* Route B builds its name-partition graph for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a declared budget place and the graph returns `Unknown`, the verifier *shall not* return that `Unknown` from Route B and *shall* hand the query over to the next phase of the dispatch."
        "*When* the verifier has built the coloured plan and the call is not under `Ignore` with environment places registered, the fixpoint query *shall* decide with the verdict of the coloured query and *shall not* downgrade it."
        "*When* the verifier has not built the coloured plan for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a ν-join, the fixpoint query *shall not* return `Proven`."
  reading "For every dispatch D, solver O, stop, options o, call q and trail t whose log of entered steps is empty, in the log of the steps the run of D enters from t: no step named Route B (ν name-partition graph) is entered after a step named colour-slot bound;"
          "on a call whose property is a quiescence property, a colour-slot bound is entered only in a run that also enters a step named Route B (ν name-partition graph);"
          "and a colour-slot bound is entered only on a call with a ν-join, a declared budget place and no injection;"
          "every step of D named Route B (ν name-partition graph), on a call whose property is a quiescence property and not a name-alignment property, with a declared budget place, no decline under environment injection and a graph that returns Unknown, under any options and replies R, can return only an aside, which hands over to the next step;"
          "every step of D named IC3/PDR query, on a call where the coloured plan is built and that is not under Ignore with environment places registered, under any options and replies R, decides with the call's coloured verdict;"
          "every step of D named IC3/PDR query, on a call with a ν-join and a quiescence property where the coloured plan is not built, under any options and replies R, never returns Proven."
  assumes "The model is a dispatch D: a list of pipeline steps (GStep of Spec/Verifier/Pipeline.lean) over a NuCall, run by runPipeline, as in the order block of VER-015 (VER_015_order). A step whose guard fails is skipped; an applicable step polls the stop, is entered and logged; an aside goes on to the next step and a decision ends the run. The run semantics are Pipeline.lean's, fixed. The step names are the runtimes' (rtStepNames; refNuDispatch_names pins them): Route B (ν name-partition graph) is Route B, colour-slot bound is the step that solves the colour-slot program of the coloured plan (Rust total_budget::step inside the slot-bound closure, Java and TypeScript enter in colouredAttempt's solve), and IC3/PDR query is the fixpoint query, coloured or flat. To run the colour-slot bound is to enter its step."
          "A NuCall carries what the runtimes' guards read of one call: the kind of property (a quiescence property, a name-alignment property of NU-055), whether the net has a ν-join and a declared budget place, whether Route A declines for injection (injection modelled on the flat net, or an arrival into a coloured place, VER-006 AC10), whether Route B declines under environment injection before building its graph (VER-006 AC8), what Route B's graph returns, whether the plan's structural checks pass and whether the colour-slot program sets a bound, the Ignore mode with environment places, the verdicts of the coloured and of the flat fixpoint query, and for every other step whether it runs and what it returns. The reference leaves the other steps free (otherNuStep), so the lines hold whatever they do; their guards and phases are their own blocks' (VER-015, VER-017, VER-018, VER-019, VER-020, VER-025). Which properties the coloured encoding decides, and with which slot count, is the first NU-053 block's; this block reads the plan as given."
          "The witness is refNuDispatch: Route B enters when the property is a name-alignment property, or the net has a ν-join and the property is a quiescence property or no budget place is declared (smt_verifier.rs, the Route B trigger; SmtVerifier.java and smt-verifier.ts likewise). Its graph's Unknown hands over exactly when the property is a quiescence property, not a name-alignment one, and a budget place is declared (defer_to_route_a in smt_verifier.rs, deferToRouteA in SmtVerifier.java and smt-verifier.ts); the decline under environment injection comes before the graph and ends the call. The colour-slot bound enters when the net has a ν-join, a budget place is declared, no injection is modelled, no arrival feeds a coloured place and build_plan's structural checks pass (coloured_attempt in smt_verifier.rs, colouredAttempt in SmtVerifier.java and smt-verifier.ts). The fixpoint query decides with the coloured verdict when the plan is built, and otherwise with the flat verdict through the name-blind guard (apply_nu_guard in smt_verifier.rs, applyNuGuard in Java and TypeScript); both pass the Ignore downgrade of VER-006 first."
          "Line 1 is 'The verifier shall not run Route B ([VER-012]) after the colour-slot bound in one verification call', killed by NU_053_dispatch_forbids_slotFirst. It is a safety line: it holds of a call that never enters Route B, as a budgeted reachability-safety call of a ν-net does (that property stays on Route A, NU-055). Line 2 is the EARS sentence that a colour-slot bound for a quiescence property needs Route B in the same call. Lines 1 and 2 together are the first half of 'The verifier routes a bounded quiescence query to Route B first', for every call that reaches the colour-slot bound: Route B was entered, and before it. A Route B whose trigger leaves out a bounded quiescence query (the trigger's inner or written as and, so that Route B runs only on an unbudgeted one) is killed (NU_053_dispatch_forbids_skipRouteB). That Route B runs on a bounded quiescence query with a ν-join even when the call never reaches the colour-slot bound is the routing itself, an offer: the coverage condition Nu053DispatchCovers asks for Route B in the log, shown of the reference by nu053DispatchCovers_reference."
          "Line 3 is 'The verifier shall not run the colour-slot bound on a net without a ν-join or without a declared budget place, or when environment injection is modelled or an arrival feeds a coloured place ([VER-006])' and the quiescence bullet's 'The encoding has no environment-injection rule, so it does not answer when injection is modelled ([VER-006] AC7)'. Each of its three conditions is killed by its own wrong guard: NU_053_dispatch_forbids_noJoin, NU_053_dispatch_forbids_noBudget and NU_053_dispatch_forbids_injection. That a coloured verdict needs a built plan, and a plan the colour-slot bound, is the call record's shape: planOk includes the guard of the colour-slot bound, and is not tied to the colour-slot step having been entered in the run."
          "Line 4 is the EARS sentence on Route B's Unknown and the second half of 'The verifier routes a bounded quiescence query to Route B first; when Route B truncates (Unknown), it defers to this scalable Route A encoding rather than returning Unknown'. The runtimes defer on every Unknown the graph returns, not only on a truncation, so the line reads 'the graph returns Unknown'. A Route B step that returns its truncation as the verdict is killed (NU_053_dispatch_forbids_noDefer). That the hand-over reaches the coloured plan, when the plan is built and no later step decides first, is an offer, not a safety line: it is the coverage condition Nu053DispatchCovers (the convention of GlossaryExec), shown of the reference by nu053DispatchCovers_reference. When the total budget or cancellation of VER-013 fires, the run ends without a next step; that is the stop of runPipeline (VER-013's block), so the hand-over holds of every run that is not stopped."
          "Line 5 is 'A verdict from the coloured plan is not downgraded as a name-blind verdict would be (the colour-aware deadlock does not over-fire joins); only the Ignore downgrade of [VER-006] applies to it' and its EARS sentence, with AC6's 'quiescence is decided, never downgraded to Unknown as a name-blind verdict would be' for the zero-slot plan. A fixpoint query that applies the name-blind quiescence downgrade to a coloured verdict is killed (NU_053_dispatch_forbids_downgrade). The Ignore downgrade of VER-006 also applies to a coloured Proven, so the line excludes a call under Ignore with environment places registered; that downgrade is VER-006's. When a stop of VER-013 fires during the query, the finisher replaces an Unknown's reason (finishVerdict); a Proven or Violated stands, as VER-013's block states."
          "Line 6 is the EARS sentence on a call without a coloured plan and the body's 'When no weighting exists (the program is infeasible) the coloured tokens are not structurally bounded, a genuine colour leak, so the plan is refused and the query falls back to the sound over-approximation', for a quiescence property: the name-blind encoding over-fires joins, so its quiescence verdict is not believed. A fixpoint query that returns the flat verdict unguarded is killed (NU_053_dispatch_forbids_unguarded). The runtimes return Unknown there, a Violated included; the line asks only for no Proven, which is what NU-053 says, and the full guard (Unknown for every verdict without a declared budget place, the over-approximation note) is NU-050's and NU-040's. For a reachability-safety property the flat Proven is sound (the first NU-053 block's NU_053_tokens_le and NU-050), so a fallback there may prove. A quiescence property of a NuCall is one of the four the sentences of lines 2, 4 and 6 list; QuiescentNameAligned, which NU-055 also calls a quiescence property, is a name-alignment property that Route B alone decides (NU-055). Lines 4 to 6 constrain every step of D with that name, whether or not its guard lets the call in; line 4 does not read whether the net is a ν-net (a NuCall has no such field) and asks for no name-alignment property, which none of the four listed properties is. Each of these makes a line stronger than its sentence, never weaker."
          "The paragraph on the linear bound of VER-015 ('For a reachability-safety property the linear state-equation bound of [VER-015] runs before the coloured query (after Route B)', its Proven 'ends the query', 'any other outcome hands over to the coloured query unchanged', 'The coloured plan, and the linear program behind its slot bound, are built only when the bound does not prove') is VER_015_order: lines 1, 2 and 6 there put the bound after Route B and before the colour-slot bound, its line 9 makes the bound only prove or hand over, and a decision ends the run. That the bound's Proven is sound on a ν-net ('written over the flat, name-blind net, which over-approximates the ν semantics') is NU-050's and Novel/RouteA/SlotBound.lean's. 'The colour-slot bound k is often several times the budget, and a trivially true bound that IC3 cannot close over k colours within the timeout is proven by the state equation in milliseconds' is motivation."
          "'Its Proven is sound while the declared mints and the coloured consumers keep their contracts ([NU-010], [NU-051])' is the soundness of the coloured plan, NU-050's Route A line over RefNuReach (wave W9, design ruling S7 (a)); the current evidence is Novel.RouteA.routeA_safety_sound_plan and routeA_quiescence_sound_reaping. The report text (colour-slot bound k=<k>, the deferral line, the transitions whose contracts it assumes) is kind N."
          "AC1 (Proven deadlock-free via the coloured Route A encoding) and the test derivation's 'a co-mint→join net is Proven deadlock-free via Route A when Route B is forced to truncate' are lines 2, 4 and 5 with the coverage condition: NU_053_dispatch_nonvacuous shows a bounded DeadlockFree call whose graph truncates enter Route B, then the colour-slot bound, and end with the coloured Proven, route smt. AC2 (removing the drain turns it Violated) is the coloured verdict, which line 5 passes unchanged; the verdict itself is the first block's and the soundness line's. AC4 and AC5 (a net with no covering weighting falls back rather than a false Proven) are line 6 for a quiescence property, with the first block's NU_053_infeasible for 'no plan'. AC3 and AC7 to AC9 are the first block's and kind Q."
  signoff "pending"
  statement : NuDispatch → Prop :=
    fun D =>
      (∀ (O : Oracle) (stop : Stop) (o : Options) (q : NuCall) (t : Trail), t.entered = [] →
        Ordered (nuLog D O stop o q t) "Route B (ν name-partition graph)" "colour-slot bound" ∧
        ("colour-slot bound" ∈ nuLog D O stop o q t → q.quiescence = true →
          "Route B (ν name-partition graph)" ∈ nuLog D O stop o q t) ∧
        ("colour-slot bound" ∈ nuLog D O stop o q t →
          q.join = true ∧ q.budget = true ∧ q.injection = false)) ∧
      (∀ s ∈ D, s.name = "Route B (ν name-partition graph)" →
        ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut)
          (w : String),
          q.defers = true → q.envDecline = false → q.graph = some (.unknown w) →
          Yields R (s.run o q) out → ∃ n, out = .aside n) ∧
      (∀ s ∈ D, s.name = "IC3/PDR query" →
        ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut),
          q.planOk = true → q.ignoreEnv = false →
          Yields R (s.run o q) out → ∃ tr c, out = .decided q.coloured tr c) ∧
      (∀ s ∈ D, s.name = "IC3/PDR query" →
        ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut),
          q.planOk = false → q.join = true → q.quiescence = true →
          Yields R (s.run o q) out → ∀ m tr c, out ≠ .decided (.proven m) tr c)

/- The pinned readable form of the dispatch block: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.NU_053_dispatch : NuDispatch → Prop :=
fun D =>
  (∀ (O : Oracle) (stop : Stop) (o : Options) (q : NuCall) (t : Trail),
      t.entered = [] →
        Ordered (nuLog D O stop o q t) "Route B (ν name-partition graph)" "colour-slot bound" ∧
          ("colour-slot bound" ∈ nuLog D O stop o q t →
              q.quiescence = true → "Route B (ν name-partition graph)" ∈ nuLog D O stop o q t) ∧
            ("colour-slot bound" ∈ nuLog D O stop o q t → q.join = true ∧ q.budget = true ∧ q.injection = false)) ∧
    (∀ s ∈ D,
        s.name = "Route B (ν name-partition graph)" →
          ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut) (w : String),
            q.defers = true →
              q.envDecline = false →
                q.graph = some (Verdict.unknown w) → Yields R (s.run o q) out → ∃ n, out = PhaseOut.aside n) ∧
      (∀ s ∈ D,
          s.name = "IC3/PDR query" →
            ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut),
              q.planOk = true →
                q.ignoreEnv = false → Yields R (s.run o q) out → ∃ tr c, out = PhaseOut.decided q.coloured tr c) ∧
        ∀ s ∈ D,
          s.name = "IC3/PDR query" →
            ∀ (o : Options) (q : NuCall) (R : String → SolverReply → Prop) (out : PhaseOut),
              q.planOk = false →
                q.join = true →
                  q.quiescence = true →
                    Yields R (s.run o q) out →
                      ∀ (m : String) (tr : List String) (c : Option Bool),
                        out ≠ PhaseOut.decided (Verdict.proven m) tr c
-/
#guard_msgs in #print NU_053_dispatch

/-- The colour-slot bound of the reference is entered only on a call with a ν-join, a declared
budget place and no injection. -/
theorem refNu_slot_guard {O : Oracle} {stop : Stop} {o : Options} {q : NuCall} {t : Trail}
    (ht : t.entered = []) (hm : "colour-slot bound" ∈ nuLog refNuDispatch O stop o q t) :
    q.join = true ∧ q.budget = true ∧ q.injection = false := by
  obtain ⟨s, hs, ha, hn⟩ := ver015_run_mem (O := O) (stop := stop) (o := o) (q := q) ht hm
  obtain rfl := (refNu_steps hs).2.1 hn
  simp only [nuSlotStep, NuCall.slotOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at ha
  exact ⟨ha.1.1.1, ha.1.1.2, ha.1.2⟩

/-- **The runtimes' dispatch meets the block.** Route B is the first step and the colour-slot
bound the tenth, so a run never enters them the other way round. A quiescence call that reaches
the colour-slot bound has a ν-join, so Route B, the first step, applies to it and was entered on
the way. The colour-slot bound is guarded on a ν-join, a budget place and no injection. Route B
hands a truncated graph over on a bounded quiescence query. The fixpoint query decides with the
coloured verdict when the plan is built, and passes a flat quiescence verdict on a net with a
ν-join through the name-blind guard, which never leaves it `Proven`. -/
@[evidence holds NU_053_dispatch]
theorem NU_053_dispatch_reference : NU_053_dispatch refNuDispatch := by
  refine ⟨fun O stop o q t ht => ⟨?_, fun hm hq => ?_, fun hm => refNu_slot_guard ht hm⟩,
    fun s hs hn o q R out w hd he hg hy => ?_,
    fun s hs hn o q R out hp hi hy => ?_, fun s hs hn o q R out hp hj hq hy m tr c => ?_⟩
  · have hsub := ver015_run_sublist (O := O) (stop := stop) (o := o) (q := q) refNuDispatch ht
    have hall : (nuLog refNuDispatch O stop o q t).Sublist rtStepNames := by
      rw [← refNuDispatch_names]; exact hsub.trans (ver015_applied_sublist _)
    exact (by decide : Before rtStepNames _ _).ordered hall
  · have hj := (refNu_slot_guard ht hm).1
    have happ : nuRouteBStep.applies o q = true := by
      simp [nuRouteBStep, NuCall.routeB, hj, hq]
    exact ver015_run_reach (P := []) (S := refNuDispatch.tail) ht happ (by simp) hm
  · obtain rfl := (refNu_steps hs).1 hn
    simp only [nuRouteBStep, he, hg, hd, Bool.false_eq_true, if_false, if_true,
      Yields.done_iff] at hy
    exact ⟨_, hy⟩
  · obtain rfl := (refNu_steps hs).2.2 hn
    simp only [nuIc3Step, nuIc3Verdict, hp, hi, Bool.false_eq_true, if_false, if_true,
      Yields.done_iff] at hy
    exact ⟨_, _, hy⟩
  · obtain rfl := (refNu_steps hs).2.2 hn
    simp only [nuIc3Step, nuIc3Verdict, hp, Bool.false_eq_true, if_false, Yields.done_iff] at hy
    subst hy
    intro h
    simp only [PhaseOut.decided.injEq] at h
    obtain ⟨hv, -, -⟩ := h
    revert hv
    generalize (if q.ignoreEnv = true then nuIgnoreDown q.flat else q.flat) = v
    cases v <;> simp [nuNameBlind, hj, hq]

/-! ## Examples -/

/-- A bounded `DeadlockFree` call on a ν-net with a ν-join: Route B's graph truncates, the plan
is built, the coloured query proves, the flat query would prove too; the linear bound (no
demand), the enumeration (a ν-join), the state-equation, firing-bound and witness phases and the
certificate check do not run, every other step steps aside. -/
def nqTrunc : NuCall :=
  { quiescence := true, nameAlign := false, join := true, budget := true, injection := false,
    envDecline := false, graph := some (.unknown "name-partition truncated"), fragment := true,
    plan := true, ignoreEnv := false, coloured := .proven "IC3/PDR", flat := .proven "IC3/PDR",
    applies := fun n => !(n == "linear bound" || n == "state-space enumeration" ||
      n == "state-equation phase" || n == "firing-bound phase" || n == "witness phase" ||
      n == "certificate check"),
    outcome := fun _ => .aside "steps aside" }

/-- ✓ **The coloured plan after Route B, on four calls.** When Route B's graph truncates on a
bounded `DeadlockFree` query, the call goes on through flattening, the structural pre-check and
the P-invariants to the colour-slot bound, and the fixpoint query ends it with the coloured
`Proven`, route `smt`. When Route B's graph decides `Violated` the call ends there. With no plan
(the colour-slot program has no covering weighting) the fixpoint query falls back and answers
`Unknown`, not `Proven`. Under modelled injection the colour-slot bound is not entered. -/
@[evidence nonvacuous NU_053_dispatch]
theorem NU_053_dispatch_nonvacuous :
    nuLog refNuDispatch satOracle noStop {} nqTrunc {} =
      ["Route B (ν name-partition graph)", "flattening", "structural pre-check",
       "P-invariant computation", "colour-slot bound", "IC3/PDR query"] ∧
    (runPipeline satOracle noStop {} nqTrunc refNuDispatch {}).1 =
      some (.smt, .decided (.proven "IC3/PDR") [] none) ∧
    nuLog refNuDispatch satOracle noStop {} { nqTrunc with graph := some .violated } {} =
      ["Route B (ν name-partition graph)"] ∧
    (runPipeline satOracle noStop {} { nqTrunc with graph := some .violated } refNuDispatch {}).1 =
      some (.nuScg, .decided .violated [] none) ∧
    (runPipeline satOracle noStop {} { nqTrunc with plan := false } refNuDispatch {}).1 =
      some (.smt, .decided (.unknown "quiescence on a ν-net needs the exact ν-analysis") [] none) ∧
    "colour-slot bound" ∉ nuLog refNuDispatch satOracle noStop {} { nqTrunc with injection := true } {} := by
  refine ⟨by decide, rfl, by decide, rfl, rfl, by decide⟩

/-! ## Coverage -/

/-- **The routing and the deferral, as an offer**: on some bounded quiescence call with a ν-join
whose Route B graph returns `Unknown`, the dispatch enters Route B, then the colour-slot bound,
and the call ends with the coloured verdict. The block's lines are safety lines and hold of a
dispatch that never routes to Route B or never defers; this condition is the existence half (the
convention of `GlossaryExec`), for the consistency theorem. -/
def Nu053DispatchCovers (D : NuDispatch) : Prop :=
  ∃ (O : Oracle) (o : Options) (q : NuCall) (w : String),
    q.defers = true ∧ q.join = true ∧ q.graph = some (.unknown w) ∧
    "Route B (ν name-partition graph)" ∈ nuLog D O noStop o q {} ∧
    "colour-slot bound" ∈ nuLog D O noStop o q {} ∧
    ∃ r, (runPipeline O noStop o q D {}).1 = some (r, .decided q.coloured [] none)

/-- The reference dispatch routes and defers: on the bounded `DeadlockFree` call `nqTrunc` with a
ν-join, Route B runs first and its graph truncates, the colour-slot bound runs, and the call ends
with the coloured `Proven`. -/
theorem nu053DispatchCovers_reference : Nu053DispatchCovers refNuDispatch :=
  ⟨satOracle, {}, nqTrunc, _, rfl, rfl, rfl, by decide, by decide, .smt, rfl⟩

/-! ## Wrong dispatches -/

/-- A dispatch that solves the colour-slot program before Route B. -/
def mutNuSlotFirst : NuDispatch := [nuSlotStep, nuRouteBStep]

/-- ✗ **Route B comes first.** On a bounded `DeadlockFree` call where Route B's graph is outside
its fragment (so Route B steps aside), a dispatch that solves the colour-slot program and then
runs Route B enters them in the wrong order. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_slotFirst : ¬ NU_053_dispatch mutNuSlotFirst := by
  intro h
  have := (h.1 satOracle noStop {} { nqTrunc with graph := none } {} rfl).1
  revert this
  rw [ver015_ordered_iff]
  decide

/-- The reference dispatch with a slip in Route B's trigger: the inner "or" written as "and", so
Route B runs only on a quiescence call with no declared budget place. -/
def mutNuSkipRouteB : NuDispatch :=
  { nuRouteBStep with applies := fun _ q => q.nameAlign || (q.join && q.quiescence && !q.budget) } ::
    refNuDispatch.tail

/-- ✗ **A bounded quiescence query goes to Route B first.** On a bounded `DeadlockFree` call with
a ν-join, a dispatch whose Route B trigger leaves out budgeted quiescence skips Route B and goes
straight through flattening, the structural pre-check and the P-invariants to the colour-slot
bound, so the exact, timed Route B never sees the query. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_skipRouteB : ¬ NU_053_dispatch mutNuSkipRouteB := by
  intro h
  have := (h.1 satOracle noStop {} nqTrunc {} rfl).2.1 (by decide) rfl
  revert this
  decide

/-- A dispatch whose colour-slot bound ignores injection. -/
def mutNuSlotInjection : NuDispatch :=
  [{ nuSlotStep with applies := fun _ q => q.join && q.budget && q.fragment }]

/-- ✗ **No coloured plan under injection.** The coloured encoding has no injection rule, so a
dispatch that solves the colour-slot program on a call with modelled injection is rejected. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_injection : ¬ NU_053_dispatch mutNuSlotInjection := by
  intro h
  have := (h.1 satOracle noStop {} { nqTrunc with injection := true } {} rfl).2.2 (by decide)
  revert this
  decide

/-- A dispatch whose colour-slot bound does not ask for a ν-join. -/
def mutNuSlotNoJoin : NuDispatch :=
  [{ nuSlotStep with applies := fun _ q => q.budget && !q.injection && q.fragment }]

/-- ✗ **No coloured plan without a ν-join.** A dispatch that solves the colour-slot program on a
budgeted call whose net has no transition with a match specification is rejected. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_noJoin : ¬ NU_053_dispatch mutNuSlotNoJoin := by
  intro h
  have := (h.1 satOracle noStop {} { nqTrunc with join := false } {} rfl).2.2 (by decide)
  revert this
  decide

/-- A dispatch whose colour-slot bound does not ask for a declared budget place. -/
def mutNuSlotNoBudget : NuDispatch :=
  [{ nuSlotStep with applies := fun _ q => q.join && !q.injection && q.fragment }]

/-- ✗ **No coloured plan without a budget place.** A dispatch that solves the colour-slot program
on a net with a ν-join but no declared budget place is rejected. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_noBudget : ¬ NU_053_dispatch mutNuSlotNoBudget := by
  intro h
  have := (h.1 satOracle noStop {} { nqTrunc with budget := false } {} rfl).2.2 (by decide)
  revert this
  decide

/-- Route B as it was before the deferral: a truncated graph ends the call with `Unknown`. -/
def mutNuNoDefer : NuDispatch :=
  [{ nuRouteBStep with run := fun _ q =>
      match q.graph with
      | some v => .done (.decided v [] none)
      | none => .done (.aside "Route B declined") }]

/-- ✗ **A truncated Route B hands over.** On a bounded `DeadlockFree` call whose graph truncates,
a Route B that returns its `Unknown` ends the call before the coloured plan can decide it. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_noDefer : ¬ NU_053_dispatch mutNuNoDefer := by
  intro h
  obtain ⟨n, hn⟩ := h.2.1 _ List.mem_cons_self rfl {} nqTrunc (fun _ _ => True) _
    "name-partition truncated" rfl rfl rfl (.done _)
  cases hn

/-- A fixpoint query that applies the name-blind quiescence downgrade to every verdict, the
coloured one included. -/
def mutNuDowngrade : NuDispatch :=
  [{ nuIc3Step with
      run := fun _ q => .done (.decided (nuNameBlind q (if q.planOk then q.coloured else q.flat)) [] none) }]

/-- ✗ **A coloured verdict is not downgraded.** On a bounded `DeadlockFree` call with a built
plan whose coloured query proves, a fixpoint query that still applies the name-blind quiescence
guard turns the `Proven` into `Unknown`. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_downgrade : ¬ NU_053_dispatch mutNuDowngrade := by
  intro h
  obtain ⟨tr, c, hc⟩ := h.2.2.1 _ List.mem_cons_self rfl {} nqTrunc (fun _ _ => True) _ rfl rfl
    (.done _)
  cases hc

/-- A fixpoint query that returns the flat verdict unguarded when there is no plan. -/
def mutNuUnguarded : NuDispatch :=
  [{ nuIc3Step with
      run := fun _ q => .done (.decided (if q.planOk then q.coloured else q.flat) [] none) }]

/-- ✗ **No `Proven` from the fallback on a quiescence property.** With no coloured plan, the
name-blind flat encoding over-fires joins; a fixpoint query that believes its `Proven` of a
`DeadlockFree` property on a net with a ν-join is rejected. -/
@[evidence forbids NU_053_dispatch]
theorem NU_053_dispatch_forbids_unguarded : ¬ NU_053_dispatch mutNuUnguarded :=
  fun h => h.2.2.2 _ List.mem_cons_self rfl {} { nqTrunc with plan := false } (fun _ _ => True) _
    rfl rfl rfl (.done _) "IC3/PDR" [] none rfl

end Libpetri.Spec
