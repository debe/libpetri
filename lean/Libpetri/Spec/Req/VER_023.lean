import Libpetri.Spec.Verifier.Result
import Libpetri.Spec.Verifier.Scg

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-023: Timed Counterexample Check (`spec/07-verification.md`)

An opt-in check that asks the timed state-class graph about a `Violated` of a timed net, and
annotates the result without changing its verdict. Two blocks share the ID.

**The check** (`VER_023`) is a predicate over three variables:

* `A : TimedGateFn K`, the gate: from the option, the verdict, the deciding route, the timed net,
  whether it declares a match transition and the environment places still registered on it,
  whether the check runs;
* `Θ : TimedOutcomeFn S Key`, the reading of a built graph: from an explorer, a build of the
  graph layer's loop at it and a property, the check's answer (`TIMED_CONFIRMED` with a path,
  `SPURIOUS_UNDER_TIMING` or `TIMED_UNDECIDED`);
* `W : TimedAnnotFn K`, the annotation: from whether the check ran, its answer and the result the
  verifier reached without it, the result it returns.

**The timed graph** (`VER_023_graph`) is a predicate over the graph's labelled successor function
`σ : TimedSuccFn` (`compute_successor` of the timed `StateClassGraph`), built by the graph
layer's loop at the class-key explorer of `Spec/Verifier/Scg.lean`: a class has no successor
exactly when its marking enables nothing, and a closed graph without a violating class speaks for
every run of the timed semantics `Novel.TimedScg.TStep` (on time, atomic firings), a safety
property on every reached marking and a quiescence property on every reached resting marking.

The witnesses are `refTimedGate`, `refTimedOutcome` and `refTimedAnnot` (`finish` and
`timed_counterexample_check` of `smt_verifier.rs`), and `refTimedSucc` (`Scg.succL` in the
canonical clock order). Wrong models are killed one per line: on small graphs at the identity
explorer for the reading, on concrete results for the annotation, and on three one-transition
timed nets for the graph.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel Libpetri.Novel.RouteB Libpetri.Spec.Verifier
  Libpetri.Spec.Verifier.Graph
open Libpetri.Novel.Dbm (Bound)

/-! ## The model -/

/-- **What the check's gate reads**, at the end of `verify()`: the option, the verdict and the
route the pipeline reached, the verified timed net, whether it declares a match (ν-join)
transition, and the environment places still registered on it. -/
structure TimedCheckInput (K : Type) where
  /-- The option `timedCounterexampleCheck`. -/
  enabled : Bool
  /-- The verdict the pipeline reached. -/
  verdict : Verifier.Verdict
  /-- The route that decided. -/
  route : Verifier.Route
  /-- The verified timed net. -/
  net : Reference.TimedNet K
  /-- Whether the net declares a match (ν-join) transition ([NU-020]). -/
  hasMatch : Bool
  /-- The environment places registered on the net; none after the `Arrivals` rewrite. -/
  envPlaces : List K

/-- **The gate**: whether the check runs. -/
abbrev TimedGateFn (K : Type) : Type := TimedCheckInput K → Bool

/-- **The reference gate** (`finish`, `smt_verifier.rs`): a `Violated` of a timed net, decided by
a route other than Route B, with the option on, no environment place and no match transition. -/
def refTimedGate {K : Type} : TimedGateFn K := fun x =>
  x.enabled && decide (x.verdict = .violated) && !decide (Untimed x.net) && x.envPlaces.isEmpty &&
    !x.hasMatch && decide (x.route ≠ .nuScg)

/-- **The check's answer**: a violating class reached, with the labels of the path to it; the
graph closed without one; or neither. -/
inductive TimedOutcome where
  /-- `TIMED_CONFIRMED`, with the labels (transition name, outcome row) of the reported path. -/
  | confirmed (path : List Scg.Label)
  /-- `SPURIOUS_UNDER_TIMING`. -/
  | spurious
  /-- `TIMED_UNDECIDED`. -/
  | undecided
  deriving DecidableEq

/-- **The reading of a built graph**: from the explorer, the built graph and the property, the
check's answer. -/
abbrev TimedOutcomeFn (S Key : Type) : Type :=
  Explorer S Key Scg.Label → Decide.Out S → Decide.Prop' S Scg.Label → TimedOutcome

/-- **The reference reading** (`decide_over_state_space_reaping` read by
`timed_counterexample_check`): nothing off a stopped build; a violating class, prefix or not,
with the shortest path of the built graph to it; `Proven` of a closed graph is
`SPURIOUS_UNDER_TIMING`; a truncation without a hit is `TIMED_UNDECIDED`. -/
def refTimedOutcome {S Key : Type} [DecidableEq Key] : TimedOutcomeFn S Key := fun E o p =>
  if o.stopped then .undecided
  else match Decide.verdict E o p with
    | .proven => .spurious
    | .violated i => .confirmed (Graph.trace E o i)
    | .unknown => .undecided

/-- **The annotation**: from whether the check ran, its answer and the result without it, the
result the verifier returns. -/
abbrev TimedAnnotFn (K : Type) : Type := Bool → TimedOutcome → Result K → Result K

/-- **The reference annotation**: a check that did not run leaves the result; otherwise the label,
the replaced path and `counterexampleConfirmed` for `TIMED_CONFIRMED`, the label alone for the
other two answers, and a report note each. -/
def refTimedAnnot {K : Type} : TimedAnnotFn K := fun ran out r =>
  if ran then
    match out with
    | .confirmed path =>
      { r with timing := some .timedConfirmed, trace := path.map Prod.fst, confirmed := some true,
               notes := r.notes ++ ["the counterexample was replaced by the timed graph's shortest path"] }
    | .spurious =>
      { r with timing := some .spuriousUnderTiming,
               notes := r.notes ++ ["spurious under timing; the timed claim assumes an on-time executor with atomic firings"] }
    | .undecided =>
      { r with timing := some .timedUndecided,
               notes := r.notes ++ ["the timed state-class graph did not close"] }
  else r

/- The reference gate, reading and annotation are witness models of VER-023's `holds` theorem. -/
#spec_witness refTimedGate
#spec_witness refTimedOutcome
#spec_witness refTimedAnnot

/-! ## VER-023 (B): the check -/

requirement VER_023
  id "VER-023"
  title "Timed Counterexample Check"
  kind B
  scope "the SMT verifier, all implementations (SHOULD; the shall sentences bind an implementation that offers the check)"
  source verbatim "spec/07-verification.md"
  quote "The verifier *shall* run the timed check exactly when the option is on, the verdict is `Violated`, some transition of the verified net is not `immediate`, no environment place is still registered on the verified net (the `Arrivals` rewrite of [VER-006] removes them), the net declares no match transition, and the route that decided is not Route B ([VER-012])."
        "*If* the build of the timed graph is stopped by the total budget or cancelled ([VER-013]), *then* the timed check *shall* answer `TIMED_UNDECIDED`."
        "*While* the build is neither stopped by the total budget nor cancelled, the timed check *shall* answer `TIMED_CONFIRMED` when a counted class of the timed graph violates the property, a counted class being any stored class for a safety property and a class the builder expanded for a quiescence property."
        "*When* the timed graph is closed and no class of it violates the property, the timed check *shall* answer `SPURIOUS_UNDER_TIMING`."
        "*When* the timed graph is truncated at the class budget and no counted class of it violates the property, the timed check *shall* answer `TIMED_UNDECIDED`."
        "*When* the timed check answers `TIMED_CONFIRMED`, the path it reports *shall* lead, in the timed graph it built, from the initial class to the first class, in the order the builder stored the classes, that is counted and violates the property, and *shall* be no longer than any other path of that graph from the initial class to that class."
        "*If* the timed check does not run, *then* the verifier *shall* leave the result unchanged, its `counterexampleTiming` at the value [VER-003] gives it."
        "*When* the timed check runs, the verifier *shall* leave the verdict, the route and the reported P-invariants unchanged."
        "*When* the timed check answers `TIMED_CONFIRMED`, the verifier *shall* report `counterexampleTiming` `TIMED_CONFIRMED`, replace the counterexample's transitions by those of the path the check reports, and report `counterexampleConfirmed` as `true`."
        "*When* the timed check answers `SPURIOUS_UNDER_TIMING`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`."
        "*When* the timed check answers `TIMED_UNDECIDED`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`."
  reading "The gate A runs the check on an input with option on, verdict v, route r, timed net X, match flag hasMatch and environment places env still registered on X (none after the Arrivals rewrite of VER-006) exactly when on is true, v is Violated, some transition of X is not immediate (not Untimed X), env is empty, hasMatch is false and r is not the ν route (Route B)."
          "For every explorer E, class budget n, stop oracle cut, fuel, initial class x0 and property p, with o the build of the graph layer's loop at E with no early stop: if o was stopped, Θ answers TIMED_UNDECIDED;"
          "if o was not stopped and some class of o violates p under the shared predicate Decide.violatesAt (any stored class for a safety property, an expanded class whose successors are all reapable for a quiescence property), Θ answers TIMED_CONFIRMED with some path;"
          "if o was not stopped, is closed and no class of it violates p, Θ answers SPURIOUS_UNDER_TIMING;"
          "if o was not stopped, is not closed (truncated at the budget) and no class of it violates p, Θ answers TIMED_UNDECIDED;"
          "if E is key-equivariant and Θ answers TIMED_CONFIRMED with path tr: some class i of o violates p, no class stored before i violates p, tr is a path of the built graph's edges from class 0 to class i, and no path of those edges from class 0 to class i is shorter."
          "The annotation W leaves the result unchanged when the check did not run;"
          "when the check ran, W keeps the verdict, the route and the reported P-invariants;"
          "on TIMED_CONFIRMED with path tr, W reports the timing TIMED_CONFIRMED, the transitions of tr (the first component of each label) as the trace, and counterexampleConfirmed true;"
          "on SPURIOUS_UNDER_TIMING, W reports that timing and keeps the trace and counterexampleConfirmed;"
          "on TIMED_UNDECIDED, W reports that timing and keeps the trace and counterexampleConfirmed."
  assumes "The model is the triple (A, Θ, W). A reads a TimedCheckInput: the option, the verdict and the route the pipeline reached, the verified timed net (after the rewrites of VER-006, VER-004 and EXEC-042, none of which changes timing or adds a match transition), whether it declares a match transition and the environment places still registered on it. Reference.TimedNet has no match transition and no environment place of its own, so both are fields of the input, as in VER-017. Under the Arrivals mode of VER-006 every runtime closes the net before any route and clears its environment places (with_arrivals in smt_verifier.rs, applyArrivals in SmtVerifier.java and in smt-verifier.ts), so the gate sees none and the check runs on the closed net; the environment places of AC5 are those registered under any other mode. The order of the reference is that of finish (smt_verifier.rs): UNTIMED_NET on an untimed net, TIMED_EXACT when Route B decided, UNTIMED_ABSTRACTION when the option is off or an environment place or a match transition is present, the check otherwise; the first three are VER-003's labels, which W leaves alone because A is false there."
          "The statement constrains A, Θ and W one at a time. That the verifier hands W the gate's answer on its own result, and Θ's answer on the timed graph of the verified net, built by the graph layer's loop at the class-key explorer of the timed graph (Scg.scgE, the explorer of VER_023_graph) from the initial class Novel.TimedScg.initCls with the class budget of VER-017 and the stop oracle of VER-013, is the wiring the model assumes and does not state. The labels are (transition name, outcome row) as the timed graph's edges carry them (StateClassEdge); the trace W reports is their names. The flat timed net TNet of the graph is the verified net's image; that image (the Link of the verified net to TNet, with the [VER-001] outcome rows) is not stated here, as the on-time bridge of this wave (premise 9 of Novel/TimedScg/Succ.lean) is not proved. So the shall sentence of line 1, and AC7, speak of the verifier under that wiring: Lean checks A, Θ and W one at a time, not the call site in verify()."
          "Lines 2 to 6 read Θ over any explorer and any build of the graph layer's loop, the same loop and the same predicate Decide.violatesAt the enumeration route of VER-017 and Route B of VER-012 read ('decide the same property over its classes with the same shared predicate'; the sinks and conditional sinks of VER-014 are inside the property's predicate). Killed: a reading that ignores a stop (VER_023_forbids_readStopped), one that never confirms from a truncated prefix (VER_023_forbids_noPrefixHit), one that never answers SPURIOUS_UNDER_TIMING (VER_023_forbids_neverSpurious), one that answers SPURIOUS_UNDER_TIMING from a truncated prefix (VER_023_forbids_prefixSpurious, the markdown's 'SPURIOUS_UNDER_TIMING needs a closed graph and never comes from a prefix'), one that reports an empty path (VER_023_forbids_emptyPath), one that reports the last violating class instead of the first (VER_023_forbids_lastHit), and one that reports a longer path to the first (VER_023_forbids_longPath). 'Stopped' is the loop's stop flag, which the stop oracle cut sets (the total budget or a cancellation, VER-013) and which the model also sets when its fuel runs out, a bound no runtime has; the shall sentence names the first two."
          "Line 6 asks for the first violating class in storage order and a shortest path to it, which the reference meets for every key-equivariant explorer (ver023_verdict_first, Graph.trace_spec); the timed class-key explorer is one (Scg.scgE_equivariant). Every runtime takes the first violating class: (0..view.count()).find in graph_decision.rs, firstWhere in GraphDecision.java and in graph-decision.ts. The markdown's 'the shortest path from the initial class to a violating class', shortest over every violating class, follows from line 6 because the build is breadth-first, so the first violating class stored is a nearest one; the breadth-first argument is proved at the identity explorer only (VER-017's ver017_build_bfs), so the line states the first class and the shortest path to it, not the minimum over every class. That the path is a run of the timed semantics ignoring priority (ruling D67 (a), VD-4) needs the exact half of the timed successor, which Lean does not prove (Novel/TimedScg.lean); it is a later line of this ID, not stated here. That it is an ordered firing sequence of the untimed abstraction, which VER-003's line 5 asks of a confirmed trace, needs the same Link to the verified net and is likewise not stated."
          "Lines 7 to 11 are the annotation. 'Why it never changes a verdict' is lines 7 and 8: the verdict is the one the pipeline reached, so a check that turns Violated into Proven or Unknown is killed (VER_023_forbids_verdictChange); VER_023_keeps_timing derives that every result W returns after the gate meets VER-003's timing line. Ruling D20 (VD-5 (6), ver-d#7): the markdown's 'every other field is unchanged' is read as the verdict, the route and the invariants, since TIMED_CONFIRMED replaces the trace and sets counterexampleConfirmed (smt_verifier.rs assigns counterexample_trace, counterexample_transitions and counterexample_confirmed = Some(true)). Killed: a check that annotates when it did not run (VER_023_forbids_annotateOff), one that keeps the untimed trace on TIMED_CONFIRMED (VER_023_forbids_keepTrace), one that drops the untimed trace on SPURIOUS_UNDER_TIMING (VER_023_forbids_dropTrace), one that leaves a stopped check at UNTIMED_ABSTRACTION (VER_023_forbids_undecidedLabel), one that reports another route (VER_023_forbids_routeChange) and one that drops the P-invariants (VER_023_forbids_dropInvariants). The trace of markings beside the transitions (counterexample_trace in Rust) is the result record's shape, kind N."
          "Ruling D22 (a): VER-023 is SHOULD, and its shall sentences bind an implementation that offers the check. 'Off by default' is the Options default (timedCheck := false), kind N. 'The check does not read or write a state-space cache' and 'It runs once, as a wrapper at the end of verify(), after every route has spoken' are the wiring above: W reads the result the pipeline reached, and the check builds its graph afresh rather than through VER-017's cache, whose graphs are untimed; neither is a line. The report text (that the trace came from the timed graph, the class count, the truncation at N classes, which stop ended the build, the plain statement that the counterexample is spurious under timing, and what the timed claim assumes, 'The report MUST also say what that timed claim assumes') is kind Q, as is the byte identity of the report with the option off."
          "AC1 (the watchdog net: UNTIMED_ABSTRACTION with the check off, SPURIOUS_UNDER_TIMING with it on, the class count in the report) is lines 1, 4, 7 and 10 with the graph block; its timed graph is not evaluated in Lean (rational zone arithmetic does not reduce under decide, so no concrete timed graph is computed here), and the class count is report text, kind Q."
          "AC2 (the watchdog at delayed(1): TIMED_CONFIRMED with the path start, watchdog) is lines 3, 6 and 9; the graph is not evaluated in Lean, as for AC1."
          "AC3 (quiescence on the timed graph) is the graph block, line 1 of VER_023_graph: the class holding S with d at delayed(5) has a successor (VER_023_graph_nonvacuous); the second net (fast and slow on A) is not evaluated in Lean, as for AC1."
          "AC4 (a class budget below the graph's size, and a total budget that runs out, give TIMED_UNDECIDED without a hit in the prefix; a hit in the prefix gives TIMED_CONFIRMED) is lines 2, 3 and 5, checked on the producer gen: G -> G, A at a budget of 6 at the identity explorer (VER_023_nonvacuous): placeBound(A, 2) is TIMED_CONFIRMED with the path gen, gen, gen, and deadlock freedom on the same truncated graph is TIMED_UNDECIDED. That the prefix path is gen, gen, gen and not the path to a later violating class (gen five times) is line 6 (VER_023_forbids_lastHit). The report naming the truncation is kind Q."
          "AC5 (environment places registered under a mode other than Arrivals, or match transitions: the check does not run and the value is UNTIMED_ABSTRACTION; a Route B verdict on a timed net stays TIMED_EXACT; an untimed net stays UNTIMED_NET) is lines 1 and 7: refTimedGate is false on each (VER_023_nonvacuous), and the value is the one VER-003 gives: line 10 of VER-003 labels a timed Violated TIMED_EXACT when Route B decided it and UNTIMED_ABSTRACTION when another route decided it with the check off (VER_003_forbids_timedExactEnum, VER_003_forbids_routeBAbstraction)."
          "AC6 (the race t1: p -> a at window(3, 5), t2: p -> b at delayed(10): Violated, SPURIOUS_UNDER_TIMING, and the report says the timed claim assumes an on-time executor with atomic firings) is the graph block with VER_023_ac6: no run of the timed semantics marks b, while a late executor that reaps t1 does (Novel.TimedScg.reaping_escapes_timed_graph); the report line is kind Q."
          "AC7 (no verdict differs between the check on and off) is lines 7 and 8."
          "The worked example 'On the [VER-002] AC11 witness the check is TIMED_CONFIRMED with the empty trace' is lines 3 and 6 with the reap-aware predicate, checked on a stand-in graph at the identity explorer (VER_023_ac11: the class that enables only the reapable t rests and is reported with the empty path; with nothing reapable the same closed graph answers SPURIOUS_UNDER_TIMING); the timed graph of that net is not evaluated, as for AC1."
          "The graph is priority-blind ('The graph is priority-blind', and the hi/lo example of TIMED_CONFIRMED): TNet has no priority and the reference successor expands every enabled clock, so a closed graph without a violating class speaks for every prioritized run too, since priority only removes runs."
  signoff "2026-11-13 fe863ee06981554b ai"
  statement : ∀ {K S Key : Type} [DecidableEq Key],
      TimedGateFn K → TimedOutcomeFn S Key → TimedAnnotFn K → Prop :=
    fun {K S Key} [DecidableEq Key] A Θ W =>
      (∀ x : TimedCheckInput K, A x = true ↔
        (x.enabled = true ∧ x.verdict = .violated ∧ ¬ Untimed x.net ∧ x.envPlaces = [] ∧
          x.hasMatch = false ∧ x.route ≠ .nuScg)) ∧
      (∀ (E : Explorer S Key Scg.Label) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (x0 : S)
          (p : Decide.Prop' S Scg.Label),
        let o := Decide.build E n cut (fun _ => false) false fuel x0
        (o.stopped = true → Θ E o p = .undecided) ∧
        (o.stopped = false → (∃ j, Decide.violatesAt E o p j = true) →
          ∃ tr, Θ E o p = .confirmed tr) ∧
        (o.stopped = false → o.complete = true → (∀ j, Decide.violatesAt E o p j = false) →
          Θ E o p = .spurious) ∧
        (o.stopped = false → o.complete = false → (∀ j, Decide.violatesAt E o p j = false) →
          Θ E o p = .undecided) ∧
        (E.Equivariant → ∀ tr, Θ E o p = .confirmed tr →
          ∃ i, Decide.violatesAt E o p i = true ∧
            (∀ j, j < i → Decide.violatesAt E o p j = false) ∧ Walk (edges E o) 0 tr i ∧
            ∀ t, Walk (edges E o) 0 t i → tr.length ≤ t.length)) ∧
      (∀ out r, W false out r = r) ∧
      (∀ out r, (W true out r).verdict = r.verdict ∧ (W true out r).route = r.route ∧
        (W true out r).invariants = r.invariants) ∧
      (∀ tr r, (W true (.confirmed tr) r).timing = some .timedConfirmed ∧
        (W true (.confirmed tr) r).trace = tr.map Prod.fst ∧
        (W true (.confirmed tr) r).confirmed = some true) ∧
      (∀ r, (W true .spurious r).timing = some .spuriousUnderTiming ∧
        (W true .spurious r).trace = r.trace ∧ (W true .spurious r).confirmed = r.confirmed) ∧
      (∀ r, (W true .undecided r).timing = some .timedUndecided ∧
        (W true .undecided r).trace = r.trace ∧ (W true .undecided r).confirmed = r.confirmed)

/- The pinned readable form of VER-023: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_023 : {K S Key : Type} →
  [DecidableEq Key] → TimedGateFn K → TimedOutcomeFn S Key → TimedAnnotFn K → Prop :=
fun {K S Key} [DecidableEq Key] A Θ W =>
  (∀ (x : TimedCheckInput K),
      A x = true ↔
        x.enabled = true ∧
          x.verdict = Verdict.violated ∧
            ¬Untimed x.net ∧ x.envPlaces = [] ∧ x.hasMatch = false ∧ x.route ≠ Route.nuScg) ∧
    (∀ (E : Explorer S Key Scg.Label) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (x0 : S) (p : Decide.Prop' S Scg.Label),
        have o := Decide.build E n cut (fun x => false) false fuel x0;
        (o.stopped = true → Θ E o p = TimedOutcome.undecided) ∧
          (o.stopped = false → (∃ j, Decide.violatesAt E o p j = true) → ∃ tr, Θ E o p = TimedOutcome.confirmed tr) ∧
            (o.stopped = false →
                o.complete = true → (∀ (j : ℕ), Decide.violatesAt E o p j = false) → Θ E o p = TimedOutcome.spurious) ∧
              (o.stopped = false →
                  o.complete = false →
                    (∀ (j : ℕ), Decide.violatesAt E o p j = false) → Θ E o p = TimedOutcome.undecided) ∧
                (E.Equivariant →
                  ∀ (tr : List Scg.Label),
                    Θ E o p = TimedOutcome.confirmed tr →
                      ∃ i,
                        Decide.violatesAt E o p i = true ∧
                          (∀ j < i, Decide.violatesAt E o p j = false) ∧
                            Walk (edges E o) 0 tr i ∧
                              ∀ (t : List Scg.Label), Walk (edges E o) 0 t i → tr.length ≤ t.length)) ∧
      (∀ (out : TimedOutcome) (r : Result K), W false out r = r) ∧
        (∀ (out : TimedOutcome) (r : Result K),
            (W true out r).verdict = r.verdict ∧
              (W true out r).route = r.route ∧ (W true out r).invariants = r.invariants) ∧
          (∀ (tr : List Scg.Label) (r : Result K),
              (W true (TimedOutcome.confirmed tr) r).timing = some CexTiming.timedConfirmed ∧
                (W true (TimedOutcome.confirmed tr) r).trace = List.map Prod.fst tr ∧
                  (W true (TimedOutcome.confirmed tr) r).confirmed = some true) ∧
            (∀ (r : Result K),
                (W true TimedOutcome.spurious r).timing = some CexTiming.spuriousUnderTiming ∧
                  (W true TimedOutcome.spurious r).trace = r.trace ∧
                    (W true TimedOutcome.spurious r).confirmed = r.confirmed) ∧
              ∀ (r : Result K),
                (W true TimedOutcome.undecided r).timing = some CexTiming.timedUndecided ∧
                  (W true TimedOutcome.undecided r).trace = r.trace ∧
                    (W true TimedOutcome.undecided r).confirmed = r.confirmed
-/
#guard_msgs in #print VER_023

/-! ### Facts about the reading -/

section Reading

variable {S Key L : Type}

/-- A class that violates is a stored class. -/
theorem ver023_violatesAt_lt {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    {j : ℕ} (h : Decide.violatesAt E o p j = true) : j < o.cls.length := by
  rcases Nat.lt_or_ge j o.cls.length with hj | hj
  · exact hj
  · have hn : o.cls[j]? = none := List.getElem?_eq_none hj
    cases p with
    | safety bad => simp [Decide.violatesAt, hn] at h
    | quiescence bad reap => simp [Decide.violatesAt, hn] at h

/-- With no violating class, the verdict of an unstopped build is `Proven` exactly when it is
closed, and `Unknown` otherwise. -/
theorem ver023_verdict_none {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    (hs : o.stopped = false) (hv : ∀ j, Decide.violatesAt E o p j = false) :
    Decide.verdict E o p = if o.complete then .proven else .unknown := by
  have hf : (List.range o.cls.length).find? (Decide.violatesAt E o p) = none :=
    List.find?_eq_none.mpr fun j _ => by simp [hv j]
  simp only [Decide.verdict, hs, hf]
  rfl

/-- A violating class makes the verdict of an unstopped build `Violated`. -/
theorem ver023_verdict_hit {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    (hs : o.stopped = false) (hv : ∃ j, Decide.violatesAt E o p j = true) :
    ∃ i, Decide.verdict E o p = .violated i := by
  obtain ⟨j, hj⟩ := hv
  cases hf : (List.range o.cls.length).find? (Decide.violatesAt E o p) with
  | none =>
    have := List.find?_eq_none.mp hf j (List.mem_range.mpr (ver023_violatesAt_lt hj))
    simp [hj] at this
  | some i =>
    exact ⟨i, by simp only [Decide.verdict, hs, hf]; rfl⟩

/-- A `Violated` verdict names a violating class. -/
theorem ver023_verdict_violated {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    {i : ℕ} (h : Decide.verdict E o p = .violated i) : Decide.violatesAt E o p i = true := by
  unfold Decide.verdict at h
  split at h
  · cases h
  · split at h
    · rename_i i' hf
      cases h
      exact List.find?_some hf
    · split at h <;> cases h

/-- A `Violated` verdict names the first violating class in the order the build stored them. -/
theorem ver023_verdict_first {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    {i : ℕ} (h : Decide.verdict E o p = .violated i) :
    ∀ j, j < i → Decide.violatesAt E o p j = false := by
  unfold Decide.verdict at h
  split at h
  · cases h
  · split at h
    · rename_i j0 hj
      cases h
      intro j hj'
      have := (List.find?_range_eq_some.mp hj).2.2 j hj'
      simpa using this
    · split at h <;> cases h

/-- No class at or past the end of the stored list violates, so a finite check settles every
index. -/
theorem ver023_noHit {E : Explorer S Key L} {o : Decide.Out S} {p : Decide.Prop' S L}
    (h : ∀ j < o.cls.length, Decide.violatesAt E o p j = false) :
    ∀ j, Decide.violatesAt E o p j = false := fun j => by
  by_cases hj : j < o.cls.length
  · exact h j hj
  · cases hv : Decide.violatesAt E o p j
    · rfl
    · exact absurd (ver023_violatesAt_lt hv) hj

end Reading

/-! ### The reference -/

/-- ✓ **The reference check meets VER-023.** Example: on a timed `Violated` decided by the SMT
route, with the option on, no environment place and no match transition, the gate lets the
check run; the reading answers `TIMED_CONFIRMED` with the shortest path of the built graph to
the first violating class, `SPURIOUS_UNDER_TIMING` when the graph closed without one, and
`TIMED_UNDECIDED` when it was truncated without one or stopped; the annotation then writes the
label, replaces the trace only for `TIMED_CONFIRMED`, and never touches the verdict. -/
@[evidence holds VER_023]
theorem VER_023_reference {K S Key : Type} [DecidableEq Key] :
    VER_023 (K := K) (S := S) (Key := Key) refTimedGate refTimedOutcome refTimedAnnot := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [refTimedGate, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, List.isEmpty_iff, ne_eq]
    tauto
  · intro E n cut fuel x0 p
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hs
      simp [refTimedOutcome, hs]
    · intro hs hv
      obtain ⟨i, hi⟩ := ver023_verdict_hit hs hv
      refine ⟨Graph.trace E (Decide.build E n cut (fun _ => false) false fuel x0) i, ?_⟩
      unfold refTimedOutcome
      rw [if_neg (by simp [hs]), hi]
    · intro hs hc hv
      simp [refTimedOutcome, hs, ver023_verdict_none hs hv, hc]
    · intro hs hc hv
      simp [refTimedOutcome, hs, ver023_verdict_none hs hv, hc]
    · intro hE tr htr
      by_cases hs : (Decide.build E n cut (fun _ => false) false fuel x0).stopped = true
      · simp [refTimedOutcome, hs] at htr
      · cases hv : Decide.verdict E (Decide.build E n cut (fun _ => false) false fuel x0) p with
        | proven => simp [refTimedOutcome, hs, hv] at htr
        | unknown => simp [refTimedOutcome, hs, hv] at htr
        | violated i =>
          simp only [refTimedOutcome, hs, hv, if_false, Bool.false_eq_true,
            TimedOutcome.confirmed.injEq] at htr
          subst htr
          have hvi := ver023_verdict_violated hv
          obtain ⟨hw, -, hmin⟩ := trace_spec hE (ver023_violatesAt_lt hvi)
          exact ⟨i, hvi, ver023_verdict_first hv, hw, hmin⟩
  · intro out r
    simp [refTimedAnnot]
  · intro out r
    cases out <;> simp [refTimedAnnot]
  · intro tr r
    simp [refTimedAnnot]
  · intro r
    simp [refTimedAnnot]
  · intro r
    simp [refTimedAnnot]

/-! ### What the statement gives -/

/-- **The check never breaks VER-003's timing line**, from the statement alone: when the gate lets
the check run, the result it returns is still `Violated`, still carries a `counterexampleTiming`,
and that label is `UNTIMED_NET` exactly when the net is untimed, which it is not. Example: a
`Violated` of the watchdog net labelled `UNTIMED_ABSTRACTION` comes back `Violated`, labelled
`SPURIOUS_UNDER_TIMING`, `TIMED_CONFIRMED` or `TIMED_UNDECIDED`, never `UNTIMED_NET`. -/
@[evidence cites "VER-023" "No verdict differs between the check on and off, for any net and property."]
theorem VER_023_keeps_timing {K S Key : Type} [DecidableEq Key] {A : TimedGateFn K}
    {Θ : TimedOutcomeFn S Key} {W : TimedAnnotFn K} (h : VER_023 A Θ W) (x : TimedCheckInput K)
    (hx : A x = true) (out : TimedOutcome) (r : Result K) (hr : r.verdict = x.verdict) :
    (W true out r).verdict = .violated ∧ (W true out r).timing ≠ none ∧
      ((W true out r).timing = some .untimedNet ↔ Untimed x.net) := by
  obtain ⟨-, hv, hu, -, -, -⟩ := (h.1 x).mp hx
  obtain ⟨-, -, hW, hW3, hW4, hW5⟩ := h.2
  refine ⟨(hW out r).1.trans (hr.trans hv), ?_, ?_⟩
  · cases out with
    | confirmed tr => simp [(hW3 tr r).1]
    | spurious => simp [(hW4 r).1]
    | undecided => simp [(hW5 r).1]
  · refine ⟨fun ht => ?_, fun ht => absurd ht hu⟩
    exfalso
    cases out with
    | confirmed tr => rw [(hW3 tr r).1] at ht; cases ht
    | spurious => rw [(hW4 r).1] at ht; cases ht
    | undecided => rw [(hW5 r).1] at ht; cases ht

/-! ### Worked examples -/

/-- The producer `gen: G → G, A` of AC4 at the identity explorer: state `n` holds `n` tokens on
`A`, and each step fires `gen` with outcome row 0. -/
def ver023GenL : ℕ → List (Scg.Label × ℕ) := fun n => [(("gen", 0), n + 1)]

/-- A fork: from `0`, `toB` gives `1` and `toA` gives `2`; from `1`, `toC` gives `3`; `2` and
`3` are dead. -/
def ver023ForkL : ℕ → List (Scg.Label × ℕ)
  | 0 => [(("toB", 0), 1), (("toA", 0), 2)]
  | 1 => [(("toC", 0), 3)]
  | _ => []

/-- `placeBound(A, 2)` on the producer: a state with three tokens or more. -/
def ver023Bound : Decide.Prop' ℕ Scg.Label := .safety fun n => decide (2 < n)

/-- Deadlock freedom with nothing reapable. -/
def ver023Dead : Decide.Prop' ℕ Scg.Label := .quiescence (fun _ => true) fun _ => false

/-- `unreachable` of state `5`, which the fork never reaches. -/
def ver023Five : Decide.Prop' ℕ Scg.Label := .safety fun n => decide (n = 5)

/-- The watchdog net of AC1 over the places `REQ = 0`, `CALLING = 1`, `RESP = 2`,
`TIMEOUT = 3`: `start: REQ → CALLING`, `answer: CALLING → RESP`, `watchdog: CALLING → TIMEOUT`. -/
def ver023WdNet : Reference.Net ℕ :=
  { places := [0, 1, 2, 3],
    transitions :=
      [ { core := { name := "start", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                    resets := [] }, out := some (.place 1) },
        { core := { name := "answer", inputs := [⟨1, .one⟩], inhibitors := [], reads := [],
                    resets := [] }, out := some (.place 2), reapable := true },
        { core := { name := "watchdog", inputs := [⟨1, .one⟩], inhibitors := [], reads := [],
                    resets := [] }, out := some (.place 3) } ] }

/-- The watchdog net timed as in AC1: `answer` at `window(0, 2)`, `watchdog` at `delayed(5)`. -/
def ver023Wd : Reference.TimedNet ℕ :=
  { net := ver023WdNet,
    timing := fun t => if t.core.name = "answer" then .window 0 2
      else if t.core.name = "watchdog" then .delayed 5 else .immediate,
    tol := 0 }

/-- The watchdog net with every transition `immediate`. -/
def ver023WdU : Reference.TimedNet ℕ := { net := ver023WdNet, timing := fun _ => .immediate, tol := 0 }

/-- A timed `Violated` of the SMT route with the check on, no environment place and no match. -/
def ver023In : TimedCheckInput ℕ :=
  { enabled := true, verdict := .violated, route := .smt, net := ver023Wd, hasMatch := false,
    envPlaces := [] }

/-- The `Violated` of AC1 before the check: the untimed trace `start, watchdog`, confirmed by the
replay, labelled `UNTIMED_ABSTRACTION`. -/
def ver023R : Result ℕ :=
  { verdict := .violated, route := .smt, trace := ["start", "watchdog"], confirmed := some true,
    timing := some .untimedAbstraction }

/-- ✓ **The reference check on small graphs and on the watchdog net.** Example: on the producer
`gen` cut off at a class budget of 6, `placeBound(A, 2)` is `TIMED_CONFIRMED` with the path
`gen, gen, gen` found in the prefix, while deadlock freedom on the same truncated graph is
`TIMED_UNDECIDED`, and a build stopped at once is `TIMED_UNDECIDED` whatever the property; on the
closed fork graph, `unreachable(5)` is `SPURIOUS_UNDER_TIMING`. The gate runs the check on the
timed watchdog net and not when the option is off, an environment place is registered, a match
transition is declared, Route B decided or the net is untimed (AC5). `SPURIOUS_UNDER_TIMING`
keeps the untimed trace `start, watchdog`; `TIMED_CONFIRMED` replaces it. -/
@[evidence nonvacuous VER_023]
theorem VER_023_nonvacuous :
    refTimedOutcome (idExplorer ver023GenL)
        (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0)
        ver023Bound = .confirmed [("gen", 0), ("gen", 0), ("gen", 0)] ∧
      refTimedOutcome (idExplorer ver023GenL)
        (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0)
        ver023Dead = .undecided ∧
      refTimedOutcome (idExplorer ver023GenL)
        (buildD (idExplorer ver023GenL) 6 (fun _ => true) (fun _ => false) false 20 0)
        (.safety fun _ => true) = .undecided ∧
      refTimedOutcome (idExplorer ver023ForkL)
        (buildD (idExplorer ver023ForkL) 10 (fun _ => false) (fun _ => false) false 20 0)
        ver023Five = .spurious ∧
      refTimedGate ver023In = true ∧
      refTimedGate { ver023In with enabled := false } = false ∧
      refTimedGate { ver023In with envPlaces := [3] } = false ∧
      refTimedGate { ver023In with hasMatch := true } = false ∧
      refTimedGate { ver023In with route := .nuScg } = false ∧
      refTimedGate { ver023In with net := ver023WdU } = false ∧
      (refTimedAnnot true .spurious ver023R).trace = ["start", "watchdog"] ∧
      (refTimedAnnot true .spurious ver023R).timing = some .spuriousUnderTiming ∧
      (refTimedAnnot true (.confirmed [("start", 0), ("watchdog", 0)]) ver023R).timing =
        some .timedConfirmed := by
  decide

/-- The reap-quiescence witness of [VER-002] AC11 at the identity explorer: state `0` holds the
token on `p0` and enables only `t`, which fires to state `1`, the token on the sink `p1`. -/
def ver023ReapL : ℕ → List (Scg.Label × ℕ)
  | 0 => [(("t", 0), 1)]
  | _ => []

/-- ✓ **The AC11 witness of VER-002, on a stand-in graph.** Example: `p0 → t → p1` with `t` at
`window(3, 5)`. The initial class enables only `t`, which a late executor may reap, so it rests
with the token stranded on `p0`; deadlock freedom is `TIMED_CONFIRMED` with the empty path. With
nothing reapable (`assumeNoReaping`) the same closed graph has no resting class off the sink, and
the answer is `SPURIOUS_UNDER_TIMING`. -/
@[evidence cites "VER-023" "On the [VER-002] AC11 witness the check is `TIMED_CONFIRMED` with the empty trace."]
theorem VER_023_ac11 :
    refTimedOutcome (idExplorer ver023ReapL)
        (buildD (idExplorer ver023ReapL) 10 (fun _ => false) (fun _ => false) false 20 0)
        (.quiescence (fun n => decide (n = 0)) fun l => decide (l.1 = "t")) = .confirmed [] ∧
      refTimedOutcome (idExplorer ver023ReapL)
        (buildD (idExplorer ver023ReapL) 10 (fun _ => false) (fun _ => false) false 20 0)
        (.quiescence (fun n => decide (n = 0)) fun _ => false) = .spurious := by
  decide

/-! ### Wrong models, one per line -/

/-- Mutant: a gate that does not look at match transitions. -/
def ver023_matchGate : TimedGateFn ℕ := fun x => refTimedGate { x with hasMatch := false }

/-- ✗ **No check on a net with a match transition** (line 1). Example: the timed watchdog net
with a match transition declared; the state-class graph is name-blind, yet this gate runs it. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_matchGate :
    ¬ VER_023 (S := ℕ) (Key := ℕ) ver023_matchGate refTimedOutcome refTimedAnnot := by
  intro h
  have hm := ((h.1 { ver023In with hasMatch := true }).mp (by decide)).2.2.2.2.1
  exact Bool.noConfusion hm

/-- Mutant: a reading that ignores a stop and reads the stopped prefix. -/
def ver023_readStopped : TimedOutcomeFn ℕ ℕ := fun E o p => refTimedOutcome E { o with stopped := false } p

/-- ✗ **Nothing off a stopped build** (line 2). Example: the producer's build stopped at once
holds its initial state; a property every state violates is read off that prefix as
`TIMED_CONFIRMED`, where the build was stopped and the answer is `TIMED_UNDECIDED`. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_readStopped :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_readStopped refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023GenL) 6 (fun _ => true) 20 0 (.safety fun _ => true)
  rw [← buildD_eq] at h2
  have := h2.1 (by decide)
  revert this
  decide

/-- Mutant: a reading that confirms only on a closed graph. -/
def ver023_noPrefixHit : TimedOutcomeFn ℕ ℕ := fun E o p =>
  if o.complete then refTimedOutcome E o p else .undecided

/-- ✗ **A hit in a truncated prefix confirms** (line 3, AC4). Example: the producer cut off at 6
classes holds the state with three tokens on `A`; `placeBound(A, 2)` is violated there, so the
answer is `TIMED_CONFIRMED`, not `TIMED_UNDECIDED`. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_noPrefixHit :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_noPrefixHit refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023GenL) 6 (fun _ => false) 20 0 ver023Bound
  rw [← buildD_eq] at h2
  obtain ⟨tr, htr⟩ := h2.2.1 (by decide) ⟨3, by decide⟩
  have hu : ver023_noPrefixHit (idExplorer ver023GenL)
      (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0)
      ver023Bound = .undecided := by decide
  rw [hu] at htr
  cases htr

/-- Mutant: a reading that never answers `SPURIOUS_UNDER_TIMING`. -/
def ver023_neverSpurious : TimedOutcomeFn ℕ ℕ := fun E o p =>
  match refTimedOutcome E o p with
  | .spurious => .undecided
  | x => x

/-- ✗ **A closed graph without a violating class is SPURIOUS_UNDER_TIMING** (line 4). Example:
the fork graph closes with four states and none is state 5, so `unreachable(5)` holds under
timing; answering `TIMED_UNDECIDED` withholds that. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_neverSpurious :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_neverSpurious refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023ForkL) 10 (fun _ => false) 20 0 ver023Five
  rw [← buildD_eq] at h2
  have := h2.2.2.1 (by decide) (by decide) (ver023_noHit (by decide))
  revert this
  decide

/-- Mutant: a reading that answers `SPURIOUS_UNDER_TIMING` from a truncated prefix. -/
def ver023_prefixSpurious : TimedOutcomeFn ℕ ℕ := fun E o p =>
  match refTimedOutcome E o p with
  | .undecided => if o.stopped then .undecided else .spurious
  | x => x

/-- ✗ **SPURIOUS_UNDER_TIMING never comes from a prefix** (line 5). Example: the producer cut off
at 6 classes has no expanded dead state, yet it never closes; deadlock freedom there is
`TIMED_UNDECIDED`, and calling it spurious under timing reads a prefix as the whole graph. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_prefixSpurious :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_prefixSpurious refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023GenL) 6 (fun _ => false) 20 0 ver023Dead
  rw [← buildD_eq] at h2
  have := h2.2.2.2.1 (by decide) (by decide) (ver023_noHit (by decide))
  revert this
  decide

/-- Mutant: a reading that confirms with the empty path. -/
def ver023_emptyPath : TimedOutcomeFn ℕ ℕ := fun E o p =>
  match refTimedOutcome E o p with
  | .confirmed _ => .confirmed []
  | x => x

/-- The empty path ends where it starts. -/
theorem ver023_walk_nil {L : Type} {es : List (ℕ × L × ℕ)} {a j : ℕ} {t : List L}
    (h : Walk es a t j) (ht : t = []) : j = a := by
  induction h with
  | nil => rfl
  | snoc _ _ _ => simp at ht

/-- ✗ **The confirmed path leads to a violating class** (line 6). Example: on the truncated
producer, `placeBound(A, 2)` is first violated three steps in; the empty path stays at the
initial state, which holds no token on `A`. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_emptyPath :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_emptyPath refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023GenL) 6 (fun _ => false) 20 0 ver023Bound
  rw [← buildD_eq] at h2
  obtain ⟨i, hv, -, hw, -⟩ := h2.2.2.2.2 (idExplorer_equivariant _) [] (by decide)
  obtain rfl := ver023_walk_nil hw rfl
  revert hv
  decide

/-- Mutant: a reading that reports the last violating class in storage order, with the shortest
path to it (a search from the end of the class list instead of from its start). -/
def ver023_lastHit : TimedOutcomeFn ℕ ℕ := fun E o p =>
  match refTimedOutcome E o p with
  | .confirmed _ =>
    match (List.range o.cls.length).reverse.find? (Decide.violatesAt E o p) with
    | some j => .confirmed (Graph.trace E o j)
    | none => .undecided
  | x => x

/-- The producer's path `gen, gen, gen` to its class `3`. -/
theorem ver023_genWalk3 :
    Walk (edges (idExplorer ver023GenL)
      (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0)) 0
      [("gen", 0), ("gen", 0), ("gen", 0)] 3 :=
  Walk.snoc (tr := [("gen", 0), ("gen", 0)]) (b := 2)
    (Walk.snoc (tr := [("gen", 0)]) (b := 1) (Walk.snoc (tr := []) (b := 0) Walk.nil (by decide))
      (by decide))
    (by decide)

/-- ✗ **The reported class is the first violating class** (line 6, AC4). Example: the producer
cut off at 6 classes stores 0 to 5 tokens on `A`, and `placeBound(A, 2)` is violated from 3
tokens on. This reading reports the class with 5 tokens and the path `gen` five times, a
shortest path to that class; the first violating class, 3 tokens after `gen, gen, gen`, is the
one to report. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_lastHit :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_lastHit refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023GenL) 6 (fun _ => false) 20 0 ver023Bound
  rw [← buildD_eq] at h2
  have hout : ver023_lastHit (idExplorer ver023GenL)
      (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0)
      ver023Bound = .confirmed [("gen", 0), ("gen", 0), ("gen", 0), ("gen", 0), ("gen", 0)] := by
    decide
  obtain ⟨i, hv, hfirst, -, hmin⟩ := h2.2.2.2.2 (idExplorer_equivariant _) _ hout
  have hlt := ver023_violatesAt_lt hv
  have hlen : (buildD (idExplorer ver023GenL) 6 (fun _ => false) (fun _ => false) false 20 0).cls.length
      = 6 := by decide
  rw [hlen] at hlt
  interval_cases i
  · revert hv; decide
  · revert hv; decide
  · revert hv; decide
  · have := hmin _ ver023_genWalk3
    revert this; decide
  · have := hfirst 3 (by norm_num)
    revert this; decide
  · have := hfirst 3 (by norm_num)
    revert this; decide

/-- A diamond: from `0`, `a` gives `1` and `b` gives `2`; from `2`, `c` gives `1` again. -/
def ver023DiaL : ℕ → List (Scg.Label × ℕ)
  | 0 => [(("a", 0), 1), (("b", 0), 2)]
  | 2 => [(("c", 0), 1)]
  | _ => []

/-- `unreachable` of state `1`, which the diamond reaches in one step and in two. -/
def ver023One : Decide.Prop' ℕ Scg.Label := .safety fun n => decide (n = 1)

/-- Mutant: a reading that reports the longer path `b, c` where the shortest is `a`. -/
def ver023_longPath : TimedOutcomeFn ℕ ℕ := fun E o p =>
  match refTimedOutcome E o p with
  | .confirmed tr => if tr = [("a", 0)] then .confirmed [("b", 0), ("c", 0)] else .confirmed tr
  | x => x

/-- ✗ **The reported path is a shortest one** (line 6). Example: in the diamond, state `1` is
reached by `a` alone and by `b, c`. Both paths lead to the first violating class of
`unreachable(1)`, yet `b, c` is one step longer, so a reading that reports it is not giving the
shortest path. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_longPath :
    ¬ VER_023 (K := ℕ) refTimedGate ver023_longPath refTimedAnnot := by
  intro h
  have h2 := h.2.1 (idExplorer ver023DiaL) 10 (fun _ => false) 20 0 ver023One
  rw [← buildD_eq] at h2
  have hout : ver023_longPath (idExplorer ver023DiaL)
      (buildD (idExplorer ver023DiaL) 10 (fun _ => false) (fun _ => false) false 20 0)
      ver023One = .confirmed [("b", 0), ("c", 0)] := by
    decide
  obtain ⟨i, hv, -, -, hmin⟩ := h2.2.2.2.2 (idExplorer_equivariant _) _ hout
  have hlt := ver023_violatesAt_lt hv
  have hlen : (buildD (idExplorer ver023DiaL) 10 (fun _ => false) (fun _ => false) false 20 0).cls.length
      = 3 := by decide
  rw [hlen] at hlt
  have w1 : Walk (edges (idExplorer ver023DiaL)
      (buildD (idExplorer ver023DiaL) 10 (fun _ => false) (fun _ => false) false 20 0)) 0
      [("a", 0)] 1 :=
    Walk.snoc (tr := []) Walk.nil (by decide)
  interval_cases i
  · revert hv; decide
  · have := hmin _ w1
    revert this; decide
  · revert hv; decide

/-- The mutant's path `b, c` is itself a path of the diamond to class `1`, so only the shortest
half of line 6 rules it out. -/
theorem ver023_diaWalkBC :
    Walk (edges (idExplorer ver023DiaL)
      (buildD (idExplorer ver023DiaL) 10 (fun _ => false) (fun _ => false) false 20 0)) 0
      [("b", 0), ("c", 0)] 1 :=
  Walk.snoc (tr := [("b", 0)]) (b := 2) (Walk.snoc (tr := []) (b := 0) Walk.nil (by decide))
    (by decide)

/-- Mutant: an annotation that also writes the label when the check did not run. -/
def ver023_annotateOff : TimedAnnotFn ℕ := fun _ out r => refTimedAnnot true out r

/-- ✗ **A check that does not run changes nothing** (line 7, AC5). Example: with the option off,
the watchdog `Violated` keeps `UNTIMED_ABSTRACTION`; this annotation relabels it. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_annotateOff :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_annotateOff := by
  intro h
  have := congrArg Result.timing (h.2.2.1 .spurious ver023R)
  simp [ver023_annotateOff, refTimedAnnot, ver023R] at this

/-- Mutant: a check that turns `Violated` into `Proven` when the graph closes without a violation. -/
def ver023_verdictChange : TimedAnnotFn ℕ := fun ran out r =>
  match ran, out with
  | true, .spurious => { refTimedAnnot true .spurious r with verdict := .proven "timed" }
  | ran, out => refTimedAnnot ran out r

/-- ✗ **The check never changes a verdict** (line 8, AC7). Example: the watchdog net is
`Violated` in the untimed abstraction, which is the contract; a closed timed graph without a
`TIMEOUT` class does not make it `Proven`. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_verdictChange :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_verdictChange := by
  intro h
  have := (h.2.2.2.1 .spurious ver023R).1
  simp [ver023_verdictChange, ver023R] at this

/-- Mutant: a check that reports the enumeration route, whose graph it built, as the deciding
route. -/
def ver023_routeChange : TimedAnnotFn ℕ := fun ran out r =>
  if ran then { refTimedAnnot true out r with route := .enumeration } else r

/-- ✗ **The check keeps the route** (line 8). Example: the watchdog `Violated` was decided by
the SMT pipeline; after the check it still names the SMT pipeline, not the state-class graph the
check built. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_routeChange :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_routeChange := by
  intro h
  have := (h.2.2.2.1 .spurious ver023R).2.1
  simp [ver023_routeChange, ver023R] at this

/-- The watchdog `Violated` with its P-invariant `REQ + CALLING + RESP + TIMEOUT = 1`. -/
def ver023RInv : Result ℕ :=
  { ver023R with invariants := [⟨[(0, 1), (1, 1), (2, 1), (3, 1)], 1⟩] }

/-- Mutant: a check that drops the reported P-invariants. -/
def ver023_dropInvariants : TimedAnnotFn ℕ := fun ran out r =>
  if ran then { refTimedAnnot true out r with invariants := [] } else r

/-- ✗ **The check keeps the P-invariants** (line 8). Example: the watchdog net's one token
moves from `REQ` to `CALLING` and on to `RESP` or `TIMEOUT`, so `REQ + CALLING + RESP + TIMEOUT
= 1` is reported; the check leaves that line in the result. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_dropInvariants :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_dropInvariants := by
  intro h
  have := (h.2.2.2.1 .spurious ver023RInv).2.2
  simp [ver023_dropInvariants, ver023RInv, ver023R] at this

/-- Mutant: a check that labels `TIMED_CONFIRMED` but keeps the untimed trace. -/
def ver023_keepTrace : TimedAnnotFn ℕ := fun ran out r =>
  match ran, out with
  | true, .confirmed _ => { r with timing := some .timedConfirmed, confirmed := some true }
  | ran, out => refTimedAnnot ran out r

/-- ✗ **TIMED_CONFIRMED replaces the trace** (line 9, AC2). Example: an untimed counterexample
`start, watchdog` and a timed graph whose path to the violating class is a different one, here
the stand-in path `watchdog` alone; a result that still reports `start, watchdog` reports a path
other than the one the timed graph found. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_keepTrace :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_keepTrace := by
  intro h
  have := (h.2.2.2.2.1 [("watchdog", 0)] ver023R).2.1
  simp [ver023_keepTrace, ver023R] at this

/-- Mutant: a check that drops the untimed trace when the counterexample is spurious. -/
def ver023_dropTrace : TimedAnnotFn ℕ := fun ran out r =>
  match ran, out with
  | true, .spurious => { r with timing := some .spuriousUnderTiming, trace := [] }
  | ran, out => refTimedAnnot ran out r

/-- ✗ **SPURIOUS_UNDER_TIMING keeps the untimed trace** (line 10, AC1). Example: the watchdog
`Violated` keeps its trace `start, watchdog`, which is still a run of the untimed abstraction. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_dropTrace :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_dropTrace := by
  intro h
  have := (h.2.2.2.2.2.1 ver023R).2.1
  simp [ver023_dropTrace, ver023R] at this

/-- Mutant: a check that leaves an undecided check at the untimed label. -/
def ver023_undecidedLabel : TimedAnnotFn ℕ := fun ran out r =>
  match ran, out with
  | true, .undecided => r
  | ran, out => refTimedAnnot ran out r

/-- ✗ **An undecided check says so** (line 11, AC4). Example: a timed graph cut off at its class
budget without a hit leaves the watchdog `Violated` at `UNTIMED_ABSTRACTION` under this
annotation, as if the check had not run. -/
@[evidence forbids VER_023]
theorem VER_023_forbids_undecidedLabel :
    ¬ VER_023 (S := ℕ) (Key := ℕ) refTimedGate refTimedOutcome ver023_undecidedLabel := by
  intro h
  have := (h.2.2.2.2.2.2 ver023R).1
  simp [ver023_undecidedLabel, ver023R] at this

/-! ## VER-023 (B): the timed graph -/

open Libpetri.Novel.TimedScg (TNet Cls TReach TimingWF initCls en rowsOf)

/-- **The labelled successor function of the timed graph**: from the net, the emptiness tolerance
`eps` and a class, its successors with their labels (transition name, outcome row). -/
abbrev TimedSuccFn : Type := TNet → ℚ → Cls → List (Scg.Label × Cls)

/-- The explorer the check builds its graph at: classes deduplicated by the class key, the
successors of `σ`, no counter. -/
def timedChkE (σ : TimedSuccFn) (N : TNet) (eps : ℚ) : Explorer Cls Scg.IdxKey Scg.Label where
  key := Scg.idxKey
  bound := fun _ => 0
  succ := fun _ C => σ N eps C

/-- **The check's graph**: the build loop of the graph layer at `timedChkE σ`, with the class
budget `n`, the stop oracle `cut` and `fuel`, no early stop, from the initial class `C0`. -/
noncomputable def timedChkGraph (σ : TimedSuccFn) (N : TNet) (eps : ℚ) (n : ℕ) (cut : ℕ → Bool)
    (fuel : ℕ) (C0 : Cls) : Decide.Out Cls :=
  Decide.build (timedChkE σ N eps) n cut (fun _ => false) false fuel C0

/-- The classes `σ` reaches from `C0`. -/
def TimedSuccReach (σ : TimedSuccFn) (N : TNet) (eps : ℚ) : Cls → Cls → Prop :=
  Relation.ReflTransGen fun a b => ∃ l, (l, b) ∈ σ N eps a

/-- **The reference successor** (`compute_successor` over every enabled clock and every outcome
row, the clocks in canonical name order): `Scg.succL` at `Scg.coByName`. -/
def refTimedSucc : TimedSuccFn := fun N eps C => Scg.succL N (Scg.coByName N) eps C

#spec_witness refTimedSucc

requirement VER_023_graph
  id "VER-023"
  title "Timed Counterexample Check: the timed graph"
  kind B
  scope "the timed state-class graph the timed check builds, all implementations (SHOULD; the shall sentences bind an implementation that offers the check)"
  source verbatim "spec/07-verification.md"
  quote "*While* every finite bound of the net is a whole number of milliseconds, a class of the timed graph *shall* have no successor exactly when its marking enables no transition."
        "*When* the timed graph is closed and no class of it violates a safety property, the property *shall* hold on every marking that an on-time run with atomic firings reaches from the initial marking."
        "*When* the timed graph is closed and no class of it violates a quiescence property, the property *shall* hold on every resting marking that an on-time run with atomic firings reaches from the initial marking, a marking resting when every transition it enables is reapable ([VER-002], [TIME-013]), which under `assumeNoReaping` means when it enables none."
  reading "For every flat timed net N whose intervals are well formed (0 ≤ earliest ≤ latest) and whose every transition has an outcome row, every emptiness tolerance eps that is exact for N (eps = 0, or below the grid step of N's bounds), every initial marking m0 with initial class C0 (initCls in canonical name order) and every class C that σ reaches from C0: σ gives C no successor exactly when no transition of N is enabled in C's marking."
          "For every flat timed net N with well-formed intervals, eps ≥ 0, initial marking m0 with initial class C0, class budget n, stop oracle cut, fuel and marking predicate b: if the build of the graph layer's loop at σ's class-key explorer is closed, not stopped, and no class of it has a marking b holds of, then b holds of no marking a run of the timed semantics TStep reaches from m0."
          "For the same data and a reapable set r over transition names: if that build is closed, not stopped, and no expanded class whose successors are all labelled by reapable transitions has a marking b holds of, then b holds of no marking that a run of TStep reaches from m0 and in which every enabled transition is reapable (with r empty: no transition is enabled)."
  assumes "The model is the successor function σ of the timed graph, from the flat timed net (Novel.TimedScg.TNet: transitions with their outcome rows and static intervals) and the emptiness tolerance. The graph is the build loop of the graph layer (Decide.build) at the explorer that keys classes by Scg.idxKey and expands them by σ, from the initial class initCls in the canonical name order (Scg.coByName): the loop and the key are VER-017's and VER-010's subject, fixed here. The timed semantics is Novel.TimedScg.TStep (strong urgency, every firing atomic, the clock rule of TIME-012 by the graph's own survives), and 'an on-time run with atomic firings' is a TStep run; that the reference executor's on-time runs (OnTimeStep RefTStep, ruling D3) are TStep runs of the verified net's flat image is premise 9 of Novel/TimedScg/Succ.lean, the on-time bridge J7 of this wave, not proved here, so these lines are about TStep (design O4)."
          "The four assumptions the markdown names for SPURIOUS_UNDER_TIMING ('an on-time executor with atomic firings, one that reaps no transition, fires none after its latest bound, and gives an action no duration') are this TStep reading. Each is needed: a late executor that reaps escapes the graph (Novel.TimedScg.reaping_escapes_timed_graph, VER_023_ac6), and so does an action with a duration (Novel.TimedScg.action_duration_escapes). The pass recheck of EXEC-003 AC3, which takes a clock from a transition a same-pass deposit keeps enabled, is part of 'atomic firings' (ruling D20, ver-d#8)."
          "Line 1 is 'For the quiescence properties the predicate reads \"this class has no successor\" as \"no transition can ever fire again\"' and 'On a timed graph that MUST still hold: a class with an enabled transition has a successor whatever its interval'. It needs an exact emptiness test (Scg.ExactEps: eps = 0, or the Rust EPSILON = 1e-9 below the grid of whole-millisecond bounds, ruling VD-7) and an outcome row per transition (a transition with no output spec has one empty row, VER-001). The shall sentence names the first as its While clause (every finite bound a whole number of milliseconds, the grid of step 1); Lean also covers eps = 0 for any bounds. Well-formed intervals and a row per transition hold of every net a runtime accepts (TIME-001's validity table rejects a latest bound below the earliest), so the sentence does not name them. A graph that drops the successors of a class whose enabled transition has no upper bound reports a timed deadlock the net does not have, and is killed (VER_023_graph_forbids_dropUnbounded, on the net S -> d -> X of AC3)."
          "Lines 2 and 3 are SPURIOUS_UNDER_TIMING's meaning ('The property holds under timing', 'SPURIOUS_UNDER_TIMING there means that no on-time run reaches a violating rest'): with lines 3 to 5 of VER_023, an answer SPURIOUS_UNDER_TIMING comes only from a closed, unstopped graph with no violating class (VER_023_spurious_sound). The quiescence predicate is VER-002's reap-aware one ('on a net with a reapable transition, also treats a class whose enabled transitions are all reapable as resting'), with the reapable set over transition names (TIME-013; empty under assumeNoReaping), and the class test is Decide.quiescentAt, which reads the labels of the class's successors. A graph that stops expanding after the initial class (VER_023_graph_forbids_noSuccessors) and one that adds a step out of a dead class (VER_023_graph_forbids_deadLoop) are killed."
          "Out of scope: the exact half of the successor (every class is realised by a timed run), which TIMED_CONFIRMED's 'a run of the timed semantics ignoring priority' needs (ruling D67 (a), a later line of this ID); environment places and match transitions, which the gate of VER_023 excludes (premise 8 of Succ.lean); and fractional millisecond bounds, which TypeScript accepts (ruling D58)."
  signoff "2026-11-13 782ed7a0ca22e868 ai"
  statement : TimedSuccFn → Prop := fun σ =>
    (∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 C : Cls), TimingWF N →
      (∀ i, i < N.length → rowsOf N i ≠ []) → Scg.ExactEps N eps →
      initCls N (Scg.coByName N) eps m0 = some C0 → TimedSuccReach σ N eps C0 C →
      (σ N eps C = [] ↔ ∀ i, en N C.m i = false)) ∧
    (∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 : Cls) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ)
        (b : AMarking → Bool), TimingWF N → 0 ≤ eps →
      initCls N (Scg.coByName N) eps m0 = some C0 →
      (timedChkGraph σ N eps n cut fuel C0).complete = true →
      (timedChkGraph σ N eps n cut fuel C0).stopped = false →
      (∀ j, Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
        (.safety fun C => b C.m) j = false) →
      ∀ s, TReach N m0 s → b s.m = false) ∧
    (∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 : Cls) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ)
        (b : AMarking → Bool) (r : String → Bool), TimingWF N → 0 ≤ eps →
      initCls N (Scg.coByName N) eps m0 = some C0 →
      (timedChkGraph σ N eps n cut fuel C0).complete = true →
      (timedChkGraph σ N eps n cut fuel C0).stopped = false →
      (∀ j, Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
        (.quiescence (fun C => b C.m) fun l => r l.1) j = false) →
      ∀ s, TReach N m0 s → (∀ i, en N s.m i = true → r (Scg.nameOf N i) = true) → b s.m = false)

/- The pinned readable form of the graph block. -/
/--
info: def Libpetri.Spec.VER_023_graph : TimedSuccFn → Prop :=
fun σ =>
  (∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 C : Cls),
      TimingWF N →
        (∀ i < List.length N, rowsOf N i ≠ []) →
          Scg.ExactEps N eps →
            initCls N (Scg.coByName N) eps m0 = some C0 →
              TimedSuccReach σ N eps C0 C → (σ N eps C = [] ↔ ∀ (i : ℕ), en N C.m i = false)) ∧
    (∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 : Cls) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (b : AMarking → Bool),
        TimingWF N →
          0 ≤ eps →
            initCls N (Scg.coByName N) eps m0 = some C0 →
              (timedChkGraph σ N eps n cut fuel C0).complete = true →
                (timedChkGraph σ N eps n cut fuel C0).stopped = false →
                  (∀ (j : ℕ),
                      Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
                          (Decide.Prop'.safety fun C => b C.m) j =
                        false) →
                    ∀ (s : TimedScg.TState), TReach N m0 s → b s.m = false) ∧
      ∀ (N : TNet) (eps : ℚ) (m0 : AMarking) (C0 : Cls) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (b : AMarking → Bool)
        (r : String → Bool),
        TimingWF N →
          0 ≤ eps →
            initCls N (Scg.coByName N) eps m0 = some C0 →
              (timedChkGraph σ N eps n cut fuel C0).complete = true →
                (timedChkGraph σ N eps n cut fuel C0).stopped = false →
                  (∀ (j : ℕ),
                      Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
                          (Decide.Prop'.quiescence (fun C => b C.m) fun l => r l.1) j =
                        false) →
                    ∀ (s : TimedScg.TState),
                      TReach N m0 s → (∀ (i : ℕ), en N s.m i = true → r (Scg.nameOf N i) = true) → b s.m = false
-/
#guard_msgs in #print VER_023_graph

/-! ### The reference -/

/-- The reference explorer is the class-key explorer of `Spec/Verifier/Scg.lean`. -/
theorem timedChkE_ref (N : TNet) (eps : ℚ) :
    timedChkE refTimedSucc N eps = Scg.scgE N (Scg.coByName N) eps := rfl

/-- The label of a successor names a clock of the class. -/
theorem ver023_succL_label {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls}
    {l : Scg.Label} (h : (l, C') ∈ Scg.succL N co eps C) :
    ∃ k, k < C.cs.length ∧ l.1 = Scg.nameOf N (C.cs.getD k 0) := by
  simp only [Scg.succL, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨k, hk, p, -, C'', -, hl, -⟩ := h
  exact ⟨k, hk, by rw [← hl]⟩

/-- The reference successor has no successor exactly when the graph's `succList` has none. -/
theorem ver023_succL_nil {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C : Cls} :
    Scg.succL N co eps C = [] ↔ TimedScg.succList N co eps C = [] := by
  constructor
  · intro h
    refine List.eq_nil_iff_forall_not_mem.mpr fun C' hC' => ?_
    obtain ⟨l, hl⟩ := Scg.mem_succL.mpr hC'
    rw [h] at hl
    simp at hl
  · intro h
    refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
    have := Scg.mem_succL.mp ⟨x.1, hx⟩
    rw [h] at this
    simp at this

/-- ✓ **The reference timed graph meets VER-023's graph lines.** Example: on the net
`S → d → X` with `d` at `delayed(5)`, the class holding `S` has the successor that fires `d`; on
a closed graph without a violating class, every timed run stays in classes of the graph
(`Scg.timed_run_stored`), so it never reaches a violating marking, nor a violating rest. -/
@[evidence holds VER_023_graph]
theorem VER_023_graph_reference : VER_023_graph refTimedSucc := by
  refine ⟨?_, ?_, ?_⟩
  · intro N eps m0 C0 C hT hrows hx h0 hr
    have hE : Relation.ReflTransGen (TimedScg.Edge N (Scg.coByName N) eps) C0 C :=
      Relation.ReflTransGen.mono (fun a b hab => Scg.mem_succL.mp hab) C0 C hr
    have key : TimedScg.succList N (Scg.coByName N) eps C = [] ↔ ∀ i, en N C.m i = false := by
      rcases hx with rfl | ⟨g, hg, hN, he0, heg⟩
      · exact TimedScg.reachable_quiescent_iff_dead hT (Scg.coByName_wf N) hrows h0 hE
      · exact TimedScg.reachable_quiescent_iff_dead_grid hT (Scg.coByName_wf N) hg hN he0 heg
          hrows h0 hE
    exact ver023_succL_nil.trans key
  · intro N eps m0 C0 n cut fuel b hT heps h0 hc hs hv s hrun
    have hp : Decide.verdict (Scg.scgE N (Scg.coByName N) eps)
        (Decide.build (Scg.scgE N (Scg.coByName N) eps) n cut (fun _ => false) false fuel C0)
        (.safety fun C => b C.m) = .proven := by
      have := ver023_verdict_none hs hv
      rw [hc] at this
      exact this
    have hall := Decide.complete_proven_safety (Scg.scgE_equivariant N _ eps)
      (fun a a' hk => by rw [(Scg.idxKey_eq_iff.mp hk).1]) hp
    obtain ⟨C, hreach, hin, -, -⟩ := TimedScg.timed_run_sound hT (Scg.coByName_wf N) heps h0 hrun
    rw [hin.1]
    exact hall C (Scg.scgE_reach_iff.mpr hreach)
  · intro N eps m0 C0 n cut fuel b r hT heps h0 hc hs hv s hrun hrest
    have hp : Decide.verdict (Scg.scgE N (Scg.coByName N) eps)
        (Decide.build (Scg.scgE N (Scg.coByName N) eps) n cut (fun _ => false) false fuel C0)
        (.quiescence (fun C => b C.m) fun l => r l.1) = .proven := by
      have := ver023_verdict_none hs hv
      rw [hc] at this
      exact this
    have hall := Decide.complete_proven_quiescence (Scg.scgE_equivariant N _ eps)
      (fun a a' hk => by rw [(Scg.idxKey_eq_iff.mp hk).1]) hp
    obtain ⟨C, hreach, hin, hwf, -⟩ :=
      TimedScg.timed_run_sound hT (Scg.coByName_wf N) heps h0 hrun
    rw [hin.1]
    refine hall C (Scg.scgE_reach_iff.mpr hreach) ⟨0, le_rfl, fun ly hly => ?_⟩
    obtain ⟨k, hk, hl⟩ := ver023_succL_label (l := ly.1) (C' := ly.2) hly
    rw [hl]
    have hen : en N C.m (C.cs.getD k 0) = true :=
      (hwf.mem _).mp (TimedScg.getD_mem 0 hk)
    rw [← hin.1] at hen
    exact hrest _ hen

/-! ### What the two blocks give together -/

/-- **SPURIOUS_UNDER_TIMING speaks for every on-time run**, from the two statements alone: when
the reading answers `SPURIOUS_UNDER_TIMING` on the check's graph for a safety property, no run of
the timed semantics reaches a marking that violates it. Example: on the race of AC6 with
`unreachable(b)`, a closed timed graph without a class marking `b` rules out every on-time run
that marks `b`. -/
@[evidence cites "VER-023" "The graph closes and no class violates: `SPURIOUS_UNDER_TIMING`. The property holds under timing."]
theorem VER_023_spurious_sound [DecidableEq Scg.IdxKey] {K : Type} {A : TimedGateFn K}
    {Θ : TimedOutcomeFn Cls Scg.IdxKey} {W : TimedAnnotFn K} {σ : TimedSuccFn}
    (h : VER_023 A Θ W) (hg : VER_023_graph σ) {N : TNet} {eps : ℚ} {m0 : AMarking} {C0 : Cls}
    {n : ℕ} {cut : ℕ → Bool} {fuel : ℕ} {b : AMarking → Bool} (hT : TimingWF N) (heps : 0 ≤ eps)
    (h0 : initCls N (Scg.coByName N) eps m0 = some C0)
    (hsp : Θ (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
      (.safety fun C => b C.m) = .spurious) :
    ∀ s, TReach N m0 s → b s.m = false := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h.2.1 (timedChkE σ N eps) n cut fuel C0 (.safety fun C => b C.m)
  have hs : (timedChkGraph σ N eps n cut fuel C0).stopped = false := by
    cases hst : (timedChkGraph σ N eps n cut fuel C0).stopped
    · rfl
    · exact absurd (hsp.symm.trans (h1 hst)) (by simp)
  have hv : ∀ j, Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
      (.safety fun C => b C.m) j = false := by
    intro j
    cases hj : Decide.violatesAt (timedChkE σ N eps) (timedChkGraph σ N eps n cut fuel C0)
      (.safety fun C => b C.m) j
    · rfl
    · obtain ⟨tr, htr⟩ := h2 hs ⟨j, hj⟩
      exact absurd (hsp.symm.trans htr) (by simp)
  have hc : (timedChkGraph σ N eps n cut fuel C0).complete = true := by
    cases hco : (timedChkGraph σ N eps n cut fuel C0).complete
    · exact absurd (hsp.symm.trans (h4 hs hco hv)) (by simp)
    · rfl
  exact hg.2.1 N eps m0 C0 n cut fuel b hT heps h0 hc hs hv

/-- **The race of AC6**: `t1: p → a` at `window(3, 5)`, `t2: p → b` at `delayed(10)`, one token
on `p`. No run of the timed semantics marks `b`, so `unreachable(b)` is `SPURIOUS_UNDER_TIMING`
once the timed graph closes; an executor that falls behind past 5 ms reaps `t1` and fires `t2`,
and marks `b`. That is why the timed claim assumes an on-time executor. -/
@[evidence cites "VER-023" "The report MUST also say what that timed claim assumes: an on-time executor with atomic firings, one that reaps no transition, fires none after its latest bound, and gives an action no duration."]
theorem VER_023_ac6 :
    (∃ s, TimedScg.LateReach TimedScg.netRP TimedScg.reapRP 0 TimedScg.m0RP s ∧ s.m 2 = 1) ∧
      ∀ s, TReach TimedScg.netRP TimedScg.m0RP s → s.m 2 = 0 := by
  obtain ⟨hl, -, ht⟩ := TimedScg.reaping_escapes_timed_graph 0 (eps := 0) le_rfl (by norm_num)
  exact ⟨hl, ht⟩

/-! ### Wrong graphs, one per line -/

/-- The marking with one token on place `0`. -/
def ver023M0 : AMarking := fun q => if q = 0 then 1 else 0

/-- `d: S → X` at `delayed(5)` with no upper bound, the net of AC3 (`S = 0`, `X = 1`). -/
def ver023NetD : TNet :=
  [{ tr := { name := "d", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
     rows := [[1]], eft := 5, lft := ⊤ }]

/-- `t: p → q`, `immediate` (`p = 0`, `q = 1`). -/
def ver023NetT : TNet :=
  [{ tr := { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
     rows := [[1]], eft := 0, lft := ⊤ }]

/-- The net with no transition. -/
def ver023Net0 : TNet := []

theorem ver023NetD_wf : TimingWF ver023NetD := by
  intro i
  match i with
  | 0 => exact ⟨by simp [TimedScg.eftOf, ver023NetD], by simp [TimedScg.lftOf, ver023NetD]⟩
  | i + 1 => exact ⟨le_refl _, by simp [TimedScg.eftOf, TimedScg.lftOf, ver023NetD]⟩

theorem ver023NetT_wf : TimingWF ver023NetT := by
  intro i
  match i with
  | 0 => exact ⟨by simp [TimedScg.eftOf, ver023NetT], by simp [TimedScg.lftOf, ver023NetT]⟩
  | i + 1 => exact ⟨le_refl _, by simp [TimedScg.eftOf, TimedScg.lftOf, ver023NetT]⟩

theorem ver023Net0_wf : TimingWF ver023Net0 := fun _ =>
  ⟨le_refl _, by simp [TimedScg.eftOf, TimedScg.lftOf, ver023Net0]⟩

theorem ver023NetD_rows : ∀ i, i < ver023NetD.length → rowsOf ver023NetD i ≠ [] := by
  intro i hi
  simp only [ver023NetD, List.length_cons, List.length_nil] at hi
  interval_cases i
  simp [TimedScg.rowsOf, ver023NetD]

/-- ✓ **A delayed transition still fires out of its class** (AC3). Example: on `S → d → X` with
`d` at `delayed(5)`, whose interval `[5, ∞)` has no upper bound, the initial class holding `S`
has a successor in the reference timed graph, so it is not a deadlock. -/
@[evidence nonvacuous VER_023_graph]
theorem VER_023_graph_nonvacuous :
    ∃ C0, initCls ver023NetD (Scg.coByName ver023NetD) 0 ver023M0 = some C0 ∧
      refTimedSucc ver023NetD 0 C0 ≠ [] := by
  obtain ⟨C0, h0, -, -⟩ := TimedScg.init_sound ver023NetD_wf (Scg.coByName_wf ver023NetD) le_rfl ver023M0
  refine ⟨C0, h0, fun hnil => ?_⟩
  have hm := (TimedScg.initCls_eq h0).1
  have := (VER_023_graph_reference.1 ver023NetD 0 ver023M0 C0 C0 ver023NetD_wf ver023NetD_rows
    (Or.inl rfl) h0 Relation.ReflTransGen.refl).mp hnil 0
  rw [hm] at this
  revert this
  decide

/-- Mutant: a graph that gives no successor to a class enabling a transition with no upper bound. -/
noncomputable def ver023_dropUnbounded : TimedSuccFn := fun N eps C =>
  if (TimedScg.enabledIds N C.m).any (fun i => decide (TimedScg.lftOf N i = ⊤)) then []
  else refTimedSucc N eps C

/-- ✗ **A class with an enabled transition has a successor whatever its interval** (line 1,
AC3). Example: on `S → d → X` with `d` at `delayed(5)`, a graph that drops the successors of the
class holding `S` reports a timed deadlock there, though `d` fires after 5. -/
@[evidence forbids VER_023_graph]
theorem VER_023_graph_forbids_dropUnbounded : ¬ VER_023_graph ver023_dropUnbounded := by
  intro h
  obtain ⟨C0, h0, -, -⟩ := TimedScg.init_sound ver023NetD_wf (Scg.coByName_wf ver023NetD) le_rfl ver023M0
  have hm := (TimedScg.initCls_eq h0).1
  have hany : (TimedScg.enabledIds ver023NetD ver023M0).any
      (fun i => decide (TimedScg.lftOf ver023NetD i = ⊤)) = true := by decide
  have hnil : ver023_dropUnbounded ver023NetD 0 C0 = [] := by
    simp only [ver023_dropUnbounded, hm, hany, if_true]
  have := (h.1 ver023NetD 0 ver023M0 C0 C0 ver023NetD_wf ver023NetD_rows (Or.inl rfl) h0
    Relation.ReflTransGen.refl).mp hnil 0
  rw [hm] at this
  revert this
  decide

/-- Mutant: a graph with no successors at all, which closes after its initial class. -/
def ver023_noSuccessors : TimedSuccFn := fun _ _ _ => []

/-- ✗ **A closed graph holds every timed run** (line 2). Example: on `t: p → q`, `immediate`,
a graph that never expands the initial class closes with one class, which does not mark `q`;
yet `t` fires at once and marks `q`, so `unreachable(q)` is not spurious under timing. -/
@[evidence forbids VER_023_graph]
theorem VER_023_graph_forbids_noSuccessors : ¬ VER_023_graph ver023_noSuccessors := by
  intro h
  obtain ⟨C0, h0, -, -⟩ := TimedScg.init_sound ver023NetT_wf (Scg.coByName_wf ver023NetT) le_rfl ver023M0
  have hm := (TimedScg.initCls_eq h0).1
  have hb : timedChkGraph ver023_noSuccessors ver023NetT 0 10 (fun _ => false) 10 C0 =
      ⟨[C0], 1, true, false, false⟩ := rfl
  have hv : ∀ j, Decide.violatesAt (timedChkE ver023_noSuccessors ver023NetT 0)
      (timedChkGraph ver023_noSuccessors ver023NetT 0 10 (fun _ => false) 10 C0)
      (.safety fun C => decide (1 ≤ C.m 1)) j = false := by
    refine ver023_noHit fun j hj => ?_
    rw [hb] at hj ⊢
    obtain rfl : j = 0 := by simpa using hj
    simp [Decide.violatesAt, hm, ver023M0]
  have hrun : TReach ver023NetT ver023M0
      ⟨ForwardDeposit.fireAD ver023M0 (TimedScg.trOf ver023NetT 0) [1], fun i =>
        if TimedScg.persists ver023NetT ver023M0 0 [1] i then (TimedScg.s0 ver023M0).ν i
        else 0⟩ :=
    Relation.ReflTransGen.single (TimedScg.TStep.fire (TimedScg.s0 ver023M0) 0 [1]
      (by decide) (by simp [TimedScg.eftOf, ver023NetT, TimedScg.s0])
      (by simp [TimedScg.rowsOf, ver023NetT]))
  have := h.2.1 ver023NetT 0 ver023M0 C0 10 (fun _ => false) 10 (fun m => decide (1 ≤ m 1))
    ver023NetT_wf le_rfl h0 (by rw [hb]) (by rw [hb]) hv _ hrun
  revert this
  decide

/-- Mutant: a graph that gives a dead class a step to itself. -/
def ver023_deadLoop : TimedSuccFn := fun N eps C =>
  if (refTimedSucc N eps C).isEmpty then [(("tick", 0), C)] else refTimedSucc N eps C

/-- ✗ **A closed graph holds every resting run** (line 3). Example: on the net with no transition
and a token on place 0, the initial marking is dead and strands that token; a graph that lets
the dead class step to itself finds no resting class, so it would call deadlock freedom
spurious under timing. -/
@[evidence forbids VER_023_graph]
theorem VER_023_graph_forbids_deadLoop : ¬ VER_023_graph ver023_deadLoop := by
  intro h
  obtain ⟨C0, h0, -, -⟩ := TimedScg.init_sound ver023Net0_wf (Scg.coByName_wf ver023Net0) le_rfl ver023M0
  obtain ⟨hm, hcs, -⟩ := TimedScg.initCls_eq h0
  have hcs0 : C0.cs = [] := by
    rw [hcs]
    apply List.eq_nil_of_length_eq_zero
    rw [TimedScg.reorder_length (Scg.coByName_wf ver023Net0)]
    simp [TimedScg.enabledIds, ver023Net0]
  have hsucc : ver023_deadLoop ver023Net0 0 C0 = [(("tick", 0), C0)] := by
    simp [ver023_deadLoop, refTimedSucc, Scg.succL, hcs0]
  have hb : timedChkGraph ver023_deadLoop ver023Net0 0 10 (fun _ => false) 10 C0 =
      ⟨[C0], 1, true, false, false⟩ := by
    simp [timedChkGraph, Decide.build, Decide.loop, Decide.expandB, timedChkE, hsucc]
  have hv : ∀ j, Decide.violatesAt (timedChkE ver023_deadLoop ver023Net0 0)
      (timedChkGraph ver023_deadLoop ver023Net0 0 10 (fun _ => false) 10 C0)
      (.quiescence (fun C => decide (1 ≤ C.m 0)) fun l => (fun _ => false) l.1) j = false := by
    refine ver023_noHit fun j hj => ?_
    rw [hb] at hj ⊢
    obtain rfl : j = 0 := by simpa using hj
    simp [Decide.violatesAt, Decide.quiescentAt, timedChkE, hsucc]
  have := h.2.2 ver023Net0 0 ver023M0 C0 10 (fun _ => false) 10 (fun m => decide (1 ≤ m 0))
    (fun _ => false) ver023Net0_wf le_rfl h0 (by rw [hb]) (by rw [hb]) hv _
    Relation.ReflTransGen.refl (fun i hi => by simp [TimedScg.en, ver023Net0] at hi)
  revert this
  decide

end Libpetri.Spec
