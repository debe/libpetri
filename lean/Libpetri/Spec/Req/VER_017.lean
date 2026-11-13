import Libpetri.Spec.Verifier.Graph
import Libpetri.Spec.Verifier.Result
import Libpetri.Spec.Verifier.Pipeline
import Libpetri.Spec.Text.VER_017

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-017: Bounded state-space enumeration route (`spec/07-verification.md`)

Before the SMT pipeline the verifier tries to decide the property by building the state-class
graph of the untimed net, breadth-first, up to a class budget. Two blocks share the ID.

**The route** (`VER_017`) is a predicate over three variables:

* `A : EnumGateFn K`, the route's guard, from what it reads of the net the dispatcher hands it
  (the timed net, whether it has a match transition, the environment places still registered)
  and the class budget;
* `G : GraphRoute S S L`, the graph route of `Spec/Verifier/Graph.lean` (the build, the verdict
  read off a built graph, the witness of a class), run at the identity explorer of a successor
  function `succ`, with no early stop;
* `P : EnumDispatchFn L`, the dispatcher around the route, from the guard's answer, the route's
  outcome and the answer of the rest of the pipeline to the verifier's answer.

**The cache** (`VER_017_cache`) is a predicate over the lookup of one entry, the keyed query and
the reading of an answer: the state machine of `cacheLookup`, `cacheQuery` and `useVerdict`.

The witnesses are `refEnumGate`, `refGraphRoute` (the build loop `Novel.RouteB.Decide.build`, its
verdict and the shortest path of the built graph) and `refEnumDispatch`, and `cacheLookup`,
`cacheQuery` and `useVerdict`. The reference proof of the witness line rests on the build being
breadth-first (`ver017_build_bfs`), so the first counted class it reports is a nearest one. Wrong
models are killed one per line on small graphs: a chain, a fork, a diamond, a graph with a dead
branch and the unbounded producer of the test derivation.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB Libpetri.Spec.Verifier Libpetri.Spec.Verifier.Graph

/-! ## The model -/

/-- **What the route's guard reads** of the net the dispatcher hands it, after the rewrites of
[VER-006] (`Arrivals` closes the net), [VER-004] (the in-flight split) and [EXEC-042]
(terminals): the timed net, whether the net declares a match (ν-join) transition, and the
environment places still registered on it. -/
structure EnumInput (K : Type) where
  /-- The timed net. -/
  net : Reference.TimedNet K
  /-- Whether the net declares a match (ν-join) transition ([NU-020]). -/
  hasMatch : Bool
  /-- The environment places registered on the net; none after the `Arrivals` rewrite. -/
  envPlaces : List K

/-- **The route's guard**: from what it reads of the net and the class budget, whether the route
runs. -/
abbrev EnumGateFn (K : Type) : Type := EnumInput K → ℕ → Bool

/-- **The reference guard** (`enumeration_applies`, `smt_verifier.rs`): no match transition, no
environment place, every transition `immediate`, a positive budget. -/
def refEnumGate {K : Type} : EnumGateFn K := fun x n =>
  !x.hasMatch && x.envPlaces.isEmpty && decide (Untimed x.net) && decide (0 < n)

/-- **What the route hands the dispatcher**: a verdict it read off the graph, a truncation with no
hit in the explored prefix, or a build stopped by the total budget or a cancellation. -/
inductive EnumOutcome (L : Type) where
  /-- The graph closed and no reachable class violates. -/
  | proven
  /-- A class of the graph violates; the witness. -/
  | violated (trace : List L)
  /-- The graph was cut off at the class budget and no counted class violates. -/
  | truncated
  /-- The build was stopped by the total budget or a cancellation ([VER-013]). -/
  | stopped
  deriving DecidableEq

/-- **The verifier's answer** around the route, and the answer of the rest of the pipeline. -/
inductive EnumAnswer (L : Type) where
  /-- `Proven`. -/
  | proven
  /-- `Violated`, with the counterexample's labels. -/
  | violated (trace : List L)
  /-- `Unknown`. -/
  | unknown
  deriving DecidableEq

/-- **The dispatcher**: from whether the guard let the route run, the route's outcome and the
answer the rest of the pipeline gives, the verifier's answer. -/
abbrev EnumDispatchFn (L : Type) : Type := Bool → EnumOutcome L → EnumAnswer L → EnumAnswer L

/-- **The reference dispatcher**: a skipped route leaves the rest of the pipeline's answer; a
decided route answers; a truncation falls through; a stop ends the call with `Unknown`. -/
def refEnumDispatch {L : Type} : EnumDispatchFn L := fun enter out rest =>
  if enter then
    match out with
    | .proven => .proven
    | .violated tr => .violated tr
    | .truncated => rest
    | .stopped => .unknown
  else rest

/-- **The enumeration build** of a graph route: the identity explorer of the successor function
`succ`, the class budget `n`, the stop oracle `cut` (the total budget and cancellation), no early
stop, and `fuel` steps from `x0`. -/
def enumBuild {S L : Type} (G : GraphRoute S S L) (succ : S → List (L × S)) (n : ℕ)
    (cut : ℕ → Bool) (fuel : ℕ) (x0 : S) : Decide.Out S :=
  G.build (idExplorer succ) n cut (fun _ => false) false fuel x0

/-- **A state violates a property**: for a safety property, the state is bad; for a quiescence
property, the state is bad and every step out of it is of a reapable transition (with nothing
reapable: it has no successor at all, [VER-002]). -/
def EnumViol {S L : Type} (succ : S → List (L × S)) : Decide.Prop' S L → S → Prop
  | .safety bad, y => bad y = true
  | .quiescence bad reap, y => bad y = true ∧ ∀ ly ∈ succ y, reap ly.1 = true


/-- **A counted class**: class `j` of a built graph is a stored state that violates the property,
and for a quiescence property the builder expanded it. -/
def EnumCounted {S L : Type} (succ : S → List (L × S)) (o : Decide.Out S) (p : Decide.Prop' S L)
    (j : ℕ) : Prop :=
  ∃ y, o.cls[j]? = some y ∧ EnumViol succ p y ∧ ∀ bad reap, p = .quiescence bad reap → j < o.exp
/-- **The route's outcome**: nothing off a stopped build, else the verdict read off the graph,
with the witness of the violating class. -/
def enumOutcome {S L : Type} (G : GraphRoute S S L) (succ : S → List (L × S)) (n : ℕ)
    (cut : ℕ → Bool) (fuel : ℕ) (x0 : S) (p : Decide.Prop' S L) : EnumOutcome L :=
  if (enumBuild G succ n cut fuel x0).stopped then .stopped
  else match G.verdict (idExplorer succ) (enumBuild G succ n cut fuel x0) p with
    | .proven => .proven
    | .violated i => .violated (G.trace (idExplorer succ) (enumBuild G succ n cut fuel x0) i)
    | .unknown => .truncated

/- The reference guard and dispatcher are witness models of VER-017's `holds` theorem, beside
`refGraphRoute` (registered in `Spec/Verifier/Graph.lean`). -/
#spec_witness refEnumGate
#spec_witness refEnumDispatch


/-! ## VER-017 (B): the route -/

requirement VER_017
  id "VER-017"
  title "Bounded State-Space Enumeration Route"
  kind B
  scope "the SMT verifier, all implementations (SHOULD; the shall sentences bind an implementation that offers the route)"
  source verbatim "spec/07-verification.md"
  covers VER_017.s1, VER_017.s2, VER_017.s3, VER_017.s4, VER_017.s5, VER_017.s6, VER_017.s7,
        VER_017.s8, VER_017.s9, VER_017.s10, VER_017.s11, VER_017.s12
  reading "The guard A runs the route on a net with timing X, match flag hasMatch and registered environment places env at budget n exactly when hasMatch is false, env is empty, every transition of X is immediate (Untimed X) and n is positive."
          "For every successor function succ, budget n, stop oracle cut, fuel and initial state x0, with E the identity explorer of succ and o the build of G at E with no early stop: if cut never fires and the fuel is above n, o was not stopped;"
          "if o was not stopped, o is closed exactly when it holds fewer than n classes;"
          "class 0 of o is x0, and every state o stores is reachable from x0;"
          "if o is closed, the verdict G reads off o for a property p is Proven exactly when no state reachable from x0 violates p;"
          "if o is closed, the verdict is never Unknown;"
          "if the verdict is Violated at class i: class i is a stored state y that violates p, expanded if p is a quiescence property; the witness G.trace E o i is a run of succ from x0 to y and a path of the built graph's edges from class 0 to class i; and no path of those edges from class 0 to a counted class (a stored state that violates p, expanded if p is a quiescence property) is shorter than the witness;"
          "if the verdict is Proven, o is closed and was not stopped;"
          "if o was stopped, the verdict is Unknown for every property;"
          "if o was not stopped and some class of o is counted for p, the verdict for p is Violated."
          "The dispatcher P gives the rest of the pipeline's answer whenever the guard did not let the route run;"
          "a route that ran and returned Proven or Violated gives that answer;"
          "a route that ran into a truncation with no hit gives the rest of the pipeline's answer;"
          "a route whose build was stopped gives Unknown."
  assumes "The model is the triple (A, G, P). A reads an EnumInput: the timed net the route receives, whether it declares a match transition, and the environment places still registered on it, after the rewrites of VER-006 (Arrivals clears the registration and closes the net, smt_verifier.rs with_arrivals), VER-004 (the in-flight split) and EXEC-042 (terminals); none of these changes timing or adds a match transition, so the guard's answer is the same before and after the split and the terminal rewrite. Reference.TimedNet has no match transition and no environment place of its own, so both are fields of EnumInput. G is a GraphRoute (Spec/Verifier/Graph.lean) at the identity explorer of a successor function succ, with no early stop: the runtimes' enumeration build (StateClassGraph::build) has none. On a reference net succ is Reference.succ, every enabled transition and every way its firing can end (enumE), so the reachable states are the untimed reachable markings of VER-004 and a run is a firing sequence (VER_017_firing_sequence). P maps the guard's answer, the route's outcome (enumOutcome) and the answer of the rest of the pipeline to the verifier's answer."
          "The statement constrains A, G and P one at a time. That the verifier hands P the guard's answer A x n on the net it verifies, and the outcome enumOutcome G (Reference.succ x.net) n cut fuel m0 p of that net's initial marking, is the wiring the model assumes and does not state; VER_017_only_adds and VER_017_firing_sequence derive what the statement gives under that wiring."
          "The property is a Decide.Prop': a safety predicate bad over states, or a quiescence predicate with the reapable labels reap (the reap-aware reading of VER-002, nothing reapable under assumeNoReaping). A state violates a quiescence property when it is bad and every step out of it is of a reapable transition (EnumViol); with nothing reapable that is the markdown's 'found without successors'. A counted class (EnumCounted) is a stored state that violates the property, expanded if the property is a quiescence property. That bad is VER-002's predicate on the marking, and that every route reads one shared implementation of it ('implementations MUST share one predicate implementation'), is code structure, kind Q; in the model the enumeration route and Route B (VER-012) read the one Decide.verdict."
          "Line 2 is 'The build shall be stopped only when the total budget runs out or the caller cancels': the stop oracle cut stands for the total budget and cancellation, and the fuel is the model's bound on loop steps, which the runtimes do not have. Each step expands one class, so with fuel above the class budget the budget ends the build first, and a build that never sees the oracle raised is not stopped (ver017_loop_noStop). A build that stops whatever the oracle says passes every other line, and is killed here (VER_017_forbids_spuriousStop)."
          "Line 3 is the budget boundary of ruling D20 (ver-c#4): the class budget is tested when a class is taken from the worklist (state_class_graph.rs, while let Some(current_idx) = queue.pop_front() { if graph.classes.len() >= max_classes), so a graph of C classes closes only at a budget above C, and a stored class count may exceed the budget. A build that closes at a budget of C is killed (VER_017_forbids_closeAtBudget). The Lean reference search of the conformance binary (Reference/Search.lean) tests its cap on insertion and closes at cap = C, so it disagrees with line 3 at that one budget; the conformance corpus never reaches that boundary: its 224 complete nets hold at most 133 classes, its 81 incomplete nets stop at the reference cap of 100000, and the four languages replay it at an enumeration budget of 5000 (checked 2026-11-12, risk R5)."
          "Line 4 is 'Every class it stored is a real reachable class': class 0 is the initial state and every stored state is reachable from it (build_par, Decide.build_reach). A build from the wrong state is killed (VER_017_forbids_wrongStart)."
          "Lines 5 to 7 are 'What the verdict means' (exact: sound and complete on a closed graph) and 'A hit is Violated, with the shortest path to a violating class inside the explored graph as the witness'. Shortest means shortest in the graph the route built (ruling D20, V5 (4)), over the paths to every counted class, not only to the class reported. The reference meets it because its build is breadth-first: a class stored before the target of an edge from class a has an edge from class a or from an earlier class (ver017_build_bfs), so an earlier class is never farther from class 0 (ver017_walk_mono), and the route reports the first counted class in storage order (ver017_verdict_first). The witness is not claimed to be a shortest run of the net: a run can pass through classes a truncated graph did not store, and under VER-024 the graph is reduced. Killed: a route that reports the last counted class (VER_017_forbids_lastHit), a longer path to its own class (VER_017_forbids_longTrace), a class that does not violate (VER_017_forbids_wrongClass), an empty witness (VER_017_forbids_emptyTrace), and a frontier class as quiescent (VER_017_forbids_frontierQuiescent)."
          "On a reference net the run of line 7 is a firing sequence of the untimed net from the initial marking (VER_017_firing_sequence), which is why the result reports it confirmed with nothing to replay (AC2) and with counterexampleTiming UNTIMED_NET (the route runs only on untimed nets, line 1); the confirmed field and the timing label are the result record of VER-003."
          "Lines 8 to 10 are 'Verdicts from a truncated graph': Proven never comes from a prefix (line 8; VER_017_forbids_eagerProven), a stopped build reads nothing (line 9; VER_017_forbids_readStopped), and a counted class makes the verdict Violated whenever the build was not stopped (line 10): a stored safety hit on the frontier (VER_017_forbids_safetyExpanded) and an expanded quiescent class on a truncated graph (VER_017_forbids_noPrefixQuiescence). 'The same rule applies to Route B and to the timed check' is VER-012's and VER-023's line, each over the same Decide.verdict."
          "Lines 11 to 14 are the dispatcher. 'Shall not run the SMT pipeline' is the pipeline's: a step that decides ends the run, so no later step is entered and no solver script starts after it (VER_017_decided_ends, over runPipeline of Spec/Verifier/Pipeline.lean), and the enumeration comes before flattening and the IC3/PDR query (rtStepNames_order). 'A reachability-safety property first tries the linear bound of VER-015, which runs ahead of this route' is VER-015's line: the linear bound is part of what runs before the route, and a Proven it returns ends the call before the route."
          "In line 13 the argument rest is the answer the rest of the pipeline gives when it runs after the route. Under a total budget (VER-013) it runs with the time the route left, so it can be Unknown where it would decide without the route: that is the 'except that the time the route took counts against a total budget' of the sentence and the 'Unless the total budget runs out or the caller cancels' of the prose (ruling D20, ver-c#6). 'The route can only add verdicts' is lines 11, 13 and 14 with line 12: the answer is the rest of the pipeline's unless the route decided or a stop ended the build (VER_017_only_adds)."
          "Line 1 is the guard, the route's applicability, and only that. An applying route still does not run when an earlier step of the pipeline decided or refused the query: the linear bound of VER-015, whose Proven ends the call; Route B for a name-alignment property, which it alone decides, even on an untimed net without match transitions (smt_verifier.rs, the Route B trigger ahead of the enumeration); the refusals of VER-003 (an unresolved place, a verified net that cannot be built), VER-004 (the in-flight split) and NU-010 (a declared mint transition the net does not hold); and a stop of VER-013. The markdown says so in the sentence after the guard ('An applying route runs unless an earlier step of the pipeline decided or refused the query'); the order of those steps is rtStepNames with the order lines of VER-015, VER-018, VER-019 and NU-053, and the refusals are VER-003's and NU-010's lines."
          "Condition 3 (untimed) is Untimed X, every transition immediate, the test VER-003's UNTIMED_NET reads. Java tests its deprecated Timing.Unconstrained as timed (ScgVerifier.java), so a net using it skips the route in Java only, with the same verdict from the rest of the pipeline; that is a kind N note (ruling D20, ver-c#8)."
          "AC1 (decided by the graph, the report names the route and its class count, no solver phase but the bound of VER-015) is lines 5 to 7 with line 12 and VER_017_decided_ends; the report text and the class count line are kind Q, and the route name is VER-003's result record."
          "AC2 (a confirmed real firing sequence) is line 7 and VER_017_firing_sequence."
          "AC3 (the result names the route and says that P-invariants were not computed) is the result record of VER-003 and report text, kind Q."
          "AC4 (exceeding the budget gives a report line naming the budget and, unless the prefix violates, falls through unchanged) is lines 3, 10 and 13; the report line is kind Q."
          "AC5 (skipped for a ν-net, a net with environment places after the rewrites of VER-006, a timed net, a budget of 0; the verdict is the rest of the pipeline's) is lines 1 and 11 (ruling D92 (a)); refEnumGate is false on each (VER_017_ac5). 'The report carries no enumeration section' is kind Q."
          "AC6 (where both routes answer, they agree) is soundness: a Proven of the route holds on every reachable marking (line 5) and a Violated is a real run (line 7), and every route meets VER-003, so no two routes give Proven and a confirmed Violated for one net and property."
          "AC7 to AC10 (the state-space cache) are the second block, VER_017_cache."
          "AC11 (truncated prefix) is lines 7 to 10, checked on the test derivation's producer gen: G -> G, A at a class budget of 50 (VER_017_nonvacuous): placeBound(A, 2) is Violated with the trace gen, gen, gen, and deadlockFree on the same truncated graph falls through."
          "The test derivation's pipeline p0 -> t0 -> p1 -> t1 -> p2 is VER_017_pipeline on the reference net: deadlockFree with p2 a sink is Proven from 3 classes at a budget of 4, without the sink it is Violated with t0, t1, at a budget of 3 (the graph size) the graph is truncated, and the delayed variant and the budget 0 skip the route. 'With and without the route the same verdict' is AC6."
          "The motivation and measurement paragraphs are not requirements."
  signoff "2026-11-13 7114d5d6fe5cd525 ai"
  statement : ∀ {K S L : Type} [DecidableEq S], EnumGateFn K → GraphRoute S S L → EnumDispatchFn L → Prop :=
    fun {K S L} [DecidableEq S] A G P =>
      (∀ (X : Reference.TimedNet K) (hasMatch : Bool) (env : List K) (n : ℕ),
        A ⟨X, hasMatch, env⟩ n = true ↔ (hasMatch = false ∧ env = [] ∧ Untimed X ∧ 0 < n)) ∧
      (∀ (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (x0 : S),
        let E := idExplorer succ
        let o := enumBuild G succ n cut fuel x0
        ((∀ k, cut k = false) → n < fuel → o.stopped = false) ∧
        (o.stopped = false → (o.complete = true ↔ o.cls.length < n)) ∧
        (o.cls[0]? = some x0 ∧ ∀ y ∈ o.cls, Explorer.Reach E x0 y) ∧
        (o.complete = true → ∀ p, (G.verdict E o p = .proven ↔
          ∀ y, Explorer.Reach E x0 y → ¬ EnumViol succ p y)) ∧
        (o.complete = true → ∀ p, G.verdict E o p ≠ .unknown) ∧
        (∀ p i, G.verdict E o p = .violated i →
          ∃ y, o.cls[i]? = some y ∧ EnumViol succ p y ∧
            (∀ bad reap, p = .quiescence bad reap → i < o.exp) ∧
            ERun E x0 (G.trace E o i) y ∧ Walk (edges E o) 0 (G.trace E o i) i ∧
            ∀ j t, EnumCounted succ o p j → Walk (edges E o) 0 t j →
              (G.trace E o i).length ≤ t.length) ∧
        (∀ p, G.verdict E o p = .proven → o.complete = true ∧ o.stopped = false) ∧
        (o.stopped = true → ∀ p, G.verdict E o p = .unknown) ∧
        (o.stopped = false → ∀ p, (∃ j, EnumCounted succ o p j) →
          ∃ i, G.verdict E o p = .violated i)) ∧
      (∀ out rest, P false out rest = rest) ∧
      (∀ rest, P true .proven rest = .proven ∧ ∀ tr, P true (.violated tr) rest = .violated tr) ∧
      (∀ rest, P true .truncated rest = rest) ∧
      (∀ rest, P true .stopped rest = .unknown)

/- The pinned readable form of VER-017: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_017 : {K S L : Type} →
  [DecidableEq S] → EnumGateFn K → GraphRoute S S L → EnumDispatchFn L → Prop :=
fun {K S L} [DecidableEq S] A G P =>
  (∀ (X : Reference.TimedNet K) (hasMatch : Bool) (env : List K) (n : ℕ),
      A { net := X, hasMatch := hasMatch, envPlaces := env } n = true ↔
        hasMatch = false ∧ env = [] ∧ Untimed X ∧ 0 < n) ∧
    (∀ (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (x0 : S),
        have E := idExplorer succ;
        have o := enumBuild G succ n cut fuel x0;
        ((∀ (k : ℕ), cut k = false) → n < fuel → o.stopped = false) ∧
          (o.stopped = false → (o.complete = true ↔ o.cls.length < n)) ∧
            (o.cls[0]? = some x0 ∧ ∀ y ∈ o.cls, E.Reach x0 y) ∧
              (o.complete = true →
                  ∀ (p : Decide.Prop' S L),
                    G.verdict E o p = Decide.Verdict.proven ↔ ∀ (y : S), E.Reach x0 y → ¬EnumViol succ p y) ∧
                (o.complete = true → ∀ (p : Decide.Prop' S L), G.verdict E o p ≠ Decide.Verdict.unknown) ∧
                  (∀ (p : Decide.Prop' S L) (i : ℕ),
                      G.verdict E o p = Decide.Verdict.violated i →
                        ∃ y,
                          o.cls[i]? = some y ∧
                            EnumViol succ p y ∧
                              (∀ (bad : S → Bool) (reap : L → Bool), p = Decide.Prop'.quiescence bad reap → i < o.exp) ∧
                                ERun E x0 (G.trace E o i) y ∧
                                  Walk (edges E o) 0 (G.trace E o i) i ∧
                                    ∀ (j : ℕ) (t : List L),
                                      EnumCounted succ o p j →
                                        Walk (edges E o) 0 t j → (G.trace E o i).length ≤ t.length) ∧
                    (∀ (p : Decide.Prop' S L),
                        G.verdict E o p = Decide.Verdict.proven → o.complete = true ∧ o.stopped = false) ∧
                      (o.stopped = true → ∀ (p : Decide.Prop' S L), G.verdict E o p = Decide.Verdict.unknown) ∧
                        (o.stopped = false →
                          ∀ (p : Decide.Prop' S L),
                            (∃ j, EnumCounted succ o p j) → ∃ i, G.verdict E o p = Decide.Verdict.violated i)) ∧
      (∀ (out : EnumOutcome L) (rest : EnumAnswer L), P false out rest = rest) ∧
        (∀ (rest : EnumAnswer L),
            P true EnumOutcome.proven rest = EnumAnswer.proven ∧
              ∀ (tr : List L), P true (EnumOutcome.violated tr) rest = EnumAnswer.violated tr) ∧
          (∀ (rest : EnumAnswer L), P true EnumOutcome.truncated rest = rest) ∧
            ∀ (rest : EnumAnswer L), P true EnumOutcome.stopped rest = EnumAnswer.unknown
-/
#guard_msgs in #print VER_017

/-! ### Facts about the enumeration build -/

section Facts

variable {S K L : Type}

/-- Without the early stop an expansion never ends the build. -/
theorem ver017_expandB_noStop (E : Explorer S K L) (bad : S → Bool) :
    ∀ (cls : List S) (ys : List (L × S)), (Decide.expandB E bad false cls ys).2 = false
  | cls, [] => by simp [Decide.expandB]
  | cls, (_, y) :: ys => by
    unfold Decide.expandB
    split
    · exact ver017_expandB_noStop E bad cls ys
    · rw [if_neg (by simp)]
      exact ver017_expandB_noStop E bad (cls ++ [y]) ys

/-- Without the early stop the loop never stops early. -/
theorem ver017_loop_noEarly (E : Explorer S K L) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool) :
    ∀ fuel cls exp c, (Decide.loop E n cut bad false fuel cls exp c).early = false
  | 0, _, _, _ => rfl
  | fuel + 1, cls, exp, c => by
    simp only [Decide.loop]
    split
    · rfl
    · rename_i x _
      split
      · rfl
      · split
        · rfl
        · have h := ver017_expandB_noStop E bad cls (E.succ c x)
          split
          · rename_i cls' heq
            rw [heq] at h
            cases h
          · exact ver017_loop_noEarly E n cut bad fuel _ _ _

/-- **The enumeration build never stops early.** -/
theorem ver017_build_noEarly (E : Explorer S K L) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool)
    (fuel : ℕ) (x0 : S) : (Decide.build E n cut bad false fuel x0).early = false := by
  simp only [Decide.build, Bool.false_and, Bool.false_eq_true, if_false]
  exact ver017_loop_noEarly E n cut bad fuel _ _ _

/-- **Without the stop oracle, a loop with more fuel than the class budget left is not
stopped**: each step expands one class, so the budget ends the loop before the fuel runs out. -/
theorem ver017_loop_noStop (E : Explorer S K L) (n : ℕ) (bad : S → Bool) :
    ∀ fuel cls exp c, exp ≤ n → n < fuel + exp →
      (Decide.loop E n (fun _ => false) bad false fuel cls exp c).stopped = false
  | 0, _, exp, _, h1, h2 => by omega
  | fuel + 1, cls, exp, c, h1, h2 => by
    simp only [Decide.loop]
    split
    · rfl
    · rename_i x hx
      split
      · rfl
      · rw [if_neg (by simp)]
        have hexp : exp < cls.length := by
          rcases Nat.lt_or_ge exp cls.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx; cases hx
        split
        · rfl
        · exact ver017_loop_noStop E n bad fuel _ (exp + 1) _ (by omega) (by omega)

/-- **What a counted class is**, at the identity explorer: a stored state that violates the
property, expanded when the property is a quiescence property. -/
theorem ver017_violatesAt_iff {succ : S → List (L × S)} {o : Decide.Out S}
    {p : Decide.Prop' S L} {i : ℕ} :
    Decide.violatesAt (idExplorer succ) o p i = true ↔ EnumCounted succ o p i := by
  unfold EnumCounted
  cases p with
  | safety bad =>
    simp only [Decide.violatesAt]
    cases h : o.cls[i]? with
    | none => simp
    | some y => simp [EnumViol]
  | quiescence bad reap =>
    simp only [Decide.violatesAt, Decide.quiescentAt]
    cases h : o.cls[i]? with
    | none => simp
    | some y =>
      simp only [EnumViol, idExplorer, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Option.some.injEq, Decide.Prop'.quiescence.injEq, exists_eq_left']
      constructor
      · rintro ⟨⟨hi, hr⟩, hb⟩
        exact ⟨⟨hb, hr⟩, fun _ _ _ => hi⟩
      · rintro ⟨⟨hb, hr⟩, hi⟩
        exact ⟨⟨hi bad reap ⟨rfl, rfl⟩, hr⟩, hb⟩

/-- A counted class in a build that was not stopped makes the verdict `Violated`. -/
theorem ver017_verdict_hit {E : Explorer S K L} {o : Decide.Out S} {p : Decide.Prop' S L}
    (hs : o.stopped = false) {j : ℕ} (hj : j < o.cls.length)
    (hv : Decide.violatesAt E o p j = true) : ∃ i, Decide.verdict E o p = .violated i := by
  unfold Decide.verdict
  rw [if_neg (by simp [hs])]
  cases h : (List.range o.cls.length).find? (Decide.violatesAt E o p) with
  | none => exact absurd hv (List.find?_eq_none.mp h j (List.mem_range.mpr hj))
  | some i => exact ⟨i, rfl⟩

/-- A `Violated` names a counted class. -/
theorem ver017_verdict_violated {E : Explorer S K L} {o : Decide.Out S} {p : Decide.Prop' S L}
    {i : ℕ} (h : Decide.verdict E o p = .violated i) : Decide.violatesAt E o p i = true := by
  unfold Decide.verdict at h
  split at h
  · cases h
  · split at h
    · rename_i j hj
      cases h
      exact Decide.find?_violated hj
    · split at h <;> cases h

/-- **A `Violated` names the first counted class** in the order the build stored them. -/
theorem ver017_verdict_first {E : Explorer S K L} {o : Decide.Out S} {p : Decide.Prop' S L}
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

end Facts

/-! ### The enumeration build is breadth-first -/

section Bfs

variable {S L : Type} [DecidableEq S]

/-- An edge of a list of stored classes at the identity explorer: a successor of class `a` is
stored as class `j`. -/
def ver017_EdgeAt (succ : S → List (L × S)) (cls : List S) (a j : ℕ) : Prop :=
  ∃ x l y, cls[a]? = some x ∧ (l, y) ∈ succ x ∧ keyIdx (idExplorer succ) cls y = some j

/-- The loop invariant of the breadth-first argument. -/
structure ver017_BInv (succ : S → List (L × S)) (cls : List S) (exp : ℕ) : Prop where
  /-- No state is stored twice. -/
  inj : KeysInj (idExplorer succ) cls
  /-- At most every stored class is expanded. -/
  exp_le : exp ≤ cls.length
  /-- Every successor of an expanded class is stored. -/
  clo : ∀ a x, a < exp → cls[a]? = some x → ∀ ly ∈ succ x, ly.2 ∈ cls
  /-- Every later class has an edge from an expanded class. -/
  par : ∀ j, 0 < j → j < cls.length → ∃ a, a < exp ∧ ver017_EdgeAt succ cls a j
  /-- Breadth-first: a class stored before the target of an edge from an expanded class `a` has
  an edge from `a` or from an earlier class. -/
  bfs : ∀ a j' j, a < exp → ver017_EdgeAt succ cls a j' → 0 < j → j < j' →
    ∃ a', a' ≤ a ∧ ver017_EdgeAt succ cls a' j

/-- A stored state keeps its index when classes are appended. -/
theorem ver017_keyIdx_append {succ : S → List (L × S)} {cls t : List S}
    (hinj : KeysInj (idExplorer succ) (cls ++ t)) {y : S} {j : ℕ}
    (hk : keyIdx (idExplorer succ) cls y = some j) :
    keyIdx (idExplorer succ) (cls ++ t) y = some j := by
  obtain ⟨z, hz, hkz⟩ := keyIdx_some hk
  have hjl : j < cls.length := by
    rcases Nat.lt_or_ge j cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hz; cases hz
  exact keyIdx_of hinj (by rw [List.getElem?_append_left hjl]; exact hz) hkz

/-- An edge stays an edge when classes are appended. -/
theorem ver017_edge_mono {succ : S → List (L × S)} {cls t : List S}
    (hinj : KeysInj (idExplorer succ) (cls ++ t)) {a j : ℕ}
    (h : ver017_EdgeAt succ cls a j) : ver017_EdgeAt succ (cls ++ t) a j := by
  obtain ⟨x, l, y, hx, hly, hk⟩ := h
  have hal : a < cls.length := by
    rcases Nat.lt_or_ge a cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  exact ⟨x, l, y, by rw [List.getElem?_append_left hal]; exact hx, hly,
    ver017_keyIdx_append hinj hk⟩

/-- An edge out of a class whose successors were all stored was an edge before the append. -/
theorem ver017_edge_back {succ : S → List (L × S)} {cls t : List S}
    (hinj : KeysInj (idExplorer succ) (cls ++ t)) {a j : ℕ} {x : S} (hx : cls[a]? = some x)
    (hclo : ∀ ly ∈ succ x, ly.2 ∈ cls)
    (h : ver017_EdgeAt succ (cls ++ t) a j) : ver017_EdgeAt succ cls a j := by
  obtain ⟨x', l, y, hx', hly, hk⟩ := h
  have hal : a < cls.length := by
    rcases Nat.lt_or_ge a cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  rw [List.getElem?_append_left hal, hx] at hx'
  cases hx'
  obtain ⟨j0, hj0⟩ := keyIdx_isSome (E := idExplorer succ) (hclo (l, y) hly) rfl
  have h2 := ver017_keyIdx_append hinj hj0
  rw [hk] at h2
  cases h2
  exact ⟨x, l, y, hx, hly, hj0⟩

/-- A class appended by the expansion of `x` has an edge from it. -/
theorem ver017_edge_new {succ : S → List (L × S)} {cls t : List S}
    (hinj : KeysInj (idExplorer succ) (cls ++ t)) {e : ℕ} {x : S} (hx : cls[e]? = some x)
    (htm : ∀ z ∈ t, ∃ l, (l, z) ∈ succ x) {j : ℕ} (hj : cls.length ≤ j)
    (hjl : j < (cls ++ t).length) : ver017_EdgeAt succ (cls ++ t) e j := by
  have hel : e < cls.length := by
    rcases Nat.lt_or_ge e cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  have hz := List.getElem?_eq_getElem hjl
  have hzt : (cls ++ t)[j] ∈ t := by
    rw [List.getElem_append_right hj]; exact List.getElem_mem _
  obtain ⟨l, hl⟩ := htm _ hzt
  exact ⟨x, l, _, by rw [List.getElem?_append_left hel]; exact hx, hl, keyIdx_of hinj hz rfl⟩

/-- One expansion keeps the invariant. -/
theorem ver017_binv_step {succ : S → List (L × S)} {cls t : List S} {exp : ℕ} {x : S}
    (hinv : ver017_BInv succ cls exp) (hx : cls[exp]? = some x)
    (hinj : KeysInj (idExplorer succ) (cls ++ t)) (htm : ∀ z ∈ t, ∃ l, (l, z) ∈ succ x)
    (hcl : ∀ ly ∈ succ x, ly.2 ∈ cls ++ t) : ver017_BInv succ (cls ++ t) (exp + 1) := by
  have hel : exp < cls.length := by
    rcases Nat.lt_or_ge exp cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  refine ⟨hinj, by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
  · intro a y ha hy ly hly
    rcases Nat.lt_or_ge a exp with h | h
    · have hal : a < cls.length := by omega
      rw [List.getElem?_append_left hal] at hy
      exact List.mem_append_left _ (hinv.clo a y h hy ly hly)
    · have : a = exp := by omega
      subst this
      rw [List.getElem?_append_left hel, hx] at hy
      cases hy
      exact hcl ly hly
  · intro j hj0 hjl
    rcases Nat.lt_or_ge j cls.length with h | h
    · obtain ⟨a, ha, he⟩ := hinv.par j hj0 h
      exact ⟨a, by omega, ver017_edge_mono hinj he⟩
    · exact ⟨exp, by omega, ver017_edge_new hinj hx htm h hjl⟩
  · intro a j' j ha he hj0 hjj
    rcases Nat.lt_or_ge a exp with h | h
    · have hal : a < cls.length := by omega
      obtain ⟨xa, hxa⟩ : ∃ xa, cls[a]? = some xa := ⟨cls[a], List.getElem?_eq_getElem hal⟩
      have he' := ver017_edge_back hinj hxa (hinv.clo a xa h hxa) he
      obtain ⟨a', ha', he''⟩ := hinv.bfs a j' j h he' hj0 hjj
      exact ⟨a', ha', ver017_edge_mono hinj he''⟩
    · have : a = exp := by omega
      subst this
      have hj'l : j' < (cls ++ t).length := by
        obtain ⟨-, -, y, -, -, hk⟩ := he
        obtain ⟨z, hz, -⟩ := keyIdx_some hk
        rcases Nat.lt_or_ge j' (cls ++ t).length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hz; cases hz
      rcases Nat.lt_or_ge j cls.length with hj | hj
      · obtain ⟨a', ha', he'⟩ := hinv.par j hj0 hj
        exact ⟨a', by omega, ver017_edge_mono hinj he'⟩
      · exact ⟨a, le_rfl, ver017_edge_new hinj hx htm hj (by omega)⟩

/-- The loop keeps the invariant to its end, and never stops early. -/
theorem ver017_loop_binv (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool) :
    ∀ fuel cls exp c, ver017_BInv succ cls exp →
      ver017_BInv succ (Decide.loop (idExplorer succ) n cut bad false fuel cls exp c).cls
        (Decide.loop (idExplorer succ) n cut bad false fuel cls exp c).exp ∧
      (Decide.loop (idExplorer succ) n cut bad false fuel cls exp c).early = false
  | 0, cls, exp, c, hinv => ⟨hinv, rfl⟩
  | fuel + 1, cls, exp, c, hinv => by
    simp only [Decide.loop]
    split
    · exact ⟨hinv, rfl⟩
    · rename_i x hx
      split
      · exact ⟨hinv, rfl⟩
      · split
        · exact ⟨hinv, rfl⟩
        · obtain ⟨⟨t, ht, htm⟩, hcl⟩ :=
            Decide.expandB_spec (idExplorer succ) bad false ((idExplorer succ).succ c x) cls
          have hinj := expandB_inj (E := idExplorer succ) bad false
            ((idExplorer succ).succ c x) cls hinv.inj
          have hnf : (Decide.expandB (idExplorer succ) bad false cls
              ((idExplorer succ).succ c x)).2 = false :=
            ver017_expandB_noStop _ bad cls _
          split
          · rename_i cls' heq
            rw [heq] at hnf; cases hnf
          · rename_i cls' heq
            rw [heq] at ht hinj hcl
            simp only at ht hinj hcl
            subst ht
            apply ver017_loop_binv succ n cut bad fuel
            refine ver017_binv_step hinv hx hinj htm ?_
            intro ly hly
            obtain ⟨z, hz, hkz⟩ := hcl trivial ly hly
            change z = ly.2 at hkz
            rw [← hkz]; exact hz

/-- The enumeration build keeps the invariant, and never stops early. -/
theorem ver017_build_binv (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool)
    (fuel : ℕ) (x0 : S) :
    ver017_BInv succ (Decide.build (idExplorer succ) n cut bad false fuel x0).cls
        (Decide.build (idExplorer succ) n cut bad false fuel x0).exp ∧
      (Decide.build (idExplorer succ) n cut bad false fuel x0).early = false := by
  simp only [Decide.build, Bool.false_and, Bool.false_eq_true, if_false]
  apply ver017_loop_binv
  refine ⟨fun i j zi zj hi hj _ => ?_, by simp, fun a _ ha => absurd ha (Nat.not_lt_zero _),
    fun j hj0 hj => by simp at hj; omega, fun a _ _ ha => absurd ha (Nat.not_lt_zero _)⟩
  have hi' : i = 0 := by
    rcases Nat.lt_or_ge i 1 with h | h
    · omega
    · rw [List.getElem?_eq_none (by simpa using h)] at hi; cases hi
  have hj' : j = 0 := by
    rcases Nat.lt_or_ge j 1 with h | h
    · omega
    · rw [List.getElem?_eq_none (by simpa using h)] at hj; cases hj
  rw [hi', hj']

/-- **The enumeration build is breadth-first**: a class stored before the target of an edge
from class `a` has an edge from class `a` or from an earlier one. -/
theorem ver017_build_bfs (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool)
    (fuel : ℕ) (x0 : S) {a j' j : ℕ} {l : L}
    (he : (a, l, j') ∈
      edges (idExplorer succ) (Decide.build (idExplorer succ) n cut bad false fuel x0))
    (hj0 : 0 < j) (hjj : j < j') :
    ∃ a' l', a' ≤ a ∧
      (a', l', j) ∈ edges (idExplorer succ) (Decide.build (idExplorer succ) n cut bad false fuel x0) := by
  obtain ⟨hinv, hearly⟩ := ver017_build_binv succ n cut bad fuel x0
  have hop : opened (Decide.build (idExplorer succ) n cut bad false fuel x0) =
      (Decide.build (idExplorer succ) n cut bad false fuel x0).exp := by
    simp [opened, hearly]
  obtain ⟨ha, x, y, hx, hy, hk⟩ := (mem_edges (idExplorer succ)).mp he
  rw [hop] at ha
  obtain ⟨a', ha', x', l', y', hx', hy', hk'⟩ := hinv.bfs a j' j ha ⟨x, l, y, hx, hy, hk⟩ hj0 hjj
  exact ⟨a', l', ha', (mem_edges (idExplorer succ)).mpr ⟨by rw [hop]; omega, x', y', hx', hy', hk'⟩⟩

end Bfs

/-- **On a breadth-first edge list an earlier class is no farther**: a path from class `0` to
class `j'` gives a path, no longer, to every class `j ≤ j'`. -/
theorem ver017_walk_mono {L : Type} {es : List (ℕ × L × ℕ)}
    (hb : ∀ a l j' j, (a, l, j') ∈ es → 0 < j → j < j' → ∃ a' l', a' ≤ a ∧ (a', l', j) ∈ es) :
    ∀ {t : List L} {j' : ℕ}, Walk es 0 t j' →
      ∀ j, j ≤ j' → ∃ t', Walk es 0 t' j ∧ t'.length ≤ t.length := by
  intro t j' hw
  induction hw with
  | nil =>
    intro j hj
    have : j = 0 := by omega
    subst this
    exact ⟨[], .nil, le_rfl⟩
  | @snoc tr b c l hw he ih =>
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨[], .nil, Nat.zero_le _⟩
    · rcases Nat.lt_or_ge j c with hjc | hjc
      · obtain ⟨a', l', ha', he'⟩ := hb b l c j he hj0 hjc
        obtain ⟨t', hw', hl'⟩ := ih a' ha'
        exact ⟨t' ++ [l'], .snoc hw' he', by simp; omega⟩
      · have : j = c := by omega
        subst this
        exact ⟨tr ++ [l], .snoc hw he, le_rfl⟩

/-- **The witness of an earlier class is no longer than a path to a later one**, on the
enumeration build. -/
theorem ver017_trace_le {S L : Type} [DecidableEq S] (succ : S → List (L × S)) (n : ℕ)
    (cut : ℕ → Bool) (bad : S → Bool) (fuel : ℕ) (x0 : S) {i j : ℕ} {t : List L}
    (hi : i < (Decide.build (idExplorer succ) n cut bad false fuel x0).cls.length) (hij : i ≤ j)
    (hw : Walk (edges (idExplorer succ) (Decide.build (idExplorer succ) n cut bad false fuel x0))
      0 t j) :
    (trace (idExplorer succ) (Decide.build (idExplorer succ) n cut bad false fuel x0) i).length ≤
      t.length := by
  obtain ⟨t', hw', hl'⟩ := ver017_walk_mono
    (fun a l j' j he hj0 hjj => ver017_build_bfs succ n cut bad fuel x0 he hj0 hjj) hw i hij
  exact Nat.le_trans ((trace_spec (idExplorer_equivariant succ) hi).2.2 t' hw') hl'

/-- The reference route's enumeration build is `Novel.RouteB.Decide.build`. -/
theorem ver017_enumBuild_ref {S L : Type} [DecidableEq S] (succ : S → List (L × S)) (n : ℕ)
    (cut : ℕ → Bool) (fuel : ℕ) (x0 : S) :
    enumBuild refGraphRoute succ n cut fuel x0 =
      Decide.build (idExplorer succ) n cut (fun _ => false) false fuel x0 :=
  refGraphRoute_build (idExplorer succ) n cut (fun _ => false) false fuel x0

/-! ### The reference -/

/-- ✓ **The reference guard, graph route and dispatcher meet VER-017.** Example: on a chain of
three markings the reference build closes at a class budget of 4 and is cut off at 3; on the
closed graph a property is `Proven` exactly when no reachable marking violates it, and a
`Violated` names the first violating class the build stored, with a path to it no longer than
any path to another violating class; on a truncated graph a bad stored class is still
`Violated`, a frontier class never counts as dead, and nothing is `Proven`; without a total
budget the build is never stopped; a skipped or truncated route leaves the rest of the
pipeline's answer. -/
@[evidence holds VER_017]
theorem VER_017_reference {K S L : Type} [DecidableEq S] :
    VER_017 (K := K) refEnumGate (refGraphRoute (S := S) (K := S) (L := L)) refEnumDispatch := by
  refine ⟨fun X hm env n => ?_, fun succ n cut fuel x0 => ?_, fun _ _ => rfl,
    fun _ => ⟨rfl, fun _ => rfl⟩, fun _ => rfl, fun _ => rfl⟩
  · simp only [refEnumGate, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff,
      decide_eq_true_eq, and_assoc]
  · have hE := idExplorer_equivariant succ
    have hkey : ∀ (bad : S → Bool) (a b : S), (idExplorer succ).key a = (idExplorer succ).key b →
        bad a = bad b := fun bad a b h => by
      change a = b at h
      rw [h]
    dsimp only
    rw [ver017_enumBuild_ref]
    change
      (_ → _ → _) ∧ (_ → _) ∧ (_ ∧ _) ∧
      (_ → ∀ p, (Decide.verdict (idExplorer succ) _ p = _ ↔ _)) ∧
      (_ → ∀ p, Decide.verdict (idExplorer succ) _ p ≠ _) ∧
      (∀ p i, Decide.verdict (idExplorer succ) _ p = _ → ∃ y, _ ∧ _ ∧ _ ∧
        ERun _ x0 (trace (idExplorer succ) _ i) y ∧ Walk _ 0 (trace (idExplorer succ) _ i) i ∧
        (∀ j t, _ → _ → (trace (idExplorer succ) _ i).length ≤ _)) ∧
      (∀ p, Decide.verdict (idExplorer succ) _ p = _ → _) ∧
      (_ → ∀ p, Decide.verdict (idExplorer succ) _ p = _) ∧
      (_ → ∀ p, _ → ∃ i, Decide.verdict (idExplorer succ) _ p = _)
    refine ⟨fun hc hf => ?_, fun hs => build_closed_iff _ hs (ver017_build_noEarly _ _ _ _ _ _),
      ⟨(build_par _ _ _ _ _ _).1, fun y hy => Decide.build_reach _ hy⟩, fun hc p => ?_,
      fun hc p => ?_, fun p i hv => ?_, fun p hp => Decide.truncated_never_proven _ _ _ hp,
      fun hs p => ?_, fun hs p hj => ?_⟩
    · -- no stop without the oracle
      have : cut = fun _ => false := funext hc
      subst this
      simp only [Decide.build, Bool.false_and, Bool.false_eq_true, if_false]
      exact ver017_loop_noStop _ n _ fuel _ 0 _ (Nat.zero_le _) (by omega)
    · -- closed: Proven exactly when no reachable state violates
      constructor
      · intro hp y hy hv
        cases p with
        | safety bad =>
          have := Decide.complete_proven_safety hE (hkey bad) hp y hy
          rw [show bad y = true from hv] at this
          cases this
        | quiescence bad reap =>
          have := Decide.complete_proven_quiescence hE (hkey bad) hp y hy
            ⟨0, Nat.le_refl _, hv.2⟩
          rw [hv.1] at this
          cases this
      · intro hno
        have hs := (build_flags _ hc).1
        unfold Decide.verdict
        rw [if_neg (by simp [hs])]
        rw [List.find?_eq_none.mpr ?_]
        · simp [hc]
        · intro i _ hv
          obtain ⟨y, hy, hvy, -⟩ := ver017_violatesAt_iff.mp hv
          exact hno y (Decide.build_reach _ (List.mem_of_getElem? hy)) hvy
    · -- closed: never Unknown
      have hs := (build_flags _ hc).1
      unfold Decide.verdict
      rw [if_neg (by simp [hs])]
      split
      · simp
      · simp [hc]
    · -- a Violated: a counted class, a real run, a path no longer than any to a counted class
      obtain ⟨y, hy, hvy, hexp⟩ := ver017_violatesAt_iff.mp (ver017_verdict_violated hv)
      have hi : i < (Decide.build (idExplorer succ) n cut (fun _ => false) false fuel x0).cls.length := by
        rcases Nat.lt_or_ge i
          (Decide.build (idExplorer succ) n cut (fun _ => false) false fuel x0).cls.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hy; cases hy
      obtain ⟨s, hrun, hks⟩ := trace_erun hE hy
      change s = y at hks
      subst hks
      obtain ⟨hw, -, -⟩ := trace_spec hE hi
      refine ⟨s, hy, hvy, hexp, hrun, hw, fun j t hj hwt => ?_⟩
      have hij : i ≤ j := by
        rcases Nat.lt_or_ge j i with h | h
        · have h1 := ver017_verdict_first hv j h
          rw [ver017_violatesAt_iff.mpr hj] at h1
          cases h1
        · exact h
      exact ver017_trace_le succ n cut _ fuel x0 hi hij hwt
    · -- a stopped build reads nothing
      unfold Decide.verdict
      rw [if_pos hs]
    · -- a counted class makes the verdict Violated
      obtain ⟨j, hj⟩ := hj
      have hj' := hj
      obtain ⟨y, hy, -⟩ := hj'
      have hjl : j < (Decide.build (idExplorer succ) n cut (fun _ => false) false fuel x0).cls.length := by
        rcases Nat.lt_or_ge j
          (Decide.build (idExplorer succ) n cut (fun _ => false) false fuel x0).cls.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hy; cases hy
      exact ver017_verdict_hit hs hjl (ver017_violatesAt_iff.mpr hj)

/-! ### What the statement gives -/

/-- **A `Violated` of the route is a firing sequence** of the untimed net, from the statement
alone: on a reference net the successor function is `Reference.succ` (every enabled transition,
every way its firing can end), so the witness the route reports is a run from the initial marking
to the marking of a class that violates the property. -/
@[evidence cites "VER-017" "A `violated` is a real firing sequence"]
theorem VER_017_firing_sequence {K P : Type} [LinearOrder P] {A : EnumGateFn K}
    {G : GraphRoute (Reference.Marking P) (Reference.Marking P) String}
    {D : EnumDispatchFn String} (h : VER_017 A G D)
    (net : Reference.Net P) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) {m0 : Reference.Marking P}
    (hc : Reference.Canon m0) {p : Decide.Prop' (Reference.Marking P) String} {i : ℕ}
    (hv : G.verdict (enumE net) (enumBuild G (Reference.succ net) n cut fuel m0) p = .violated i) :
    ∃ y, Reference.Canon y ∧ EnumViol (Reference.succ net) p y ∧
      Reference.Run net (G.trace (enumE net) (enumBuild G (Reference.succ net) n cut fuel m0) i)
        (Reference.get m0) (Reference.get y) := by
  obtain ⟨y, -, hvy, -, hrun, -⟩ := (h.2.1 (Reference.succ net) n cut fuel m0).2.2.2.2.2.1 p i hv
  obtain ⟨hcy, hr⟩ := enum_erun hrun hc
  exact ⟨y, hcy, hvy, hr⟩

/-- **The route only adds verdicts**, from the statement alone: around the route, the verifier
answers what the rest of the pipeline answers, or the route's own verdict (a `Proven` only off a
closed graph, a `Violated` with a real run to a violating state), or `Unknown` when the total
budget or a cancellation stopped the build. -/
theorem VER_017_only_adds {K S L : Type} [DecidableEq S] {A : EnumGateFn K}
    {G : GraphRoute S S L} {P : EnumDispatchFn L} (h : VER_017 A G P) (enter : Bool)
    (succ : S → List (L × S)) (n : ℕ) (cut : ℕ → Bool) (fuel : ℕ) (x0 : S)
    (p : Decide.Prop' S L) (rest : EnumAnswer L) :
    P enter (enumOutcome G succ n cut fuel x0 p) rest = rest ∨
      ((enumBuild G succ n cut fuel x0).stopped = true ∧
        P enter (enumOutcome G succ n cut fuel x0 p) rest = .unknown) ∨
      ((enumBuild G succ n cut fuel x0).complete = true ∧
        P enter (enumOutcome G succ n cut fuel x0 p) rest = .proven) ∨
      (∃ tr y, P enter (enumOutcome G succ n cut fuel x0 p) rest = .violated tr ∧
        ERun (idExplorer succ) x0 tr y ∧ EnumViol succ p y) := by
  obtain ⟨-, hr, h9, h10, h11, h12⟩ := h
  cases enter with
  | false => exact Or.inl (h9 _ _)
  | true =>
    unfold enumOutcome
    by_cases hs : (enumBuild G succ n cut fuel x0).stopped = true
    · rw [if_pos hs]
      exact Or.inr (Or.inl ⟨hs, h12 rest⟩)
    · rw [if_neg hs]
      cases hv : G.verdict (idExplorer succ) (enumBuild G succ n cut fuel x0) p with
      | proven =>
        exact Or.inr (Or.inr (Or.inl
          ⟨((hr succ n cut fuel x0).2.2.2.2.2.2.1 p hv).1, (h10 rest).1⟩))
      | violated i =>
        obtain ⟨y, -, hvy, -, hrun, -⟩ := (hr succ n cut fuel x0).2.2.2.2.2.1 p i hv
        exact Or.inr (Or.inr (Or.inr ⟨_, y, (h10 rest).2 _, hrun, hvy⟩))
      | unknown => exact Or.inl (h11 rest)

/-- **A decided step ends the pipeline.** Example: when the enumeration step is entered and
decides, the run returns that decision at once: the steps entered are the earlier ones and the
enumeration, so flattening and the IC3/PDR query that follow it in the step list are never
entered and start no solver process. -/
@[evidence cites "VER-017" "shall not run the SMT pipeline"]
theorem VER_017_decided_ends {Q : Type} {O : Oracle} {stop : Stop} {o : Options} {q : Q}
    (s : GStep Q) (ss : List (GStep Q)) (t : Trail) (happ : s.applies o q = true)
    (hns : (pollStop stop t).1 = false) {v tr c} {t' : Trail}
    (hd : execProg O stop (s.run o q) ((pollStop stop t).2.enter s) = (.decided v tr c, t')) :
    runPipeline O stop o q (s :: ss) t = (some (s.route, .decided v tr c), t') ∧
      t'.entered = t.entered ++ [s.name] := by
  refine ⟨by simp only [runPipeline, happ, hns, hd, if_true, Bool.false_eq_true, if_false], ?_⟩
  have hf := (execProg_frame (O := O) (stop := stop) (s.run o q)
    ((pollStop stop t).2.enter s)).2.2
  rw [hd] at hf
  rw [hf]
  simp only [Trail.enter]
  rw [pollStop_frame.2.2.1]

/-! ### Examples -/

/-- `t0 : p0 → p1`, the first step of the test derivation's pipeline. -/
def ver017_t0 : Reference.Trans ℕ :=
  { core := { name := "t0", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `t1 : p1 → p2`, the second step. -/
def ver017_t1 : Reference.Trans ℕ :=
  { core := { name := "t1", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The pipeline `p0 → t0 → p1 → t1 → p2`. -/
def ver017_pipe : Reference.Net ℕ := { places := [0, 1, 2], transitions := [ver017_t0, ver017_t1] }

/-- The pipeline, untimed. -/
def ver017_pipeX : Reference.TimedNet ℕ :=
  { net := ver017_pipe, timing := fun _ => .immediate, tol := 0 }

/-- The pipeline's `delayed` variant. -/
def ver017_pipeD : Reference.TimedNet ℕ :=
  { net := ver017_pipe, timing := fun _ => .delayed 5, tol := 0 }

/-- One token on `p0`. -/
def ver017_m0 : Reference.Marking ℕ := [(0, 1)]

/-- `deadlockFree` with `p2` a sink, as a quiescence predicate: a dead marking is bad while
`p2` is empty. -/
def ver017_deadlockSink : Decide.Prop' (Reference.Marking ℕ) String :=
  .quiescence (fun m => decide (Reference.get m 2 = 0)) fun _ => false

/-- `deadlockFree` without a sink: every dead marking is bad. -/
def ver017_deadlock : Decide.Prop' (Reference.Marking ℕ) String :=
  .quiescence (fun _ => true) fun _ => false

/-- ✓ **The test derivation's pipeline**, on the reference net. Example: from one token on `p0`
the enumeration of `p0 → t0 → p1 → t1 → p2` finds three markings. At a class budget of 4 the
graph closes: `deadlockFree` with `p2` a sink is `Proven`, and without the sink it is `Violated`
with the firing sequence `t0, t1`, and the verifier answers that without the rest of the
pipeline. At a budget of 3 the same three markings are a truncated graph: a graph closes only
with fewer classes than the budget. The `delayed` variant is timed, so the route does not run on
it, nor at a budget of 0, and the verifier answers what the rest of the pipeline answers. -/
@[evidence cites "VER-017" "Test derivation"]
theorem VER_017_pipeline :
    (enumBuild refGraphRoute (Reference.succ ver017_pipe) 4 (fun _ => false) 20 ver017_m0).complete
        = true ∧
      (enumBuild refGraphRoute (Reference.succ ver017_pipe) 4 (fun _ => false) 20
        ver017_m0).cls.length = 3 ∧
      enumOutcome refGraphRoute (Reference.succ ver017_pipe) 4 (fun _ => false) 20 ver017_m0
        ver017_deadlockSink = .proven ∧
      enumOutcome refGraphRoute (Reference.succ ver017_pipe) 4 (fun _ => false) 20 ver017_m0
        ver017_deadlock = .violated ["t0", "t1"] ∧
      refEnumDispatch true (enumOutcome refGraphRoute (Reference.succ ver017_pipe) 4
        (fun _ => false) 20 ver017_m0 ver017_deadlock) .unknown = .violated ["t0", "t1"] ∧
      (enumBuild refGraphRoute (Reference.succ ver017_pipe) 3 (fun _ => false) 20
        ver017_m0).complete = false ∧
      refEnumGate ⟨ver017_pipeX, false, []⟩ 4 = true ∧
      refEnumGate ⟨ver017_pipeD, false, []⟩ 4 = false ∧
      refEnumGate ⟨ver017_pipeX, false, []⟩ 0 = false ∧
      refEnumDispatch (refEnumGate ⟨ver017_pipeD, false, []⟩ 4)
        (enumOutcome refGraphRoute (Reference.succ ver017_pipe) 4 (fun _ => false) 20 ver017_m0
          ver017_deadlock) .proven = .proven := by
  decide +kernel

/-- **AC5**: the route does not run on a net with a match transition, on a net with an
environment place still registered, on a timed net, or at a class budget of 0. -/
theorem VER_017_ac5 :
    refEnumGate ⟨ver017_pipeX, true, []⟩ 4 = false ∧
      refEnumGate ⟨ver017_pipeX, false, [0]⟩ 4 = false ∧
      refEnumGate ⟨ver017_pipeD, false, []⟩ 4 = false ∧
      refEnumGate ⟨ver017_pipeX, false, []⟩ 0 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- ✓ **AC11, the unbounded producer** `gen : G → G, A`, seen through the tokens on `A`.
Example: at a class budget of 50 the graph never closes; it is cut off with 50 classes. The
safety property "at most 2 tokens on `A`" is violated by a stored class, so the route answers
`Violated` with the firing sequence `gen, gen, gen`, and the verifier returns it. Deadlock
freedom has no expanded class without a successor (the frontier class does not count), so the
route hands over a truncation and the verifier answers what the rest of the pipeline answers. -/
@[evidence nonvacuous VER_017]
theorem VER_017_nonvacuous :
    (enumBuild refGraphRoute genSucc 50 (fun _ => false) 60 0).complete = false ∧
      (enumBuild refGraphRoute genSucc 50 (fun _ => false) 60 0).stopped = false ∧
      (enumBuild refGraphRoute genSucc 50 (fun _ => false) 60 0).cls.length = 50 ∧
      enumOutcome refGraphRoute genSucc 50 (fun _ => false) 60 0
        (.safety fun a => decide (2 < a)) = .violated ["gen", "gen", "gen"] ∧
      refEnumDispatch true (enumOutcome refGraphRoute genSucc 50 (fun _ => false) 60 0
        (.safety fun a => decide (2 < a))) .unknown = .violated ["gen", "gen", "gen"] ∧
      enumOutcome refGraphRoute genSucc 50 (fun _ => false) 60 0
        (.quiescence (fun _ => true) fun _ => false) = .truncated ∧
      refEnumDispatch true (enumOutcome refGraphRoute genSucc 50 (fun _ => false) 60 0
        (.quiescence (fun _ => true) fun _ => false)) .proven = .proven := by
  decide +kernel


/-! ### Wrong guards, routes and dispatchers, one per line -/

/-- The reference graph route on natural-number states with string labels. -/
abbrev ver017_ref : GraphRoute ℕ ℕ String := refGraphRoute

/-- A guard that also takes timed nets. -/
def ver017_timedGate : EnumGateFn ℕ := fun x n =>
  !x.hasMatch && x.envPlaces.isEmpty && decide (0 < n)

/-- ✗ A guard that runs the route on a timed net violates VER-017 (line 1): on the `delayed`
pipeline the graph would explore only the runs the timing allows, and its `Proven` would be the
weaker timed claim. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_timedGate : ¬ VER_017 ver017_timedGate ver017_ref refEnumDispatch := by
  intro h
  obtain ⟨-, -, hu, -⟩ := (h.1 ver017_pipeD false [] 4).mp (by decide)
  revert hu
  decide

/-- A route whose build stops at its first look at the stop oracle, raised or not (the stop poll
read as "stop" when no total budget is set). -/
def ver017_spuriousStop : GraphRoute ℕ ℕ String :=
  { refGraphRoute with
    build := fun E n _ bad stopAt fuel x0 => buildD E n (fun _ => true) bad stopAt fuel x0 }

/-- ✗ Stopping a build that no total budget and no cancellation stopped violates VER-017
(line 2). Example: with no total budget the chain `0 → 1 → 2` must close at a class budget of 4;
this route stops it, and every query on it would end in `Unknown`. Every other line holds of it,
because each is the reference's at a stop oracle that is always raised. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_spuriousStop :
    ¬ VER_017 refEnumGate ver017_spuriousStop refEnumDispatch (K := ℕ) := by
  intro h
  have := (h.2.1 chainSucc 4 (fun _ => false) 20 0).1 (fun _ => rfl) (by decide)
  revert this
  decide

/-- A route that closes a graph at a budget equal to its class count (the cap tested when a class
is stored, as the reference search of the conformance binary does). -/
def ver017_closeAtBudget : GraphRoute ℕ ℕ String :=
  { refGraphRoute with build := fun E n cut bad stopAt fuel x0 => buildD E (n + 1) cut bad stopAt fuel x0 }

/-- ✗ Closing a graph at a budget equal to its class count violates VER-017 (line 3): the chain
`0 → 1 → 2` has three classes, and at a budget of 3 it must be truncated. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_closeAtBudget :
    ¬ VER_017 refEnumGate ver017_closeAtBudget refEnumDispatch (K := ℕ) := by
  intro h
  have := ((h.2.1 chainSucc 3 (fun _ => false) 20 0).2.1 (by decide)).mp (by decide)
  revert this
  decide

/-- A route that builds from the class after the initial one. -/
def ver017_wrongStart : GraphRoute ℕ ℕ String :=
  { refGraphRoute with build := fun E n cut bad stopAt fuel x0 => buildD E n cut bad stopAt fuel (x0 + 1) }

/-- ✗ A graph whose first class is not the initial class violates VER-017 (line 4). Example: on
the chain `0 → 1 → 2` this route's graph starts at `1`, so it never looks at the initial
marking `0` itself. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_wrongStart :
    ¬ VER_017 refEnumGate ver017_wrongStart refEnumDispatch (K := ℕ) := by
  intro h
  have := (h.2.1 chainSucc 4 (fun _ => false) 20 0).2.2.1.1
  revert this
  decide

/-- A route whose closed graph always proves. -/
def ver017_alwaysProven : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p => if o.complete then .proven else Decide.verdict E o p }

/-- ✗ Proving on every closed graph violates VER-017 (line 5): on the closed chain `0 → 1 → 2`,
"never reach 2" is violated by a reachable state. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_alwaysProven :
    ¬ VER_017 refEnumGate ver017_alwaysProven refEnumDispatch (K := ℕ) := by
  intro h
  have h3 := ((h.2.1 chainSucc 4 (fun _ => false) 20 0).2.2.2.1 (by decide)
    (.safety fun a => decide (a = 2))).mp (by decide)
  have hr : Explorer.Reach (idExplorer chainSucc) 0 2 :=
    Explorer.Reach.step (c := 0) (l := "t") (s := 2)
      (Explorer.Reach.step (c := 0) (l := "t") (s := 1) Explorer.Reach.init (Nat.le_refl 0)
        (by decide))
      (Nat.le_refl 0) (by decide)
  exact h3 2 hr rfl

/-- A route that never proves. -/
def ver017_neverProven : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p =>
      match Decide.verdict E o p with
      | .proven => .unknown
      | v => v }

/-- ✗ Answering `Unknown` on a closed graph violates VER-017 (line 6): the closed chain decides
every property. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_neverProven :
    ¬ VER_017 refEnumGate ver017_neverProven refEnumDispatch (K := ℕ) := by
  intro h
  have := (h.2.1 chainSucc 4 (fun _ => false) 20 0).2.2.2.2.1 (by decide) (.safety fun _ => false)
  revert this
  decide

/-- A route that counts a frontier class as quiescent: it reads every stored class as expanded. -/
def ver017_frontierQuiescent : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p => Decide.verdict E { o with exp := o.cls.length } p }

/-- ✗ Counting a frontier class as quiescent violates VER-017 (line 7): the fork at a budget of 3
stores the dead class `2` without expanding it, and the route must not call it dead. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_frontierQuiescent :
    ¬ VER_017 refEnumGate ver017_frontierQuiescent refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨y, -, -, hexp, -⟩ := (h.2.1 forkSucc 3 (fun _ => false) 20 0).2.2.2.2.2.1
    (.quiescence (fun _ => true) fun _ => false) 2 (by decide)
  have := hexp _ _ rfl
  revert this
  decide

/-- A route that names the initial class whenever the property is violated. -/
def ver017_wrongClass : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p =>
      match Decide.verdict E o p with
      | .violated _ => .violated 0
      | v => v }

/-- ✗ Reporting a class that does not violate the property violates VER-017 (line 7). Example:
on the chain `0 → 1 → 2`, "never reach 2" is violated at class `2`, and this route names class
`0`, which does not violate it. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_wrongClass :
    ¬ VER_017 refEnumGate ver017_wrongClass refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨y, hy, hv, -⟩ := (h.2.1 chainSucc 4 (fun _ => false) 20 0).2.2.2.2.2.1
    (.safety fun a => decide (a = 2)) 0 (by decide)
  have h0 : (enumBuild ver017_wrongClass chainSucc 4 (fun _ => false) 20 0).cls[0]? = some 0 := by
    decide
  rw [h0] at hy
  cases hy
  have h1 : decide ((0 : ℕ) = 2) = true := hv
  revert h1
  decide

/-- An empty run is a run to its start. -/
theorem ver017_erun_nil {S K L : Type} {E : Explorer S K L} {a s : S} {t : List L}
    (h : ERun E a t s) (ht : t = []) : s = a := by
  cases h with
  | nil => rfl
  | snoc => simp at ht

/-- A route that reports an empty witness. -/
def ver017_emptyTrace : GraphRoute ℕ ℕ String :=
  { refGraphRoute with trace := fun _ _ _ => [] }

/-- ✗ A witness that is not a run to the reported class violates VER-017 (line 7). Example: on
the chain `0 → 1 → 2`, "never reach 2" is violated at class `2`, two steps away, and an empty
firing sequence stays at `0`. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_emptyTrace :
    ¬ VER_017 refEnumGate ver017_emptyTrace refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨y, hy, -, -, hrun, -⟩ := (h.2.1 chainSucc 4 (fun _ => false) 20 0).2.2.2.2.2.1
    (.safety fun a => decide (a = 2)) 2 (by decide)
  have := ver017_erun_nil hrun rfl
  subst this
  revert hy
  decide

/-- A diamond: from `0`, `a` gives `1` and `b` gives `2`; from `1`, `c` gives `2`. -/
def ver017_diaSucc : ℕ → List (String × ℕ)
  | 0 => [("a", 1), ("b", 2)]
  | 1 => [("c", 2)]
  | _ => []

/-- A route that reports a path to class `2` that is not the shortest. -/
def ver017_longTrace : GraphRoute ℕ ℕ String :=
  { refGraphRoute with trace := fun E o i => if i = 2 then ["a", "c"] else trace E o i }

/-- ✗ A witness longer than a path of the built graph violates VER-017 (line 7): in the diamond,
class `2` is one step `b` away, and `a, c` is longer. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_longTrace :
    ¬ VER_017 refEnumGate ver017_longTrace refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨y, -, -, -, -, -, hmin⟩ := (h.2.1 ver017_diaSucc 10 (fun _ => false) 20 0).2.2.2.2.2.1
    (.safety fun a => decide (a = 2)) 2 (by decide)
  have hw : Walk (edges (idExplorer ver017_diaSucc)
      (enumBuild ver017_longTrace ver017_diaSucc 10 (fun _ => false) 20 0)) 0 ["b"] 2 :=
    Walk.snoc (tr := []) Walk.nil (by decide)
  have := hmin 2 ["b"] ⟨2, by decide, rfl, fun _ _ h => by cases h⟩ hw
  revert this
  decide

/-- The verdict that names the last counted class in the order the build stored them. -/
def ver017_lastVerdict (E : Explorer ℕ ℕ String) (o : Decide.Out ℕ)
    (p : Decide.Prop' ℕ String) : Decide.Verdict :=
  match Decide.verdict E o p with
  | .violated _ =>
    match (List.range o.cls.length).reverse.find? (Decide.violatesAt E o p) with
    | some j => .violated j
    | none => .unknown
  | v => v

/-- A route that reports the last violating class it stored (a search from the end of the class
list instead of from its start). -/
def ver017_lastHit : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := ver017_lastVerdict }

/-- ✗ A witness longer than the path to another violating class violates VER-017 (line 7).
Example: the producer's graph at a class budget of 6 stores 0 to 5 tokens on `A`, and "at most
2 tokens on `A`" is violated from 3 tokens on. This route reports the class with 5 tokens and the
firing sequence `gen` five times, although `gen, gen, gen` reaches a violation. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_lastHit :
    ¬ VER_017 refEnumGate ver017_lastHit refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨y, -, -, -, -, -, hmin⟩ := (h.2.1 genSucc 6 (fun _ => false) 20 0).2.2.2.2.2.1
    (.safety fun a => decide (2 < a)) 5 (by decide)
  have w1 : Walk (edges (idExplorer genSucc)
      (enumBuild ver017_lastHit genSucc 6 (fun _ => false) 20 0)) 0 ["gen"] 1 :=
    Walk.snoc (tr := []) Walk.nil (by decide)
  have w2 : Walk (edges (idExplorer genSucc)
      (enumBuild ver017_lastHit genSucc 6 (fun _ => false) 20 0)) 0 ["gen", "gen"] 2 :=
    Walk.snoc (tr := ["gen"]) w1 (by decide)
  have w3 : Walk (edges (idExplorer genSucc)
      (enumBuild ver017_lastHit genSucc 6 (fun _ => false) 20 0)) 0 ["gen", "gen", "gen"] 3 :=
    Walk.snoc (tr := ["gen", "gen"]) w2 (by decide)
  have := hmin 3 _ ⟨3, by decide, rfl, fun _ _ h => by cases h⟩ w3
  revert this
  decide

/-- A route that proves off any graph: it reads every graph as closed. -/
def ver017_eagerProven : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p => Decide.verdict E { o with complete := true } p }

/-- ✗ A `Proven` from a prefix violates VER-017 (line 8): the producer's truncated graph at a
budget of 6 has no class violating `false`, and that proves nothing. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_eagerProven :
    ¬ VER_017 refEnumGate ver017_eagerProven refEnumDispatch (K := ℕ) := by
  intro h
  have := ((h.2.1 genSucc 6 (fun _ => false) 20 0).2.2.2.2.2.2.1 (.safety fun _ => false)
    (by decide)).1
  revert this
  decide

/-- A route that reads a stopped graph as a prefix. -/
def ver017_readStopped : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p => Decide.verdict E { o with stopped := false } p }

/-- ✗ Reading a graph whose build the total budget stopped violates VER-017 (line 9): with the
stop raised at once, the chain's build stores only class `0`, and nothing may be read off it. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_readStopped :
    ¬ VER_017 refEnumGate ver017_readStopped refEnumDispatch (K := ℕ) := by
  intro h
  have := (h.2.1 chainSucc 4 (fun _ => true) 20 0).2.2.2.2.2.2.2.1 (by decide)
    (.safety fun _ => true)
  revert this
  decide

/-- A route that counts only expanded classes for a safety property too. -/
def ver017_safetyExpanded : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p =>
      match p with
      | .safety bad => Decide.verdict E o (.quiescence bad fun _ => true)
      | q => Decide.verdict E o q }

/-- ✗ Ignoring a stored but unexpanded class for a safety property violates VER-017 (line 10):
the producer's graph at a budget of 4 stores three tokens on `A` on its frontier, and "at most 2
tokens on `A`" is violated there. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_safetyExpanded :
    ¬ VER_017 refEnumGate ver017_safetyExpanded refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨i, hi⟩ := (h.2.1 genSucc 4 (fun _ => false) 20 0).2.2.2.2.2.2.2.2 (by decide)
    (.safety fun a => decide (2 < a)) ⟨3, 3, by decide, rfl, fun _ _ h => by cases h⟩
  rw [show ver017_safetyExpanded.verdict (idExplorer genSucc)
      (enumBuild ver017_safetyExpanded genSucc 4 (fun _ => false) 20 0)
      (.safety fun a => decide (2 < a)) = .unknown by decide] at hi
  cases hi

/-- A graph with a dead branch: from `0`, `a` gives the dead class `1` and `b` gives `2`; from
there on, `g` adds one forever. -/
def ver017_deadSucc : ℕ → List (String × ℕ)
  | 0 => [("a", 1), ("b", 2)]
  | 1 => []
  | n => [("g", n + 1)]

/-- A route that reads a quiescence property only off a closed graph. -/
def ver017_noPrefixQuiescence : GraphRoute ℕ ℕ String :=
  { refGraphRoute with verdict := fun E o p =>
      match p with
      | .quiescence _ _ => if o.complete then Decide.verdict E o p else .unknown
      | q => Decide.verdict E o q }

/-- ✗ Ignoring an expanded dead class on a truncated graph violates VER-017 (line 10). Example:
at a class budget of 4 the graph with a dead branch is cut off after expanding `0`, `1` and `2`;
class `1` was expanded and has no successor, so deadlock freedom is violated in the prefix. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_noPrefixQuiescence :
    ¬ VER_017 refEnumGate ver017_noPrefixQuiescence refEnumDispatch (K := ℕ) := by
  intro h
  obtain ⟨i, hi⟩ := (h.2.1 ver017_deadSucc 4 (fun _ => false) 20 0).2.2.2.2.2.2.2.2 (by decide)
    (.quiescence (fun _ => true) fun _ => false)
    ⟨1, 1, by decide, ⟨rfl, fun _ h => by simp [ver017_deadSucc] at h⟩, fun _ _ _ => by decide⟩
  rw [show ver017_noPrefixQuiescence.verdict (idExplorer ver017_deadSucc)
      (enumBuild ver017_noPrefixQuiescence ver017_deadSucc 4 (fun _ => false) 20 0)
      (.quiescence (fun _ => true) fun _ => false) = .unknown by decide] at hi
  cases hi

/-- A dispatcher that runs the route although the guard said no. -/
def ver017_ignoreGate : EnumDispatchFn String := fun _ out rest => refEnumDispatch true out rest

/-- ✗ Answering from the route when it does not apply violates VER-017 (line 11). -/
@[evidence forbids VER_017]
theorem VER_017_forbids_ignoreGate :
    ¬ VER_017 refEnumGate ver017_ref ver017_ignoreGate (K := ℕ) := by
  intro h
  have := h.2.2.1 .proven .unknown
  revert this
  decide

/-- A dispatcher that drops the route's `Proven` and asks the rest of the pipeline. -/
def ver017_dropProven : EnumDispatchFn String := fun enter out rest =>
  match enter, out with
  | true, .proven => rest
  | _, _ => refEnumDispatch enter out rest

/-- ✗ Not returning the route's verdict violates VER-017 (line 12). -/
@[evidence forbids VER_017]
theorem VER_017_forbids_dropProven :
    ¬ VER_017 refEnumGate ver017_ref ver017_dropProven (K := ℕ) := by
  intro h
  have := (h.2.2.2.1 .unknown).1
  revert this
  decide

/-- A dispatcher that ends with `Unknown` on a truncation instead of falling through. -/
def ver017_unknownOnTruncation : EnumDispatchFn String := fun enter out rest =>
  match enter, out with
  | true, .truncated => .unknown
  | _, _ => refEnumDispatch enter out rest

/-- ✗ Turning a truncation into `Unknown` violates VER-017 (line 13): a query the rest of the
pipeline proves would become `Unknown`. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_unknownOnTruncation :
    ¬ VER_017 refEnumGate ver017_ref ver017_unknownOnTruncation (K := ℕ) := by
  intro h
  have := h.2.2.2.2.1 .proven
  revert this
  decide

/-- A dispatcher that falls through after a stop. -/
def ver017_fallAfterStop : EnumDispatchFn String := fun enter out rest =>
  match enter, out with
  | true, .stopped => rest
  | _, _ => refEnumDispatch enter out rest

/-- ✗ Running the rest of the pipeline after the total budget stopped the build violates VER-017
(line 14): the call ends with `Unknown`. -/
@[evidence forbids VER_017]
theorem VER_017_forbids_fallAfterStop :
    ¬ VER_017 refEnumGate ver017_ref ver017_fallAfterStop (K := ℕ) := by
  intro h
  have := h.2.2.2.2.2 .proven
  revert this
  decide

/-! ## VER-017 (B): the state-space cache -/

/-- **One query on one cache entry**: from the entry, the query's class budget and what a build at
that budget returns (`none`: the build failed; read only when the query builds), the answer
(`none` when the build failed) and the entry afterwards. The shape of `cacheLookup`. -/
abbrev CacheLookupFn (S : Type) : Type :=
  Slot S → ℕ → Option (Decide.Out S) → Option (Use S) × Slot S

/-- **One query on a keyed cache**: the shape of `cacheQuery` at the key of [VER-017] (net,
in-flight split, initial marking, reduced or full graph). -/
abbrev CacheQueryFn (N M S : Type) : Type :=
  Cache (CacheKey N M) S → CacheKey N M → ℕ → Option (Decide.Out S) →
    Option (Use S) × Cache (CacheKey N M) S

/-- **How a query reads its answer**: the verdict off a graph it built, reused or declined. The
shape of `useVerdict` at the identity explorer. -/
abbrev CacheReadFn (S L : Type) : Type := Explorer S S L → Use S → Decide.Prop' S L → Decide.Verdict

/-- **The query builds** at its budget: the entry is empty, or holds a truncation remembered at a
smaller budget. -/
def CacheBuilds {S : Type} : Slot S → ℕ → Prop
  | .empty, _ => True
  | .closed _, _ => False
  | .truncated B _, b => B < b

requirement VER_017_cache
  id "VER-017"
  title "Bounded State-Space Enumeration Route: State-Space Cache"
  kind B
  scope "the SMT verifier with a state-space cache, all implementations (SHOULD; the shall sentences bind an implementation that offers the cache)"
  source verbatim "spec/07-verification.md"
  covers VER_017.s13, VER_017.s14, VER_017.s15, VER_017.s16, VER_017.s17, VER_017.s18
  reading "For every lookup Lk, keyed query Q and reading R: a closed entry o at budget b answers reused o when o holds fewer than b classes and declined o otherwise, and stays as it was, whatever the build would return;"
          "a truncation remembered at B answers declined, and stays, at every budget b of B or less;"
          "when the query builds (the entry is empty, or a truncation at B below b) and the build returns o, the answer is built o and the entry becomes closed o if o closed, stays as it was if o was stopped, and becomes the truncation of o at b otherwise;"
          "when the query builds and the build fails, the answer is none and the entry stays as it was;"
          "R reads a built or reused graph o with the route's verdict on o, and a declined graph o with the verdict on o marked not closed;"
          "on a keyed cache c, a query at key k answers what the lookup of c k answers, leaves at k what that lookup leaves, and leaves every other key's entry as it was."
  assumes "The model is the triple (Lk, Q, R) of CacheLookupFn, CacheQueryFn and CacheReadFn, with witnesses cacheLookup, cacheQuery and useVerdict (Spec/Verifier/Graph.lean). An entry is a Slot: empty, a closed graph, or a truncation kept with its budget and its explored prefix (the stored classes, from which the successors are re-read, and the expanded count). The build argument is what a build at the query's budget would return, none when it fails (a panic or an exception in the runtimes); a model that reads it only when it builds is what 'without building' means here. That a cached graph is a graph some build returned is cacheLookup_ok in Graph.lean, and that a reused graph is the uncached build at the query's budget is VER_017_cache_reuse below."
          "Line 5 fixes the reading R to the reference reading Decide.verdict, not to the route block's G: 'as the route reads it without the cache' holds through the reference, whose graph route reads with Decide.verdict (refGraphRoute), so the two blocks meet at the reference and not at an arbitrary G. Which key a query uses (its net, split, initial marking and whether the graph is reduced), and that the answer it gets is what the route's dispatcher receives, is wiring the model assumes and does not state."
          "The key is CacheKey: the net (or a structural fingerprint of it; Rust and Python key on the Debug rendering of the net every route reads, Java and TypeScript on the net instance), the transitions the in-flight split rewrote (a key without them is killed, VER_017_forbids_cacheNoSplit), the initial marking (with the order in which it lists its places where a witness shows it) and whether the graph is reduced (VER-024). That the fingerprint covers everything the graph reads, and never hits where the graphs differ, is the key's job, not the state machine's: here a key is any value with decidable equality, and two different keys never share an entry (line 6)."
          "Under Arrivals the graph is that of the closed net, which depends on the registered environment places and the mode as well as on the caller's net and marking: on the net tA: A -> OA, tB: B -> OB with an empty marking under Arrivals(1), PlaceBound(OA, 0) is Violated with A registered and Proven with B registered, so a key without the closure would hand one query the other's graph. The EARS sentence '*While* the mode is `Arrivals(k)` or `Arrivals(min, max)` of [VER-006] and environment places are registered, *when* a state-space cache is passed, the verifier *shall* either key each entry also by the closure (the registered environment places in registration order and the mode), or not use the cache for that query and say so in the report.' is again the key's job: CacheKey is abstract here, and a key that covers the closure is one more field of it. Rust and Python key the fingerprint of the closed net (smt_verifier.rs, state_space_cache.rs), which covers the closure; Java and TypeScript do not use the cache when Arrivals closed the net over registered environment places, and say so in the report with one line (SmtVerifier.java and smt-verifier.ts, the enumeration step); Arrivals(0) closes nothing there, and the cache is used. A key of the caller's net with the closed initial marking, whose arrival sources are new Place objects on every call, misses on every such query and adds an entry with no report line (the TypeScript behaviour RD-28 recorded); it returns no wrong verdict, since it never hits."
          "'The graph depends only on the net, the in-flight split, its initial marking and whether it is reduced; the property, the sinks and the conditional sinks only read it' is the key of line 6 with line 5: the property is an argument of R only. The measurement paragraph is not a requirement."
          "Line 1 is the closed bullet: a closed graph of C classes is reused above C and answered as truncated at C or less, where it is read as a prefix (line 5), as Rust's StateSpaceLookup::Declined does for a closed graph (state_space_cache.rs, smt_verifier.rs enumerate). Reusing a closed graph at a budget of C is killed (VER_017_forbids_reuseAtBudget)."
          "Lines 2 to 4 are the truncation and failure bullets; a cache that builds again at a budget a remembered truncation covers (VER_017_forbids_rebuildBelow), one that stores a stopped build as a truncation (VER_017_forbids_storeStopped) and one that empties the entry on a failed build (VER_017_forbids_failClears) are killed. 'The failure reaches the query that ran the build' is the answer none of line 4; how it reaches the caller (an exception, a panic) is per language."
          "Line 5 is 'The verdict, the witness and the route are the same with and without the cache, with two exceptions' (ruling D92 (a)): a graph the query built or reused is read as the route reads it (VER_017_cache_reuse: a reused closed graph is the build at the query's budget, so verdict and witness match the uncached query), and a declined graph is read as a prefix, never Proven (VER_017_cache_declined_not_proven), where it can find a violation an uncached query at the smaller budget would not reach. A reading that takes a declined closed graph as closed is killed (VER_017_forbids_declinedClosed). 'The report says when a cached graph, or a cached truncation, was used' is report text, kind Q."
          "The concurrency bullets (one build per entry, waiting queries, a budget of B or less declining at once during a larger rebuild, waiters retrying after a failed build) and 'the cache holds its graphs until the caller drops it or clears it' are not modelled: the model is the sequential state machine, kind Q (AC10, the runtimes' concurrency tests). Rust also answers Stopped to a query whose total budget runs out while it waits on another query's build; that is the route's stopped outcome (line 14 of the route block)."
          "AC7 (a later query with the same key at the same budget builds no graph and answers as without the cache; under Arrivals the key covers the closure, and the claim is for a query the cache serves) is lines 1, 2 and 5 with VER_017_cache_reuse (ruling D92 (a)), the Arrivals half being the key's, as above. AC8 (a cached truncation at B answers a budget of B or less from its prefix, a larger budget builds and replaces it; a cached closed graph of C classes answers a budget of C or less from the whole graph read as a prefix, without building and never Proven) is lines 1, 2, 3 and 5 with VER_017_cache_declined_not_proven. AC9 (a different marking, net or split never hits another entry; with and without assumeAtomicFiring on a net the split rewrites each query builds) is line 6 (VER_017_cache_nonvacuous checks two keys that differ only in the split). AC10 (parallel queries build once) is concurrency, kind Q."
  signoff "2026-11-13 05b8497a4705c1b5 ai"
  statement : ∀ {S L N M : Type} [DecidableEq N] [DecidableEq M],
      CacheLookupFn S → CacheQueryFn N M S → CacheReadFn S L → Prop :=
    fun {S L N M} [DecidableEq N] [DecidableEq M] Lk Q R =>
      (∀ (o : Decide.Out S) (b : ℕ) (build : Option (Decide.Out S)),
        Lk (.closed o) b build =
          (some (if o.cls.length < b then .reused o else .declined o), .closed o)) ∧
      (∀ (B : ℕ) (o : Decide.Out S) (b : ℕ) (build : Option (Decide.Out S)), b ≤ B →
        Lk (.truncated B o) b build = (some (.declined o), .truncated B o)) ∧
      (∀ (slot : Slot S) (b : ℕ) (o : Decide.Out S), CacheBuilds slot b →
        Lk slot b (some o) = (some (.built o),
          if o.complete then .closed o else if o.stopped then slot else .truncated b o)) ∧
      (∀ (slot : Slot S) (b : ℕ), CacheBuilds slot b → Lk slot b none = (none, slot)) ∧
      (∀ (E : Explorer S S L) (o : Decide.Out S) (p : Decide.Prop' S L),
        R E (.built o) p = Decide.verdict E o p ∧ R E (.reused o) p = Decide.verdict E o p ∧
        R E (.declined o) p = Decide.verdict E { o with complete := false } p) ∧
      (∀ (c : Cache (CacheKey N M) S) (k : CacheKey N M) (b : ℕ) (build : Option (Decide.Out S)),
        (Q c k b build).1 = (Lk (c k) b build).1 ∧ (Q c k b build).2 k = (Lk (c k) b build).2 ∧
        ∀ k', k' ≠ k → (Q c k b build).2 k' = c k')

/- The pinned readable form of VER-017's cache block: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.VER_017_cache : {S L N M : Type} →
  [DecidableEq N] → [DecidableEq M] → CacheLookupFn S → CacheQueryFn N M S → CacheReadFn S L → Prop :=
fun {S L N M} [DecidableEq N] [DecidableEq M] Lk Q R =>
  (∀ (o : Decide.Out S) (b : ℕ) (build : Option (Decide.Out S)),
      Lk (Slot.closed o) b build = (some (if o.cls.length < b then Use.reused o else Use.declined o), Slot.closed o)) ∧
    (∀ (B : ℕ) (o : Decide.Out S) (b : ℕ) (build : Option (Decide.Out S)),
        b ≤ B → Lk (Slot.truncated B o) b build = (some (Use.declined o), Slot.truncated B o)) ∧
      (∀ (slot : Slot S) (b : ℕ) (o : Decide.Out S),
          CacheBuilds slot b →
            Lk slot b (some o) =
              (some (Use.built o),
                if o.complete = true then Slot.closed o else if o.stopped = true then slot else Slot.truncated b o)) ∧
        (∀ (slot : Slot S) (b : ℕ), CacheBuilds slot b → Lk slot b none = (none, slot)) ∧
          (∀ (E : Explorer S S L) (o : Decide.Out S) (p : Decide.Prop' S L),
              R E (Use.built o) p = Decide.verdict E o p ∧
                R E (Use.reused o) p = Decide.verdict E o p ∧
                  R E (Use.declined o) p =
                    Decide.verdict E
                      { cls := o.cls, exp := o.exp, complete := false, stopped := o.stopped, early := o.early } p) ∧
            ∀ (c : Cache (CacheKey N M) S) (k : CacheKey N M) (b : ℕ) (build : Option (Decide.Out S)),
              (Q c k b build).1 = (Lk (c k) b build).1 ∧
                (Q c k b build).2 k = (Lk (c k) b build).2 ∧ ∀ (k' : CacheKey N M), k' ≠ k → (Q c k b build).2 k' = c k'
-/
#guard_msgs in #print VER_017_cache

/-! ### The reference -/

/-- ✓ **The reference cache meets VER-017's cache block.** Example: a first query on the chain
`0 → 1 → 2` at a budget of 4 builds the closed graph of 3 classes and stores it; a query at a
budget of 10 reuses it without building; a query at a budget of 3 reads it as a prefix; a
truncation remembered at a budget of 2 answers a budget of 1 without building; a failed build
leaves the entry as it was; and a query never touches another key's entry. -/
@[evidence holds VER_017_cache]
theorem VER_017_cache_reference {S L N M : Type} [DecidableEq N] [DecidableEq M] :
    VER_017_cache (S := S) (L := L) (N := N) (M := M) cacheLookup cacheQuery
      (useVerdict (K := S)) := by
  refine ⟨fun o b build => rfl, fun B o b build hb => cacheLookup_truncated_le o hb build,
    fun slot b o hb => ?_, fun slot b hb => ?_, fun E o p => ⟨rfl, rfl, rfl⟩,
    fun c k b build => ⟨rfl, cacheQuery_self c k b build,
      fun k' hk => cacheQuery_frame c hk b build⟩⟩
  · cases slot with
    | empty => rfl
    | closed o' => exact hb.elim
    | truncated B o' =>
      change B < b at hb
      simp [cacheLookup, Nat.not_le.mpr hb, buildInto, store]
  · cases slot with
    | empty => rfl
    | closed o' => exact hb.elim
    | truncated B o' =>
      change B < b at hb
      simp [cacheLookup, Nat.not_le.mpr hb, buildInto]

/-! ### What the statement gives -/

/-- **Reusing a closed graph is answering without the cache**, from the statement alone: when an
entry holds the closed graph a build returned and a query's budget is above its class count, the
query reuses the graph the build at its own budget would return, with the same stop oracle and
fuel, so the verdict and the witness are the uncached ones. -/
@[evidence cites "VER-017" "AC7"]
theorem VER_017_cache_reuse {S K L N M : Type} [DecidableEq N] [DecidableEq M]
    {Lk : CacheLookupFn S} {Q : CacheQueryFn N M S} {R : CacheReadFn S L}
    (h : VER_017_cache Lk Q R) (E : Explorer S K L) {n b : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (hb : (Decide.build E n cut bad stopAt fuel x0).cls.length < b)
    (build : Option (Decide.Out S)) :
    (Lk (.closed (Decide.build E n cut bad stopAt fuel x0)) b build).1 =
      some (.reused (Decide.build E b cut bad stopAt fuel x0)) := by
  rw [h.1, build_budget_eq E hc hb]
  simp [hb]

/-- **A prefix reading never proves**, from the statement alone: a graph a query declined is read
as a graph that is not closed, so a cached truncation, or a closed graph at a budget of its class
count or less, never yields `Proven`. -/
theorem VER_017_cache_declined_not_proven {S L N M : Type} [DecidableEq N] [DecidableEq M]
    {Lk : CacheLookupFn S} {Q : CacheQueryFn N M S} {R : CacheReadFn S L}
    (h : VER_017_cache Lk Q R) (E : Explorer S S L) (o : Decide.Out S) (p : Decide.Prop' S L) :
    R E (.declined o) p ≠ .proven := by
  rw [(h.2.2.2.2.1 E o p).2.2]
  exact verdict_declined_ne_proven E o p

/-! ### Examples -/

/-- The key of the chain's net `0` and initial marking `0`, with the transitions `split` the
in-flight split rewrote, on the full graph. -/
def ver017_key (split : List String) : CacheKey ℕ ℕ := ⟨0, split, 0, false⟩

/-- ✓ **The cache on the chain `0 → 1 → 2`.** Example: a first query at a budget of 4 builds the
closed graph of 3 classes and stores it. A second query at a budget of 10 reuses it without
building and proves "never `false`"; a query at a budget of 3 reads the same graph as a prefix:
it still finds class `2` for "never reach 2", but proves nothing. A query whose key differs only
in the split (`t` rewritten) leaves the first key's entry alone, and the first query leaves the
second key's entry empty. -/
@[evidence nonvacuous VER_017_cache]
theorem VER_017_cache_nonvacuous :
    (cacheLookup .empty 4 (some (chainGraph 4))).2 = .closed (chainGraph 4) ∧
      (cacheLookup (.closed (chainGraph 4)) 10 none).1 = some (.reused (chainGraph 4)) ∧
      (cacheLookup (.closed (chainGraph 4)) 3 none).1 = some (.declined (chainGraph 4)) ∧
      useVerdict (idExplorer chainSucc) (.reused (chainGraph 4)) (.safety fun _ => false) =
        .proven ∧
      useVerdict (idExplorer chainSucc) (.declined (chainGraph 4)) (.safety fun _ => false) =
        .unknown ∧
      useVerdict (idExplorer chainSucc) (.declined (chainGraph 4))
        (.safety fun a => decide (a = 2)) = .violated 2 ∧
      (cacheQuery (fun _ => .empty) (ver017_key []) 4 (some (chainGraph 4))).2 (ver017_key ["t"]) =
        .empty := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide,
    cacheQuery_frame _ (by decide) _ _⟩
  · simp only [cacheLookup, buildInto, store]
    rw [if_pos (by decide)]
  · simp only [cacheLookup]
    rw [if_pos (by decide)]
  · simp only [cacheLookup]
    rw [if_neg (by decide)]

/-! ### Wrong caches, one per line -/

/-- A cache that reuses a closed graph at a budget equal to its class count. -/
def ver017_reuseAtBudget : CacheLookupFn ℕ := fun slot b build =>
  match slot with
  | .closed o => (some (if o.cls.length ≤ b then .reused o else .declined o), slot)
  | _ => cacheLookup slot b build

/-- ✗ Reusing a closed graph at a budget equal to its class count violates the cache block
(line 1): the chain's closed graph has 3 classes, and a query at a budget of 3 would have
truncated, so it reads the graph as a prefix. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_reuseAtBudget :
    ¬ VER_017_cache (L := String) ver017_reuseAtBudget (cacheQuery (κ := CacheKey ℕ ℕ))
      (useVerdict (K := ℕ)) := by
  intro h
  have := congrArg Prod.fst (h.1 (chainGraph 4) 3 none)
  simp only [ver017_reuseAtBudget] at this
  rw [if_pos (by decide), if_neg (by decide)] at this
  cases this

/-- A cache that builds again although a remembered truncation covers the query's budget. -/
def ver017_rebuildBelow : CacheLookupFn ℕ := fun slot b build =>
  match slot with
  | .truncated _ _ => buildInto slot b build
  | _ => cacheLookup slot b build

/-- ✗ Building at a budget a remembered truncation covers violates the cache block (line 2): a
truncation remembered at a budget of 2 answers a query at a budget of 1 from its prefix, without
building. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_rebuildBelow :
    ¬ VER_017_cache (L := String) ver017_rebuildBelow (cacheQuery (κ := CacheKey ℕ ℕ))
      (useVerdict (K := ℕ)) := by
  intro h
  have := congrArg Prod.fst (h.2.1 2 (chainGraph 2) 1 (some (chainGraph 1)) (by decide))
  simp only [ver017_rebuildBelow, buildInto, Option.some.injEq] at this
  cases this

/-- A cache that stores a stopped build as a truncation. -/
def ver017_storeStopped : CacheLookupFn ℕ := fun slot b build =>
  match slot, build with
  | .empty, some o => (some (.built o), if o.complete then .closed o else .truncated b o)
  | _, _ => cacheLookup slot b build

/-- The chain's build stopped at once by the total budget. -/
def ver017_stopped : Decide.Out ℕ :=
  buildD (idExplorer chainSucc) 4 (fun _ => true) (fun _ => false) false 20 0

/-- ✗ Storing a build the total budget stopped violates the cache block (line 3): a stopped
graph is not a truncation at the class budget, and the entry stays empty. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_storeStopped :
    ¬ VER_017_cache (L := String) ver017_storeStopped (cacheQuery (κ := CacheKey ℕ ℕ))
      (useVerdict (K := ℕ)) := by
  intro h
  have := congrArg Prod.snd (h.2.2.1 .empty 4 ver017_stopped trivial)
  simp only [ver017_storeStopped] at this
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)] at this
  cases this

/-- A cache that empties the entry when a build fails. -/
def ver017_failClears : CacheLookupFn ℕ := fun slot b build =>
  match build with
  | none => ((cacheLookup slot b none).1, if CacheBuilds.dec slot b then .empty else slot)
  | some o => cacheLookup slot b (some o)
where
  /-- Whether the query builds, as a Boolean. -/
  CacheBuilds.dec : Slot ℕ → ℕ → Bool
    | .empty, _ => true
    | .closed _, _ => false
    | .truncated B _, b => decide (B < b)

/-- ✗ Emptying the entry on a failed build violates the cache block (line 4): a truncation
remembered at a budget of 2 survives a failed build at a budget of 5. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_failClears :
    ¬ VER_017_cache (L := String) ver017_failClears (cacheQuery (κ := CacheKey ℕ ℕ))
      (useVerdict (K := ℕ)) := by
  intro h
  have := congrArg Prod.snd (h.2.2.2.1 (.truncated 2 (chainGraph 2)) 5 (show 2 < 5 by decide))
  simp only [ver017_failClears, ver017_failClears.CacheBuilds.dec] at this
  rw [if_pos (by decide)] at this
  cases this

/-- A reading that takes a declined graph as it is, closed or not. -/
def ver017_declinedClosed : CacheReadFn ℕ String := fun E u p => Decide.verdict E u.graph p

/-- ✗ Reading a declined closed graph as closed violates the cache block (line 5): at a budget of
3 the chain's closed graph of 3 classes is a prefix, and "never `false`" must not be proven from
it. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_declinedClosed :
    ¬ VER_017_cache cacheLookup (cacheQuery (κ := CacheKey ℕ ℕ)) ver017_declinedClosed := by
  intro h
  have := (h.2.2.2.2.1 (idExplorer chainSucc) (chainGraph 4) (.safety fun _ => false)).2.2
  revert this
  decide

/-- A keyed cache whose key leaves out the in-flight split. -/
def ver017_noSplitKey : CacheQueryFn ℕ ℕ ℕ := fun c k b build =>
  cacheQuery c { k with split := [] } b build

/-- ✗ A key without the in-flight split violates the cache block (line 6): a query on the split
net would read the closed graph of the atomic net, and that `Proven` can be wrong. -/
@[evidence forbids VER_017_cache]
theorem VER_017_forbids_cacheNoSplit :
    ¬ VER_017_cache (L := String) cacheLookup ver017_noSplitKey (useVerdict (K := ℕ)) := by
  intro h
  have := ((h.2.2.2.2.2 (fun k => if k.split = [] then .closed (chainGraph 4) else .empty)
    (ver017_key ["t"]) 10 none).1)
  simp only [ver017_noSplitKey, cacheQuery, ver017_key, cacheLookup, buildInto] at this
  rw [if_pos (by decide)] at this
  cases this

end Libpetri.Spec

