import Libpetri.Spec.Verifier.Scg
import Libpetri.Spec.Req.VER_011

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-010: State Class Graph Analysis (`spec/07-verification.md`)

The timed state class graph of Berthomieu and Diaz: a class is a marking with a firing domain
(a difference bound matrix over the clocks of the enabled transitions), and the graph lists,
for each class, one successor per transition and outcome that can fire. The model is
`Novel/TimedScg` (the successor `compute_successor`, the Time Petri net semantics `TStep`, run
coverage) with the class-key layer of `Spec/Verifier/Scg.lean` (names, the canonical clock
order, the class key). Three blocks share the ID:

* `VER_010` (B), over a step `G : ScgStep` (an initial class per net and initial marking, the
  labelled successors of a class): every class the graph reaches is well formed and lists its
  clocks in name order, and every state of a timed run lies in a class reachable from the
  initial class; a transition that can fire with an outcome from an urgent state a well-formed
  class holds gives the class a successor labelled with its name and the outcome's index,
  holding the state after the firing; and every successor has the marking the firing leaves,
  each input less its `consumptionCount(available)` of [IO-007], not its `requiredCount()`.
* `VER_010_persist` (F), over the survival test of the successor: a clock enabled before the
  firing is kept exactly when it is not the fired transition and is enabled after the firing and
  in the intermediate marking `M - Pre(t)` (ruling of 2026-09-10, [TIME-012]).
* `VER_010_key` (F), over the canonical order and the class identity: clocks in ascending name
  order by code point, and two classes shaped as the graph shapes them are one exactly when they
  have one marking and one zone. `ver010_key_graph` carries this to the classes the graph
  reaches when every bound is a whole number of milliseconds (ruling D58).

The witnesses are `refScg`, `refSurv` and `coByName` with `refSameKey`. Each block is checked
against the reference and against one wrong model per line: an initial class with no clocks,
one in enabling order, one with no timing, a step that keeps only the first outcome, a step
that removes `requiredCount()` tokens, the pre-6.0.0 survival test with no intermediate
marking, a key over the projections alone, a key that merges two markings, an order that keeps the enabling order and one that
drops every clock. `VER_010_joint` shows the three hold of one graph.

The exact half of the successor (every state a class holds is reached by a timed run, ruling
D67) and the bridge from the reference executor to `TStep` (the J7 bridge, premise 9 of
`Succ.lean`) are not here; the `assumes` lines say where they bear.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.TimedScg Libpetri.Novel.ForwardDeposit Libpetri.Spec.Verifier.Scg
open Libpetri.Novel.Dbm (Bound)

/-! ## The model -/

/-- **A state class graph step**: the initial class of a net from an initial marking, and the
labelled successors of a class, each label the fired transition's name and the index of the
outcome it took (`StateClassEdge`: `transition_name`, `branch_index`). -/
structure ScgStep where
  /-- The initial class of the net from the marking, if any. -/
  init : TNet → AMarking → Option Cls
  /-- The labelled successors of a class. -/
  succ : TNet → Cls → List (Label × Cls)

/-- The graph's edge relation: `C'` is a successor of `C` under some label. -/
def ScgStep.Edge (G : ScgStep) (N : TNet) (C C' : Cls) : Prop := ∃ l, (l, C') ∈ G.succ N C

/-- The state after transition `f` fires with outcome row `d` from state `s`: the marking
`fireAD`, and each clock kept when the clock rule `persists` keeps it, restarted at `0`
otherwise. -/
def firedState (N : TNet) (s : TState) (f : Nat) (d : Deposit) : TState :=
  ⟨fireAD s.m (trOf N f) d, fun i => if persists N s.m f d i then s.ν i else 0⟩

/-- The labelled successors of a class under the survival test `surv`: `succL` with
`succWith surv` in place of `succ`. -/
def ver010_succLWith (surv : Nat → AMarking → AMarking → Nat → Bool) (N : TNet)
    (co : List Nat → Option (List Nat)) (eps : ℚ) (C : Cls) : List (Label × Cls) :=
  (List.range C.cs.length).flatMap fun k =>
    (rowsOf N (C.cs.getD k 0)).zipIdx.filterMap fun p =>
      (succWith surv N co eps C k p.1).map fun C' => ((nameOf N (C.cs.getD k 0), p.2), C')

/-- **The reference step** (`state_class_graph.rs`: `initial_state_class`, and the loop of
`build_core` over `compute_successor`): clocks in canonical name order (`coByName`), the
emptiness check at the Rust `EPSILON = 1e-9` seconds, the successors with their labels
(`succL`). -/
def refScg : ScgStep where
  init N m0 := initCls N (coByName N) ver011_eps m0
  succ N C := succL N (coByName N) ver011_eps C

#spec_witness refScg

/-- **A survival test**: `surv N f a' mid c` says whether clock `c` keeps its time when `f`
fires, `a'` being the successor marking and `mid` the intermediate one. The successor of the
graph is `succWith (surv N)` (`compute_successor_gated`, `state_class_graph.rs`). -/
abbrev SurvTest : Type := TNet → Nat → AMarking → AMarking → Nat → Bool

/-- **The reference survival test** (`survives`, the rule since 6.0.0): not the fired
transition, enabled after the firing and in the intermediate marking. -/
def refSurv : SurvTest := survives

#spec_witness refSurv

/-- **A class as the graph shapes it**: its clocks are the transitions enabled in its marking,
listed once each in ascending name order, and its firing domain is canonical (closed, zero on
the diagonal, every clock with a finite lower bound). -/
def GoodCls (N : TNet) (C : Cls) : Prop :=
  (∀ c, c ∈ C.cs ↔ en N C.m c = true) ∧ ClocksOrdered N C.cs ∧ CanonZone (C.cs.length + 1) C.D

/-- **The reference class identity** (`StateClass::canonical_key`): two classes are one when
their class keys (marking, clock names in clock order, every bound of the firing domain) are
equal. -/
def refSameKey (N : TNet) (C C' : Cls) : Prop := classKey N C = classKey N C'

#spec_witness refSameKey

/-! ## VER-010 (B): the successor step and run coverage -/

requirement VER_010
  id "VER-010"
  title "State Class Graph Analysis"
  kind B
  scope "the timed state class graph builder (StateClassGraph.build), Java, TypeScript and Rust (MAY; the shall sentences bind an implementation that offers it)"
  source verbatim "spec/07-verification.md"
  quote "In them a timed run of the net starts at an initial marking with every clock at zero, on a net in which no transition's earliest firing time is below zero or above its latest, and follows the Time Petri net semantics: time may pass only as far as no enabled transition goes past its latest firing time, a transition fires no earlier than its earliest firing time and deposits its outputs at the instant it fires, and a clock is kept or restarted by the persistence rule below."
        "A class holds a state when the class's marking is the state's marking and its firing domain holds every combination of firing times the state allows the class's clocks."
        "A class is well formed when its clocks are the transitions enabled in its marking and its firing domain has the form letting time pass leaves: the closure of a matrix with a finite reference bound in which every clock's lower bound is zero."
        "*When* a timed run of the net reaches a state, the state class graph *shall* hold a class, reachable from its initial class, that holds the state."
        "Every class the state class graph reaches from its initial class *shall* be well formed and *shall* list its clocks once each, in ascending order of transition name compared by Unicode code point ([VER-013])."
        "*When* a transition can fire with one of its outcomes ([VER-001]) from a state in which no enabled transition is past its latest firing time, and a well-formed class holds that state, the state class graph *shall* give that class a successor, labelled with the transition's name and the outcome's index, that holds the state the firing leaves."
        "Every successor of a class *shall* be labelled with the name of a transition among the class's clocks and the index of one of that transition's outcomes, and *shall* have the marking that firing the transition with that outcome leaves: each input place less the `consumptionCount(available)` of [IO-007], so an `All` or `AtLeast` input empties its place, each reset place emptied, and the outcome's tokens added."
  reading "For every step G (an initial class per net and initial marking, and the labelled successors of a class) and every net N whose static intervals are well formed (0 ≤ eft ≤ lft for every transition):"
          "for every initial marking m0, G gives N an initial class C0; every class C reachable from C0 along G's successors is well formed (ClsWF: its clocks are the transitions enabled in its marking, and its zone is the closure of a matrix whose clock lower bounds are zero and whose reference entry is finite) and lists its clocks once each in ascending order of the code points of their names (ClocksOrdered); and every state s of every timed run of N from m0 (TReach from s0 m0, every clock at 0: delays that take no enabled transition past its latest bound, firings at or after the earliest bound, clocks kept by persists) lies in a class C reachable from C0 that holds s (InCls: C has s's marking and its zone holds every combination of the possible firing times of C's clocks in s);"
          "for every well-formed class C, every urgent state s that C holds (no enabled clock past its latest bound), and every transition f enabled in s whose clock has reached its earliest bound, with the outcome row d at index i: G gives C a successor labelled (name of f, i) that holds the state the firing leaves (firedState);"
          "every labelled successor (l, C') of every class C fires a clock f of C whose name is l.1 with the outcome row d at index l.2 of f, and C' has the marking fireAD C.m f d: each input less its consumption (all of an All or AtLeast place, requiredCount otherwise), each reset place emptied, then d deposited."
  assumes "The model is the timed state class graph of Novel/TimedScg on index nets: a net (TNet) lists transitions with their structural core, their outcome rows (branch_outcomes::outcomes, one constant deposit each) and their static interval [eft, lft] in seconds; a class (Cls) is a marking, a clock list and a positional firing domain. The step G is abstract (ScgStep). The witness is refScg: initial_state_class and compute_successor with the canonical order coByName and the emptiness check at EPSILON = 1e-9 seconds, its successors listed with their labels (succL, the order of state_class_graph.rs:186-247). It holds the block (VER_010_reference) by init_sound, Progress.graph_classes_ok, Scg.graph_ordered, timed_run_sound and successor_sound."
          "A timed run is a run of TStep, the Time Petri net semantics with strong urgency: time passes only while no enabled transition is past its latest bound, a transition fires at or after its earliest bound and deposits at that instant, and a clock is kept by persists, the rule of VER_010_persist. That TStep is what the executor does is premise 9 of TimedScg/Succ.lean, assumed: the on-time bridge from the reference executor's steps to TStep (J7 of this wave) is not proved, and until it is the block speaks of TStep. The executor behaviours outside TStep are the assumptions AC4 now lists (ruling D20, clash ver-d#8): a late executor that reaps or fires past a latest bound ([TIME-013], Retrodict.reaping_escapes_timed_graph), an action that takes time (Retrodict.action_duration_escapes), and the pass recheck of [EXEC-003] AC3, which belongs to atomic firings. The model's latest bound of an immediate or delayed transition is the finite MAX_DURATION_MS read as no bound (Timing.lean, assumed)."
          "Line 1 binds the shape of every class G reaches: well formed (ClsWF), so a class that holds a state holds every combination of firing times of the state's enabled transitions, which is the markdown's definition of holding, and ordered by name (ClocksOrdered). An initial class whose zone has no bound at all, no lower bound either, is not well formed and is killed (VER_010_forbids_untimedInit). Line 1 does not rule out the untimed reachability graph: a zone in which every clock's lower bound is zero and no clock has an upper bound is well formed (it is closed and is its own let-time-pass form), holds every state with its marking, and a graph that gives every class it reaches that zone, with the clocks and successors lines 1 to 3 ask, meets this block. Ruling out that widening is the exact half (ruling D67, see line 2), not this block. An initial class left in enabling order is killed (VER_010_forbids_initUnordered): a port that reorders only in compute_successor and forgets initial_state_class (state_class_graph.rs:361-381, the regression test canonical_order_applies_to_the_initial_class_too) is this mutant. The reference meets the line by Progress.graph_classes_ok and Scg.graph_ordered."
          "Line 2 ranges over well-formed classes and urgent states, the sentence's state in which no enabled transition is past its latest firing time. Without urgency the line would ask too much: a state with an overdue enabled clock is held vacuously by every class with its marking (that clock allows no firing time), and the firing rule TStep.fire does not ask for urgency. Every state of a timed run is urgent (Run.timed_run_sound), so line 2 loses no run. Run coverage in line 1 follows from line 2, the shape of line 1 and an initial class that holds the start state (ver010_covers_of). Line 2 is the sound half of AC2: the successor holds every state the firing rule allows. The exact half, that every state a successor holds is reached by a timed run, is a later block under ruling D67 (Lean proves the sound half only, TimedScg/Succ.lean), so AC2's 'correctly' is covered here for soundness only: the sound half does not forbid a successor that keeps an empty zone or widens a zone, and so adds markings no run reaches."
          "AC1, first sentence (the graph enumerates the reachable marking and zone pairs) is line 1, for soundness; a closed build at the class-key explorer of the model holds every state of every timed run (ver010_closed_covers, from Scg.scgGraph_covers). The Rust, Java and TypeScript builds do too, since their class keys tell markings apart (VER_010_key's assumes). A build that dedups classes by a marking string that does not escape place names, the behaviour RD-40 recorded, can give two classes with different markings one key and miss a marking a timed run reaches from a graph reported complete. AC1's canonical order is line 1 at the classes of G and VER_010_key's first line at the order; AC1's key over the full matrix is VER_010_key. An initial class that ignores the transitions enabled at the start loses every run that fires (VER_010_forbids_noClockInit). AC1's 'Two arrivals at the same marking and zone by different interleavings are one class' is not a line of any block: ScgStep stores no classes. It is evidence on the reference build, cited (ver010_key_graph, ver010_stored_one_class); the markdown states it as a remark, not a shall sentence."
          "AC2 (successor computation and consumption by consumptionCount(available)) is lines 2 and 3. Line 3's marking is fireAD, the model of consume_marking then produce_marking (state_class_graph.rs:669-700, input_consume_count deferring to input::consumption_count, IO-007): All and AtLeast inputs drain their place (Basic.consumeAllAt), other inputs lose requiredCount, reset places are emptied. A step that removes requiredCount() tokens from an AtLeast(2) input over 5 tokens leaves 3 and is killed (VER_010_forbids_requiredCount); any step that meets the block empties the place (VER_010_atLeast_drains, the second regression of the test derivation). The first regression (an All input followed by a transition inhibited on its place: the inhibited successor must be reachable) is VER_010_all_enables_inhibited: any step that meets the block reaches a class in which the inhibited transition is enabled."
          "AC3 (every outcome, each XOR branch and a timeout outcome that deposits differently, is a virtual transition of its own, [VER-001]) is the label of lines 2 and 3: one successor per outcome index of the fired transition, the index counting the outcomes in the order of branch_outcomes::outcomes, the order in which [VER-001] numbers the _b<i> virtual transitions. A step that keeps only the first outcome is killed (VER_010_forbids_firstOutcome). The rows are constant deposits (premise 3 of Succ.lean): a timeout that forwards an input, whose count produce_marking reads from the tokens the firing consumed (state_class_graph.rs:702-705), is outside the model, so AC3 is not covered for such a transition; an action deposits one token per named place of its branch ([IO-016] AC4)."
          "AC4 (the persistence rule of the intermediate marking) is VER_010_persist; its fresh-interval clause is covered for soundness only: in succWith the newly enabled clocks are those enabled in M' and not kept, and [VER-011]'s successor line holds each of them between its static bounds, held, not exact, so a graph that widens a newly enabled clock's interval meets VER-010 and VER-011. The exact half is VER-011's later D67 block. 'This is the executor's rule' is premise 9, assumed as above. The environment modes of AC4's last sentence are out of scope: the model has no environment places (premise 8 of Succ.lean), and [VER-006] states the modes. A transition outside the in-flight split fires atomically in the model; the split is AC5."
          "AC5 (the builder builds the net it is given and does not apply the in-flight split; a caller outside SmtVerifier must apply it; the documentation must say so) is not a line: the model's builder takes the net it is given (Scg.scgGraph), the caller's obligation to split first is kind A ([VER-004], Novel.InFlight.split_covers_executor), and the documentation sentence is kind Q."
          "The persistence sentence and the key sentences are lines of VER_010_persist and VER_010_key, over the survival test, the canonical order and the class identity; ScgStep has no survival test and no key, so those lines bind the graph by construction (ver010_succWith_of, VER_010_joint), not as lines of this block. A graph that restarts a clock the rule keeps, when the fresh interval contains the time the clock had left, meets this block: the restart only widens the zone, which is the exact half. The clock order alone is also bound here, at the classes of G (line 1)."
          "Further premises of Succ.lean: one input arc per place (premise 2, Basic.InputsDistinctPlaces), exact rational arithmetic (premise 4; floating point is not modelled), and well-formed timing (premise 6, TimingWF, the markdown's net in which no transition's earliest firing time is below zero or above its latest; every net built from the shipped Timing constructors meets it, Timing.timingWF_of_valid_timings, and Rust's TransitionBuilder::build validates it again). Unique transition names (premise 1) are the shared assumption of rulings D10 and D23, for the whole block and not only for the key block: Rust's state-class builder looks up the fired transition, and the transitions behind a clock, by name (state_class_graph.rs, compute_successor, which finds a transition by comparing names), so on a net with two transitions of one name its successors (lines 2 and 3) follow the first one's arcs; Java and TypeScript keep the transition objects (StateClassGraph.java, initialStateClass). Python exposes no state class graph, so the block binds Java, TypeScript and Rust. VER-010 is MAY; its shall sentences bind an implementation that offers the graph (ruling D22)."
  signoff "2026-11-13 e8ab985ddefc931d ai"
  statement : ScgStep → Prop :=
    fun G =>
      ∀ N : TNet, TimingWF N →
        (∀ m0 : AMarking, ∃ C0, G.init N m0 = some C0 ∧
          (∀ C, Relation.ReflTransGen (G.Edge N) C0 C → ClsWF N C ∧ ClocksOrdered N C.cs) ∧
          ∀ s, TReach N m0 s → ∃ C, Relation.ReflTransGen (G.Edge N) C0 C ∧ InCls N s C) ∧
        (∀ (C : Cls) (s : TState) (f i : Nat) (d : Deposit), ClsWF N C → InCls N s C →
          Urgent N s → en N s.m f = true → eftOf N f ≤ s.ν f → (rowsOf N f)[i]? = some d →
          ∃ C', ((nameOf N f, i), C') ∈ G.succ N C ∧ InCls N (firedState N s f d) C') ∧
        (∀ (C C' : Cls) (l : Label), (l, C') ∈ G.succ N C →
          ∃ f d, f ∈ C.cs ∧ nameOf N f = l.1 ∧ (rowsOf N f)[l.2]? = some d ∧
            C'.m = fireAD C.m (trOf N f) d)

/- The pinned readable form of VER-010 (the successor block): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_010 : ScgStep → Prop :=
fun G =>
  ∀ (N : TNet),
    TimingWF N →
      (∀ (m0 : AMarking),
          ∃ C0,
            G.init N m0 = some C0 ∧
              (∀ (C : Cls), Relation.ReflTransGen (G.Edge N) C0 C → ClsWF N C ∧ ClocksOrdered N C.cs) ∧
                ∀ (s : TState), TReach N m0 s → ∃ C, Relation.ReflTransGen (G.Edge N) C0 C ∧ InCls N s C) ∧
        (∀ (C : Cls) (s : TState) (f i : ℕ) (d : Deposit),
            ClsWF N C →
              InCls N s C →
                Urgent N s →
                  en N s.m f = true →
                    eftOf N f ≤ s.ν f →
                      (rowsOf N f)[i]? = some d →
                        ∃ C', ((nameOf N f, i), C') ∈ G.succ N C ∧ InCls N (firedState N s f d) C') ∧
          ∀ (C C' : Cls) (l : Label),
            (l, C') ∈ G.succ N C →
              ∃ f d, f ∈ C.cs ∧ nameOf N f = l.1 ∧ (rowsOf N f)[l.2]? = some d ∧ C'.m = fireAD C.m (trOf N f) d
-/
#guard_msgs in #print VER_010

/-! ## VER-010 (F): the persistence rule -/

requirement VER_010_persist
  id "VER-010"
  title "State Class Graph Analysis: clock persistence"
  kind F
  scope "the survival test of the timed state class graph successor (compute_successor), Java, TypeScript and Rust"
  source verbatim "spec/07-verification.md"
  quote "*When* a transition `t` fires from marking `M` into marking `M'`, the successor step of the state class graph *shall* keep the clock of a transition `t'` enabled in `M` exactly when `t'` is not `t` and is enabled both in `M'` and in the intermediate marking `M - Pre(t)`, which has the inputs of `t` consumed, its reset places drained and none of its outputs deposited."
  reading "For every net N, marking M, fired transition t, outcome row d and transition t' enabled in M, with M' = fireAD M t d (the successor marking) and Mid = inter M t (the intermediate marking: inputs consumed by consumptionCount, reset places drained, nothing deposited): the survival test keeps t' exactly when t' ≠ t, t' is enabled in M' and t' is enabled in Mid."
  assumes "The survival test is abstract (SurvTest): the successor of the graph is succWith (surv N), compute_successor_gated with both gates true (state_class_graph.rs:493-547), and the test is read only at the clocks of the class, the transitions enabled in its marking. The witness is refSurv = survives (since 6.0.0); it meets the line by its definition (persistence_rule). Any test that meets the line gives the reference successor on every class whose clocks are enabled in its marking (ver010_succWith_of), so VER_010 holds of the graph built with it. The line is stronger than the sentence in one way: the fired transition and the outcome row are arbitrary, not only an enabled transition and one of its rows."
          "The pre-6.0.0 rule (survivesOld, Rust 5.x and earlier: not the fired transition and enabled after, with no look at the intermediate marking) is killed on the refresh net of the test derivation (VER_010_persist_forbids_old: Retrodict.netRT, where Refresh takes and puts back the timer token that CloseSession waits on). Retrodict.old_rule_loses_run shows what the old rule cost: a timed run whose state no successor of the old graph holds (ver010_old_rule_loses_run)."
          "AC4's other sentences: 'Every other transition enabled in M' gets a fresh firing interval' is the shape of succWith (newly enabled = enabled in M' and not kept) with [VER-011]'s successor line; 'This is the executor's rule ([TIME-012])' is premise 9 of TimedScg/Succ.lean, assumed (see VER_010); the limits of the graph are VER_010's assumptions. The bullets of [TIME-012] in the graph are Run.fired_never_persists, inhibitor_never_restarts, reset_restarts and surplus_keeps, cited there."
          "The test derivation's three cases are VER_010_persist_nonvacuous: on the refresh net with one timer token the delayed transition restarts, with a second token it keeps its clock, and with a reset arc on the timer place it restarts."
  signoff "2026-11-13 9d3d1118dedb2015 ai"
  statement : SurvTest → Prop :=
    fun surv =>
      ∀ (N : TNet) (m : AMarking) (f : Nat) (d : Deposit) (c : Nat), en N m c = true →
        (surv N f (fireAD m (trOf N f) d) (inter m (trOf N f)) c = true ↔
          c ≠ f ∧ en N (fireAD m (trOf N f) d) c = true ∧ en N (inter m (trOf N f)) c = true)

/- The pinned readable form of VER-010 (the persistence block): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_010_persist : SurvTest → Prop :=
fun surv =>
  ∀ (N : TNet) (m : AMarking) (f : ℕ) (d : Deposit) (c : ℕ),
    en N m c = true →
      (surv N f (fireAD m (trOf N f) d) (inter m (trOf N f)) c = true ↔
        c ≠ f ∧ en N (fireAD m (trOf N f) d) c = true ∧ en N (inter m (trOf N f)) c = true)
-/
#guard_msgs in #print VER_010_persist

/-! ## VER-010 (F): the canonical order and the class key -/

requirement VER_010_key
  id "VER-010"
  title "State Class Graph Analysis: canonical class identity"
  kind F
  scope "the canonical clock order and the class key of the timed state class graph, Java, TypeScript and Rust"
  source verbatim "spec/07-verification.md"
  quote "The canonical order of the state class graph *shall* either keep a list of transitions or return a permutation of its positions, and *shall* leave every list it is given in ascending order of transition name, compared by Unicode code point ([VER-013])."
        "*If* the transition names of the net are unique, *then* the class key of the state class graph *shall* give two classes, each with the transitions enabled in its marking as clocks, once each in that order, and a canonical firing domain (closed, zero on the diagonal, every clock with a finite lower bound), the same key exactly when they have the same marking and their firing domains hold the same firing times."
  reading "For every canonical order co (from a net and a clock list to no reordering or an order of the positions) and every class identity same (from a net and two classes to whether they share a key):"
          "for every net N and every list l of transitions, co N either keeps l or returns a permutation of its positions (CoWF), and l reordered by co N is in ascending order of the code points of the transition names;"
          "for every net N whose transition names are unique and every two classes C, C' whose clocks are the transitions enabled in their marking, listed once each in name order, and whose firing domains are canonical (closed, zero on the diagonal, a finite reference row): same N C C' holds exactly when C and C' have the same marking and their firing domains hold the same valuations."
  assumes "The canonical order and the class identity are abstract. The witnesses are coByName (canonical_order, state_class_graph.rs:406-415: none when the names are already in order, otherwise the positions sorted by name with a stable sort, comparing code points as CodePointOrder in Java and compareCodePoints in TypeScript do) and refSameKey (equality of StateClass::canonical_key: the marking, the clock names in clock order and every bound of the firing domain, state_class.rs:59-61). They meet the block (VER_010_key_reference) by Scg.reorder_sorted and Scg.canon_unique, the new lemma that two canonical domains holding the same firing times agree on every bound. The model's key compares the index marking, which is injective, and so do the runtime keys: Rust's canonical_key and zone_key backslash-escape the separators \\ , : | # in place and clock names (marking_state.rs:149-166 push_key_name, dbm.rs:289), TypeScript's class key starts with MarkingState.key(), the JSON of the sorted [name, count] entries (marking-state.ts:76), and Java compares markings and zones by structure (StateClass.equals). A key that renders the marking as a string that does not escape place names, the behaviour RD-40 recorded, gives the markings {a:1, b:1} and {'a:1,b':1} one key, and line 2 fails there. VER_010_key_forbids_markingBlind kills a key that gives two markings one key."
          "Line 2 speaks of classes shaped as the graph shapes them (GoodCls). Every class the model's successor step builds (initCls and succ with any order that meets line 1) has that shape when the emptiness check is exact (Scg.ExactEps: every bound a whole number of milliseconds at the Rust EPSILON, ruling D58), so two classes of the graph are one exactly when they have the same marking and the same firing domain, whatever interleavings reached them (ver010_key_graph, for any order and identity that meet the block). The model's key compares exact rationals; the runtimes render each bound at three decimals of a second, which is exact on whole-millisecond bounds ([VER-011] line 8). A fractional TypeScript bound is outside both (VER_011_key_submillisecond)."
          "Unique names are a premise: with a repeated name the stable sort keeps two enabling orders apart (Scg.ex_order_dupNames). The canonical-domain premise needs the zero diagonal (Scg.ex_diag_needed). The model's explorer dedups by the index key, which is the class key on a net with unique names (Scg.idxKey_eq_iff_classKey), and a build stores one class per marking and zone (Scg.stored_one_class, ver010_stored_one_class). That a graph stores one class per key (AC1's 'Two arrivals ... are one class') is not a line: neither ScgStep nor the key block stores classes, so it is evidence on the reference build only (ver010_key_graph, ver010_stored_one_class, cited). The markdown says that a net with a repeated name ([CORE-021] allows one) falls outside the key sentence."
          "The key sentence is phrased about the class key, and the line is about the abstract identity same; the graph is tied to it by construction (VER_010_joint), and line 1 of VER_010 binds the clock order at the classes of the graph. A graph that dedups by another identity meets VER_010; the key sentence forbids it through the identity it uses."
          "Mutants: a key over the projections alone (the bounds of each clock against the reference clock, not the bounds between two clocks) merges the two classes ver010_C1 and ver010_C2, which differ in one difference bound (VER_010_key_forbids_projections); a key that leaves the marking out merges ver010_C1 and ver010_C1m, which have one zone and two markings (VER_010_key_forbids_markingBlind, the shape of the behaviour RD-40 recorded); an order that keeps the enabling order lists the clocks b, a, Z as they came (VER_010_key_forbids_enablingOrder); an order that returns no position at all leaves every list empty, and so sorted, but is no permutation (VER_010_key_forbids_dropAll). A key without the clock names is not killed: on good classes of a net with unique names the marking fixes the clock list, so the names add nothing to the identity."
          "AC1's measurement (the order-sensitive key inflated the class count 1.5 times on an untimed workflow net, one marking held by fourteen classes) is kind Q, and its remark that a projection-only key can lose a reachable marking is the reason for line 2, not a line."
  signoff "2026-11-13 a4639db8259032ea ai"
  statement : (TNet → List Nat → Option (List Nat)) → (TNet → Cls → Cls → Prop) → Prop :=
    fun co same =>
      (∀ N : TNet, CoWF (co N) ∧
        ∀ l : List Nat, (reorder (co N) l).Pairwise (fun a b => nameKey N a ≤ nameKey N b)) ∧
      (∀ N : TNet, NamesUnique N → ∀ C C' : Cls, GoodCls N C → GoodCls N C' →
        (same N C C' ↔ C.m = C'.m ∧
          ∀ θ, SatN (C.cs.length + 1) C.D θ ↔ SatN (C'.cs.length + 1) C'.D θ))

/- The pinned readable form of VER-010 (the key block): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_010_key : (TNet → List ℕ → Option (List ℕ)) → (TNet → Cls → Cls → Prop) → Prop :=
fun co same =>
  (∀ (N : TNet),
      CoWF (co N) ∧ ∀ (l : List ℕ), List.Pairwise (fun a b => nameKey N a ≤ nameKey N b) (reorder (co N) l)) ∧
    ∀ (N : TNet),
      NamesUnique N →
        ∀ (C C' : Cls),
          GoodCls N C →
            GoodCls N C' →
              (same N C C' ↔ C.m = C'.m ∧ ∀ (θ : ℕ → ℚ), SatN (C.cs.length + 1) C.D θ ↔ SatN (C'.cs.length + 1) C'.D θ)
-/
#guard_msgs in #print VER_010_key

/-! ## The references -/

theorem ver010_eps_nonneg : (0 : ℚ) ≤ ver011_eps := by norm_num [ver011_eps]

theorem refScg_edge_iff {N : TNet} {C C' : Cls} :
    refScg.Edge N C C' ↔ Edge N (coByName N) ver011_eps C C' := by
  unfold ScgStep.Edge Edge
  exact mem_succL

/-- The label and row of a labelled successor of `succL`. -/
theorem mem_succL_iff {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls}
    {l : Label} :
    (l, C') ∈ succL N co eps C ↔ ∃ k, k < C.cs.length ∧ ∃ d, (rowsOf N (C.cs.getD k 0))[l.2]? = some d ∧
      succ N co eps C k d = some C' ∧ l.1 = nameOf N (C.cs.getD k 0) := by
  obtain ⟨n, i⟩ := l
  simp only [succL, List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, p, hp, C'', hs, ⟨hn, hi⟩, rfl⟩
    refine ⟨k, hk, p.1, ?_, hs, hn.symm⟩
    rw [← hi]
    exact List.mem_zipIdx_iff_getElem?.mp hp
  · rintro ⟨k, hk, d, hd, hs, hn⟩
    exact ⟨k, hk, (d, i), List.mem_zipIdx_iff_getElem?.mpr hd, C', hs, ⟨hn.symm, rfl⟩, rfl⟩

/-- ✓ **The reference step meets VER-010.** Example: on the net `t : p0 → p1 xor p2` from one
token in `p0`, the initial class holds the start state, and the graph gives it two successors,
`("t", 0)` with the token in `p1` and `("t", 1)` with it in `p2`, each holding the state after
that firing (`ver010_ref_outcomes`). -/
@[evidence holds VER_010]
theorem VER_010_reference : VER_010 refScg := by
  intro N hT
  have hco := coByName_wf N
  have heps := ver010_eps_nonneg
  refine ⟨fun m0 => ?_, fun C s f i d hwf hin hu hen hready hd => ?_, fun C C' l h => ?_⟩
  · obtain ⟨C0, h0, -, -⟩ := init_sound hT hco heps m0
    refine ⟨C0, h0, fun C hC => ?_, fun s hs => ?_⟩
    · have hC' : Relation.ReflTransGen (Edge N (coByName N) ver011_eps) C0 C :=
        Relation.ReflTransGen.mono (fun a b h => refScg_edge_iff.mp h) C0 C hC
      exact ⟨(graph_classes_ok hT hco heps h0 hC').1, graph_ordered h0 hC'⟩
    obtain ⟨C, hreach, hin, -, -⟩ := timed_run_sound hT hco heps h0 hs
    exact ⟨C, Relation.ReflTransGen.mono (fun a b h => refScg_edge_iff.mpr h) C0 C hreach, hin⟩
  · have hfC : f ∈ C.cs := (hwf.mem f).mpr (hin.1 ▸ hen)
    obtain ⟨k, hk, hkf⟩ := List.getElem_of_mem hfC
    have hk' : C.cs[k]? = some f := by rw [List.getElem?_eq_getElem hk, hkf]
    obtain ⟨C', hs, hin', -, -⟩ := successor_sound hT hco heps hwf hin hu hen hready (d := d) hk'
    have hgd : C.cs.getD k 0 = f := by
      simp only [List.getD_eq_getElem?_getD, hk', Option.getD_some]
    refine ⟨C', ?_, hin'⟩
    exact mem_succL_iff.mpr ⟨k, hk, d, by rw [hgd]; exact hd, hs, by rw [hgd]⟩
  · obtain ⟨k, hk, d, hd, hs, hn⟩ := mem_succL_iff.mp h
    obtain ⟨f, hkf, hm⟩ := succWith_marking hs
    have hgd : C.cs.getD k 0 = f := by
      simp only [List.getD_eq_getElem?_getD, hkf, Option.getD_some]
    rw [hgd] at hd hn
    exact ⟨f, d, List.mem_of_getElem? hkf, hn.symm, hd, hm⟩

/-- ✓ **The reference survival test meets the persistence rule.** Example: when `Refresh` takes
the timer token and puts it back, `CloseSession` is enabled before and after, but not in the
intermediate marking, where the timer place is empty, so its clock restarts. -/
@[evidence holds VER_010_persist]
theorem VER_010_persist_reference : VER_010_persist refSurv := by
  intro N m f d c _
  simp only [refSurv, survives, Bool.and_eq_true, bne_iff_ne, ne_eq]
  tauto

/-- Two good classes with one marking have one clock list. -/
theorem ver010_cs_eq {N : TNet} (hN : NamesUnique N) {C C' : Cls} (hC : GoodCls N C)
    (hC' : GoodCls N C') (hm : C.m = C'.m) : C.cs = C'.cs := by
  obtain ⟨hmem, ⟨hn, hs⟩, -⟩ := hC
  obtain ⟨hmem', ⟨hn', hs'⟩, -⟩ := hC'
  have hp : C.cs.Perm C'.cs := (List.perm_ext_iff_of_nodup hn hn').mpr fun c => by
    rw [hmem, hmem', hm]
  refine eq_of_perm_sorted hp hs hs' fun a ha b hb hab => ?_
  exact nameKey_inj hN (en_lt ((hmem a).mp ha)) (en_lt ((hmem b).mp hb)) hab

/-- ✓ **The reference order and key meet the key block.** Example: the clocks `b, a, Z`, in
whatever order they became enabled, are listed `Z, a, b` (code points: `Z` is 90, `a` is 97);
and two classes with the same marking get one key exactly when their firing domains hold the
same firing times, so a domain that tightens one bound between two clocks gets another key. -/
@[evidence holds VER_010_key]
theorem VER_010_key_reference : VER_010_key coByName refSameKey := by
  refine ⟨fun N => ⟨coByName_wf N, reorder_sorted N⟩, fun N hN C C' hC hC' => ?_⟩
  constructor
  · intro h
    simp only [refSameKey, classKey, ClassKey.mk.injEq] at h
    obtain ⟨hm, -, hz⟩ := h
    have hcs := ver010_cs_eq hN hC hC' hm
    refine ⟨hm, fun θ => ?_⟩
    rw [hcs] at hz ⊢
    exact satN_agree (corner_eq_iff.mp hz) θ
  · rintro ⟨hm, hz⟩
    have hcs := ver010_cs_eq hN hC hC' hm
    have hc := hC.2.2
    have hc' := hC'.2.2
    rw [hcs] at hz hc
    simp only [refSameKey, classKey, ClassKey.mk.injEq]
    refine ⟨hm, by rw [hcs], ?_⟩
    rw [hcs]
    exact corner_eq_iff.mpr (canon_unique hc hc' hz)

/-! ## Small nets for the examples -/

/-- One transition `t` from place 0, with two outcomes: a token into place 1, or one into
place 2 (a XOR output). Immediate, no upper bound. -/
def ver010_netX : TNet :=
  [{ tr := { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
     rows := [[1], [2]], eft := 0, lft := ⊤ }]

/-- One token in place 0. -/
def ver010_m0X : AMarking := fun p => if p = 0 then 1 else 0

theorem ver010_netX_wf : TimingWF ver010_netX := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, le_top⟩
  | _ + 1 => exact ⟨le_refl _, le_top⟩

/-- One transition `take` with an `atLeast(2)` input on place 0 and one outcome into place 1. -/
def ver010_netA : TNet :=
  [{ tr := { name := "take", inputs := [⟨0, .atLeast 2, none⟩], inhibitors := [], reads := [],
             resets := [] },
     rows := [[1]], eft := 0, lft := ⊤ }]

/-- Five tokens in place 0. -/
def ver010_m0A : AMarking := fun p => if p = 0 then 5 else 0

theorem ver010_netA_wf : TimingWF ver010_netA := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, le_top⟩
  | _ + 1 => exact ⟨le_refl _, le_top⟩

/-- The initial class of `ver010_netX` exists, holds the initial state and is well formed. -/
theorem ver010_initX : ∃ C0, refScg.init ver010_netX ver010_m0X = some C0 ∧
    InCls ver010_netX (s0 ver010_m0X) C0 ∧ ClsWF ver010_netX C0 :=
  init_sound ver010_netX_wf (coByName_wf _) ver010_eps_nonneg _

/-! ## Wrong steps -/

/-- A step whose initial class holds no clocks: it ignores the transitions enabled at the
start. -/
def ver010_noClockInit : ScgStep where
  init _ m0 := some ⟨m0, [], fun _ _ => 0⟩
  succ := refScg.succ

/-- A step that keeps only the first outcome of every transition: XOR outputs not expanded. -/
def ver010_firstOutcome : ScgStep where
  init := refScg.init
  succ N C := (refScg.succ N C).filter fun p => p.1.2 == 0

/-- The marking a firing leaves when it removes `requiredCount()` tokens from every input,
`All` and `AtLeast` included, in place of `consumptionCount(available)`. -/
def ver010_fireReq (a : AMarking) (t : Transition) (d : Deposit) : AMarking :=
  fun p => if t.resets.contains p then d.count p else a p - pre t p + d.count p

/-- A step that removes `requiredCount()` tokens per input: the reference successors, with the
marking of each replaced by `ver010_fireReq`. -/
def ver010_requiredCount : ScgStep where
  init := refScg.init
  succ N C := (List.range C.cs.length).flatMap fun k =>
    (rowsOf N (C.cs.getD k 0)).zipIdx.filterMap fun p =>
      (succ N (coByName N) ver011_eps C k p.1).map fun C' =>
        ((nameOf N (C.cs.getD k 0), p.2),
          { C' with m := ver010_fireReq C.m (trOf N (C.cs.getD k 0)) p.1 })

/-- A class whose clock list is empty has no successor. -/
theorem ver010_succL_nil {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C : Cls}
    (h : C.cs = []) : succL N co eps C = [] := by
  simp [succL, h]

/-- ✗ **An initial class without clocks loses every firing (line 1).** On the net
`t : p0 → p1 xor p2` with one token in `p0`, the run that fires `t` at once reaches a state with
a token in `p1`. A step whose initial class holds no clocks gives that class no successor, so
the only class it reaches has the initial marking, and no class holds the state. -/
@[evidence forbids VER_010]
theorem VER_010_forbids_noClockInit : ¬ VER_010 ver010_noClockInit := by
  intro h
  obtain ⟨C0, h0, -, hcov⟩ := (h ver010_netX ver010_netX_wf).1 ver010_m0X
  simp only [ver010_noClockInit, Option.some.injEq] at h0
  subst h0
  have hs : TReach ver010_netX ver010_m0X (firedState ver010_netX (s0 ver010_m0X) 0 [1]) :=
    Relation.ReflTransGen.single
      (TStep.fire _ 0 [1] (by decide) (by simp [s0, eftOf, ver010_netX])
        (by simp [rowsOf, ver010_netX]))
  obtain ⟨C, hreach, hin⟩ := hcov _ hs
  have hC : C = ⟨ver010_m0X, [], fun _ _ => 0⟩ := by
    clear hin
    induction hreach with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      obtain ⟨l, hl⟩ := hstep
      simp [ver010_noClockInit, refScg, ver010_succL_nil] at hl
  subst hC
  have := congrFun hin.1 1
  revert this
  decide

/-- ✗ **Keeping only the first outcome loses the XOR branch (line 2).** On the net
`t : p0 → p1 xor p2`, `t` can fire from the start with its second outcome (index 1, the token
into `p2`), so line 2 asks for a successor labelled `("t", 1)`; a step that keeps only outcome
0 has none. -/
@[evidence forbids VER_010]
theorem VER_010_forbids_firstOutcome : ¬ VER_010 ver010_firstOutcome := by
  intro h
  obtain ⟨C0, -, hin, hwf⟩ := ver010_initX
  obtain ⟨C', hC', -⟩ := (h ver010_netX ver010_netX_wf).2.1 C0 (s0 ver010_m0X) 0 1 [2] hwf hin
    (urgent_s0 ver010_netX_wf _) (by decide) (by simp [s0, eftOf, ver010_netX])
    (by simp [rowsOf, ver010_netX])
  simp only [ver010_firstOutcome, List.mem_filter] at hC'
  exact absurd hC'.2 (by decide)

/-- ✗ **Consuming `requiredCount()` leaves tokens an `AtLeast` input drains (line 3).** The
transition `take` has an `atLeast(2)` input on `p0`, which holds 5 tokens. The executor takes
all 5; a step that takes the required 2 leaves 3 in its successor, while line 3 asks for the
marking that leaves `p0` empty. -/
@[evidence forbids VER_010]
theorem VER_010_forbids_requiredCount : ¬ VER_010 ver010_requiredCount := by
  intro h
  obtain ⟨C0, h0, hin, hwf⟩ := init_sound ver010_netA_wf (coByName_wf ver010_netA)
    ver010_eps_nonneg ver010_m0A
  obtain ⟨hm0, hcs0, -⟩ := initCls_eq h0
  have hcs : C0.cs = [0] := by rw [hcs0]; decide
  obtain ⟨C', hs, -, -, -⟩ := successor_sound ver010_netA_wf (coByName_wf ver010_netA)
    ver010_eps_nonneg hwf hin (urgent_s0 ver010_netA_wf _) (f := 0) (d := [1]) (by decide)
    (by simp [s0, eftOf, ver010_netA]) (k := 0) (by rw [hcs]; rfl)
  have hmem : (("take", 0), { C' with m := ver010_fireReq C0.m (trOf ver010_netA 0) [1] }) ∈
      ver010_requiredCount.succ ver010_netA C0 := by
    simp only [ver010_requiredCount, List.mem_flatMap, List.mem_range, List.mem_filterMap,
      Option.map_eq_some_iff]
    refine ⟨0, by rw [hcs]; simp, ([1], 0), ?_, C', ?_, ?_⟩
    · rw [hcs]; decide
    · exact hs
    · rw [hcs]; rfl
  obtain ⟨f, d, hf, -, hd, hm⟩ := (h ver010_netA ver010_netA_wf).2.2 C0 _ _ hmem
  rw [hcs, List.mem_singleton] at hf
  subst hf
  simp only [rowsOf, ver010_netA, List.getElem?_cons_zero, Option.some.injEq] at hd
  subst hd
  have h0' := congrFun hm 0
  simp only [hm0] at h0'
  exact absurd h0' (by decide)

/-- A step whose initial class leaves its clocks in the order they became enabled; every
successor is the reference successor, in name order. -/
def ver010_initKeep : ScgStep where
  init N m0 := initCls N (fun _ => none) ver011_eps m0
  succ := refScg.succ

/-- A step whose initial class has the enabled transitions as clocks, in name order, and a
firing domain with no bound at all; every successor is the reference successor. -/
def ver010_untimedInit : ScgStep where
  init N m0 := some ⟨m0, reorder (coByName N) (enabledIds N m0), fun _ _ => ⊤⟩
  succ := refScg.succ

theorem ver010_exNet_wf : TimingWF exNet := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, le_top⟩
  | 1 => exact ⟨le_refl _, le_top⟩
  | 2 => exact ⟨le_refl _, le_top⟩
  | _ + 3 => exact ⟨le_refl _, le_top⟩

/-- ✗ **An initial class in enabling order breaks the name order (line 1).** The net has three
transitions with no input arcs, `b`, `a` and `Z`, all enabled from the start. A step that
keeps them in that order for its initial class lists `b` before `a`; line 1 asks for `Z, a, b`
(code points: `Z` is 90, `a` 97, `b` 98). This is the port that sorts the clocks of every
successor and forgets the initial class. -/
@[evidence forbids VER_010]
theorem VER_010_forbids_initUnordered : ¬ VER_010 ver010_initKeep := by
  intro h
  obtain ⟨C0, h0, hshape, -⟩ := (h exNet ver010_exNet_wf).1 (fun _ => 0)
  have hord := (hshape C0 Relation.ReflTransGen.refl).2.2
  change initCls exNet (fun _ => none) ver011_eps (fun _ => 0) = some C0 at h0
  obtain ⟨-, hcs, -⟩ := initCls_eq h0
  rw [hcs] at hord
  revert hord
  decide

/-- ✗ **An initial class with no timing holds every state (line 1).** On the net
`t : p0 → p1 xor p2` with one token in `p0`, a step whose initial class lists the clock `t` but
puts no bound in its firing domain holds every state with that marking, so the graph forgets
all timing. Line 1 asks every class to be well formed: letting time pass leaves the lower bound
of `t` at zero, and this domain has none. -/
@[evidence forbids VER_010]
theorem VER_010_forbids_untimedInit : ¬ VER_010 ver010_untimedInit := by
  intro h
  obtain ⟨C0, h0, hshape, -⟩ := (h ver010_netX ver010_netX_wf).1 ver010_m0X
  simp only [ver010_untimedInit, Option.some.injEq] at h0
  subst h0
  obtain ⟨Y, hD, -⟩ := (hshape _ Relation.ReflTransGen.refl).1.down
  have hcs : reorder (coByName ver010_netX) (enabledIds ver010_netX ver010_m0X) = [0] := by
    decide
  dsimp only at hD
  rw [hcs] at hD
  have h01 := congrFun (congrFun hD 0) 1
  have hle := canonN_le (d := [0].length + 1) (ltpPre ([0].length + 1) Y) (a := 0) (b := 1)
    (by simp) (by simp)
  rw [← h01] at hle
  simp [ltpPre] at hle

/-- On `ver010_netX` the reference step has an initial class with two successors, one per
outcome of `t`: label `("t", 0)` with the token in place 1, label `("t", 1)` with it in place 2. -/
theorem ver010_ref_outcomes : ∃ C0, refScg.init ver010_netX ver010_m0X = some C0 ∧
    (∃ C1, (("t", 0), C1) ∈ refScg.succ ver010_netX C0 ∧ C1.m 1 = 1) ∧
    (∃ C2, (("t", 1), C2) ∈ refScg.succ ver010_netX C0 ∧ C2.m 2 = 1) := by
  obtain ⟨C0, h0, hin, hwf⟩ := ver010_initX
  have L2 := (VER_010_reference ver010_netX ver010_netX_wf).2.1 C0 (s0 ver010_m0X)
  obtain ⟨C1, h1, hin1⟩ := L2 0 0 [1] hwf hin (urgent_s0 ver010_netX_wf _) (by decide)
    (by simp [s0, eftOf, ver010_netX]) (by simp [rowsOf, ver010_netX])
  obtain ⟨C2, h2, hin2⟩ := L2 0 1 [2] hwf hin (urgent_s0 ver010_netX_wf _) (by decide)
    (by simp [s0, eftOf, ver010_netX]) (by simp [rowsOf, ver010_netX])
  refine ⟨C0, h0, ⟨C1, h1, ?_⟩, ⟨C2, h2, ?_⟩⟩
  · rw [← hin1.1]; decide
  · rw [← hin2.1]; decide

/-- ✓ **The lines apply: one successor per outcome.** On the net `t : p0 → p1 xor p2` with one
token in `p0`, the reference graph has an initial class and two successors of it, labelled
`("t", 0)` with the token in `p1` and `("t", 1)` with the token in `p2`. -/
@[evidence nonvacuous VER_010]
theorem VER_010_nonvacuous : ∃ C0, refScg.init ver010_netX ver010_m0X = some C0 ∧
    (∃ C1, (("t", 0), C1) ∈ refScg.succ ver010_netX C0 ∧ C1.m 1 = 1) ∧
    (∃ C2, (("t", 1), C2) ∈ refScg.succ ver010_netX C0 ∧ C2.m 2 = 1) :=
  ver010_ref_outcomes

/-! ## Consequences of VER-010 -/

/-- **Run coverage follows from line 2 and the shape of line 1.** Take a step whose initial
class holds the start state, whose classes are all well formed, and which meets line 2. Then
every state of every timed run lies in a class reachable from the initial class: a delay stays
in the class, and a firing moves to the successor line 2 gives. -/
theorem ver010_covers_of {G : ScgStep} {N : TNet} (hT : TimingWF N) {m0 : AMarking} {C0 : Cls}
    (h0 : InCls N (s0 m0) C0)
    (hwf : ∀ C, Relation.ReflTransGen (G.Edge N) C0 C → ClsWF N C)
    (h2 : ∀ (C : Cls) (s : TState) (f i : Nat) (d : Deposit), ClsWF N C → InCls N s C →
      Urgent N s → en N s.m f = true → eftOf N f ≤ s.ν f → (rowsOf N f)[i]? = some d →
      ∃ C', ((nameOf N f, i), C') ∈ G.succ N C ∧ InCls N (firedState N s f d) C')
    {s : TState} (hs : TReach N m0 s) :
    ∃ C, Relation.ReflTransGen (G.Edge N) C0 C ∧ InCls N s C ∧ Urgent N s := by
  induction hs with
  | refl => exact ⟨C0, Relation.ReflTransGen.refl, h0, urgent_s0 hT m0⟩
  | tail _ hstep ih =>
    obtain ⟨C, hreach, hin, hu⟩ := ih
    have hwfC := hwf C hreach
    cases hstep with
    | delay δ hδ hurg => exact ⟨C, hreach, delay_sound hwfC hin hδ, hurg⟩
    | fire f d hen hready hd =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
      obtain ⟨C', hC', hin'⟩ := h2 C _ f i d hwfC hin hu hen hready hi
      have hfC : f ∈ C.cs := (hwfC.mem f).mpr (hin.1 ▸ hen)
      obtain ⟨k, hk, hkf⟩ := List.getElem_of_mem hfC
      have hk' : C.cs[k]? = some f := by rw [List.getElem?_eq_getElem hk, hkf]
      obtain ⟨-, -, -, -, hu'⟩ := successor_sound hT (coByName_wf N) ver010_eps_nonneg hwfC hin hu
        hen hready (d := d) hk'
      exact ⟨C', Relation.ReflTransGen.tail hreach ⟨_, hC'⟩, hin', hu'⟩

/-- **Any step that meets VER-010 drains an `AtLeast` input** (the test derivation's second
regression). The transition `take` has an `atLeast(2)` input on `p0`: whatever class it fires
from, every successor has `p0` empty, so from 5 tokens none is left. -/
@[evidence cites "VER-010" "an `atLeast(2, p)` input over 5 tokens MUST leave `p` empty"]
theorem VER_010_atLeast_drains {G : ScgStep} (h : VER_010 G) {C C' : Cls} {l : Label}
    (hC : (l, C') ∈ G.succ ver010_netA C) : C'.m 0 = 0 := by
  obtain ⟨f, d, -, -, hd, hm⟩ := (h ver010_netA ver010_netA_wf).2.2 C C' l hC
  rw [hm]
  match f, hd with
  | 0, hd =>
    simp only [rowsOf, ver010_netA, List.getElem?_cons_zero] at hd
    have hd' : d = [1] := by
      rcases l with ⟨n, i⟩
      cases i with
      | zero => simpa using hd.symm
      | succ i => simp at hd
    subst hd'
    simp [fireAD, trOf, ver010_netA, consumeAllAt, specAt, Card.consumesAll]
  | f + 1, hd => simp [rowsOf, ver010_netA] at hd

/-- `take` drains place 0 through an `all` input into place 1; `wait` is inhibited on place 0
and puts a token into place 2. Both immediate, with no upper bound. -/
def ver010_netI : TNet :=
  [{ tr := { name := "take", inputs := [⟨0, .all, none⟩], inhibitors := [], reads := [],
             resets := [] },
     rows := [[1]], eft := 0, lft := ⊤ },
   { tr := { name := "wait", inputs := [], inhibitors := [0], reads := [], resets := [] },
     rows := [[2]], eft := 0, lft := ⊤ }]

/-- Three tokens in place 0. -/
def ver010_m0I : AMarking := fun p => if p = 0 then 3 else 0

theorem ver010_netI_wf : TimingWF ver010_netI := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, le_top⟩
  | 1 => exact ⟨le_refl _, le_top⟩
  | _ + 2 => exact ⟨le_refl _, le_top⟩

/-- **Any step that meets VER-010 reaches the inhibited transition** (the test derivation's
first regression). Place `p0` holds 3 tokens, so `wait`, inhibited on `p0`, is disabled at the
start. `take` has an `all` input on `p0` and drains it, so the graph reaches a class in which
`wait` is enabled. A step that takes only one token would leave 2 and never get there. -/
@[evidence cites "VER-010" "the inhibited successor MUST be reachable, since `p` is drained"]
theorem VER_010_all_enables_inhibited {G : ScgStep} (h : VER_010 G) :
    en ver010_netI ver010_m0I 1 = false ∧
      ∃ C0 C, G.init ver010_netI ver010_m0I = some C0 ∧
        Relation.ReflTransGen (G.Edge ver010_netI) C0 C ∧ en ver010_netI C.m 1 = true := by
  obtain ⟨C0, h0, -, hcov⟩ := (h ver010_netI ver010_netI_wf).1 ver010_m0I
  have hs : TReach ver010_netI ver010_m0I (firedState ver010_netI (s0 ver010_m0I) 0 [1]) :=
    Relation.ReflTransGen.single
      (TStep.fire _ 0 [1] (by decide) (by simp [s0, eftOf, ver010_netI])
        (by simp [rowsOf, ver010_netI]))
  obtain ⟨C, hreach, hin⟩ := hcov _ hs
  refine ⟨by decide, C0, C, h0, hreach, ?_⟩
  rw [← hin.1]
  decide

/-- **A closed graph holds every timed run** (the reference build). When the build of the timed
graph at the class-key explorer closes within its class budget, every state of every timed run
lies in a stored class, which has the state's marking and a zone that holds its firing
times. -/
@[evidence cites "VER-010" "State class graph enumerates reachable (marking, timing zone) pairs"]
theorem ver010_closed_covers {N : TNet} (hT : TimingWF N) {maxClasses : Nat} {cut : Nat → Bool}
    {fuel : Nat} {m0 : AMarking} {o : Libpetri.Novel.RouteB.Decide.Out Cls}
    (ho : scgGraph N ver011_eps maxClasses cut fuel m0 = some o) (hcomp : o.complete = true)
    {s : TState} (hs : TReach N m0 s) : ∃ T ∈ o.cls, InCls N s T ∧ ClsWF N T :=
  scgGraph_covers hT ver010_eps_nonneg ho hcomp hs

/-! ## The persistence rule: wrong rule, examples, bridge -/

/-- ✗ **The rule without the intermediate marking keeps a clock it must restart.** On the
refresh net (`CloseSession` waits on the timer place; `Refresh` takes the timer token and puts
it back), `CloseSession` is enabled before and after `Refresh`, so the pre-6.0.0 test keeps its
clock; but the timer place is empty in the intermediate marking, so the rule restarts it. -/
@[evidence forbids VER_010_persist]
theorem VER_010_persist_forbids_old : ¬ VER_010_persist survivesOld := by
  intro h
  have := h netRT m0RT 1 [1] 0 (by decide)
  revert this
  decide

/-- `netRT` (`Retrodict.lean`: `CloseSession` on the timer place 1, `Refresh` from places 0 and
1 back into 1) with two tokens on the timer. -/
def ver010_m0RT2 : AMarking := fun p => if p = 0 then 1 else if p = 1 then 2 else 0

/-- `netRT` with a reset arc of `Refresh` on the timer place 1. -/
def ver010_netRTreset : TNet :=
  [ { tr := { name := "CloseSession", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [],
              resets := [] },
      rows := [[2]], eft := 0, lft := ((150 : ℚ) : Bound) },
    { tr := { name := "Refresh", inputs := [⟨0, .one, none⟩, ⟨1, .one, none⟩], inhibitors := [],
              reads := [], resets := [1] },
      rows := [[1]], eft := 100, lft := ((100 : ℚ) : Bound) } ]

/-- ✓ **The test derivation, on the reference rule.** On the refresh net, `CloseSession`
(enabled before the firing) restarts its clock when `Refresh` takes the one timer token and puts
it back; with a second token on the timer it keeps its clock, since the timer is never empty;
with a reset arc of `Refresh` on the timer it restarts again, since the reset empties it. -/
@[evidence nonvacuous VER_010_persist]
theorem VER_010_persist_nonvacuous :
    en netRT m0RT 0 = true ∧
      refSurv netRT 1 (fireAD m0RT (trOf netRT 1) [1]) (inter m0RT (trOf netRT 1)) 0 = false ∧
    en netRT ver010_m0RT2 0 = true ∧
      refSurv netRT 1 (fireAD ver010_m0RT2 (trOf netRT 1) [1])
        (inter ver010_m0RT2 (trOf netRT 1)) 0 = true ∧
    en ver010_netRTreset ver010_m0RT2 0 = true ∧
      refSurv ver010_netRTreset 1 (fireAD ver010_m0RT2 (trOf ver010_netRTreset 1) [1])
        (inter ver010_m0RT2 (trOf ver010_netRTreset 1)) 0 = false := by
  decide

/-- **Any rule that meets the persistence line builds the reference successor.** On a class
whose clocks are enabled in its marking (every class the graph builds), the successor computed
with such a survival test is the reference successor, so VER-010's lines hold of the graph built
with it. -/
@[evidence cites "VER-010" "a transition `t' ≠ t` keeps its clock only if it is enabled in `M`, in the successor marking `M'`, and in the intermediate marking `M - Pre(t)`"]
theorem ver010_succWith_of {surv : SurvTest} (h : VER_010_persist surv) {N : TNet}
    {co : List Nat → Option (List Nat)} {eps : ℚ} {C : Cls}
    (hC : ∀ c ∈ C.cs, en N C.m c = true) (k : Nat) (d : Deposit) :
    succWith (surv N) N co eps C k d = succ N co eps C k d := by
  have hp : ∀ f, persPos (surv N) C f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f)) =
      persPos (survives N) C f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f)) := by
    intro f
    unfold persPos
    refine List.filter_congr fun i hi => ?_
    have hc := hC _ (getD_mem 0 (List.mem_range.mp hi))
    have e := (h N C.m f d _ hc)
    have e' := (VER_010_persist_reference N C.m f d _ hc)
    simp only [refSurv] at e'
    exact Bool.eq_iff_iff.mpr (e.trans e'.symm)
  unfold succ succWith
  cases C.cs[k]? with
  | none => rfl
  | some f => simp only [hp f]

/-- **The old rule loses a timed run.** On the refresh net, the run that waits 100 time units
and fires `Refresh` reaches a state no successor of the initial class holds when the clock of
`CloseSession` is kept across `Refresh`, while the graph built with the intermediate-marking
rule has a successor that holds it (`Retrodict.old_rule_loses_run`). -/
@[evidence cites "VER-010" "A successor that keeps a clock the executor restarts under-approximates the executor's behaviors"]
theorem ver010_old_rule_loses_run {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls netRT (fun _ => none) eps m0RT = some C0) :
    TReach netRT m0RT s2RT ∧
      (∀ C' ∈ succListWith (survivesOld netRT) netRT (fun _ => none) eps C0,
        ¬ InCls netRT s2RT C') ∧
      ∃ C' ∈ succList netRT (fun _ => none) eps C0, InCls netRT s2RT C' :=
  old_rule_loses_run heps h0

/-! ## The class key: examples and wrong keys -/

/-- Two transitions `a` and `b` with no input arcs, so both are always enabled. -/
def ver010_netAB : TNet :=
  [⟨exTr "a", [], 0, ⊤⟩, ⟨exTr "b", [], 0, ⊤⟩]

/-- A firing domain of the two clocks `a` (index 1) and `b` (index 2): each fires between 0 and
2 time units from now, and `a` at most `c` after `b`. -/
def ver010_D (c : ℚ) : NMat := fun i j =>
  if i = j then 0 else if i = 0 then 0 else if j = 0 then ((2 : ℚ) : Bound)
  else if i = 1 ∧ j = 2 then (c : Bound) else ((2 : ℚ) : Bound)

/-- The class with the box domain: `a` at most 2 after `b`, which the box already implies. -/
def ver010_C1 : Cls := ⟨fun _ => 0, [0, 1], ver010_D 2⟩

/-- The class with one difference bound tightened: `a` at most 1 after `b`. -/
def ver010_C2 : Cls := ⟨fun _ => 0, [0, 1], ver010_D 1⟩

theorem ver010_D2_canon : CanonZone 3 (ver010_D 2) := by
  refine ⟨by omega, fun i j k hi hj hk => ?_, fun i hi => by simp [ver010_D],
    fun i hi => by interval_cases i <;> simp [ver010_D]⟩
  interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num [ver010_D] <;>
    exact WithTop.coe_le_coe.mpr (by norm_num)

theorem ver010_D1_canon : CanonZone 3 (ver010_D 1) := by
  refine ⟨by omega, fun i j k hi hj hk => ?_, fun i hi => by simp [ver010_D],
    fun i hi => by interval_cases i <;> simp [ver010_D]⟩
  interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num [ver010_D] <;>
    exact WithTop.coe_le_coe.mpr (by norm_num)

theorem ver010_C_good {D : NMat} (hD : CanonZone 3 D) {m : AMarking} :
    GoodCls ver010_netAB ⟨m, [0, 1], D⟩ := by
  refine ⟨fun x => ?_, ⟨by simp, ?_⟩, hD⟩
  swap
  · show List.Pairwise (fun a b => nameKey ver010_netAB a ≤ nameKey ver010_netAB b) [0, 1]
    decide
  constructor
  · intro hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  · intro hx
    have := en_lt hx
    simp only [ver010_netAB, List.length_cons, List.length_nil] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem ver010_netAB_names : NamesUnique ver010_netAB := by
  intro i j hi hj h
  simp only [ver010_netAB, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> first | rfl | (revert h; decide)

/-- `C1` holds the firing times `a = 2, b = 0`; `C2` does not, since there `a` is 2 after `b`. -/
theorem ver010_C12_differ :
    SatN 3 ver010_C1.D (fun i => if i = 1 then 2 else 0) ∧
      ¬ SatN 3 ver010_C2.D (fun i => if i = 1 then 2 else 0) := by
  refine ⟨fun i j hi hj => ?_, fun h => ?_⟩
  · interval_cases i <;> interval_cases j <;> simp only [ver010_C1, ver010_D] <;>
      exact WithTop.coe_le_coe.mpr (by norm_num)
  · have := h 1 2 (by omega) (by omega)
    simp only [ver010_C2, ver010_D] at this
    norm_num at this

/-- A key over the projections alone: the marking, the clock names, and the bounds of each
clock against the reference clock, not the bounds between two clocks. -/
def ver010_projSame (N : TNet) (C C' : Cls) : Prop :=
  C.m = C'.m ∧ C.cs.map (nameOf N) = C'.cs.map (nameOf N) ∧
    ∀ i, i < C.cs.length + 1 → C.D 0 i = C'.D 0 i ∧ C.D i 0 = C'.D i 0

/-- ✗ **A key over the projections alone merges two classes.** On the net with two always
enabled transitions `a` and `b`, two classes with the same marking give each clock a firing time
between 0 and 2; in the second, `a` fires at most 1 after `b`. They agree on every projection,
so the projection key calls them one class, but the first holds `a = 2, b = 0` and the second
does not. -/
@[evidence forbids VER_010_key]
theorem VER_010_key_forbids_projections : ¬ VER_010_key coByName ver010_projSame := by
  intro h
  have hk := (h.2 ver010_netAB ver010_netAB_names ver010_C1 ver010_C2
    (ver010_C_good ver010_D2_canon) (ver010_C_good ver010_D1_canon)).mp
  have hp : ver010_projSame ver010_netAB ver010_C1 ver010_C2 := by
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    simp only [ver010_C1, List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp [ver010_C1, ver010_C2, ver010_D]
  obtain ⟨-, hz⟩ := hk hp
  obtain ⟨h1, h2⟩ := ver010_C12_differ
  exact h2 ((hz _).mp h1)

/-- The class `C1` with one token in place 0: the same clocks and the same zone, another
marking. -/
def ver010_C1m : Cls := ⟨fun p => if p = 0 then 1 else 0, [0, 1], ver010_D 2⟩

/-- A key that does not tell markings apart: the clock names and the zone, the marking left
out. It stands for any key that gives two markings one key, as a rendered key that does not
escape place names holding `:` or `,` does (the Rust and TypeScript behaviour RD-40 recorded). -/
def ver010_markingBlind (N : TNet) (C C' : Cls) : Prop :=
  C.cs.map (nameOf N) = C'.cs.map (nameOf N) ∧
    ∀ θ, SatN (C.cs.length + 1) C.D θ ↔ SatN (C'.cs.length + 1) C'.D θ

/-- ✗ **A key that merges two markings merges two classes.** On the net with two always
enabled transitions `a` and `b`, the classes `C1` and `C1m` have one clock list and one zone and
differ in their marking (no token in place 0 against one). A key that does not separate the
markings calls them one class; line 2 asks the same marking. -/
@[evidence forbids VER_010_key]
theorem VER_010_key_forbids_markingBlind : ¬ VER_010_key coByName ver010_markingBlind := by
  intro h
  have hk := (h.2 ver010_netAB ver010_netAB_names ver010_C1 ver010_C1m
    (ver010_C_good ver010_D2_canon) (ver010_C_good ver010_D2_canon)).mp
    ⟨rfl, fun _ => Iff.rfl⟩
  have := congrFun hk.1 0
  simp [ver010_C1, ver010_C1m] at this

/-- The canonical order that keeps the enabling order: it never reorders. -/
def ver010_coKeep : TNet → List Nat → Option (List Nat) := fun _ _ => none

/-- ✗ **Keeping the enabling order is not the canonical order.** With transitions `b`, `a`
and `Z` enabled in that order, an order that keeps the list leaves `b` before `a`, out of name
order. -/
@[evidence forbids VER_010_key]
theorem VER_010_key_forbids_enablingOrder : ¬ VER_010_key ver010_coKeep refSameKey := by
  intro h
  have := (h.1 exNet).2 [0, 1, 2]
  revert this
  decide

/-- The canonical order that returns no position at all. -/
def ver010_coDrop : TNet → List Nat → Option (List Nat) := fun _ _ => some []

/-- ✗ **An order that drops the clocks is no permutation.** An order that answers every list
with no positions turns the clock list `a` into the empty list, which is trivially in name
order. The first key line also asks for a permutation of the positions, so the clock `a` must
stay. -/
@[evidence forbids VER_010_key]
theorem VER_010_key_forbids_dropAll : ¬ VER_010_key ver010_coDrop refSameKey := by
  intro h
  have := ((h.1 exNet).1 [1] [] rfl).1
  simp at this

/-- ✓ **The key lines apply.** The two classes of the projection example are both shaped as
the graph shapes them, and the reference key tells them apart; and the clocks `b, a, Z` come
out as `Z, a, b` from two different enabling orders. -/
@[evidence nonvacuous VER_010_key]
theorem VER_010_key_nonvacuous :
    GoodCls ver010_netAB ver010_C1 ∧ GoodCls ver010_netAB ver010_C2 ∧
      ¬ refSameKey ver010_netAB ver010_C1 ver010_C2 ∧
      reorder (coByName exNet) [1, 0, 2] = reorder (coByName exNet) [0, 2, 1] := by
  refine ⟨ver010_C_good ver010_D2_canon, ver010_C_good ver010_D1_canon, fun h => ?_, by decide⟩
  have := (VER_010_key_reference.2 ver010_netAB ver010_netAB_names ver010_C1 ver010_C2
    (ver010_C_good ver010_D2_canon) (ver010_C_good ver010_D1_canon)).mp h
  obtain ⟨h1, h2⟩ := ver010_C12_differ
  exact h2 ((this.2 _).mp h1)

/-! ## The key lines on the classes of the graph -/

/-- A canonical order that returns a permutation of the positions reorders a list into a
permutation of it. -/
theorem ver010_reorder_perm {co : List Nat → Option (List Nat)} (hco : CoWF co) (l : List Nat) :
    (reorder co l).Perm l := by
  unfold reorder
  cases h : co l with
  | none => exact List.Perm.refl _
  | some ord =>
    obtain ⟨hlen, -, hall⟩ := hco l ord h
    have hsub : (List.range l.length).Subperm ord :=
      List.subperm_of_subset List.nodup_range fun i hi => hall i (List.mem_range.mp hi)
    have hp : (List.range l.length).Perm ord := hsub.perm_of_length_le (by simp [hlen])
    have := hp.symm.map (fun i => l.getD i 0)
    rwa [map_getD_range] at this

/-- Under the first key line, a list without repeats is reordered into name order, still
without repeats. -/
theorem ver010_ordered_of {N : TNet} {co : List Nat → Option (List Nat)} (hco : CoWF co)
    (hs : ∀ l : List Nat, (reorder co l).Pairwise (fun a b => nameKey N a ≤ nameKey N b))
    {l : List Nat} (hn : l.Nodup) : ClocksOrdered N (reorder co l) :=
  ⟨(ver010_reorder_perm hco l).nodup_iff.mpr hn, hs l⟩

/-- Under the first key line, a successor lists its clocks once each, in name order. -/
theorem ver010_succ_ordered {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}
    (hco : CoWF co)
    (hs : ∀ l : List Nat, (reorder co l).Pairwise (fun a b => nameKey N a ≤ nameKey N b))
    {C C' : Cls} {k : Nat} {d : Deposit} (hC : C.cs.Nodup) (h : succ N co eps C k d = some C') :
    ClocksOrdered N C'.cs := by
  obtain ⟨f, ps, newly, Y, -, hps, hnew, -, -, hcs, -⟩ := succ_shape h
  rw [hcs]
  refine ver010_ordered_of hco hs (List.nodup_append.mpr ⟨?_, ?_, ?_⟩)
  · have hsub : (ps.map fun i => C.cs.getD i 0).Sublist C.cs := by
      have := (List.filter_sublist (l := List.range C.cs.length)
        (p := fun i => survives N f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f))
          (C.cs.getD i 0))).map (fun i => C.cs.getD i 0)
      rw [map_getD_range] at this
      rw [hps]
      exact this
    exact hC.sublist hsub
  · rw [hnew]
    exact (enabledIds_nodup _).filter _
  · intro a ha b hb hab
    subst hab
    rw [hnew, List.mem_filter, Bool.not_eq_true', contains_false_iff] at hb
    exact hb.2 ha

/-- Under the first key line, every class the graph reaches lists its clocks once each, in
name order. -/
theorem ver010_graph_ordered {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}
    (hco : CoWF co)
    (hs : ∀ l : List Nat, (reorder co l).Pairwise (fun a b => nameKey N a ≤ nameKey N b))
    {m0 : AMarking} {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge N co eps) C0 C) : ClocksOrdered N C.cs := by
  induction h with
  | refl =>
    obtain ⟨-, hcs, -⟩ := initCls_eq h0
    rw [hcs]
    exact ver010_ordered_of hco hs (enabledIds_nodup _)
  | tail _ hstep ih =>
    simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_filterMap] at hstep
    obtain ⟨k, -, d, -, hsucc⟩ := hstep
    exact ver010_succ_ordered hco hs ih.1 hsucc

/-- **The key block on the classes of the graph.** For any canonical order and class identity
that meet the key block, on a net with unique names whose emptiness check is exact (every bound
a whole number of milliseconds at the Rust `EPSILON`), two classes the graph reaches from its
initial class are one exactly when they have the same marking and the same firing domain. So two
interleavings that arrive at one marking and one zone arrive at one class. -/
@[evidence cites "VER-010" "Two arrivals at the same marking and zone by different interleavings are one class; two zones that agree on every projection but differ in a difference constraint are two."]
theorem ver010_key_graph {co : TNet → List Nat → Option (List Nat)}
    {same : TNet → Cls → Cls → Prop} (h : VER_010_key co same) {N : TNet} (hT : TimingWF N)
    (hN : NamesUnique N) {eps : ℚ} (hx : ExactEps N eps) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N (co N) eps m0 = some C0) {C C' : Cls}
    (hC : Relation.ReflTransGen (Edge N (co N) eps) C0 C)
    (hC' : Relation.ReflTransGen (Edge N (co N) eps) C0 C') :
    same N C C' ↔ C.m = C'.m ∧
      ∀ θ, SatN (C.cs.length + 1) C.D θ ↔ SatN (C'.cs.length + 1) C'.D θ := by
  obtain ⟨hco, hs⟩ := h.1 N
  have good : ∀ {X : Cls}, Relation.ReflTransGen (Edge N (co N) eps) C0 X → GoodCls N X :=
    fun hX => ⟨(graph_classes_ok hT hco hx.nonneg h0 hX).1.mem,
      ver010_graph_ordered hco hs h0 hX, graph_canon hT hco hx h0 hX⟩
  exact h.2 N hN C C' (good hC) (good hC')

open Classical in
/-- **The reference build stores one class per marking and zone.** Two classes the build of
the timed graph stores, with the same marking and the same firing times, are stored at one
index: a second interleaving that reaches them adds no class (`Scg.stored_one_class`). -/
@[evidence cites "VER-010" "Two arrivals at the same marking and zone by different interleavings are one class"]
theorem ver010_stored_one_class {N : TNet} (hT : TimingWF N) (hN : NamesUnique N) {eps : ℚ}
    (hx : ExactEps N eps) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N (coByName N) eps m0 = some C0) {n : Nat} {cut : Nat → Bool}
    {bad : Cls → Bool} {stopAt : Bool} {fuel : Nat} {i j : Nat} {A B : Cls}
    (hA : (Libpetri.Novel.RouteB.Decide.build (scgE N (coByName N) eps) n cut bad stopAt fuel
      C0).cls[i]? = some A)
    (hB : (Libpetri.Novel.RouteB.Decide.build (scgE N (coByName N) eps) n cut bad stopAt fuel
      C0).cls[j]? = some B)
    (hm : A.m = B.m) (hz : ∀ θ, SatN (A.cs.length + 1) A.D θ ↔ SatN (B.cs.length + 1) B.D θ) :
    i = j :=
  stored_one_class hT hN hx h0 hA hB hm hz

/-! ## One graph for the three blocks -/

/-- ✓ **The three blocks hold of one graph.** One canonical order, one survival test and one
class identity meet the key and persistence blocks, and the step built from that order and
that test (initial class in that order, successors computed with that test) meets VER-010:
it is the reference step `refScg`. -/
@[evidence consistent VER_010 VER_010_persist VER_010_key]
theorem VER_010_joint : ∃ (co : TNet → List Nat → Option (List Nat)) (surv : SurvTest)
    (same : TNet → Cls → Cls → Prop),
    VER_010_key co same ∧ VER_010_persist surv ∧
      VER_010 ⟨fun N m0 => initCls N (co N) ver011_eps m0,
        fun N C => ver010_succLWith (surv N) N (co N) ver011_eps C⟩ :=
  ⟨coByName, refSurv, refSameKey, VER_010_key_reference, VER_010_persist_reference,
    VER_010_reference⟩

end Libpetri.Spec
