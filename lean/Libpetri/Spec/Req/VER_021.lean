import Libpetri.Spec.Verifier.Graph
import Libpetri.Spec.Req.VER_001

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-021: XOR Branch Analysis (`spec/07-verification.md`)

The XOR branch analysis reads a built graph and reports, for every transition with two or more
outcomes, which outcomes the graph takes. It is graph-relative (ruling D94 (a)): it reads the
edges of the graph it is handed and says nothing about whether that graph is closed. The
requirement is a predicate over a pair `(Xp, A)`:

* `Xp : ExpandFn N`, the expansion of [VER-001]: the virtual transitions of a transition, one
  per outcome (its XOR branches in enumeration order, then a timeout outcome that deposits
  differently); its length is the transition's number of outcomes (`outCount`);
* `A : XorAnalysis N`, the analysis: from the net and a graph (`XorGraph`: labelled edges, each
  label a transition name and an outcome index, and which transitions some class holds in
  flight) to one entry per reported transition, with its number of outcomes and its taken and
  untaken outcome indices.

The lines: the reported transitions are those with two or more outcomes, each once with its
count, leaving aside the names of drained forwards ([IO-014]), which VER-001 does not expand;
an index is taken exactly when an edge fires the transition with it, the transition read off its
completion step `complete:<t>` when the graph splits it in flight ([VER-004]); the untaken
outcomes are the others below the count; and on a closed graph built by the build loop of the
graph layer at a key-equivariant explorer, an outcome is untaken exactly when no run of that
explorer fires it.

The witness is `refVirtual` and `refXor` (`analyzer.rs` `analyze_xor_branches`), and the
statement holds of it (`VER_021_reference`). Wrong analyses are killed one per line: one that
counts the XOR branches and not the timeout outcome, one that reports nothing for a net holding
a drained forward, one that reads a split transition under its start name (on a hand-written
graph and on a closed build), one that counts the start edges of a split transition too, one
that ignores the in-flight mark, and one whose untaken list stops before the timeout outcome.
`VER_021_outCount_of_VER_001` shows that the count is VER-001's: an expansion meeting VER-001
fixes it. `VER_021_together` shows why the old test derivation (one branch unreachable beside a
reachable one) cannot be met on a closed graph whose semantics fires every outcome of a
transition from the same states.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.RouteB Libpetri.Spec.Verifier.Graph

/-! ## The model -/

/-- The completion step of transition `t` in the in-flight split of [VER-004]: `complete:<t>`
(`in_flight.rs` `completion_transition`). -/
def completionName (t : String) : String := "complete:" ++ t

/-- **What the analysis reads of a graph**: its labelled edges `(from, (transition, outcome),
to)`, and whether some class of the graph marks the in-flight place `inflight:<t>` of the
transition named `t`. -/
structure XorGraph where
  /-- The edges, each labelled with the transition it fires and the outcome index it takes. -/
  edges : List (ℕ × (String × ℕ) × ℕ)
  /-- `inFlight t`: some class of the graph marks `inflight:<t>`. -/
  inFlight : String → Bool

namespace XorGraph

/-- The graph splits the transition named `t` in flight: an edge fires `complete:<t>`, or a
class marks `inflight:<t>` (`analyzer.rs`, the `split` test). -/
def split (G : XorGraph) (t : String) : Bool :=
  G.edges.any (fun e => e.2.1.1 == completionName t) || G.inFlight t

/-- The label the outcomes of `t` are read under: `complete:<t>` when the graph splits `t`,
`t` otherwise. -/
def label (G : XorGraph) (t : String) : String := if G.split t then completionName t else t

/-- Some edge of the graph fires the label `l` with outcome `i`. -/
def Fires (G : XorGraph) (l : String) (i : ℕ) : Prop := ∃ a b, (a, (l, i), b) ∈ G.edges

instance (G : XorGraph) (l : String) (i : ℕ) : Decidable (G.Fires l i) :=
  decidable_of_iff (∃ e ∈ G.edges, e.2.1 = (l, i)) (by
    constructor
    · rintro ⟨⟨a, li, b⟩, he, h⟩
      simp only at h
      subst h
      exact ⟨a, b, he⟩
    · rintro ⟨a, b, he⟩
      exact ⟨(a, (l, i), b), he, rfl⟩)

end XorGraph

/-- **One entry of the report**: the transition's name, its number of outcomes, the outcome
indices some edge takes and those it does not. Only membership counts: the runtimes hold the
indices as sets. -/
structure XorEntry where
  /-- The transition's name. -/
  name : String
  /-- Its number of outcomes. -/
  total : ℕ
  /-- The taken outcome indices. -/
  taken : List ℕ
  /-- The untaken outcome indices. -/
  untaken : List ℕ
  deriving DecidableEq, Repr

/-- **An XOR branch analysis**: from the net and a graph to the report. -/
abbrev XorAnalysis (N : Type) : Type := Reference.Net N → XorGraph → List XorEntry

/-- The number of outcomes of `t` under the expansion `Xp`: its number of virtual transitions. -/
def outCount {N : Type} (Xp : ExpandFn N) (t : Reference.Trans N) : ℕ := ((Xp t).getD []).length

/-- Some transition of `net` named `name` is a drained forward ([IO-014]): a `Timeout` of it
forwards an `All` or `AtLeast` input, so VER-001 gives it no virtual transitions. -/
def drainedNamed {N : Type} [DecidableEq N] (net : Reference.Net N) (name : String) : Bool :=
  net.transitions.any fun t => t.core.name == name && decide (DrainedForward t)

/-- **The graph a build gives the analysis**: the labelled edges of the build (`edges` of the
graph layer), and `inflight:<t>` marked when some stored class marks it, as `fl` reads a class. -/
def graphView {S K : Type} [DecidableEq K] (E : Explorer S K (String × ℕ))
    (fl : S → String → Bool) (o : Decide.Out S) : XorGraph :=
  { edges := edges E o, inFlight := fun t => o.cls.any fun x => fl x t }

/-- Some run of the explorer from `x0` fires the label `l` with outcome `i`: a state reachable
from `x0` has that step among its successors. -/
def ExplFires {S K : Type} (E : Explorer S K (String × ℕ)) (x0 : S) (l : String) (i : ℕ) :
    Prop :=
  ∃ y c s, Explorer.Reach E x0 y ∧ E.bound y ≤ c ∧ ((l, i), s) ∈ E.succ c y

/-! ## The reference analysis -/

section Reference

variable {N : Type} [DecidableEq N]

/-- The outcome indices the edges of `G` take under the label of `name`. -/
def refXorTaken (G : XorGraph) (name : String) : List ℕ :=
  (G.edges.filterMap fun e => if e.2.1.1 = G.label name then some e.2.1.2 else none).dedup

/-- The entry of the transition named `name` with `k` outcomes. -/
def refXorEntry (G : XorGraph) (name : String) (k : ℕ) : XorEntry :=
  { name := name, total := k, taken := refXorTaken G name,
    untaken := (List.range k).filter fun i => decide (i ∉ refXorTaken G name) }

/-- **The reference analysis** (`analyzer.rs` `analyze_xor_branches`): every transition of the
net with two or more outcomes (`branch_outcomes::outcomes`, VER-001's rows), in net order; its
taken outcomes are the outcome indices of the edges with its label, and its untaken ones the
other indices below its count. -/
def refXor : XorAnalysis N := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (refVirtualRows t).length)).map fun t =>
    refXorEntry G t.core.name (refVirtualRows t).length

#spec_witness refXor

theorem refXorTaken_mem (G : XorGraph) (name : String) (i : ℕ) :
    i ∈ refXorTaken G name ↔ G.Fires (G.label name) i := by
  simp only [refXorTaken, List.mem_dedup, List.mem_filterMap, XorGraph.Fires]
  constructor
  · rintro ⟨⟨a, ⟨l, j⟩, b⟩, he, h⟩
    simp only at h
    split_ifs at h with hl
    · cases h
      subst hl
      exact ⟨a, b, he⟩
  · rintro ⟨a, b, he⟩
    exact ⟨(a, (G.label name, i), b), he, by simp⟩

/-- Without a drained forward, VER-001's expansion has one virtual transition per row. -/
theorem outCount_refVirtual {t : Reference.Trans N} (ht : ¬ DrainedForward t) :
    outCount refVirtual t = (refVirtualRows t).length := by
  have hb : ver001_drainedB t = false := by
    cases h : ver001_drainedB t with
    | false => rfl
    | true => exact absurd ((ver001_drainedB_iff t).mp h) ht
  simp [outCount, refVirtual, hb, ver001_labelRows]

/-- A transition of the net whose name no drained forward carries is no drained forward. -/
theorem not_drained_of_drainedNamed {net : Reference.Net N} {t : Reference.Trans N}
    (ht : t ∈ net.transitions) (h : drainedNamed net t.core.name = false) :
    ¬ DrainedForward t := by
  intro hd
  have := List.any_eq_false.mp h t ht
  simp [hd] at this

end Reference

/-! ## VER-021 (F): the XOR branch report -/

requirement VER_021
  id "VER-021"
  title "XOR Branch Analysis"
  kind F
  scope "the XOR branch analysis over a built graph, Java, TypeScript and Rust (SHOULD; the shall sentences bind an implementation that offers it)"
  source verbatim "spec/07-verification.md"
  quote "The XOR branch analysis *shall* report every transition of the net with two or more outcomes, and no other, once each with its number of outcomes."
        "*While* the graph it reads does not split a transition in flight, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires the transition with that index."
        "*While* the graph it reads splits a transition in flight ([VER-004]), that is, while an edge fires its completion `complete:<t>` or a class marks its place `inflight:<t>`, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires `complete:<t>` with that index."
        "The XOR branch analysis *shall* report as untaken exactly the outcomes of a reported transition, numbered from 0 below its number of outcomes, that it does not report as taken."
        "*When* the graph is closed, the XOR branch analysis *shall* report an outcome of a reported transition as untaken exactly when no run of the net from its initial marking fires the transition with that outcome, or fires `complete:<t>` with it when the graph splits the transition."
  reading "For every expansion Xp, analysis A and net, with outCount Xp t the number of virtual transitions Xp gives t, and a name drained when some transition of the net with that name is a drained forward:"
          "for every graph G, the (name, count) pairs of the entries of A on G whose name is not drained are, up to order, the (name, outCount Xp t) pairs of the transitions t of the net whose name is not drained and with outCount Xp t at least 2;"
          "for every graph G and entry e of A on G, an index i is in e's taken list exactly when some edge of G fires the label of e's transition with index i, the label being complete:<t> when G splits the transition (an edge fires complete:<t>, or a class marks inflight:<t>) and its own name otherwise;"
          "for every graph G and entry e of A on G, an index i is in e's untaken list exactly when i is below e's count and not in e's taken list;"
          "for every key-equivariant explorer E labelled with (transition, outcome) pairs, every reading fl of the in-flight places of a state, and every build of the graph layer at E that is closed: for every entry e of A on the graph of that build, an index i is in e's untaken list exactly when i is below e's count and no state reachable from the initial state fires e's label with outcome i."
  assumes "The analysis is graph-relative (ruling D94 (a)): it reads the graph it is handed, closed or truncated, and reports which outcomes that graph's edges take. All three runtimes do so and report no completeness of their own (analyzer.rs:341-376, TimePetriNetAnalyzer.java:325-372, time-petri-net-analyzer.ts:258-300); the caller reads the graph's isComplete. Line 4 is the reading on a closed graph, and it follows from lines 2 and 3 for any analysis at any key-equivariant explorer (VER_021_closed_of, from taken_complete of the graph layer), so its mutants are those of line 2 (VER_021_forbids_startNameClosed). On a truncated graph an untaken outcome may fire beyond the class budget: VER_021_nonvacuous reports both outcomes of t untaken on the graph truncated at two classes, which is not closed, and both taken on the closed one. A truncated graph never makes a taken outcome false: every edge of any build is a step of a reachable state (taken_sound of the graph layer)."
          "The graph is abstract: an explorer of the graph layer whose labels are a transition name and an outcome index, built by Novel.RouteB.Decide.build (breadth-first, class budget tested when a class is taken from the worklist, every successor stored), the shape of StateClassGraph.build (state_class_graph.rs:179-256). All three runtimes analyse a StateClassGraph, the timed state class graph of VER-010; its class-key explorer is the timed key layer of this wave (Spec/Verifier/Scg.lean), and line 4 holds for it once that explorer is shown key-equivariant, which is open (an item of the graph layer, not of the analysis: line 4 follows from lines 2 and 3 at any key-equivariant explorer). The reading of a state's in-flight places (fl) is a parameter: the graph marks inflight:<t> when some stored class does."
          "Line 2's split rule is Rust's: an edge fires complete:<t> or a class marks inflight:<t> (analyzer.rs:352-356; TypeScript the same, time-petri-net-analyzer.ts:267-273). Java iterates the transitions of the graph's own net and keys the entries of complete:<t> by t (TimePetriNetAnalyzer.java:333, :362-369), so it reads complete:<t> exactly when the graph's net is split. The two agree: the start of a split transition deposits into inflight:<t>, and the builder stores every successor, so a graph that fires the start marks the place, and a graph that never fires it has no edge of either label. A reading under the start name is killed (VER_021_forbids_startName on a hand-written graph, VER_021_forbids_startNameClosed on a closed build), so is one that counts the start edges of a split transition too (VER_021_forbids_startEdges), and one whose split test looks at completion edges and not at the in-flight mark (VER_021_forbids_edgesOnlySplit)."
          "Line 1 counts outcomes, not only XOR branches (ruling D20, clash ver-d#4): a transition with one branch and a timeout outcome that deposits differently has two outcomes and is reported, as branch_outcomes::outcomes counts it in every runtime (analyzer.rs:347-350, BranchOutcomes.outcomes, branch-outcomes.ts). An analysis that counts the action branches alone is killed on such a transition (VER_021_forbids_actionOnly), and an untaken list that stops before the timeout outcome is killed by line 3 (VER_021_forbids_untakenActions). The count is VER-001's expansion Xp, and the two blocks hold together of one expansion (VER_021_joint); any expansion that meets VER-001 gives every transition without a drained forward the reference count (VER_021_outCount_of_VER_001), so an empty expansion, under which line 1 asks for nothing, breaks VER-001. The order of the entries is not a line (the lines compare up to order): Rust follows the net's transitions, Java the graph net's, in which complete:<t> may stand elsewhere. A drained forward ([IO-014]) is set aside by name in line 1: VER-001 gives it no expansion, and the runtimes report it with the count of branch_outcomes::outcomes, whose Drained deposit the reference rows do not model (the graph routes count its batch exactly, Novel/TransferRows.lean); lines 2 and 3 still bind its entry when one is reported. Every other transition of such a net is bound: an analysis that reports nothing for a net holding a drained forward, as the net-wide guard of the linear routes (branch_outcomes.rs drained_forward) would, is killed (VER_021_forbids_netWide)."
          "Taken indices are read raw from the edges (line 2 has no bound, and the markdown says so): all three runtimes insert every branch index of a matching edge; a builder that fires a transition only with its own outcomes puts no index above the count there."
          "AC1 (every outcome is expanded into a separate virtual transition) is VER-001's expansion, the line 1 count and VER-001's lines 3 to 5 (VER_021_joint shares Xp); that the graph builder fires each virtual transition as its own edge is the builder's (expand_transition in state_class_graph.rs), the explorer's labels here."
          "AC2 (an outcome no edge of the graph fires is reported untaken; on a closed graph it is one no run fires) is lines 2, 3 and 4. The test derivation is checked by VER_021_nonvacuous: on the closed graph the reachable XOR transition t reports both outcomes taken and the never-enabled u both untaken; at two classes the graph is truncated and t's outcomes are reported untaken; a split transition is read off complete:t. The other test-derivation cases are the forbids theorems: a start edge alone takes no outcome (VER_021_forbids_startEdges), an in-flight mark splits before any completion fires (VER_021_forbids_edgesOnlySplit), and a XOR transition beside a drained forward is reported (VER_021_forbids_netWide). The former test derivation (one branch structurally unreachable beside a reachable one) cannot be met on a closed graph whose semantics fires every outcome of an enabled transition from the same states (VER_021_together): the build loop of the timed graph expands every outcome of a firing clock from the same class and drops a successor only when its zone is empty (state_class_graph.rs:206-222). That the zone of the successor is empty for no outcome when it is non-empty for one is the open lemma from sat_fireMat under TimingWF (Novel/TimedScg/Zone.lean), not proved here."
          "The report text (XorBranchAnalysis.report, 'All XOR branches are reachable.'), is_xor_complete, unreachable_branches and the record fields are kind Q or N. Python exposes no XOR branch analysis (the binding has none), so the block binds Java, TypeScript and Rust. VER-021 is SHOULD; its shall sentences bind an implementation that offers the analysis (ruling D22)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], ExpandFn N → XorAnalysis N → Prop :=
    fun Xp A =>
      ∀ net : Reference.Net _,
        (∀ G, (((A net G).filter fun e => !drainedNamed net e.name).map
              fun e => (e.name, e.total)).Perm
            ((net.transitions.filter fun t =>
                !drainedNamed net t.core.name && decide (2 ≤ outCount Xp t)).map fun t =>
              (t.core.name, outCount Xp t))) ∧
        (∀ G, ∀ e ∈ A net G, ∀ i, i ∈ e.taken ↔ G.Fires (G.label e.name) i) ∧
        (∀ G, ∀ e ∈ A net G, ∀ i, i ∈ e.untaken ↔ i < e.total ∧ i ∉ e.taken) ∧
        (∀ (S K : Type) [DecidableEq K] (E : Explorer S K (String × ℕ)), E.Equivariant →
          ∀ (fl : S → String → Bool) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool)
            (fuel : ℕ) (x0 : S), (Decide.build E n cut bad stopAt fuel x0).complete = true →
            ∀ e ∈ A net (graphView E fl (Decide.build E n cut bad stopAt fuel x0)), ∀ i,
              i ∈ e.untaken ↔ i < e.total ∧
                ¬ ExplFires E x0
                  ((graphView E fl (Decide.build E n cut bad stopAt fuel x0)).label e.name) i)

/- The pinned readable form of VER-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_021 : {N : Type} → [DecidableEq N] → ExpandFn N → XorAnalysis N → Prop :=
fun {N} [inst : DecidableEq N] Xp A =>
  ∀ (net : Reference.Net N),
    (∀ (G : XorGraph),
        (List.map (fun e => (e.name, e.total)) (List.filter (fun e => !drainedNamed net e.name) (A net G))).Perm
          (List.map (fun t => (t.core.name, outCount Xp t))
            (List.filter (fun t => !drainedNamed net t.core.name && decide (2 ≤ outCount Xp t)) net.transitions))) ∧
      (∀ (G : XorGraph), ∀ e ∈ A net G, ∀ (i : ℕ), i ∈ e.taken ↔ G.Fires (G.label e.name) i) ∧
        (∀ (G : XorGraph), ∀ e ∈ A net G, ∀ (i : ℕ), i ∈ e.untaken ↔ i < e.total ∧ i ∉ e.taken) ∧
          ∀ (S K : Type) [inst : DecidableEq K] (E : Explorer S K (String × ℕ)),
            E.Equivariant →
              ∀ (fl : S → String → Bool) (n : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (fuel : ℕ) (x0 : S),
                (Decide.build E n cut bad stopAt fuel x0).complete = true →
                  ∀ e ∈ A net (graphView E fl (Decide.build E n cut bad stopAt fuel x0)),
                    ∀ (i : ℕ),
                      i ∈ e.untaken ↔
                        i < e.total ∧
                          ¬ExplFires E x0 ((graphView E fl (Decide.build E n cut bad stopAt fuel x0)).label e.name) i
-/
#guard_msgs in #print VER_021

/-! ## The closed-graph line follows from lines 2 and 3 -/

/-- On a closed build at a key-equivariant explorer, an edge of the graph fires a label with an
outcome exactly when some run of the explorer does. -/
theorem graphView_fires {S K : Type} [DecidableEq K] {E : Explorer S K (String × ℕ)}
    (hE : E.Equivariant) (fl : S → String → Bool) {n : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true) (l : String) (i : ℕ) :
    (graphView E fl (Decide.build E n cut bad stopAt fuel x0)).Fires l i ↔ ExplFires E x0 l i := by
  have h := taken_complete hE hc (l, i)
  simp only [ExplFires]
  rw [← h]
  simp only [XorGraph.Fires, graphView, taken, List.mem_map]
  constructor
  · rintro ⟨a, b, he⟩
    exact ⟨(a, (l, i), b), he, rfl⟩
  · rintro ⟨⟨a, li, b⟩, he, hli⟩
    simp only at hli
    subst hli
    exact ⟨a, b, he⟩

/-- **The closed-graph line is the reading of lines 2 and 3.** Any analysis that reads taken
outcomes off the edges (line 2) and reports the rest below the count as untaken (line 3) reports,
on a closed graph, exactly the outcomes no run fires. Example: on the closed graph of a net
whose transition `u` never becomes enabled, `u`'s outcomes are untaken because no reachable
class fires `u`. -/
theorem VER_021_closed_of {N : Type} [DecidableEq N] {A : XorAnalysis N} {net : Reference.Net N}
    (h2 : ∀ G, ∀ e ∈ A net G, ∀ i, i ∈ e.taken ↔ G.Fires (G.label e.name) i)
    (h3 : ∀ G, ∀ e ∈ A net G, ∀ i, i ∈ e.untaken ↔ i < e.total ∧ i ∉ e.taken)
    {S K : Type} [DecidableEq K] {E : Explorer S K (String × ℕ)} (hE : E.Equivariant)
    (fl : S → String → Bool) {n : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (e : XorEntry) (he : e ∈ A net (graphView E fl (Decide.build E n cut bad stopAt fuel x0)))
    (i : ℕ) :
    i ∈ e.untaken ↔ i < e.total ∧
      ¬ ExplFires E x0 ((graphView E fl (Decide.build E n cut bad stopAt fuel x0)).label e.name) i := by
  rw [h3 _ e he, h2 _ e he, graphView_fires hE fl hc]

/-! ## The reference -/

/-- ✓ **The reference analysis meets VER-021.** Example: for the transition `t : p0 → p1 xor
p2`, `refXor` reports `t` with two outcomes; on a graph whose edges fire `t` with outcome 0
only, outcome 0 is taken and outcome 1 untaken; on a graph that splits `t` in flight it reads
the edges of `complete:t` instead. -/
@[evidence holds VER_021]
theorem VER_021_reference {N : Type} [DecidableEq N] : VER_021 (refVirtual (N := N)) refXor := by
  intro net
  have h2 : ∀ G, ∀ e ∈ refXor net G, ∀ i, i ∈ e.taken ↔ G.Fires (G.label e.name) i := by
    intro G e he i
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp he
    exact refXorTaken_mem G _ i
  have h3 : ∀ G, ∀ e ∈ refXor net G, ∀ i, i ∈ e.untaken ↔ i < e.total ∧ i ∉ e.taken := by
    intro G e he i
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp he
    simp [refXorEntry]
  refine ⟨fun G => ?_, h2, h3, fun S K _ E hE fl n cut bad stopAt fuel x0 hcl e he i =>
    VER_021_closed_of h2 h3 hE fl hcl e he i⟩
  apply List.Perm.of_eq
  simp only [refXor, List.filter_map, List.map_map, List.filter_filter, Function.comp_def,
    refXorEntry]
  have hf : net.transitions.filter
        (fun t => !drainedNamed net t.core.name && decide (2 ≤ (refVirtualRows t).length)) =
      net.transitions.filter
        (fun t => !drainedNamed net t.core.name && decide (2 ≤ outCount refVirtual t)) := by
    apply List.filter_congr
    intro t ht
    cases hn : drainedNamed net t.core.name with
    | true => rfl
    | false => simp [outCount_refVirtual (not_drained_of_drainedNamed ht hn)]
  rw [hf]
  apply List.map_congr_left
  intro t ht
  have ⟨htm, hb⟩ := List.mem_filter.mp ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
  rw [outCount_refVirtual (not_drained_of_drainedNamed htm hb.1)]

/-- ✓ **One expansion for VER-001 and VER-021.** Example: VER-001's reference verified net and
expansion, and `refXor` counting outcomes by that expansion, meet both blocks at once: the
outcome count of a transition in the XOR report is its number of virtual transitions. -/
@[evidence consistent VER_001 VER_021]
theorem VER_021_joint {N : Type} [DecidableEq N] :
    ∃ (VN : VerifiedNetFn N) (Xp : ExpandFn N) (A : XorAnalysis N), VER_001 VN Xp ∧ VER_021 Xp A :=
  ⟨refVerifiedNet, refVirtual, refXor, VER_001_reference, VER_021_reference⟩

/-! ## Worked examples -/

/-- The successors of a reference marking with the outcome index on the label: every enabled
transition, every outcome, in the order of `Reference.succ` (`state_class_graph.rs` fires the
virtual transitions of each enabled clock the same way). -/
def branchSucc {K : Type} [LinearOrder K] (net : Reference.Net K) (m : Reference.Marking K) :
    List ((String × ℕ) × Reference.Marking K) :=
  net.transitions.flatMap fun t =>
    if Novel.Seam.enabledNA (Reference.get m) t.core then
      ((Reference.outcomesB (Novel.Seam.nconsumed (Reference.get m) t.core) t.out).zipIdx).map
        fun bi => ((t.core.name, bi.2), Reference.fire m t.core bi.1)
    else []

/-- `a : p6 → p0`, one outcome. -/
def ver021A : Reference.Trans Nat :=
  { core := { name := "a", inputs := [⟨6, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- `t : p0 → p1 xor p2`, two outcomes. -/
def ver021T : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 1) (.place 2)) }

/-- `u : p3 → p4 xor p5`, two outcomes; nothing ever marks `p3`. -/
def ver021U : Reference.Trans Nat :=
  { core := { name := "u", inputs := [⟨3, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 4) (.place 5)) }

/-- The test-derivation net: `a`, then the XOR transition `t`; `u` is never enabled. -/
def ver021Net : Reference.Net Nat :=
  { places := [0, 1, 2, 3, 4, 5, 6], transitions := [ver021A, ver021T, ver021U] }

/-- The graph of the test-derivation net from `{p6: 1}` at a class budget, as the analysis reads
it (no transition in flight). -/
def ver021Graph (n : ℕ) : XorGraph :=
  graphView (idExplorer (branchSucc ver021Net)) (fun _ _ => false)
    (buildD (idExplorer (branchSucc ver021Net)) n (fun _ => false) (fun _ => false) false 20
      [(6, 1)])

/-- A graph of the net that splits `t` in flight: the start `t` leads to a class that marks
`inflight:t`, and the completion `complete:t` fires both outcomes from there. -/
def ver021SplitG : XorGraph :=
  { edges := [(0, ("t", 0), 1), (1, ("complete:t", 0), 2), (1, ("complete:t", 1), 3)],
    inFlight := fun s => s == "t" }

/-- The net holding `t` alone. -/
def ver021NetT : Reference.Net Nat := { places := [0, 1, 2], transitions := [ver021T] }

/-- ✓ **The test derivation, worked.** Example: from `{p6: 1}`, `a` puts a token on `p0`, and
`t` then fires either way. At a budget of 10 the graph closes with four classes: `t` reports
outcomes 0 and 1 taken, and `u`, which nothing enables, reports both untaken. At a budget of 2
the graph is cut off before `t` fires: it is not complete, and `t`'s outcomes are reported
untaken too, which is why the caller reads completeness. On a graph that splits `t` in flight,
both outcomes are read off `complete:t`. -/
@[evidence nonvacuous VER_021]
theorem VER_021_nonvacuous :
    refXor ver021Net (ver021Graph 10) = [⟨"t", 2, [0, 1], []⟩, ⟨"u", 2, [], [0, 1]⟩] ∧
    (buildD (idExplorer (branchSucc ver021Net)) 10 (fun _ => false) (fun _ => false) false 20
      [(6, 1)]).complete = true ∧
    refXor ver021Net (ver021Graph 2) = [⟨"t", 2, [], [0, 1]⟩, ⟨"u", 2, [], [0, 1]⟩] ∧
    (buildD (idExplorer (branchSucc ver021Net)) 2 (fun _ => false) (fun _ => false) false 20
      [(6, 1)]).complete = false ∧
    refXor ver021NetT ver021SplitG = [⟨"t", 2, [0, 1], []⟩] := by
  decide

/-! ## Wrong analyses, one per line -/

/-- `w : 2·p0 → p1` with only a `Timeout` that forwards the input: one action branch, which
deposits one token in `p1`, and a timeout outcome that forwards both tokens, which deposits
two. The two outcomes differ, so `w` has two outcomes ([VER-001] AC4). -/
def ver021W : Reference.Trans Nat :=
  { core :=
      { name := "w", inputs := [⟨0, .exactly 2⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.timeout (.forward 0 1)) }

/-- The net holding `w` alone. -/
def ver021NetW : Reference.Net Nat := { places := [0, 1], transitions := [ver021W] }

/-- The graph with no edge and nothing in flight. -/
def ver021Empty : XorGraph := { edges := [], inFlight := fun _ => false }

/-- Mutant: an analysis that counts the XOR branches and not the timeout outcome. -/
def ver021_actionOnly : XorAnalysis Nat := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (ver001_actionRows t).length)).map fun t =>
    refXorEntry G t.core.name (ver001_actionRows t).length

/-- ✗ **The timeout outcome counts** (line 1). Example: `w` has one action branch and a timeout
outcome that deposits two tokens where the branch deposits one; it has two outcomes, so the
report must list it, but an analysis that counts only the XOR branches sees one and leaves it
out. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_actionOnly : ¬ VER_021 refVirtual ver021_actionOnly := by
  intro h
  have h1 := (h ver021NetW).1 ver021Empty
  revert h1
  decide

/-- The taken indices read under the transition's own name, never `complete:<t>`. -/
def ver021_startTaken (G : XorGraph) (name : String) : List ℕ :=
  (G.edges.filterMap fun e => if e.2.1.1 = name then some e.2.1.2 else none).dedup

/-- Mutant: an analysis that reads a split transition under its start name. -/
def ver021_startName : XorAnalysis Nat := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (refVirtualRows t).length)).map fun t =>
    { name := t.core.name, total := (refVirtualRows t).length,
      taken := ver021_startTaken G t.core.name,
      untaken := (List.range (refVirtualRows t).length).filter
        fun i => decide (i ∉ ver021_startTaken G t.core.name) }

/-- ✗ **A split transition is read off its completion** (line 2). Example: on a graph that splits
`t` in flight, the start `t` fires with index 0 (its only outcome) and `complete:t` fires with
outcomes 0 and 1. Reading `t`'s outcomes under the start name reports outcome 1 untaken, though
an edge of `complete:t` takes it. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_startName : ¬ VER_021 refVirtual ver021_startName := by
  intro h
  have he : (⟨"t", 2, [0], [1]⟩ : XorEntry) ∈ ver021_startName ver021NetT ver021SplitG := by
    decide
  have h2 := (h ver021NetT).2.1 ver021SplitG _ he 1
  revert h2
  decide

/-- The labelled successors of a net split in flight, by hand: `t` starts from class 0 into
class 1, which holds `t` in flight, and `complete:t` ends it either way. -/
def ver021SplitSucc : ℕ → List ((String × ℕ) × ℕ)
  | 0 => [(("t", 0), 1)]
  | 1 => [(("complete:t", 0), 2), (("complete:t", 1), 3)]
  | _ => []

/-- Class 1 marks `inflight:t`. -/
def ver021SplitFl : ℕ → String → Bool := fun x s => x == 1 && s == "t"

/-- ✗ **On a closed graph an untaken outcome fires in no run** (line 4). Example: the split graph
closes with four classes, and the run `t`, `complete:t` (second outcome) fires outcome 1 of
`complete:t`; an analysis that reads `t` under its start name still reports outcome 1
untaken. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_startNameClosed : ¬ VER_021 refVirtual ver021_startName := by
  intro h
  have hb : Decide.build (idExplorer ver021SplitSucc) 10 (fun _ => false) (fun _ => false) false
      20 0 = buildD (idExplorer ver021SplitSucc) 10 (fun _ => false) (fun _ => false) false 20 0 :=
    (buildD_eq _ _ _ _ _ _ _).symm
  have hc : (Decide.build (idExplorer ver021SplitSucc) 10 (fun _ => false) (fun _ => false) false
      20 0).complete = true := by
    rw [hb]; decide
  have he : (⟨"t", 2, [0], [1]⟩ : XorEntry) ∈ ver021_startName ver021NetT
      (graphView (idExplorer ver021SplitSucc) ver021SplitFl
        (Decide.build (idExplorer ver021SplitSucc) 10 (fun _ => false) (fun _ => false) false
          20 0)) := by
    rw [hb]; decide
  have hl : (graphView (idExplorer ver021SplitSucc) ver021SplitFl
      (Decide.build (idExplorer ver021SplitSucc) 10 (fun _ => false) (fun _ => false) false
        20 0)).label "t" = "complete:t" := by
    rw [hb]; decide
  have h4 := ((h ver021NetT).2.2.2 ℕ ℕ (idExplorer ver021SplitSucc)
    (idExplorer_equivariant _) ver021SplitFl 10 (fun _ => false) (fun _ => false) false 20 0 hc
    _ he 1).mp (by decide)
  apply h4.2
  rw [hl]
  refine ⟨1, 0, 3, Explorer.Reach.step (c := 0) (l := ("t", 0)) Explorer.Reach.init le_rfl ?_,
    le_rfl, ?_⟩ <;> decide

/-- Mutant: an analysis whose untaken list stops before the timeout outcome. -/
def ver021_untakenActions : XorAnalysis Nat := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (refVirtualRows t).length)).map fun t =>
    { refXorEntry G t.core.name (refVirtualRows t).length with
      untaken := (List.range (ver001_actionRows t).length).filter
        fun i => decide (i ∉ refXorTaken G t.core.name) }

/-- ✗ **Every outcome below the count is taken or untaken** (line 3). Example: on a graph with no
edge, `w`'s two outcomes are both untaken; an analysis that lists untaken indices only up to
the action branches reports outcome 0 and leaves the timeout outcome 1 out of both lists. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_untakenActions : ¬ VER_021 refVirtual ver021_untakenActions := by
  intro h
  have he : (⟨"w", 2, [], [0]⟩ : XorEntry) ∈ ver021_untakenActions ver021NetW ver021Empty := by
    decide
  have h3 := (h ver021NetW).2.2.1 ver021Empty _ he 1
  revert h3
  decide

/-- `d : all(p5) → p6 xor timeout(forward p5 → p7)`, a drained forward: its timeout outcome
forwards every token the `All` input drained ([IO-014]). -/
def ver021D : Reference.Trans Nat :=
  { core := { name := "d", inputs := [⟨5, .all⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 6) (.timeout (.forward 5 7))) }

/-- The XOR transition `t` beside the unrelated drained forward `d`. -/
def ver021NetTD : Reference.Net Nat :=
  { places := [0, 1, 2, 5, 6, 7], transitions := [ver021T, ver021D] }

/-- Mutant: an analysis that reports nothing for a net holding a drained forward, the net-wide
guard of the linear routes (`branch_outcomes.rs` `drained_forward`), and is the reference on
every other net. -/
def ver021_netWide : XorAnalysis Nat := fun net G =>
  if net.transitions.any fun t => decide (DrainedForward t) then [] else refXor net G

/-- ✗ **A drained forward does not hide the rest of the net** (line 1). Example: the net holds
the XOR transition `t` and, beside it, the drained forward `d`. `t` has two outcomes and is no
drained forward, so the report must list it; an analysis that gives up on the whole net because
of `d` reports nothing. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_netWide : ¬ VER_021 refVirtual ver021_netWide := by
  intro h
  have h1 := (h ver021NetTD).1 ver021Empty
  revert h1
  decide

/-- The taken indices read under the start name and under `complete:<t>` both. -/
def ver021_bothTaken (G : XorGraph) (name : String) : List ℕ :=
  (G.edges.filterMap fun e =>
    if e.2.1.1 = name ∨ e.2.1.1 = completionName name then some e.2.1.2 else none).dedup

/-- Mutant: an analysis that counts the edges of the start `t` and of `complete:t` alike for
`t`. -/
def ver021_startEdges : XorAnalysis Nat := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (refVirtualRows t).length)).map fun t =>
    { name := t.core.name, total := (refVirtualRows t).length,
      taken := ver021_bothTaken G t.core.name,
      untaken := (List.range (refVirtualRows t).length).filter
        fun i => decide (i ∉ ver021_bothTaken G t.core.name) }

/-- A graph that splits `t`: the start fires (with index 0, its only outcome), and the
completion fires only outcome 1. -/
def ver021SplitG1 : XorGraph :=
  { edges := [(0, ("t", 0), 1), (1, ("complete:t", 1), 2)], inFlight := fun s => s == "t" }

/-- ✗ **A start edge takes no outcome** (line 2). Example: on a graph that splits `t`, the
start `t` always fires with index 0, and here `complete:t` fires only outcome 1. Outcome 0 is
untaken, but an analysis that counts the start edges too reports it taken. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_startEdges : ¬ VER_021 refVirtual ver021_startEdges := by
  intro h
  have he : (⟨"t", 2, [0, 1], []⟩ : XorEntry) ∈ ver021_startEdges ver021NetT ver021SplitG1 := by
    decide
  have h2 := (h ver021NetT).2.1 ver021SplitG1 _ he 0
  revert h2
  decide

/-- The label of `t` when only a completion edge splits it, never the in-flight mark. -/
def ver021_edgesOnlyLabel (G : XorGraph) (t : String) : String :=
  if G.edges.any (fun e => e.2.1.1 == completionName t) then completionName t else t

/-- The taken indices under `ver021_edgesOnlyLabel`. -/
def ver021_edgesOnlyTaken (G : XorGraph) (name : String) : List ℕ :=
  (G.edges.filterMap fun e =>
    if e.2.1.1 = ver021_edgesOnlyLabel G name then some e.2.1.2 else none).dedup

/-- Mutant: an analysis whose split test looks at the completion edges and ignores the
in-flight mark `inflight:<t>`. -/
def ver021_edgesOnlySplit : XorAnalysis Nat := fun net G =>
  (net.transitions.filter fun t => decide (2 ≤ (refVirtualRows t).length)).map fun t =>
    { name := t.core.name, total := (refVirtualRows t).length,
      taken := ver021_edgesOnlyTaken G t.core.name,
      untaken := (List.range (refVirtualRows t).length).filter
        fun i => decide (i ∉ ver021_edgesOnlyTaken G t.core.name) }

/-- A graph where `t` has started, a class marks `inflight:t`, and no completion has fired. -/
def ver021StartedG : XorGraph :=
  { edges := [(0, ("t", 0), 1)], inFlight := fun s => s == "t" }

/-- ✗ **The in-flight mark splits a transition** (line 2). Example: `t` has started and a
class holds it in flight, but `complete:t` has not fired yet. The outcomes are those of
`complete:t`, so none is taken; an analysis that splits only on a completion edge reads the
start edge and reports outcome 0 taken. -/
@[evidence forbids VER_021]
theorem VER_021_forbids_edgesOnlySplit : ¬ VER_021 refVirtual ver021_edgesOnlySplit := by
  intro h
  have he : (⟨"t", 2, [0], [1]⟩ : XorEntry) ∈ ver021_edgesOnlySplit ver021NetT ver021StartedG := by
    decide
  have h2 := (h ver021NetT).2.1 ver021StartedG _ he 0
  revert h2
  decide

/-! ## The count is VER-001's -/

/-- **An expansion that meets VER-001 fixes the number of outcomes.** Whatever expansion an
implementation pairs with its analysis, if it meets VER-001 then every transition without a
drained forward gets as many virtual transitions as the reference gives it. Example: `t : p0 →
p1 xor p2` gets two, so line 1 asks the analysis to report `t` with two outcomes. An expansion
that gives no transition any virtual transition, under which line 1 asks for nothing, fails
VER-001. -/
@[evidence cites "VER-021" "the number of outcomes is that of the virtual transitions of VER-001"]
theorem VER_021_outCount_of_VER_001 {N : Type} [DecidableEq N] {VN : VerifiedNetFn N}
    {Xp : ExpandFn N} (h : VER_001 VN Xp) {t : Reference.Trans N} (ht : ¬ DrainedForward t) :
    outCount Xp t = (refVirtualRows t).length := by
  obtain ⟨rows, hx, acts, tos, hr, ha, hto⟩ := h.2.2.1 t ht
  have hu := VER_001_rows_unique hr ha hto
  simp only [outCount, hx, Option.getD_some]
  simpa using hu.length_eq

/-! ## Outcomes of one transition fire together -/

/-- **On a closed graph whose semantics fires every outcome together, a transition's outcomes
are all taken or all untaken.** Suppose every state that fires a label with one outcome fires it
with every outcome below that label's count. Then, on a closed graph, an analysis meeting
VER-021 reports a transition either with no untaken outcome or with every outcome untaken.
Example: in the test-derivation net, `t` fires both ways from the class `{p0: 1}`, so the closed
graph takes both of its outcomes; `u` is never enabled, so it takes neither. A net "where one
branch is structurally unreachable" beside a reachable one does not exist for such a graph: an
untaken outcome on a closed graph marks a transition that never fires. -/
@[evidence cites "VER-021" "test derivation: one XOR branch unreachable beside a reachable one"]
theorem VER_021_together {N : Type} [DecidableEq N] {Xp : ExpandFn N} {A : XorAnalysis N}
    (h : VER_021 Xp A) {net : Reference.Net N}
    {S K : Type} [DecidableEq K] {E : Explorer S K (String × ℕ)} (hE : E.Equivariant)
    (fl : S → String → Bool) {n : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (cnt : String → ℕ)
    (hT : ∀ y c l i s j, ((l, i), s) ∈ E.succ c y → j < cnt l → ∃ s', ((l, j), s') ∈ E.succ c y)
    (e : XorEntry) (he : e ∈ A net (graphView E fl (Decide.build E n cut bad stopAt fuel x0)))
    (hcnt : e.total ≤ cnt ((graphView E fl (Decide.build E n cut bad stopAt fuel x0)).label e.name)) :
    (∀ i, i ∉ e.untaken) ∨ (∀ i, i < e.total → i ∈ e.untaken) := by
  have h4 := (h net).2.2.2 S K E hE fl n cut bad stopAt fuel x0 hc e he
  set l := (graphView E fl (Decide.build E n cut bad stopAt fuel x0)).label e.name
  by_cases hf : ∃ i0, ExplFires E x0 l i0
  · left
    obtain ⟨i0, y, c, s, hy, hb, hs⟩ := hf
    intro i hi
    obtain ⟨hlt, hn⟩ := (h4 i).mp hi
    obtain ⟨s', hs'⟩ := hT y c l i0 s i hs (by omega)
    exact hn ⟨y, c, s', hy, hb, hs'⟩
  · right
    intro i hi
    exact (h4 i).mpr ⟨hi, fun hfi => hf ⟨i, hfi⟩⟩

end Libpetri.Spec
