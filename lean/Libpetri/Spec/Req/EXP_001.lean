import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_001

set_option linter.missingDocs true

/-!
# EXP-001: Graph export format (`spec/09-export.md`)

Which nodes and edges an export draws for a net: every place an arc touches and every transition
gets exactly one node, no node stands for a place or a transition the net does not have, and
every arc gets an edge between the nodes of its place and its transition (as many input,
inhibitor and read edges as arcs). The requirement is a predicate over an abstract exporter
`E : Exporter` (glossary `GlossaryExport.lean`): from a configuration and the export view of a
net, the typed graph the runtimes build before DOT text. The arcs are read with the glossary's
arc predicates over the firing view `ExportTrans.toTrans` (`inPlaces`, `OutputArc`,
`InhibitorArc`, `ReadArc`, `ResetArc`), so they are the arcs the firing relations fire on.

The witness is the reference exporter `refExportWith S` (`Reference/Export.lean`) for every
cluster stage `S` (`EXP_001_any`); the holds evidence is its instance at the reference cluster
stage, the clustered exporter `refExport`. The wrong exporters are the ones a mapper that derives its nodes or edges from
the wrong source would produce, one or more per line: place nodes for the input and output
places only, one place node per arc end, a transition node only for a transition with an arc
(the nodes DOT creates implicitly from edges), a node for a place or a transition the net does
not have, no input, inhibitor or read edges, input edges drawn from the transition to the place,
every place-to-transition edge drawn twice, output edges drawn from another transition's node,
the reset places read net-wide (an output edge drawn as a combined reset+output edge for a
transition that does not reset the place), no standalone reset edges, and a standalone reset
edge drawn as an output edge or as a combined edge.

Ruling D60 (c): the set of place nodes is stated in its common form. Rust draws a node for every
place the net declares, Java and TypeScript only for the places some arc touches; the block asks
for the touched places and allows the declared ones, so both shapes satisfy it
(`EXP_001_allows_arcDerived`), and a declared place that no arc touches is left open
(`EXP_001_untouched_open`). The two readings are recorded at the end of this file
(`exp001DeclaredReading`, `exp001TouchedOnlyReading`, `EXP_001_placeSet`); the end state of
D60 (a), a node for every declared place, is the reference's answer.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## What the block reads off a drawn graph -/

/-- The number of edges of arc type `a` from the node of place `p` to the node of transition `t`
in graph `g`. -/
def exp001Drawn (g : XGraph) (a : ArcType) (p t : String) : Nat :=
  g.edges.countP fun e => decide (e.arc = a ∧ e.src = .place p ∧ e.dst = .trans t)

/-! ## EXP-001: Graph export format -/

requirement EXP_001
  id "EXP-001"
  title "Graph Export Format"
  kind F
  scope "every exporter, the nodes and the arc edges of one exported net"
  source verbatim "spec/09-export.md"
  covers EXP_001.s1, EXP_001.s2, EXP_001.s3, EXP_001.s4, EXP_001.s5, EXP_001.s6, EXP_001.s7,
        EXP_001.s8
  reading "For the exporter E, every configuration cfg and every net X:"
          "(1) every place p on which some transition t of X has an input arc, an output arc, an inhibitor arc, a read arc or a reset arc (the glossary predicates over the firing view t.toTrans) is the place of exactly one node of E cfg X;"
          "(2) if the transitions of X have pairwise distinct names, every transition t of X is the transition of exactly one node of E cfg X (keyed by its name);"
          "(3) every node of E cfg X that stands for a place p has p declared by X or has some transition of X with an input, output, inhibitor, read or reset arc on p, and every node that stands for a transition named u has a transition of X named u;"
          "(4) for every transition t of X and place p: an input arc, an inhibitor arc or a read arc of t on p has an edge of E cfg X of arc type input, inhibitor or read respectively, from the node of p to the node of t;"
          "(5) if the transitions of X have pairwise distinct names, then for every transition t of X and place p the number of edges of E cfg X of arc type input (inhibitor, read) from the node of p to the node of t is the number of times p occurs among the input places (inhibitor places, read places) of t;"
          "(6) an output arc of t on p (p named by t's output spec) has an edge of E cfg X into the node of p whose source is the node of t or a junction of t (NodeRef.owner? is t's name), of arc type output, or of arc type resetOutput when t also has a reset arc on p;"
          "(7) a reset arc of t on p has an edge of E cfg X into the node of p whose source is the node of t or a junction of t, of arc type reset, or of arc type resetOutput when t's output spec also names p."
  assumes "The model is an exporter E : Exporter (glossary): from a configuration and the export view of a net (glossary ExportNet: declared places, transitions with their input, inhibitor, read and reset arcs and their n-ary output tree, terminal places, membership), the typed graph (glossary XGraph: nodes with what they stand for, edges with their two ends and their arc type) the runtimes build before DOT text (the graph module of the Rust crate libpetri-export, graph.ts, the Java export/graph layer). The arcs are the glossary's arc predicates over the firing view ExportTrans.toTrans, which has the same arcs (ExportTrans.toTrans_core) and whose output arcs are the places the output tree's leaves name (ExportTrans.outputArc_iff), so the block speaks of the arcs the firing relations fire on."
          "AC1 (export produces valid, parseable output in the chosen format) is kind Q: the DOT text, its escaping and its grammar are not modelled, and the runtimes' renderer tests parse it. The canonical-format sentence of the body names DOT, which is what all three runtimes render the typed graph to; that the typed graph exists for every net is the block's model, a total function. The block's kind is F: its seven lines are the functional content of the requirement, and AC1 and the test derivation's parse check stay with the runtimes' tests."
          "AC2 (all places and transitions in the net are represented) is lines 1 to 3. A node is identified by what it stands for (glossary NodeRef: a place by its name, a transition by its name), not by its DOT ID; that two names map to two IDs is EXP-014's line under ruling D46, so a sanitising collision does not reach this block. Line 3 bounds the nodes from above: no node stands for a place that the net neither declares nor touches, or for a transition the net does not have (EXP_001_forbids_phantomPlace, EXP_001_forbids_phantomTrans). Junction nodes are not bounded here: which junctions an output tree has is EXP-012's, and that every junction an edge touches has a node is EXP-014's."
          "Ruling D60 (c): line 1 is the common form of the place set, and line 3 allows a node for every declared place. Rust draws a node for every place the net declares, Java and TypeScript only for the places some arc touches; a place that the net declares and that no arc touches may have a node or none (EXP_001_untouched_open), and both shapes satisfy the block (EXP_001_allows_arcDerived). The end state D60 (a), a node for every declared place, is the reference's answer; the line that asks for it waits for the Java and TypeScript mappers to change and is not encoded. The two readings are recorded in this file as candidate definitions, not requirement blocks (exp001DeclaredReading for D60 (a), exp001TouchedOnlyReading for D60 (b)), with EXP_001_placeSet: the reference meets the first and not the second, the Java and TypeScript shape the second and not the first. The markdown records the open case and the intended answer in a sentence without shall."
          "Lines 2 and 5 are stated for nets whose transitions have pairwise distinct names, as the timing requirements are (TIME-010): two transition instances that share a name are distinct under CORE-021, and all three mappers key a transition node by its name, so a net holding both draws one DOT ID for two transitions and the edges of both end at it. The exporter is not asked to draw anything particular for such a net beyond lines 1, 3, 4, 6 and 7."
          "AC3 (all arcs, input, output, inhibitor, read and reset, are represented) is lines 4 to 7. The direction of each edge is the runtimes' and EXP-004's (ruling D20): input, inhibitor and read edges run from the place to the transition (EXP_001_forbids_reversedInput), output and reset edges from the transition to the place. An output arc may be drawn from a junction of its transition (EXP-012); the edge's source is required to belong to the arc's own transition (NodeRef.owner?), so an exporter that draws the output of one transition from the node of another violates line 6 (EXP_001_forbids_foreignOutput). That a junction an edge leaves has a node is EXP-014's line, and that the junctions between the transition and the place form a path is EXP-012's and EXP-014's wiring line; neither is this block's."
          "An output arc and a reset arc of one transition on one place may be drawn as one combined reset+output edge (EXP-013). Lines 6 and 7 allow the combined arc type only where the transition has both arcs on the place, so an exporter that draws a plain output arc as a combined edge because another transition resets the place violates line 6 (EXP_001_forbids_globalResets), and one that draws a standalone reset arc as a combined edge violates line 7 (EXP_001_forbids_resetAsCombined). That the combined edge replaces the plain output edge and the standalone reset edge in exactly that case is EXP-013's line."
          "How many edges an arc gets: line 5 counts the input, inhibitor and read edges (one per arc, so an exporter that draws every such edge twice violates it, EXP_001_forbids_doubled); the output edges and the standalone reset edges of a transition into a place are counted by EXP-013 (one per leaf naming the place, one per reset arc on a place no leaf names), under the same distinct-names condition, and which output edges pass through which junctions is EXP-012's. Lines 4, 6 and 7 ask for at least one edge per arc. The labels (EXP-006, EXP-018), the style rows (EXP-004) and the categories of the nodes (EXP-002, EXP-003, EXP-008) are other blocks' lines. Ghost edges and clusters (EXP-016, EXP-017) add to the graph and are not read here; the block holds of the reference exporter with every cluster stage (EXP_001_any)."
          "The implementation notes name the format each runtime renders (DOT in all three) and the test derivation (a net with all arc types, exported and checked) is EXP_001_nonvacuous on the reference exporter: the worked net of EXP-013, which has every arc kind."
  signoff "2026-11-13 96ff8e5fe57ed0b0 ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (∀ t ∈ X.trans, ∀ p : String,
        (p ∈ inPlaces t.toTrans ∨ OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨
          ReadArc t.toTrans p ∨ ResetArc t.toTrans p) →
        (E cfg X).nodes.countP (fun n => decide (n.ref = .place p)) = 1) ∧
      ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
        (E cfg X).nodes.countP (fun n => decide (n.ref = .trans t.name)) = 1) ∧
      (∀ n ∈ (E cfg X).nodes,
        (∀ p : String, n.ref = .place p → p ∈ X.places ∨ ∃ t ∈ X.trans,
          p ∈ inPlaces t.toTrans ∨ OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨
            ReadArc t.toTrans p ∨ ResetArc t.toTrans p) ∧
        (∀ u : String, n.ref = .trans u → ∃ t ∈ X.trans, t.name = u)) ∧
      (∀ t ∈ X.trans, ∀ p : String,
        (p ∈ inPlaces t.toTrans → ∃ e ∈ (E cfg X).edges,
          e.arc = .input ∧ e.src = .place p ∧ e.dst = .trans t.name) ∧
        (InhibitorArc t.toTrans p → ∃ e ∈ (E cfg X).edges,
          e.arc = .inhibitor ∧ e.src = .place p ∧ e.dst = .trans t.name) ∧
        (ReadArc t.toTrans p → ∃ e ∈ (E cfg X).edges,
          e.arc = .read ∧ e.src = .place p ∧ e.dst = .trans t.name)) ∧
      ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans, ∀ p : String,
        exp001Drawn (E cfg X) .input p t.name = (inPlaces t.toTrans).count p ∧
        exp001Drawn (E cfg X) .inhibitor p t.name = t.toTrans.core.inhibitors.count p ∧
        exp001Drawn (E cfg X) .read p t.name = t.toTrans.core.reads.count p) ∧
      (∀ t ∈ X.trans, ∀ p : String, OutputArc t.toTrans p →
        ∃ e ∈ (E cfg X).edges, e.src.owner? = some t.name ∧
          (e.arc = .output ∨ (e.arc = .resetOutput ∧ ResetArc t.toTrans p)) ∧
          e.dst = .place p) ∧
      (∀ t ∈ X.trans, ∀ p : String, ResetArc t.toTrans p →
        ∃ e ∈ (E cfg X).edges, e.src.owner? = some t.name ∧
          (e.arc = .reset ∨ (e.arc = .resetOutput ∧ OutputArc t.toTrans p)) ∧
          e.dst = .place p)

/- The pinned readable form of EXP-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_001 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (∀ t ∈ X.trans,
        ∀ (p : String),
          p ∈ inPlaces t.toTrans ∨
              OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨ ReadArc t.toTrans p ∨ ResetArc t.toTrans p →
            List.countP (fun n => decide (n.ref = NodeRef.place p)) (E cfg X).nodes = 1) ∧
      ((List.map ExportTrans.name X.trans).Nodup →
          ∀ t ∈ X.trans, List.countP (fun n => decide (n.ref = NodeRef.trans t.name)) (E cfg X).nodes = 1) ∧
        (∀ n ∈ (E cfg X).nodes,
            (∀ (p : String),
                n.ref = NodeRef.place p →
                  p ∈ X.places ∨
                    ∃ t ∈ X.trans,
                      p ∈ inPlaces t.toTrans ∨
                        OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨ ReadArc t.toTrans p ∨ ResetArc t.toTrans p) ∧
              ∀ (u : String), n.ref = NodeRef.trans u → ∃ t ∈ X.trans, t.name = u) ∧
          (∀ t ∈ X.trans,
              ∀ (p : String),
                (p ∈ inPlaces t.toTrans →
                    ∃ e ∈ (E cfg X).edges,
                      e.arc = ArcType.input ∧ e.src = NodeRef.place p ∧ e.dst = NodeRef.trans t.name) ∧
                  (InhibitorArc t.toTrans p →
                      ∃ e ∈ (E cfg X).edges,
                        e.arc = ArcType.inhibitor ∧ e.src = NodeRef.place p ∧ e.dst = NodeRef.trans t.name) ∧
                    (ReadArc t.toTrans p →
                      ∃ e ∈ (E cfg X).edges,
                        e.arc = ArcType.read ∧ e.src = NodeRef.place p ∧ e.dst = NodeRef.trans t.name)) ∧
            ((List.map ExportTrans.name X.trans).Nodup →
                ∀ t ∈ X.trans,
                  ∀ (p : String),
                    exp001Drawn (E cfg X) ArcType.input p t.name = List.count p (inPlaces t.toTrans) ∧
                      exp001Drawn (E cfg X) ArcType.inhibitor p t.name = List.count p t.toTrans.core.inhibitors ∧
                        exp001Drawn (E cfg X) ArcType.read p t.name = List.count p t.toTrans.core.reads) ∧
              (∀ t ∈ X.trans,
                  ∀ (p : String),
                    OutputArc t.toTrans p →
                      ∃ e ∈ (E cfg X).edges,
                        e.src.owner? = some t.name ∧
                          (e.arc = ArcType.output ∨ e.arc = ArcType.resetOutput ∧ ResetArc t.toTrans p) ∧
                            e.dst = NodeRef.place p) ∧
                ∀ t ∈ X.trans,
                  ∀ (p : String),
                    ResetArc t.toTrans p →
                      ∃ e ∈ (E cfg X).edges,
                        e.src.owner? = some t.name ∧
                          (e.arc = ArcType.reset ∨ e.arc = ArcType.resetOutput ∧ OutputArc t.toTrans p) ∧
                            e.dst = NodeRef.place p
-/
#guard_msgs in #print EXP_001

/-! ### The reference -/

section Reference

variable {cfg : ExportCfg} {X : ExportNet}

/-- No transition node and no junction node stands for a place. -/
theorem exp001_countP_place_rest (p : String) :
    (X.trans.map (refTransNode cfg) ++ X.trans.flatMap refJunctionNodes).countP
      (fun n => decide (n.ref = .place p)) = 0 := by
  rw [List.countP_eq_zero]
  intro n hn
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, refJunctionNodes] at hn
  rcases hn with ⟨t, _, rfl⟩ | ⟨t, _, n', ⟨j, _, rfl⟩⟩ <;> simp [refTransNode, refJunctionNode]

/-- **Each place that gets a node gets exactly one**: the reference draws one node per name in
`refPlaceNames`, which has no repetition. -/
theorem exp001_refNodes_place {p : String} (hp : p ∈ refPlaceNames X) :
    (refNodes cfg X).countP (fun n => decide (n.ref = .place p)) = 1 := by
  rw [refNodes, List.append_assoc, List.countP_append, exp001_countP_place_rest, Nat.add_zero,
    List.countP_map]
  have : ((fun n : XNode => decide (n.ref = .place p)) ∘ refPlaceNode cfg X) = fun q => q == p := by
    funext q
    simp only [Function.comp_apply, refPlaceNode, NodeRef.place.injEq]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  rw [this, ← List.count]
  exact List.count_eq_one_of_mem refPlaceNames_nodup hp

/-- **Each transition gets exactly one node** when the names are distinct. -/
theorem exp001_refNodes_trans (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) :
    (refNodes cfg X).countP (fun n => decide (n.ref = .trans t.name)) = 1 := by
  have h1 : ((refPlaceNames X).map (refPlaceNode cfg X)).countP
      (fun n => decide (n.ref = .trans t.name)) = 0 := by
    rw [List.countP_eq_zero]
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨q, _, rfl⟩ := hn
    simp [refPlaceNode]
  have h3 : (X.trans.flatMap refJunctionNodes).countP
      (fun n => decide (n.ref = .trans t.name)) = 0 := by
    rw [List.countP_eq_zero]
    intro n hn
    simp only [List.mem_flatMap, refJunctionNodes, List.mem_map] at hn
    obtain ⟨u, _, j, _, rfl⟩ := hn
    simp [refJunctionNode]
  rw [refNodes, List.countP_append, List.countP_append, h1, h3, Nat.zero_add, Nat.add_zero,
    List.countP_map]
  have : ((fun n : XNode => decide (n.ref = .trans t.name)) ∘ refTransNode cfg) =
      fun u => u.name == t.name := by
    funext u
    simp only [Function.comp_apply, refTransNode, NodeRef.trans.injEq]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  have hc : X.trans.countP (fun u => u.name == t.name) = (X.trans.map ExportTrans.name).count t.name := by
    rw [List.count, List.countP_map]
    rfl
  rw [this, hc]
  exact List.count_eq_one_of_mem hX (List.mem_map_of_mem ht)

/-- **No phantom node**: a place node of the reference stands for a declared or touched place, a
transition node for a transition of the net. -/
theorem exp001_refNodes_bound {n : XNode} (hn : n ∈ refNodes cfg X) :
    (∀ p : String, n.ref = .place p → p ∈ X.places ∨ ∃ t ∈ X.trans,
      p ∈ inPlaces t.toTrans ∨ OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨
        ReadArc t.toTrans p ∨ ResetArc t.toTrans p) ∧
    (∀ u : String, n.ref = .trans u → ∃ t ∈ X.trans, t.name = u) := by
  rcases mem_refNodes.mp hn with ⟨q, hq, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, _, j, _, rfl⟩
  · refine ⟨fun p hp => ?_, fun u hu => by simp [refPlaceNode] at hu⟩
    simp only [refPlaceNode, NodeRef.place.injEq] at hp
    subst hp
    rcases mem_refPlaceNames.mp hq with h | ⟨t, ht, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, (ExportTrans.mem_touched t q).mp h⟩
  · refine ⟨fun p hp => by simp [refTransNode] at hp, fun u hu => ⟨v, hv, ?_⟩⟩
    simpa [refTransNode] using hu
  · exact ⟨fun p hp => by simp [refJunctionNode] at hp, fun u hu => by simp [refJunctionNode] at hu⟩

/-- The output side of a transition is drawn into every place its output spec names: some edge
of the reference emitter for `t` ends in `p`. -/
theorem exp001_refEmit_into {t : ExportTrans} {p : String} (hp : p ∈ t.outLeaves) :
    ∃ e ∈ (refEmit.ofTrans t).edges, e.dst = .place p := by
  rw [← refEmit_ofTrans_places, List.mem_filterMap] at hp
  obtain ⟨e, he, hd⟩ := hp
  refine ⟨e, he, ?_⟩
  unfold XEdge.placeTarget at hd
  cases h : e.dst with
  | place q => rw [h] at hd; simp [NodeRef.place?] at hd; rw [hd]
  | trans _ => rw [h] at hd; simp [NodeRef.place?] at hd
  | junction _ _ _ => rw [h] at hd; simp [NodeRef.place?] at hd

/-- The edges of one transition of arc type `a` (input, inhibitor or read) from place `p` to the
node of transition `t`: as many as `u` has arcs of that type on `p` when `u` is named `t`, none
otherwise. The output side and the reset edges have other arc types. -/
theorem exp001_refTransEdges_count (u : ExportTrans) (p t : String) :
    (refTransEdges u).countP (fun e => decide (e.arc = .input ∧ e.src = .place p ∧ e.dst = .trans t)) =
        (if u.name = t then (u.core.inputs.map (·.place)).count p else 0) ∧
    (refTransEdges u).countP (fun e => decide (e.arc = .inhibitor ∧ e.src = .place p ∧ e.dst = .trans t)) =
        (if u.name = t then u.core.inhibitors.count p else 0) ∧
    (refTransEdges u).countP (fun e => decide (e.arc = .read ∧ e.src = .place p ∧ e.dst = .trans t)) =
        (if u.name = t then u.core.reads.count p else 0) := by
  have hem : ∀ a : ArcType, a ≠ .output → a ≠ .resetOutput →
      (refEmit.ofTrans u).edges.countP
        (fun e => decide (e.arc = a ∧ e.src = .place p ∧ e.dst = .trans t)) = 0 := by
    intro a h1 h2
    rw [List.countP_eq_zero]
    intro e he
    rcases (refEmit_ofTrans_arc he).1 with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]; simp [Ne.symm h1]
    · rw [ha]; simp [Ne.symm h2]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [refTransEdges, List.countP_append, List.countP_append, List.countP_append,
      List.countP_append, hem _ (by decide) (by decide)]
    by_cases hu : u.name = t
    · subst hu
      simp only [List.countP_map, refInputEdge, refInhibitorEdge, refReadEdge, refResetEdge,
        Function.comp_def, List.count, if_true]
      simp only [reduceCtorEq, NodeRef.place.injEq, true_and, false_and, and_true, and_false,
        List.countP_false, Function.const_apply, Nat.add_zero, Nat.zero_add, decide_false]
      exact List.countP_congr (fun x _ => by simp)
    · simp [List.countP_map, refInputEdge, refInhibitorEdge, refReadEdge, refResetEdge,
        Function.comp_def, hu]

/-- Summed over transitions with distinct names, only the transition named `t.name` counts. -/
theorem exp001_countP_flatMap {L : List ExportTrans} (hL : (L.map ExportTrans.name).Nodup)
    {t : ExportTrans} (ht : t ∈ L) (q : XEdge → Bool) (c : ExportTrans → Nat)
    (hq : ∀ u, (refTransEdges u).countP q = if u.name = t.name then c u else 0) :
    (L.flatMap refTransEdges).countP q = c t := by
  have hz : ∀ L' : List ExportTrans, (∀ w ∈ L', w.name ≠ t.name) →
      (L'.flatMap refTransEdges).countP q = 0 := by
    intro L' h
    induction L' with
    | nil => rfl
    | cons w L' ih =>
      rw [List.flatMap_cons, List.countP_append, hq w, if_neg (h w (List.mem_cons_self ..)),
        ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
  induction L with
  | nil => cases ht
  | cons u L ih =>
    rw [List.map_cons, List.nodup_cons] at hL
    rw [List.flatMap_cons, List.countP_append, hq u]
    rcases List.mem_cons.mp ht with rfl | ht'
    · rw [if_pos rfl, hz L (fun w hw he => hL.1 (he ▸ List.mem_map_of_mem hw)), Nat.add_zero]
    · have hne : u.name ≠ t.name := fun he => hL.1 (he ▸ List.mem_map_of_mem ht')
      rw [if_neg hne, ih hL.2 ht', Nat.zero_add]

/-- **One edge per input, inhibitor and read arc** in the reference, when the names are
distinct: the ghost edges a cluster stage adds have arc type `ghost`. -/
theorem exp001_refDrawn {S : ClusterStage} (hX : (X.trans.map ExportTrans.name).Nodup)
    {t : ExportTrans} (ht : t ∈ X.trans) (p : String) :
    exp001Drawn (refExportWith S cfg X) .input p t.name = (inPlaces t.toTrans).count p ∧
    exp001Drawn (refExportWith S cfg X) .inhibitor p t.name = t.toTrans.core.inhibitors.count p ∧
    exp001Drawn (refExportWith S cfg X) .read p t.name = t.toTrans.core.reads.count p := by
  have hg : ∀ a : ArcType, a ≠ .ghost →
      (S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X)).countP
        (fun e => decide (e.arc = a ∧ e.src = .place p ∧ e.dst = .trans t.name)) = 0 := by
    intro a ha
    rw [List.countP_eq_zero]
    intro e he
    rw [S.ghosts_arc _ _ _ _ e he]
    simp [Ne.symm ha]
  simp only [exp001Drawn, refExportWith_edges, List.countP_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [hg _ (by decide), Nat.add_zero, refEdges, exp001_countP_flatMap hX ht _ _
      (fun u => (exp001_refTransEdges_count u p t.name).1)]
    rfl
  · rw [hg _ (by decide), Nat.add_zero, refEdges, exp001_countP_flatMap hX ht _ _
      (fun u => (exp001_refTransEdges_count u p t.name).2.1)]
    rfl
  · rw [hg _ (by decide), Nat.add_zero, refEdges, exp001_countP_flatMap hX ht _ _
      (fun u => (exp001_refTransEdges_count u p t.name).2.2)]
    rfl

end Reference

/-- **The reference exporter satisfies EXP-001 with every cluster stage.** -/
theorem EXP_001_any (S : ClusterStage) : EXP_001 (refExportWith S) := by
  intro cfg X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht p hp
    rw [refExportWith_nodes]
    apply exp001_refNodes_place
    rw [mem_refPlaceNames]
    exact Or.inr ⟨t, ht, (ExportTrans.mem_touched t p).mpr hp⟩
  · intro hX t ht
    rw [refExportWith_nodes]
    exact exp001_refNodes_trans hX ht
  · intro n hn
    exact exp001_refNodes_bound hn
  · intro t ht p
    refine ⟨?_, ?_, ?_⟩
    · intro hp
      simp only [inPlaces, ExportTrans.toTrans_core, List.mem_map] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      exact ⟨refInputEdge t s, refExportWith_edge_of_trans ht
        (mem_refTransEdges.mpr (Or.inl ⟨s, hs, rfl⟩)), rfl, rfl, rfl⟩
    · intro hp
      exact ⟨refInhibitorEdge t p, refExportWith_edge_of_trans ht
        (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))), rfl, rfl, rfl⟩
    · intro hp
      exact ⟨refReadEdge t p, refExportWith_edge_of_trans ht
        (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))), rfl, rfl, rfl⟩
  · intro hX t ht p
    exact exp001_refDrawn hX ht p
  · intro t ht p hp
    rw [ExportTrans.outputArc_iff] at hp
    obtain ⟨e, he, hd⟩ := exp001_refEmit_into hp
    refine ⟨e, refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inr (Or.inl he))),
      refEmit_ofTrans_owner he, ?_, hd⟩
    rcases (refEmit_ofTrans_arc he).1 with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Or.inl ha
    · obtain ⟨q, hq, hdq⟩ := (refEmit_ofTrans_arc he).2.1.mp ha
      rw [hd, NodeRef.place.injEq] at hdq
      subst hdq
      exact Or.inr ⟨ha, hq⟩
  · intro t ht p hp
    by_cases hl : p ∈ t.outLeaves
    · obtain ⟨e, he, hd⟩ := exp001_refEmit_into hl
      refine ⟨e, refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inr (Or.inl he))),
        refEmit_ofTrans_owner he, Or.inr ⟨?_, (ExportTrans.outputArc_iff t p).mpr hl⟩, hd⟩
      exact (refEmit_ofTrans_arc he).2.1.mpr ⟨p, hp, hd⟩
    · exact ⟨refResetEdge t p, refExportWith_edge_of_trans ht
        (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hl, rfl⟩))))),
        rfl, Or.inl rfl, rfl⟩

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-001 (`EXP_001_any` at the reference cluster stage). -/
@[evidence holds EXP_001]
theorem EXP_001_reference : EXP_001 refExport := EXP_001_any _

/-! ### The open case of ruling D60 -/

/-- The exporter of the Java and TypeScript mappers: place nodes for the places some arc touches
only (`PlaceAnalysis` in Java, `analyzePlaces` in `petri-net-mapper.ts`), everything else as the
reference draws it. It is the reference exporter on the net with its declared places dropped. -/
def exp001_arcDerived : Exporter := fun cfg X => refExportFlat cfg { X with places := [] }

/-- ✓ The Java and TypeScript shape satisfies EXP-001 as ruling D60 (c) states it now: the
common form asks for a node for every touched place, not for every declared one, and allows
the declared ones. -/
@[evidence allows EXP_001]
theorem EXP_001_allows_arcDerived : EXP_001 exp001_arcDerived := by
  intro cfg X
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := EXP_001_any .flat cfg { X with places := [] }
  refine ⟨h1, h2, fun n hn => ⟨fun p hp => ?_, (h3 n hn).2⟩, h4, h5, h6, h7⟩
  rcases (h3 n hn).1 p hp with h | h
  · cases h
  · exact Or.inr h

/-- A net that declares place `d` and has one transition `t` with no arc. -/
def exp001_untouchedNet : ExportNet :=
  { places := ["d"], trans := [{ core := ⟨"t", [], [], [], []⟩ }] }

/-- The case the common form leaves open: a place that the net declares and no arc touches has a
node in the reference (Rust, the end state of D60) and none in the Java and TypeScript shape, and
both exporters satisfy the block. -/
theorem EXP_001_untouched_open :
    (refExportFlat {} exp001_untouchedNet).nodes.countP (fun n => decide (n.ref = .place "d")) = 1 ∧
    (exp001_arcDerived {} exp001_untouchedNet).nodes.countP
      (fun n => decide (n.ref = .place "d")) = 0 := by
  decide

/-! ### Wrong exporters, one or more per line -/

/-! Line 1. -/

/-- `t` with an inhibitor arc on `i` and nothing else. -/
def exp001_inhNet : ExportNet := { trans := [{ core := ⟨"t", [], ["i"], [], []⟩ }] }

/-- Does some transition of `X` have an input arc on `p`, or name `p` in its output spec? -/
def exp001IoPlace (X : ExportNet) (p : String) : Bool :=
  X.trans.any fun t => decide (p ∈ t.core.inputs.map (·.place) ∨ p ∈ t.outLeaves)

/-- An exporter that draws place nodes for the input and output places only (the places of the
incidence matrix), as the reference otherwise draws. -/
def exp001_ioPlacesOnly : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.filter fun n =>
      match n.ref with
      | .place p => exp001IoPlace X p
      | _ => true }

/-- ✗ Drawing no node for a place only an inhibitor arc touches violates EXP-001 (line 1). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_ioPlacesOnly : ¬ EXP_001 exp001_ioPlacesOnly := by
  intro h
  have := (h {} exp001_inhNet).1 _ (List.mem_singleton_self _) "i" (by decide)
  revert this
  decide

/-- An exporter that draws one place node per arc end, without merging the ends on one place. -/
def exp001_perArc : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := (X.places ++ X.trans.flatMap ExportTrans.touched).map (refPlaceNode cfg X) ++
      X.trans.map (refTransNode cfg) ++ X.trans.flatMap refJunctionNodes }

/-- `t` consumes from `a` and produces into `a`. -/
def exp001_loopNet : ExportNet :=
  { trans := [{ core := ⟨"t", [⟨"a", .one⟩], [], [], []⟩, out := some (.place "a") }] }

/-- ✗ Two nodes for place `a`, one per arc, violate EXP-001 (line 1: exactly one node). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_perArc : ¬ EXP_001 exp001_perArc := by
  intro h
  have := (h {} exp001_loopNet).1 _ (List.mem_singleton_self _) "a" (by decide)
  revert this
  decide

/-! Line 2. -/

/-- An exporter that draws a transition node only for a transition with some arc, as DOT does
when it creates its nodes from the edges. -/
def exp001_edgeImplicit : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.filter fun n =>
      match n.ref with
      | .trans u => X.trans.any fun t => t.name == u && !t.touched.isEmpty
      | _ => true }

/-- `t` with no arc at all. -/
def exp001_bareNet : ExportNet := { trans := [{ core := ⟨"t", [], [], [], []⟩ }] }

/-- ✗ No node for a transition without arcs violates EXP-001 (line 2). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_edgeImplicit : ¬ EXP_001 exp001_edgeImplicit := by
  intro h
  have := (h {} exp001_bareNet).2.1 (by decide) _ (List.mem_singleton_self _)
  revert this
  decide

/-! Line 3. -/

/-- An exporter that also draws a node for a place `zz` in every net, whether the net has it or
not (a node left over from an earlier net, or one taken from a stale name list). -/
def exp001_phantomPlace : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes ++ [refPlaceNode cfg X "zz"] }

/-- ✗ A node for place `zz`, which `exp001_bareNet` neither declares nor touches, violates
EXP-001 (line 3, places). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_phantomPlace : ¬ EXP_001 exp001_phantomPlace := by
  intro h
  have := ((h {} exp001_bareNet).2.2.1 (refPlaceNode {} exp001_bareNet "zz")
    (List.mem_append_right _ (List.mem_singleton_self _))).1 "zz" rfl
  revert this
  decide

/-- An exporter that also draws a node for a transition `zz` in every net. -/
def exp001_phantomTrans : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes ++ [refTransNode cfg { core := ⟨"zz", [], [], [], []⟩ }] }

/-- ✗ A node for transition `zz`, which `exp001_bareNet` does not have, violates EXP-001
(line 3, transitions). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_phantomTrans : ¬ EXP_001 exp001_phantomTrans := by
  intro h
  have := ((h {} exp001_bareNet).2.2.1 (refTransNode {} { core := ⟨"zz", [], [], [], []⟩ })
    (List.mem_append_right _ (List.mem_singleton_self _))).2 "zz" rfl
  revert this
  decide

/-! Line 4. -/

/-- An exporter that draws no edges of arc type `a`. -/
def exp001_without (a : ArcType) : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.filter fun e => e.arc != a }

/-- ✗ Dropping the input edge of `t` on `a` violates EXP-001 (line 4, input). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_noInput : ¬ EXP_001 (exp001_without .input) := by
  intro h
  have := ((h {} exp001_loopNet).2.2.2.1 _ (List.mem_singleton_self _) "a").1 (by decide)
  revert this
  decide

/-- ✗ Dropping the inhibitor edge of `t` on `i` violates EXP-001 (line 4, inhibitor). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_noInhibitor : ¬ EXP_001 (exp001_without .inhibitor) := by
  intro h
  have := ((h {} exp001_inhNet).2.2.2.1 _ (List.mem_singleton_self _) "i").2.1 (by decide)
  revert this
  decide

/-- `t` with a read arc on `c` and nothing else. -/
def exp001_readNet : ExportNet := { trans := [{ core := ⟨"t", [], [], ["c"], []⟩ }] }

/-- ✗ Dropping the read edge of `t` on `c` violates EXP-001 (line 4, read). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_noRead : ¬ EXP_001 (exp001_without .read) := by
  intro h
  have := ((h {} exp001_readNet).2.2.2.1 _ (List.mem_singleton_self _) "c").2.2 (by decide)
  revert this
  decide

/-- An exporter that draws every input edge from the transition to the place (the direction of
the firing's token flow read backwards). -/
def exp001_reversedInput : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.map fun e =>
      if e.arc == .input then { e with src := e.dst, dst := e.src } else e }

/-- ✗ The input edge of `t` on `a` drawn from `t` to `a` violates EXP-001 (line 4, direction). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_reversedInput : ¬ EXP_001 exp001_reversedInput := by
  intro h
  have := ((h {} exp001_loopNet).2.2.2.1 _ (List.mem_singleton_self _) "a").1 (by decide)
  revert this
  decide

/-! Line 5. -/

/-- An exporter that draws every input, inhibitor and read edge twice (a mapper that runs its
place-to-transition loop once per place and once per transition). -/
def exp001_doubled : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges ++ g.edges.filter fun e =>
      e.arc == .input || e.arc == .inhibitor || e.arc == .read }

/-- ✗ Two inhibitor edges for the one inhibitor arc of `t` on `i` violate EXP-001 (line 5);
lines 1 to 4, 6 and 7 still hold of it, since they ask for at least one edge. -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_doubled : ¬ EXP_001 exp001_doubled := by
  intro h
  have := ((h {} exp001_inhNet).2.2.2.2.1 (by decide) _ (List.mem_singleton_self _) "i").2.1
  revert this
  decide

/-! Line 6. -/

/-- `r` with the node of transition `t` or its junctions handed to transition `u`. -/
def exp001Reown (u : String) : NodeRef → NodeRef
  | .trans _ => .trans u
  | .junction _ k i => .junction u k i
  | r => r

/-- An exporter that draws every output edge from the node of the net's first transition (or
its junctions), whichever transition the output arc belongs to. -/
def exp001_foreignOutput : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  let u := (X.trans.head?.map ExportTrans.name).getD ""
  { g with edges := g.edges.map fun e =>
      if e.arc == .output || e.arc == .resetOutput then { e with src := exp001Reown u e.src } else e }

/-- `s` with no arc, then `t` producing into `b`. -/
def exp001_twoNet : ExportNet :=
  { trans := [{ core := ⟨"s", [], [], [], []⟩ },
              { core := ⟨"t", [], [], [], []⟩, out := some (.place "b") }] }

/-- ✗ Drawing the output of `t` into `b` from the node of `s` violates EXP-001 (line 6: the edge
starts at a node of the arc's own transition). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_foreignOutput : ¬ EXP_001 exp001_foreignOutput := by
  intro h
  have := (h {} exp001_twoNet).2.2.2.2.2.1 _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) "b" (by decide)
  revert this
  decide

/-- An output edge into a place of `R` redrawn as the combined reset+output edge. -/
def exp001Retag (R : List String) (e : XEdge) : XEdge :=
  if e.arc = .output ∧ e.dst.inPlaces R = true then
    { e with arc := .resetOutput, row := .resetOutput, dashed := false, label := some "reset+out" }
  else e

/-- An exporter that reads the reset places net-wide: the mappers build the set of reset places
inside the loop over transitions (Rust `mapper.rs`, Java `PetriNetGraphMapper`, TypeScript
`petri-net-mapper.ts`), and this one builds it once from the reset arcs of every transition, so an
output edge into a place that another transition resets is drawn as a combined edge. -/
def exp001_globalResets : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.map (exp001Retag (X.trans.flatMap (·.core.resets))) }

/-- `a` produces into `P` with no reset arc; `b` resets `P`. -/
def exp001_sharedResetNet : ExportNet :=
  { trans := [{ core := ⟨"a", [], [], [], []⟩, out := some (.place "P") },
              { core := ⟨"b", [], [], [], ["P"]⟩ }] }

/-- ✗ The plain output arc of `a` on `P` drawn only as a combined reset+output edge, which `a` has
no reset arc for, violates EXP-001 (line 6: the combined type only where the transition also
resets the place). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_globalResets : ¬ EXP_001 exp001_globalResets := by
  intro h
  have := (h {} exp001_sharedResetNet).2.2.2.2.2.1 _ (List.mem_cons_self ..) "P" (by decide)
  revert this
  decide

/-! Line 7. -/

/-- `t` with a reset arc on `r` and no output spec. -/
def exp001_resetNet : ExportNet := { trans := [{ core := ⟨"t", [], [], [], ["r"]⟩ }] }

/-- ✗ Drawing nothing for the reset arc of `t` on `r` violates EXP-001 (line 7): a reset arc is
drawn only where it is combined with an output edge. -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_noStandaloneReset : ¬ EXP_001 (exp001_without .reset) := by
  intro h
  have := (h {} exp001_resetNet).2.2.2.2.2.2 _ (List.mem_singleton_self _) "r" (by decide)
  revert this
  decide

/-- An exporter that draws each standalone reset edge with arc type `a` in place of `reset`. -/
def exp001_resetAs (a : ArcType) : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.map fun e => if e.arc == .reset then { e with arc := a } else e }

/-- ✗ The reset arc of `t` on `r` drawn as an output edge violates EXP-001 (line 7, arc type). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_resetAsOutput : ¬ EXP_001 (exp001_resetAs .output) := by
  intro h
  have := (h {} exp001_resetNet).2.2.2.2.2.2 _ (List.mem_singleton_self _) "r" (by decide)
  revert this
  decide

/-- ✗ The reset arc of `t` on `r` drawn as a combined reset+output edge, though no output arc of
`t` ends in `r`, violates EXP-001 (line 7: the combined type only where the output spec also
names the place). -/
@[evidence forbids EXP_001]
theorem EXP_001_forbids_resetAsCombined : ¬ EXP_001 (exp001_resetAs .resetOutput) := by
  intro h
  have := (h {} exp001_resetNet).2.2.2.2.2.2 _ (List.mem_singleton_self _) "r" (by decide)
  revert this
  decide

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference exporter: the worked net of EXP-013 has an arc of every
kind (input, output, inhibitor, read, reset) and distinct transition names; its export draws one
node per place and per transition (and the xor junction of `Try`), an input, inhibitor and read
edge from the place to the transition, the output edges from `Try`'s junction and from
`RefreshCache` (combined with the reset arcs on `Fail` and `Cache`), and the standalone reset
edge into `Junk`. -/
@[evidence nonvacuous EXP_001]
theorem EXP_001_nonvacuous :
    ("In" ∈ inPlaces exportExTry.toTrans ∧ OutputArc exportExTry.toTrans "Ok" ∧
      InhibitorArc exportExCache.toTrans "Stop" ∧ ReadArc exportExCache.toTrans "Cfg" ∧
      ResetArc exportExCache.toTrans "Junk") ∧
    (exportExNet.trans.map ExportTrans.name).Nodup ∧
    (refExportFlat {} exportExNet).nodes.map XNode.ref =
      [.place "In", .place "Ok", .place "Fail", .place "Q", .place "Stop", .place "Cfg",
       .place "Cache", .place "Junk", .trans "Try", .trans "RefreshCache",
       .junction "Try" .xor 0] ∧
    (refExportFlat {} exportExNet).edges.map (fun e => (e.src, e.dst, e.arc)) =
      [(.place "In", .trans "Try", .input),
       (.trans "Try", .junction "Try" .xor 0, .output),
       (.junction "Try" .xor 0, .place "Ok", .output),
       (.junction "Try" .xor 0, .place "Fail", .resetOutput),
       (.place "Q", .trans "RefreshCache", .input),
       (.trans "RefreshCache", .place "Cache", .resetOutput),
       (.place "Stop", .trans "RefreshCache", .inhibitor),
       (.place "Cfg", .trans "RefreshCache", .read),
       (.trans "RefreshCache", .place "Junk", .reset)] := by
  decide

/-! ### Ruling D60: the two readings of the place set

Candidate readings, not requirement blocks (as `ClashesTime.lean` records its candidate readings): the
registry's `ambiguity` role needs two requirement blocks, so the two readings stay candidate
definitions, and `EXP_001_placeSet` records their disagreement without an evidence tag.
`Spec/ClashesExport.lean` keeps it that way: its `clashExport_placeSet` shows that EXP-001 and
EXP-014 hold of both runtime shapes, and promotes neither reading to a block. -/

/-- **Candidate reading D60 (a)** of EXP-001 AC2 ("all places in the net are represented"), the
end state: every place the net declares has a node, whether or not an arc touches it. The Rust
(and Python) mapper's shape. -/
def exp001DeclaredReading (E : Exporter) : Prop :=
  ∀ (cfg : ExportCfg) (X : ExportNet), ∀ p ∈ X.places, ∃ n ∈ (E cfg X).nodes, n.ref = .place p

/-- **Candidate reading D60 (b)** of EXP-001 AC2: the places are the places of the arcs, so a
place node stands for a place some arc touches. The Java and TypeScript mappers' shape. -/
def exp001TouchedOnlyReading (E : Exporter) : Prop :=
  ∀ (cfg : ExportCfg) (X : ExportNet), ∀ n ∈ (E cfg X).nodes, ∀ p : String,
    n.ref = .place p → ∃ t ∈ X.trans,
      p ∈ inPlaces t.toTrans ∨ OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨
        ReadArc t.toTrans p ∨ ResetArc t.toTrans p

/-- **The two readings disagree on both runtime shapes**, and EXP-001 holds of both (D60 (c)):
the reference (Rust shape) meets D60 (a) and not D60 (b), the Java and TypeScript shape meets
D60 (b) and not D60 (a). -/
theorem EXP_001_placeSet :
    (exp001DeclaredReading refExportFlat ∧ ¬ exp001TouchedOnlyReading refExportFlat) ∧
    (¬ exp001DeclaredReading exp001_arcDerived ∧ exp001TouchedOnlyReading exp001_arcDerived) ∧
    EXP_001 refExportFlat ∧ EXP_001 exp001_arcDerived := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, EXP_001_any _, EXP_001_allows_arcDerived⟩
  · intro cfg X p hp
    exact ⟨refPlaceNode cfg X p,
      mem_refNodes.mpr (Or.inl ⟨p, mem_refPlaceNames.mpr (Or.inl hp), rfl⟩), rfl⟩
  · intro h
    have := h {} exp001_untouchedNet (refPlaceNode {} exp001_untouchedNet "d") (by decide) "d" rfl
    revert this
    decide
  · intro h
    obtain ⟨n, hn, hr⟩ := h {} exp001_untouchedNet "d" (by decide)
    have : (exp001_arcDerived {} exp001_untouchedNet).nodes.any
        (fun m => decide (m.ref = .place "d")) = true :=
      List.any_eq_true.mpr ⟨n, hn, by simp [hr]⟩
    revert this
    decide
  · intro cfg X n hn p hp
    rcases (exp001_refNodes_bound (cfg := cfg) (X := { X with places := [] }) hn).1 p hp with h | h
    · cases h
    · exact h

end Libpetri.Spec
