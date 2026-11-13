import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_002

set_option linter.missingDocs true

/-!
# EXP-002: Visual semantics, places (`spec/09-export.md`)

How an exporter draws the node of a place: with a place category (one of the five place rows of
the style table, `Libpetri.Export.NodeCat`), never with the transition row or a junction row,
and with the place's own name, unsanitised, as the node's external label (`xlabel`), nothing
inside the node. The place a node stands for is a place of the net (declared, or on an arc of one
of its transitions), so the name drawn is a name of the net, not one the mapper made up. The requirement is a predicate over an abstract exporter `E : Exporter`
(glossary `GlossaryExport.lean`).

The statement speaks of node categories, not of shapes (export design P2): which shape a row
has is a fact about the generated style table, decided once (`EXP_002_place_rows`: every place
row is a circle or a double circle and shares its shape with neither the transition row nor a
junction row). Which of the five rows a place node gets is EXP-008's subject (ruling D51); the
exporter is tied to EXP-008's place classifier by the glossary agreement `ExportAgrees` (its
third clause), and the reference draws each place node with the row `refPlaceCategory` gives
(`EXP_002_draws_EXP_008`, cited for EXP-008's AC1 and AC2).

The witness is the reference exporter `refExportWith S` for every cluster stage `S`
(`EXP_002_any`); the holds evidence names the clustered exporter `refExport`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## Vocabulary: the place rows -/

/-- **The place rows** of the style table: the five node categories a place is drawn with by the
mapper (EXP-008: terminal, environment, start, end, and the regular `place` row). The
interface-port and sync-channel rows are not among them: only the documentation generators'
later rewrite of a subnet diagram uses them (EXP-011, MOD-040). -/
def NodeCat.placeRows : List NodeCat := [.place, .start, .«end», .environment, .terminal]

/-! ## EXP-002: Visual Semantics, Places -/

requirement EXP_002
  id "EXP-002"
  title "Visual Semantics: Places"
  kind F
  scope "every exporter's mapper, on the nodes of the exported graph (before a documentation generator restyles interface ports)"
  source verbatim "spec/09-export.md"
  covers EXP_002.s1, EXP_002.s2, EXP_002.s3, EXP_002.s4, EXP_002.s5
  reading "For the exporter E, every configuration cfg, every net X and every node n of the graph E draws for them:"
          "n has a place category (one of NodeCat.placeRows) exactly when n stands for a place;"
          "and when n stands for place p, p is a place of X (declared in X, or on an arc of a transition of X), the external label of n is p itself and its label is empty."
  assumes "The model is an exporter E : Exporter (glossary): from an export configuration and a net, the typed graph the mapper builds before DOT text, whose nodes (glossary XNode) carry what they stand for (a place, a transition or a junction of a transition), a DOT ID, a node category (a row of the node table of spec/petri-net-styles.json, generated as Libpetri.Export.NodeCat), a label drawn inside the node and an optional external label (xlabel). The DOT text and the attribute syntax are not modelled (EXP-001 AC1, kind Q)."
          "The body bullet on shapes is read on the style table, not on the graph: statement line 1 puts every place node in a place row and no other node in one, and EXP_002_place_rows (decided on the generated table) shows that every place row has shape circle or doublecircle, both circle forms the bullet allows, and that no place row shares its shape with the transition row or a junction row. That a transition node is drawn with the transition row itself is EXP-003's line (the first EARS sentence points to it); with it, line 1 and the table fact give the body's first sentence and AC1 (places are visually distinguishable from transitions). The typed graph has no shape field: a node is drawn with the shape of its category's row, and the runtimes' mappers set each node's shape from its row (Rust writes the transition shape as a literal box), so a mapper that overrides a place node's shape while keeping its category is caught by the runtimes' tests, not here. The colours and pen widths of the rows are the table's and are also checked by the runtimes' tests."
          "Which of the five place rows a place node gets (terminal, environment, start, end or the regular row) is EXP-008's subject, with the precedence of ruling D51. The exporter is tied to EXP-008's place classifier by the glossary agreement ExportAgrees (each place node has the category the classifier gives it), which the export consistency theorem carries; the reference draws each place node with the row of refPlaceCategory for every cluster stage (EXP_002_draws_EXP_008), so a mapper that draws an end place with the start row violates EXP-008 through that agreement, not this block."
          "The body bullet on names and AC2 (place names are readable) are read as statement line 2: the name is drawn beside the node as its external label, exactly as written (a place b1/x reads b1/x, not its sanitized DOT ID p_b1_x, EXP_002_forbids_sanitizedXlabel), and nothing is drawn inside the small fixed-size circle; all three mappers do this (an empty label and an xlabel attribute holding the name). An empty label is not the absence of a label: Graphviz draws a node's DOT ID inside it when the label attribute is missing, which statement line 2 rejects (EXP_002_forbids_idInside). Whether the drawn text is legible (font, size, overlap) is kind Q."
          "Which places get a node at all, and how many, is EXP-001's subject (ruling D60), and the DOT ID of a place node is EXP-014's (ruling D46); this block constrains only the nodes the exporter draws. It does ask, as its second shall sentence says, that the place a node stands for is a place of the net, in the common form of ruling D60 (declared, or on an arc), so that a mapper that records a place node as standing for its sanitized name b1_x and labels it so violates line 2 on its own (EXP_002_forbids_semanticSanitized), and not only through EXP-001's count of the nodes of b1/x. A junction node stands for a junction of a transition and gets a junction row (EXP-012); line 1 only excludes the place rows for it."
          "Out of scope: the documentation generators (EXP-011) rewrite the DOT of a subnet body after mapping and redraw its interface-port places with the interface-port row, which is not a place row here; that rewrite is a later step on the DOT text, as in EXP-008. Clustering (EXP-016, EXP-017) adds clusters and ghost edges and changes no node, so the block holds of the reference for every cluster stage."
          "The test derivation (export a net, check the place nodes' shape) is EXP_002_nonvacuous on the reference: a net whose place b1/x is consumed by transition t, which outputs to place done, draws b1/x as a start circle and done as an end double circle, both with an empty label and their names as external labels, and t as a box."
  signoff "2026-11-13 5d04aca30379fbb7 ai"
  statement : Exporter → Prop :=
    fun E => ∀ cfg X, ∀ n ∈ (E cfg X).nodes,
      (n.cat ∈ NodeCat.placeRows ↔ ∃ p, n.ref = .place p) ∧
      (∀ p, n.ref = .place p → (p ∈ X.places ∨ X.Touched p) ∧ n.xlabel = some p ∧ n.label = "")

/- The pinned readable form of EXP-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_002 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    ∀ n ∈ (E cfg X).nodes,
      (n.cat ∈ NodeCat.placeRows ↔ ∃ p, n.ref = NodeRef.place p) ∧
        ∀ (p : String), n.ref = NodeRef.place p → (p ∈ X.places ∨ X.Touched p) ∧ n.xlabel = some p ∧ n.label = ""
-/
#guard_msgs in #print EXP_002

/-! ### The reference -/

/-- The reference place classifier answers a place row. -/
theorem refPlaceCategory_mem_placeRows (Y : Reference.Net String) (env term : String → Bool)
    (p : String) : refPlaceCategory Y env term p ∈ NodeCat.placeRows := by
  unfold refPlaceCategory
  split
  · decide
  split
  · decide
  split
  · decide
  split <;> decide

/-- The reference exporter satisfies EXP-002 for every cluster stage: place nodes stand for the
declared or touched places (`refPlaceNames`) and get the row `refPlaceCategory` gives, which is a
place row, an empty label and the raw name as external label; transition nodes the transition row; junction nodes a junction row. -/
theorem EXP_002_any (S : ClusterStage) : EXP_002 (refExportWith S) := by
  intro cfg X n hn
  rw [refExportWith_nodes] at hn
  rcases mem_refNodes.mp hn with ⟨p, hp, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩
  · refine ⟨⟨fun _ => ⟨p, rfl⟩, fun _ => refPlaceCategory_mem_placeRows _ _ _ _⟩, ?_⟩
    intro q hq
    simp only [refPlaceNode, NodeRef.place.injEq] at hq
    subst hq
    exact ⟨mem_refPlaceNames.mp hp, rfl, rfl⟩
  · refine ⟨⟨fun h => by simp [refTransNode, NodeCat.placeRows] at h,
      fun ⟨_, h⟩ => by simp [refTransNode] at h⟩, ?_⟩
    intro q hq
    simp [refTransNode] at hq
  · obtain ⟨k, i⟩ := j
    refine ⟨⟨fun h => ?_, fun ⟨_, h⟩ => by simp [refJunctionNode] at h⟩, ?_⟩
    · cases k <;> simp [refJunctionNode, JKind.cat, NodeCat.placeRows] at h
    · intro q hq
      simp [refJunctionNode] at hq

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-002 (`EXP_002_any` at the reference cluster stage). -/
@[evidence holds EXP_002]
theorem EXP_002_reference : EXP_002 refExport := EXP_002_any _

/-! ### The style table: the body bullet and AC1 -/

/-- The body bullet on shapes and AC1, on the generated style table: every place row is a circle
or a double circle, and no place row shares its shape with the transition row or a junction
row. -/
@[evidence cites "EXP-002" "Places: circles, ellipses, or stadium-shaped nodes; places are visually distinguishable from transitions (AC1)"]
theorem EXP_002_place_rows :
    ∀ c ∈ NodeCat.placeRows,
      ((nodeStyle c).shape = "circle" ∨ (nodeStyle c).shape = "doublecircle") ∧
      ∀ d ∈ [NodeCat.transition, .xorJunction, .andJunction],
        (nodeStyle c).shape ≠ (nodeStyle d).shape := by
  decide

/-! ### The join with EXP-008 -/

/-- The six rows a mapper draws places and transitions with are pairwise different rows of the
table. -/
theorem exp002_rows_distinct :
    ∀ a ∈ NodeCat.placeRows, ∀ b ∈ NodeCat.transition :: NodeCat.placeRows,
      a ≠ b → nodeStyle a ≠ nodeStyle b := by
  decide

/-- **EXP-008's rows are the drawn rows.** In the graph the reference exporter draws (every
cluster stage), each place node has the category EXP-008's reference classifier gives its place,
and its style differs from that of every place or transition node of another category: a start
or end place is visually distinct from every other place (EXP-008 AC1 and AC2), and every place
from every transition (EXP-002 AC1). -/
@[evidence cites "EXP-008" "AC1 and AC2: start and end places are drawn with their own rows, visually distinct from other places"]
theorem EXP_002_draws_EXP_008 (S : ClusterStage) (cfg : ExportCfg) (X : ExportNet) :
    ∀ n ∈ (refExportWith S cfg X).nodes, ∀ p, n.ref = .place p →
      n.cat = refPlaceCategory X.toNet cfg.isEnv X.isTerm p ∧
      ∀ m ∈ (refExportWith S cfg X).nodes, (∃ q, m.ref = .place q ∨ m.ref = .trans q) →
        m.cat ≠ n.cat → nodeStyle m.cat ≠ nodeStyle n.cat := by
  intro n hn p hp
  have hnr := (refNodes_ref_cases (by simpa using hn)).1 p hp
  have hnc : n.cat ∈ NodeCat.placeRows := ((EXP_002_any S cfg X n hn).1).2 ⟨p, hp⟩
  refine ⟨by rw [hnr.2]; rfl, ?_⟩
  intro m hm ⟨q, hq⟩ hne
  have hmc : m.cat ∈ NodeCat.transition :: NodeCat.placeRows := by
    rcases hq with hq | hq
    · exact List.mem_cons_of_mem _ (((EXP_002_any S cfg X m hm).1).2 ⟨q, hq⟩)
    · obtain ⟨t, _, _, rfl⟩ := (refNodes_ref_cases (by simpa using hm)).2.1 q hq
      exact List.mem_cons_self
  exact fun h => exp002_rows_distinct n.cat hnc m.cat hmc (Ne.symm hne) h.symm

/-! ### Wrong exporters, one per line -/

/-- The reference exporter with every node rewritten by `f`. -/
def exp002_mapNodes (f : XNode → XNode) : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.map f }

/-- A mapper that draws places as boxes: the transition row for every place node. -/
def exp002_boxes : Exporter := exp002_mapNodes fun n =>
  match n.ref with
  | .place _ => { n with cat := .transition }
  | _ => n

/-- A mapper that draws transitions as circles: the regular place row for every transition
node. -/
def exp002_circleTransitions : Exporter := exp002_mapNodes fun n =>
  match n.ref with
  | .trans _ => { n with cat := .place }
  | _ => n

/-- A mapper that shows a place's sanitized name (the body of its DOT ID) as its external
label. -/
def exp002_sanitizedXlabel : Exporter := exp002_mapNodes fun n =>
  match n.ref with
  | .place p => { n with xlabel := some (sanitize p) }
  | _ => n

/-- A mapper that sets no label on a place node, so Graphviz draws the node's DOT ID inside it. -/
def exp002_idInside : Exporter := exp002_mapNodes fun n =>
  match n.ref with
  | .place _ => { n with label := n.id }
  | _ => n

/-- A mapper that records each place node as standing for the body of its DOT ID, the sanitized
name, and labels it with that name (the semantic ID taken from the DOT ID). -/
def exp002_semanticSanitized : Exporter := exp002_mapNodes fun n =>
  match n.ref with
  | .place p => { n with ref := .place (sanitize p), xlabel := some (sanitize p) }
  | _ => n

/-- The example net: transition `t` consumes the place `b1/x` (a name from a composed instance,
which sanitizing changes) and outputs to `done`. -/
def exp002_net : ExportNet :=
  { trans := [{ core := ⟨"t", [⟨"b1/x", .one⟩], [], [], []⟩, out := some (.place "done") }] }

/-- The nodes the reference draws for the example net: the place `b1/x`, the place `done`, the
transition `t`. -/
theorem exp002_net_nodes :
    (refExportFlat {} exp002_net).nodes.map (fun n => (n.ref, n.id, n.cat, n.label, n.xlabel)) =
      [(.place "b1/x", "p_b1_x", .start, "", some "b1/x"),
       (.place "done", "p_done", .«end», "", some "done"),
       (.trans "t", "t_t", .transition, "t [0, ∞]ms", none)] := by
  decide

/-- ✗ Drawing a place as a box violates EXP-002 (line 1, a place node has a place category). -/
@[evidence forbids EXP_002]
theorem EXP_002_forbids_boxes : ¬ EXP_002 exp002_boxes := by
  intro h
  have := (h {} exp002_net _ (List.getElem_mem (n := 0) (by decide))).1.2 ⟨"b1/x", by decide⟩
  revert this
  decide

/-- ✗ Drawing a transition with a place row violates EXP-002 (line 1, only a place node has a
place category). -/
@[evidence forbids EXP_002]
theorem EXP_002_forbids_circleTransitions : ¬ EXP_002 exp002_circleTransitions := by
  intro h
  obtain ⟨p, hp⟩ :=
    (h {} exp002_net _ (List.getElem_mem (n := 2) (by decide))).1.1 (by decide)
  have ht : ((exp002_circleTransitions {} exp002_net).nodes[2]'(by decide)).ref = .trans "t" := by
    decide
  rw [ht] at hp
  cases hp

/-- ✗ Showing the sanitized name `b1_x` for the place `b1/x` violates EXP-002 (line 2, the
external label is the name as written). -/
@[evidence forbids EXP_002]
theorem EXP_002_forbids_sanitizedXlabel : ¬ EXP_002 exp002_sanitizedXlabel := by
  intro h
  have := ((h {} exp002_net _ (List.getElem_mem (n := 0) (by decide))).2 "b1/x" (by decide)).2.1
  revert this
  decide

/-- ✗ Leaving the label unset, so the DOT ID `p_b1_x` is drawn inside the node, violates EXP-002
(line 2, no label inside the node). -/
@[evidence forbids EXP_002]
theorem EXP_002_forbids_idInside : ¬ EXP_002 exp002_idInside := by
  intro h
  have := ((h {} exp002_net _ (List.getElem_mem (n := 0) (by decide))).2 "b1/x" (by decide)).2.2
  revert this
  decide

/-- ✗ A place node that stands for, and is labelled with, the sanitized name `b1_x`, which is no
place of the net, violates EXP-002 (line 2, the place a node stands for is a place of the net). -/
@[evidence forbids EXP_002]
theorem EXP_002_forbids_semanticSanitized : ¬ EXP_002 exp002_semanticSanitized := by
  intro h
  have := ((h {} exp002_net _ (List.getElem_mem (n := 0) (by decide))).2 "b1_x" (by decide)).1
  revert this
  simp only [ExportNet.Touched]
  decide

/-! ### Non-vacuity -/

/-- The test derivation on the reference: the example net's place `b1/x` is drawn as a start
circle and `done` as an end double circle, both with an empty label and the name as written as
external label, and the transition `t` as a box. -/
@[evidence nonvacuous EXP_002]
theorem EXP_002_nonvacuous :
    (refExportFlat {} exp002_net).nodes.map
        (fun n => (n.ref, n.cat, (nodeStyle n.cat).shape, n.label, n.xlabel)) =
      [(.place "b1/x", .start, "circle", "", some "b1/x"),
       (.place "done", .«end», "doublecircle", "", some "done"),
       (.trans "t", .transition, "box", "t [0, ∞]ms", none)] := by
  decide

end Libpetri.Spec
