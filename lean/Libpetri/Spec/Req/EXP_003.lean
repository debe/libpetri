import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster

set_option linter.missingDocs true

/-!
# EXP-003: Visual semantics, transitions (`spec/09-export.md`)

How an exporter draws a transition: as a node of the transition category (the `transition` row
of the node table in `spec/petri-net-styles.json`, shape `box`, a rectangle), labelled with a
text that starts with the transition's name, and only for the transitions of the net. The requirement is a predicate over an abstract
exporter `E : Exporter` (glossary `GlossaryExport.lean`), read on the typed graph it draws for
a configuration and a net.

The witness is the reference exporter `refExportWith S` for every cluster stage `S`
(`Reference/Export.lean`), written as the three runtime mappers draw a transition node
(`map_to_graph` and `transition_label` in the Rust crate `libpetri-export`,
`PetriNetGraphMapper.java`, `petri-net-mapper.ts`). `EXP_003_any` proves the block for every
stage; the tagged holds evidence is its instance at the reference cluster stage, `refExport`,
the witness of the joint theorem.

Ruling D41 (a) pins the label format; the format itself (intervals, `∞`, ` prio=n`) is
EXP-007's label block, and this block states what every label of that format has: it starts
with the name, and it is the name alone when intervals and priority are hidden.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## EXP-003: Visual Semantics, Transitions -/

requirement EXP_003
  id "EXP-003"
  title "Visual Semantics: Transitions"
  kind F
  scope "every exporter, on the nodes of the graph it draws for a configuration and a net"
  source verbatim "spec/09-export.md"
  quote "Transitions are rendered as rectangles or bars (following Petri net convention)."
        "Transition names are displayed as labels."
        "The export *shall* draw a node for every transition of the net."
        "The export *shall* draw no node that stands for a transition the net does not have."
        "The export *shall* give a node the transition category exactly when the node stands for a transition."
        "The export *shall* label the node of a transition with a text that starts with the transition's name as written in the net."
        "*Where* the configuration hides the timing interval and the priority, the export *shall* label the node of a transition with the transition's name alone."
  reading "For the exporter E, every configuration cfg and every net X:"
          "every transition t of X has a node in the graph E cfg X that stands for t (its reference is the transition named t.name);"
          "a node that stands for the transition named tn stands for a transition of X: some transition of X has the name tn;"
          "a node of the graph has the transition category exactly when it stands for a transition;"
          "the label of a node that stands for the transition named tn starts with tn (as character lists);"
          "and when cfg hides both the timing interval and the priority, the label of a node that stands for the transition named tn is tn."
  assumes "The model is an exporter E : Exporter (glossary): from an export configuration (glossary ExportCfg: direction, the show flags, environment places, cluster source) and a net as the exporter reads it (glossary ExportNet), the typed graph the runtimes' mappers build before DOT text (glossary XGraph). A node (glossary XNode) carries what it stands for (ref), its DOT ID, its node category (a row of the node table, Libpetri.Export.NodeCat), its label and its external label. The DOT text, its attribute syntax and the fonts are not modelled."
          "Rectangles or bars: the transition category is the transition row of the node table, generated into Lean from spec/petri-net-styles.json (Libpetri.Export.Styles); its shape is box, a rectangle, so the export draws rectangles and does not use bars. No place row (the five rows place, start, end, environment and terminal of EXP-002), no junction row and not the interface-port row has that shape (EXP_003_nonvacuous, decided on the generated table). The third line is therefore the shape sentence: transitions are drawn box-shaped, and no place and no junction is drawn with the transition row. Which place row a place gets is EXP-008's and EXP-002's subject. The sync-channel row is also box-shaped (EXP_003_syncChannel_row); no mapper gives a node that row (only the documentation generators' rewrite of a subnet diagram would, EXP-011), line 3 forbids it for a transition node, and EXP-002's line 1 forbids it for a place node."
          "AC1 (transitions are visually distinguishable from places) is met jointly with EXP-002: line 3 gives a transition node the transition row and keeps every other node out of it, EXP-002's line 1 gives a place node a place row, and the transition row's shape differs from every place row's shape (the table fact above). This block alone does not keep a place node on a place row: an exporter that draws a place with the box-shaped sync-channel row meets EXP-003 and fails EXP-002's line 1, so the joint theorem rejects it (the row facts are EXP_003_syncChannel_row). The test derivation (verify transition nodes use correct shape syntax) is the table fact and line 3 on the reference; the DOT attribute syntax itself is kind Q."
          "AC2 (transition names are readable) is kind Q, a property of the rendered picture. What is checked is that the name is displayed: lines 4 and 5 put the transition's name, as written in the net and not its sanitised DOT ID (EXP-014), at the start of its label, so a mapper that labels a transition with its node ID violates the block (EXP_003_forbids_idLabel)."
          "The label format is ruling D41 (a), pinned in EXP-007's label block: the name, then the timing interval when intervals are shown, then the priority when it is shown and is not 0. Lines 4 and 5 are the two consequences of that format this requirement states; the rest of the label is EXP-007's, and the agreement predicate ExportAgrees (glossary) ties the exporter's transition labels to EXP-007's labeller in the joint theorem."
          "Line 1 overlaps EXP-001's line on transition nodes, which also says that each transition has exactly one node and needs distinct transition names (glossary ExportNet.Distinct); this block states only that the node is drawn, so that an exporter that draws no transition node does not meet it vacuously (EXP_003_forbids_noTransNodes). Line 2 is the converse, which EXP-001 does not state (it counts only the nodes of the net's own transitions): a node whose reference names a transition names one the net has, whatever its row, so an edge pass that makes a node again from a sanitised endpoint ID (a_b from t_a_b) violates the block (EXP_003_forbids_ghostTrans). Lines 3 to 5 speak of every node that stands for a transition name, so two transitions of one name, which no net that builds has, change nothing here."
          "The external label of a transition node, its DOT ID (EXP-014), the cluster it is drawn in (EXP-016) and the order of the nodes are not stated here; node order is kind Q."
  signoff "pending"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (∀ t ∈ X.trans, ∃ n ∈ (E cfg X).nodes, n.ref = .trans t.name) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ tn, n.ref = .trans tn → ∃ t ∈ X.trans, t.name = tn) ∧
      (∀ n ∈ (E cfg X).nodes, n.cat = .transition ↔ ∃ tn, n.ref = .trans tn) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ tn, n.ref = .trans tn → tn.toList <+: n.label.toList) ∧
      (cfg.showIntervals = false → cfg.showPriority = false →
        ∀ n ∈ (E cfg X).nodes, ∀ tn, n.ref = .trans tn → n.label = tn)

/- The pinned readable form of EXP-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_003 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (∀ t ∈ X.trans, ∃ n ∈ (E cfg X).nodes, n.ref = NodeRef.trans t.name) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ (tn : String), n.ref = NodeRef.trans tn → ∃ t ∈ X.trans, t.name = tn) ∧
        (∀ n ∈ (E cfg X).nodes, n.cat = NodeCat.transition ↔ ∃ tn, n.ref = NodeRef.trans tn) ∧
          (∀ n ∈ (E cfg X).nodes, ∀ (tn : String), n.ref = NodeRef.trans tn → tn.toList <+: n.label.toList) ∧
            (cfg.showIntervals = false →
              cfg.showPriority = false →
                ∀ n ∈ (E cfg X).nodes, ∀ (tn : String), n.ref = NodeRef.trans tn → n.label = tn)
-/
#guard_msgs in #print EXP_003

/-! ### The reference -/

/-- The reference place classifier never gives the transition category. -/
theorem refPlaceCategory_ne_transition (X : Reference.Net String) (env term : String → Bool)
    (p : String) : refPlaceCategory X env term p ≠ .transition := by
  unfold refPlaceCategory
  split_ifs <;> simp

/-- A junction category is not the transition category. -/
theorem JKind.cat_ne_transition (k : JKind) : k.cat ≠ .transition := by
  cases k <;> simp [JKind.cat]

/-- The reference exporter satisfies EXP-003 at every cluster stage: the nodes are `refNodes`,
whatever the stage; a transition node stands for a transition of the net, has the transition
category and the label
`refTransLabel`, which starts with the name and is the name when intervals and priority are
hidden; place and junction nodes have a place or a junction category. -/
theorem EXP_003_any (S : ClusterStage) : EXP_003 (refExportWith S) := by
  intro cfg X
  simp only [refExportWith_nodes]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨refTransNode cfg t, mem_refNodes.mpr (Or.inr (Or.inl ⟨t, ht, rfl⟩)), rfl⟩
  · intro n hn tn hr
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, _, j, _, rfl⟩
    · simp [refPlaceNode] at hr
    · simp only [refTransNode, NodeRef.trans.injEq] at hr
      exact ⟨t, ht, hr⟩
    · simp [refJunctionNode] at hr
  · intro n hn
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩
    · simp [refPlaceNode, refPlaceCategory_ne_transition]
    · simp [refTransNode]
    · simp [refJunctionNode, JKind.cat_ne_transition]
  · intro n hn tn hr
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩
    · simp [refPlaceNode] at hr
    · simp only [refTransNode, NodeRef.trans.injEq] at hr ⊢
      subst hr
      exact refTransLabel_prefix _ _ _ _
    · simp [refJunctionNode] at hr
  · intro hi hp n hn tn hr
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩
    · simp [refPlaceNode] at hr
    · simp only [refTransNode, NodeRef.trans.injEq] at hr ⊢
      subst hr
      exact refTransLabel_hidden _ _ _ _ hi hp
    · simp [refJunctionNode] at hr

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-003 (`EXP_003_any` at the reference cluster stage). -/
@[evidence holds EXP_003]
theorem EXP_003_reference : EXP_003 refExport := EXP_003_any _

/-! ### Wrong exporters, one per line -/

/-- The reference exporter with every node rewritten by `f`, which may read the configuration. -/
def exp003MapNodes (f : ExportCfg → XNode → XNode) : Exporter := fun cfg X =>
  { refExportFlat cfg X with nodes := (refExportFlat cfg X).nodes.map (f cfg) }

/-- The small net the examples draw: transition `a/b` consumes `p` and outputs to `q`, with a
window timing and priority 2. -/
def exp003Net : ExportNet :=
  { trans := [{ core := ⟨"a/b", [⟨"p", .one⟩], [], [], []⟩, out := some (.place "q"),
                timing := .window 1 5, prio := 2 }] }

/-- The configuration with intervals and priority hidden (the minimal preset of EXP-007). -/
def exp003Hidden : ExportCfg := { showIntervals := false, showPriority := false }

/-- An exporter that draws no transition node (it keeps only place and junction nodes). -/
def exp003_noTransNodes : Exporter := fun cfg X =>
  { refExportFlat cfg X with
    nodes := (refExportFlat cfg X).nodes.filter fun n => n.cat != .transition }

/-- ✗ Drawing no node for a transition violates EXP-003 (line 1). -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_noTransNodes : ¬ EXP_003 exp003_noTransNodes := by
  intro h
  obtain ⟨n, hn, hr⟩ := (h {} exp003Net).1 _ (List.mem_singleton_self _)
  have hs : (exp003_noTransNodes {} exp003Net).nodes.map XNode.ref =
      [.place "p", .place "q"] := by decide
  have := List.mem_map_of_mem (f := XNode.ref) hn
  rw [hs, hr] at this
  simp at this

/-- The node a slipped edge pass makes for transition `t`: it recovers the transition from the
sanitised endpoint ID (`t_a_b` gives `a_b`) and makes a node for that name, of the transition
row and labelled with that name, next to the real node. -/
def exp003GhostNode (t : ExportTrans) : XNode :=
  ⟨.trans (sanitize t.name), nodeId (.trans (sanitize t.name)), .transition, sanitize t.name, none⟩

/-- An exporter with a get-or-create-by-ID slip in its edge pass: besides the reference nodes it
draws a node for the sanitised name of every transition. -/
def exp003_ghostTrans : Exporter := fun cfg X =>
  { refExportFlat cfg X with nodes := (refExportFlat cfg X).nodes ++ X.trans.map exp003GhostNode }

/-- ✗ Drawing a node for a transition the net does not have (`a_b`, made from the ID of `a/b`)
violates EXP-003 (line 2). Lines 1, 3, 4 and 5 still hold of it: the ghost node has the
transition row and its name as label. -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_ghostTrans : ¬ EXP_003 exp003_ghostTrans := by
  intro h
  have hn : (⟨.trans "a_b", "t_a_b", .transition, "a_b", none⟩ : XNode) ∈
      (exp003_ghostTrans {} exp003Net).nodes := by decide
  obtain ⟨t, ht, hname⟩ := (h {} exp003Net).2.1 _ hn "a_b" rfl
  simp only [exp003Net, List.mem_singleton] at ht
  subst ht
  revert hname
  decide

/-- An exporter that draws transitions as circles: the transition node gets the regular place
row. -/
def exp003_circles : Exporter :=
  exp003MapNodes fun _ n => if n.cat = .transition then { n with cat := .place } else n

/-- ✗ Drawing a transition as a circle violates EXP-003 (line 3). -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_circles : ¬ EXP_003 exp003_circles := by
  intro h
  have h3 := (h {} exp003Net).2.2.1
  have hn : (⟨.trans "a/b", "t_a_b", .place, "a/b [1, 5]ms prio=2", none⟩ : XNode) ∈
      (exp003_circles {} exp003Net).nodes := by decide
  have := (h3 _ hn).mpr ⟨"a/b", rfl⟩
  simp at this

/-- An exporter that draws places as boxes: every place node gets the transition row. -/
def exp003_boxPlaces : Exporter :=
  exp003MapNodes fun _ n => match n.ref with
    | .place _ => { n with cat := .transition }
    | _ => n

/-- ✗ Drawing a place with the transition row violates EXP-003 (line 3, its "only when" half:
AC1, places stay distinguishable from transitions). -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_boxPlaces : ¬ EXP_003 exp003_boxPlaces := by
  intro h
  have h3 := (h {} exp003Net).2.2.1
  have hn : (⟨.place "p", "p_p", .transition, "", some "p"⟩ : XNode) ∈
      (exp003_boxPlaces {} exp003Net).nodes := by decide
  obtain ⟨tn, htn⟩ := (h3 _ hn).mp rfl
  simp at htn

/-- An exporter that labels a transition node with its sanitised DOT ID (`t_a_b` for `a/b`). -/
def exp003_idLabel : Exporter :=
  exp003MapNodes fun _ n => match n.ref with
    | .trans _ => { n with label := n.id }
    | _ => n

/-- ✗ Labelling a transition with its node ID violates EXP-003 (line 4: the label starts with
the name as written, `a/b`, not `t_a_b`). -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_idLabel : ¬ EXP_003 exp003_idLabel := by
  intro h
  have h4 := (h {} exp003Net).2.2.2.1
  have hn : (⟨.trans "a/b", "t_a_b", .transition, "t_a_b", none⟩ : XNode) ∈
      (exp003_idLabel {} exp003Net).nodes := by decide
  have := h4 _ hn "a/b" rfl
  revert this
  decide

/-- An exporter that ignores the show flags: it draws its nodes as under the default
configuration (intervals and priority shown), whatever the configuration says. -/
def exp003_ignoreFlags : Exporter := fun cfg X =>
  { refExportFlat cfg X with nodes := (refExportFlat {} X).nodes }

/-- ✗ Showing the interval and the priority when the configuration hides them violates EXP-003
(line 5: with intervals and priority hidden the label is the name alone). Lines 1 to 4 still
hold of it: the label starts with the name. -/
@[evidence forbids EXP_003]
theorem EXP_003_forbids_ignoreFlags : ¬ EXP_003 exp003_ignoreFlags := by
  intro h
  have h5 := (h exp003Hidden exp003Net).2.2.2.2 rfl rfl
  have hn : (⟨.trans "a/b", "t_a_b", .transition, "a/b [1, 5]ms prio=2", none⟩ : XNode) ∈
      (exp003_ignoreFlags exp003Hidden exp003Net).nodes := by decide
  have := h5 _ hn "a/b" rfl
  revert this
  decide

/-! ### Non-vacuity: the acceptance criteria on the reference -/

/-- The test derivation and AC1 on the reference: the transition row of the generated node
table is box-shaped and no place row and no junction row is; the transition `a/b` of the small
net is drawn as one node of the transition category with ID `t_a_b` and the label
`a/b [1, 5]ms prio=2` under the default configuration (the name first, as written), and the
label `a/b` with intervals and priority hidden; its places are drawn with place rows. -/
@[evidence nonvacuous EXP_003]
theorem EXP_003_nonvacuous :
    (nodeStyle .transition).shape = "box" ∧
    (∀ c ∈ [NodeCat.place, .start, .«end», .environment, .terminal, .interfacePort,
        .xorJunction, .andJunction], (nodeStyle c).shape ≠ "box") ∧
    (refExportFlat {} exp003Net).nodes.map (fun n => (n.ref, n.id, n.cat, n.label)) =
      [(.place "p", "p_p", .start, ""), (.place "q", "p_q", .«end», ""),
       (.trans "a/b", "t_a_b", .transition, "a/b [1, 5]ms prio=2")] ∧
    (refExportFlat exp003Hidden exp003Net).nodes.map (fun n => (n.cat, n.label)) =
      [(.start, ""), (.«end», ""), (.transition, "a/b")] := by
  decide

/-- Why AC1 also needs EXP-002's line 1: the `sync-channel` row of the generated node table is
box-shaped like the transition row, and it is not one of EXP-002's five place rows. A place
node drawn with it would be a rectangle; this block's line 3 keeps it out of the transition
row only, and EXP-002's line 1 (a node has a place row exactly when it stands for a place)
rejects it. -/
theorem EXP_003_syncChannel_row :
    (nodeStyle .syncChannel).shape = (nodeStyle .transition).shape ∧
    NodeCat.syncChannel ∉ [NodeCat.place, .start, .«end», .environment, .terminal] := by
  decide

end Libpetri.Spec
