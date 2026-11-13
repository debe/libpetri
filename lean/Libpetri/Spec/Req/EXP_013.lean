import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_013

set_option linter.missingDocs true

/-!
# EXP-013: combined reset+output edge (`spec/09-export.md`)

How an exporter draws a place that a transition both resets and outputs to. The requirement is a
predicate over an abstract exporter `E : Exporter` (glossary `GlossaryExport.lean`), not over the
output emitter: the standalone reset edges are drawn outside the emitter, and the sentence "the
standalone reset edge to P MUST be suppressed" can only be stated where both are in one graph
(export design, skeptic correction S-1).

For a transition `t` of the net and a place `P`, the block reads two lists off the drawn graph:
the output-side edges of `t` into `P` (`exp013OutInto`: arc type `output` or `resetOutput`, from
the node of `t` or one of its junctions, into the node of `P`) and the reset edges of `t` into
`P` (`exp013ResetInto`). Five lines constrain them, one per EARS sentence, on nets whose
transition names are pairwise distinct (as the EARS sentences say): the combined style
where `t` resets `P`, no reset edge beside a combined one, one standalone reset edge per reset arc
otherwise, the plain style where `t` does not reset `P`, and one output-side edge per output leaf
into `P` (the existence line the per-edge spike statement lacked: an exporter that draws nothing
met it). A sixth line, on every net, reads every edge of the graph: an edge of arc type `resetOutput` starts at a
transition or one of its junctions and ends in a place that transition resets, so no combined
edge is drawn into a junction or backwards from the place.

The witness is the reference exporter `refExportWith S` (`Reference/Export.lean`), for every
cluster stage `S`; the `holds` evidence is its clustered instance `refExport`. The wrong
exporters are those the export design names: the pre-EXP-013 mapper, one that combines only a
leaf drawn from the transition (AC4), one that keeps the branch label on the combined edge, one
that keeps the `ForwardInput` dash, one that keeps the standalone reset edge beside the combined
edge, one that draws no edge at all into a reset place, plus one that drops the standalone reset
edges of a transition with an output spec and one that reads the reset places net-wide. The
repair round added the slips the mutation review found: a combined edge in the output row, a
standalone reset edge labelled `reset+out` or drawn from a junction, one reset edge per reset
place instead of per reset arc, an output edge styled from the net's reset places, a junction
edge restyled as a combined edge, and a combined edge drawn a second time backwards.

The sentences restate ruling D26 item 4 ("every output edge to P becomes a reset+out edge and no
standalone reset edge is emitted" in place of "exactly one edge to P") and item 3 (the combined
edge replaces the branch, timeout and `ForwardInput` labels and the dash).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## What the block reads off a drawn graph -/

/-- The output-side edges of transition `t` into place `P` in graph `g`, in the order drawn: the
edges of arc type `output` or `resetOutput` that start at the node of `t` or at one of its
junctions (`XEdge.outSideOf`) and end at the node of `P`. -/
def exp013OutInto (g : XGraph) (t P : String) : List XEdge :=
  g.edges.filter fun e => XEdge.outSideOf t e && e.dst == .place P

/-- The reset edges of transition `t` into place `P` in graph `g`, in the order drawn: the edges
of arc type `reset` that start at the node of `t` or at one of its junctions and end at the node
of `P`. -/
def exp013ResetInto (g : XGraph) (t P : String) : List XEdge :=
  g.edges.filter fun e => e.arc == .reset && e.src.owner? == some t && e.dst == .place P

/-! ## EXP-013: combined reset+output edge -/

requirement EXP_013
  id "EXP-013"
  title "Combined reset+output Edge"
  kind F
  scope "every exporter, the edges of one transition into one place"
  source verbatim "spec/09-export.md"
  covers EXP_013.s1, EXP_013.s2, EXP_013.s3, EXP_013.s4, EXP_013.s5, EXP_013.s6, EXP_013.s7,
        EXP_013.s8, EXP_013.s9, EXP_013.s10, EXP_013.s11, EXP_013.s12, EXP_013.s13, EXP_013.s14,
        EXP_013.s15
  reading "For every configuration cfg and net X, in the graph E cfg X, when the transitions of X have distinct names, for every transition t of X and every place name P:"
          "if t resets P, every output-side edge of t into P (exp013OutInto: arc type output or resetOutput, from the node of t or one of its junctions, into the node of P) has arc type resetOutput, style row resetOutput, is not dashed and is labelled reset+out;"
          "if t resets P and a leaf of t's output spec ends in P, there is no reset edge of t into P (exp013ResetInto);"
          "if t resets P and no leaf of t's output spec ends in P, the reset edges of t into P are as many as t's reset arcs on P, and each starts at the node of t, has style row reset, is not dashed and is labelled reset;"
          "if t does not reset P, every output-side edge of t into P has arc type output and style row output;"
          "the output-side edges of t into P are as many as the leaves of t's output spec that end in P (t.outLeaves, a ForwardInput leaf counted by its target);"
          "and, whatever the names of the transitions, every edge of the graph of arc type resetOutput starts at the node of some transition t of X or one of its junctions and ends at the node of a place t resets."
  assumes "The model is an exporter E : Exporter (glossary): from a configuration and the export view of a net (ExportNet: declared places, transitions in declaration order with their input, inhibitor, read and reset arcs and their n-ary output tree), the typed graph a mapper builds before DOT text. The block reads only its edges: the output-side edges and the reset edges of one transition into one place, and the edges of arc type resetOutput of the whole graph. The edges of a transition are found by their ends (the node of t or a junction of t), and the exporter keys transition nodes by name, so the five per-transition lines, like the five EARS sentences they encode, bind only nets whose transition names are pairwise distinct: with two transitions named T, each with Out.Place(P), every mapper draws two edges from t_T into p_P where each transition has one leaf. The sixth line needs no such condition and binds every net. Ghost edges between clusters (EXP-017) have their own arc type and are in none of the three."
          "Which leaves end in P is read off the output tree: a Place leaf for P and a ForwardInput leaf into P (t.outLeaves). Which edge belongs to which leaf, where each edge starts (the transition or the nearest junction above the leaf, so the junction edge of the sentence on a leaf under a junction) and the order of the edges are EXP-012's lines, carried to the exporter by the agreement ExportAgrees; this block fixes their number per place and their arc type, style row, dash and label. The combined edge is never dashed and carries reset+out alone, so it replaces the branch label of an Xor child, the timeout label and the ForwardInput label and dash (ruling D26 item 3), which is the last shall sentence of EXP-012. The sixth line keeps the combined style off every other edge: an edge into a junction (the parent edge of a group, an output edge of EXP-012) and an edge from the place back to the transition are never of arc type resetOutput."
          "For an edge into a place t does not reset, this block fixes the arc type output and the style row output: that is the black output edge of AC2 and the plain output style of AC4, whose colour is a constant of the style table. Its label and dash (the branch label Q of AC4, a timeout label, the ForwardInput label and dash) are EXP-012's, and that the row of an output edge is output is also EXP-004's output line."
          "An output spec may name P in more than one leaf (Xor(P, And(P, Q)) builds: its branches differ). Then all three mappers draw one combined edge per leaf, and the first line and the fifth line say so (ruling D26 item 4: every output edge to P becomes a reset+out edge)."
          "A transition may hold two reset arcs on one place (the TypeScript and Rust builders append without removing duplicates); the third line then asks for one standalone reset edge per arc, as all three mappers draw them. That a reset arc is drawn transition to place is the drawing convention of all three mappers (EXP-004)."
          "The style rows name the rows of the style table (Libpetri.Export.Styles, generated from spec/petri-net-styles.json): the colour #fd7e14, the bold line, the pen width 2.0 and the arrowhead of the reset-output and reset rows are constants of that table, checked by tests (kind Q). The worked DOT of the section is illustrative: its four edges are among refExportFlat_example_edges (Reference/Export.lean) at the level of IDs, arc types and labels, where the example net has further arcs (two input arcs, an inhibitor arc, a read arc and a reset arc on a second place) and the edges come in declaration order, those of Try before those of RefreshCache."
          "AC1, AC2, AC3 and AC4 are EXP_013_nonvacuous on the reference exporter: Out.Place(P) with reset(P) gives one reset+out edge from the transition and no reset edge; Out.Place(P) without a reset one plain output edge; reset(P) without an output to P one reset edge labelled reset; Out.Xor(P, Q) with reset(P) a combined edge from the junction to P and a plain edge, labelled Q, from the junction to Q."
          "AC5 (Java, TypeScript and Rust mappers produce byte-identical edges) is kind Q: a Lean function is deterministic and cross-language equality is a property of three programs (export design P3, ruling D60 (c)); the export corpus EP-2 replays the reference against the runtimes after the migration. The test derivation is AC1 to AC4."
  signoff "2026-11-13 de8231f060c029c7 ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans, ∀ P : String,
        (P ∈ t.core.resets → ∀ e ∈ exp013OutInto (E cfg X) t.name P,
          e.arc = .resetOutput ∧ e.row = .resetOutput ∧ e.dashed = false ∧
            e.label = some "reset+out") ∧
        (P ∈ t.core.resets → P ∈ t.outLeaves → exp013ResetInto (E cfg X) t.name P = []) ∧
        (P ∈ t.core.resets → P ∉ t.outLeaves →
          (exp013ResetInto (E cfg X) t.name P).length = t.core.resets.count P ∧
          ∀ e ∈ exp013ResetInto (E cfg X) t.name P,
            e.src = .trans t.name ∧ e.row = .reset ∧ e.dashed = false ∧ e.label = some "reset") ∧
        (P ∉ t.core.resets → ∀ e ∈ exp013OutInto (E cfg X) t.name P,
          e.arc = .output ∧ e.row = .output) ∧
        (exp013OutInto (E cfg X) t.name P).length = t.outLeaves.count P) ∧
      ∀ e ∈ (E cfg X).edges, e.arc = .resetOutput →
        ∃ t ∈ X.trans, e.src.owner? = some t.name ∧ ∃ P ∈ t.core.resets, e.dst = .place P

/- The pinned readable form of EXP-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_013 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    ((List.map ExportTrans.name X.trans).Nodup →
        ∀ t ∈ X.trans,
          ∀ (P : String),
            (P ∈ t.core.resets →
                ∀ e ∈ exp013OutInto (E cfg X) t.name P,
                  e.arc = ArcType.resetOutput ∧
                    e.row = EdgeRow.resetOutput ∧ e.dashed = false ∧ e.label = some "reset+out") ∧
              (P ∈ t.core.resets → P ∈ t.outLeaves → exp013ResetInto (E cfg X) t.name P = []) ∧
                (P ∈ t.core.resets →
                    P ∉ t.outLeaves →
                      (exp013ResetInto (E cfg X) t.name P).length = List.count P t.core.resets ∧
                        ∀ e ∈ exp013ResetInto (E cfg X) t.name P,
                          e.src = NodeRef.trans t.name ∧
                            e.row = EdgeRow.reset ∧ e.dashed = false ∧ e.label = some "reset") ∧
                  (P ∉ t.core.resets →
                      ∀ e ∈ exp013OutInto (E cfg X) t.name P, e.arc = ArcType.output ∧ e.row = EdgeRow.output) ∧
                    (exp013OutInto (E cfg X) t.name P).length = List.count P t.outLeaves) ∧
      ∀ e ∈ (E cfg X).edges,
        e.arc = ArcType.resetOutput →
          ∃ t ∈ X.trans, e.src.owner? = some t.name ∧ ∃ P ∈ t.core.resets, e.dst = NodeRef.place P
-/
#guard_msgs in #print EXP_013

/-! ### The reference -/

section Reference

variable {S : ClusterStage} {cfg : ExportCfg} {X : ExportNet}

/-- The output-side edges of `t` into `P` in the reference's graph are the edges the reference
emitter draws for `t` into `P`, whatever the cluster stage. -/
theorem exp013OutInto_ref (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) (P : String) :
    exp013OutInto (refExportWith S cfg X) t.name P =
      (refEmit.ofTrans t).edges.filter fun e => e.dst == .place P := by
  unfold exp013OutInto
  rw [refExportWith_filter_trans hX ht]
  · have hc : (fun e : XEdge => XEdge.outSideOf t.name e && e.dst == .place P) =
        fun e => (e.dst == .place P) && XEdge.outSideOf t.name e :=
      funext fun e => Bool.and_comm _ _
    rw [hc, ← List.filter_filter, refTransEdges_filter_outSide, if_pos rfl]
  · intro e he
    simp only [XEdge.outSideOf, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at he
    obtain ⟨⟨ho, ha⟩, -⟩ := he
    refine ⟨?_, Or.inl ho⟩
    rcases ha with ha | ha <;> rw [ha] <;> exact nofun

/-- The reset edges of `t` into `P` in the reference's graph are its standalone reset edges on
`P`, one per reset arc on `P` whose place no output leaf names, whatever the cluster stage. -/
theorem exp013ResetInto_ref (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) (P : String) :
    exp013ResetInto (refExportWith S cfg X) t.name P =
      ((refStandaloneResets t).filter fun p => p == P).map (refResetEdge t) := by
  unfold exp013ResetInto
  rw [refExportWith_filter_trans hX ht]
  · simp only [refTransEdges, List.filter_append, List.filter_map]
    have e1 : t.core.inputs.filter ((fun e : XEdge => e.arc == .reset && e.src.owner? == some t.name &&
        e.dst == .place P) ∘ refInputEdge t) = [] := by
      rw [List.filter_eq_nil_iff]; intro s _; simp [refInputEdge]
    have e2 : (refEmit.ofTrans t).edges.filter (fun e : XEdge => e.arc == .reset &&
        e.src.owner? == some t.name && e.dst == .place P) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      rcases (refEmit_ofTrans_arc he).1 with ⟨ha, _⟩ | ⟨ha, _⟩ <;> simp [ha]
    have e3 : t.core.inhibitors.filter ((fun e : XEdge => e.arc == .reset &&
        e.src.owner? == some t.name && e.dst == .place P) ∘ refInhibitorEdge t) = [] := by
      rw [List.filter_eq_nil_iff]; intro s _; simp [refInhibitorEdge]
    have e4 : t.core.reads.filter ((fun e : XEdge => e.arc == .reset &&
        e.src.owner? == some t.name && e.dst == .place P) ∘ refReadEdge t) = [] := by
      rw [List.filter_eq_nil_iff]; intro s _; simp [refReadEdge]
    have e5 : (refStandaloneResets t).filter ((fun e : XEdge => e.arc == .reset &&
        e.src.owner? == some t.name && e.dst == .place P) ∘ refResetEdge t) =
        (refStandaloneResets t).filter fun p => p == P := by
      apply List.filter_congr
      intro p _
      simp [refResetEdge, NodeRef.owner?]
    rw [e1, e2, e3, e4, e5]
    simp
  · intro e he
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨ha, ho⟩, -⟩ := he
    exact ⟨by rw [ha]; exact nofun, Or.inl ho⟩

/-- Counting a place among the places a list of edges ends in counts the edges into it. -/
theorem exp013_count_placeTarget (P : String) :
    ∀ l : List XEdge, (l.filterMap XEdge.placeTarget).count P =
      (l.filter fun e => e.dst == .place P).length
  | [] => rfl
  | e :: l => by
    have ih := exp013_count_placeTarget P l
    rcases e with ⟨src, dst, arc, row, dashed, label, ltail, lhead⟩
    rw [List.filterMap_cons, List.filter_cons]
    cases dst with
    | place q =>
      have hq : XEdge.placeTarget ⟨src, .place q, arc, row, dashed, label, ltail, lhead⟩ = some q :=
        rfl
      rw [hq]
      by_cases h : q = P
      · subst h; simp [ih]
      · simp [ih, h]
    | trans u =>
      have hq : XEdge.placeTarget ⟨src, .trans u, arc, row, dashed, label, ltail, lhead⟩ = none :=
        rfl
      rw [hq]; simp [ih]
    | junction u k i =>
      have hq : XEdge.placeTarget ⟨src, .junction u k i, arc, row, dashed, label, ltail, lhead⟩ =
        none := rfl
      rw [hq]; simp [ih]

/-- **The reference exporter satisfies EXP-013, whatever its cluster stage.** The output-side
edges into a reset place are the emitter's combined edges (`refEmit_ofTrans_arc`), one per leaf
(`refEmit_ofTrans_places`); the reset edges are the standalone reset edges of the places no
output leaf names (`refStandaloneResets`). -/
theorem EXP_013_any (S : ClusterStage) : EXP_013 (refExportWith S) := by
  intro cfg X
  refine ⟨fun hX t ht P => ?_, ?_⟩
  swap
  · intro e he ha
    rw [refExportWith_edges, List.mem_append] at he
    rcases he with he | he
    · rw [refEdges, List.mem_flatMap] at he
      obtain ⟨t, ht, he⟩ := he
      refine ⟨t, ht, ?_⟩
      rcases mem_refTransEdges.mp he with ⟨s, -, rfl⟩ | he | ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩ |
          ⟨p, -, -, rfl⟩
      · simp [refInputEdge] at ha
      · exact ⟨refEmit_ofTrans_owner he, (refEmit_ofTrans_arc he).2.1.mp ha⟩
      · simp [refInhibitorEdge] at ha
      · simp [refReadEdge] at ha
      · simp [refResetEdge] at ha
    · rw [S.ghosts_arc _ _ _ _ e he] at ha; cases ha
  rw [exp013OutInto_ref hX ht, exp013ResetInto_ref hX ht]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hP e he
    rw [List.mem_filter, beq_iff_eq] at he
    obtain ⟨he, hd⟩ := he
    obtain ⟨hc, hiff, -⟩ := refEmit_ofTrans_arc he
    have ha : e.arc = .resetOutput := hiff.mpr ⟨P, hP, hd⟩
    rcases hc with ⟨h1, _⟩ | h
    · rw [ha] at h1; cases h1
    · exact h
  · intro _ hL
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hpP
    rw [beq_iff_eq] at hpP
    subst hpP
    simp only [refStandaloneResets, List.mem_filter, decide_eq_true_eq] at hp
    exact hp.2 hL
  · intro _ hL
    refine ⟨?_, ?_⟩
    · rw [List.length_map, List.count_eq_length_filter, refStandaloneResets, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro p _
      by_cases h : p = P
      · subst h; simp [hL]
      · simp [h]
    · intro e he
      rw [List.mem_map] at he
      obtain ⟨p, -, rfl⟩ := he
      exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hP e he
    rw [List.mem_filter, beq_iff_eq] at he
    obtain ⟨he, hd⟩ := he
    obtain ⟨hc, hiff, -⟩ := refEmit_ofTrans_arc he
    rcases hc with h1 | ⟨h1, _⟩
    · exact h1
    · obtain ⟨p, hp, hpd⟩ := hiff.mp h1
      rw [hd] at hpd
      cases hpd
      exact absurd hp hP
  · rw [← exp013_count_placeTarget, refEmit_ofTrans_places]

end Reference

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-013 (`EXP_013_any` at the reference cluster stage). -/
@[evidence holds EXP_013]
theorem EXP_013_reference : EXP_013 refExport := EXP_013_any _

/-! ### Wrong exporters, one per line -/

/-- How a leaf edge is drawn: from the reset places `R`, the parent node, the leaf's place, whether
the leaf is a `ForwardInput` and the inherited label, the edges drawn for the leaf. -/
abbrev Exp013Leaf := List String → NodeRef → String → Bool → Option String → List XEdge

/-- A copy of the reference walk (`refEmitOut`) with the leaf edge as a parameter: groups,
junction numbering, branch and timeout labels as the reference draws them. -/
def exp013Walk (leaf : Exp013Leaf) : Emitter := fun t R o =>
  (go t R (.trans t) none o (0, {})).2
where
  /-- The walk over one subtree. -/
  go (t : String) (R : List String) (par : NodeRef) (l : Option String) :
      OutTree → Nat × Emitted → Nat × Emitted
    | .place p, (n, e) => (n, { e with edges := e.edges ++ leaf R par p false l })
    | .forward src dst, (n, e) =>
      (n, { e with edges := e.edges ++ leaf R par dst true (some (forwardLabel l src)) })
    | .timeout ms c, s => go t R par (some (timeoutLabel ms)) c s
    | .and cs, (n, e) =>
      if 2 ≤ cs.length then
        goL t R (.junction t .and n) (.junction .and) cs
          (n + 1, { junctions := e.junctions ++ [(.and, n)],
                    edges := e.edges ++ [refJunctionEdge par (.junction t .and n) l] })
      else goL t R par (.pass l) cs (n, e)
    | .xor cs, (n, e) =>
      if 2 ≤ cs.length then
        goL t R (.junction t .xor n) (.junction .xor) cs
          (n + 1, { junctions := e.junctions ++ [(.xor, n)],
                    edges := e.edges ++ [refJunctionEdge par (.junction t .xor n) l] })
      else goL t R par (.pass l) cs (n, e)
  /-- The walk over the children of a group. -/
  goL (t : String) (R : List String) (par : NodeRef) (u : Under) :
      List OutTree → Nat × Emitted → Nat × Emitted
    | [], s => s
    | c :: cs, s => goL t R par u cs (go t R par (u.label c) c s)

/-- With the reference's leaf edge the walk is the reference emitter, checked on a tree with an
`Xor` and an `And` junction, a `Timeout` and a `ForwardInput` into a reset place. -/
theorem exp013Walk_ref_example :
    exp013Walk (fun R par p d l => [refLeafEdge R par p d l]) "T" ["P"]
        (.xor [.place "P", .and [.timeout 5 (.forward "In" "P"), .place "Q"]]) =
      refEmit "T" ["P"] (.xor [.place "P", .and [.timeout 5 (.forward "In" "P"), .place "Q"]]) := by
  decide

/-- An exporter built as the reference is, with three parts swapped: the output emitter `Em`, the
reset places `rs X t` the emitter is handed, and the places `sa t` that get a standalone reset
edge. Nodes and clusters are the reference's. -/
def exp013Export (Em : Emitter) (rs : ExportNet → ExportTrans → List String)
    (sa : ExportTrans → List String) : Exporter := fun cfg X =>
  { refExportFlat cfg X with
    edges := X.trans.flatMap fun t =>
      t.core.inputs.map (refInputEdge t) ++
        (match t.out with | some o => (Em t.name (rs X t) o).edges | none => []) ++
        t.core.inhibitors.map (refInhibitorEdge t) ++ t.core.reads.map (refReadEdge t) ++
        (sa t).map (refResetEdge t) }

/-- The reset places of the transition itself, as the reference hands them to the emitter. -/
def exp013OwnResets : ExportNet → ExportTrans → List String := fun _ t => t.core.resets

/-- A one-transition net: transition `T` with input `In`, output tree `o` and reset arcs `rs`. -/
def exp013Net (o : OutTree) (rs : List String) : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"In", .one⟩], [], [], rs⟩, out := some o }] }

/-- The pre-EXP-013 mapper: plain output edges whatever the resets, and a standalone reset edge
for every reset arc. -/
def exp013_preCombine : Exporter :=
  exp013Export (exp013Walk fun _ par p d l => [refLeafEdge [] par p d l]) exp013OwnResets
    (·.core.resets)

/-- ✗ The pre-EXP-013 mapper violates EXP-013 on `Out.Place(P)` with `reset(P)` (line 1: the
edge into `P` is a plain output edge; AC1). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_preCombine : ¬ EXP_013 exp013_preCombine := by
  intro h
  have := ((h {} (exp013Net (.place "P") ["P"])).1 (by decide) _ (List.mem_singleton_self _) "P").1
    (by decide)
  revert this
  decide

/-- A mapper that combines a leaf edge only when it starts at the transition, not below a
junction. -/
def exp013_directOnly : Exporter :=
  exp013Export (exp013Walk fun R par p d l =>
    match par with
    | .trans _ => [refLeafEdge R par p d l]
    | _ => [refLeafEdge [] par p d l]) exp013OwnResets refStandaloneResets

/-- ✗ Combining only direct leaves violates EXP-013 on `Out.Xor(P, Q)` with `reset(P)` (line 1:
the edge from the junction into `P` stays a plain output edge; AC4). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_directOnly : ¬ EXP_013 exp013_directOnly := by
  intro h
  have := ((h {} (exp013Net (.xor [.place "P", .place "Q"]) ["P"])).1 (by decide) _
    (List.mem_singleton_self _) "P").1 (by decide)
  revert this
  decide

/-- A mapper whose combined edge keeps the label the leaf edge would carry (the branch label of an
`Xor` child). -/
def exp013_keepLabel : Exporter :=
  exp013Export (exp013Walk fun R par p d l =>
    if p ∈ R then [⟨par, .place p, .resetOutput, .resetOutput, false, l, none, none⟩]
    else [refLeafEdge R par p d l]) exp013OwnResets refStandaloneResets

/-- ✗ Keeping the branch label `P` on the combined edge violates EXP-013 on `Out.Xor(P, Q)` with
`reset(P)` (line 1: the combined edge is labelled `reset+out`; ruling D26 item 3). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_keepLabel : ¬ EXP_013 exp013_keepLabel := by
  intro h
  have := ((h {} (exp013Net (.xor [.place "P", .place "Q"]) ["P"])).1 (by decide) _
    (List.mem_singleton_self _) "P").1 (by decide)
  revert this
  decide

/-- A mapper whose combined edge for a `ForwardInput` leaf stays dashed. -/
def exp013_keepDash : Exporter :=
  exp013Export (exp013Walk fun R par p d l =>
    if p ∈ R then [⟨par, .place p, .resetOutput, .resetOutput, d, some "reset+out", none, none⟩]
    else [refLeafEdge R par p d l]) exp013OwnResets refStandaloneResets

/-- ✗ A dashed combined edge violates EXP-013 on `Timeout(5, ForwardInput(In, P))` with
`reset(P)` (line 1: the combined edge is not dashed; ruling D26 item 3). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_keepDash : ¬ EXP_013 exp013_keepDash := by
  intro h
  have := ((h {} (exp013Net (.timeout 5 (.forward "In" "P")) ["P"])).1 (by decide) _
    (List.mem_singleton_self _) "P").1 (by decide)
  revert this
  decide

/-- A mapper that draws the combined edge and keeps the standalone reset edge beside it. -/
def exp013_keepReset : Exporter := exp013Export refEmit exp013OwnResets (·.core.resets)

/-- ✗ Keeping the standalone reset edge beside the combined edge violates EXP-013 on
`Out.Place(P)` with `reset(P)` (line 2; AC1: no standalone reset edge labelled `reset`). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_keepReset : ¬ EXP_013 exp013_keepReset := by
  intro h
  have := ((h {} (exp013Net (.place "P") ["P"])).1 (by decide) _ (List.mem_singleton_self _)
    "P").2.1 (by decide) (by decide)
  revert this
  decide

/-- A mapper that suppresses every standalone reset edge of a transition that has an output
spec, the sentence "the standalone reset edge to P MUST be suppressed" read without its place. -/
def exp013_dropResets : Exporter :=
  exp013Export refEmit exp013OwnResets fun t => if t.out.isSome then [] else t.core.resets

/-- ✗ Dropping the reset edge into `R` of a transition with `Out.Place(P)`, `reset(P)` and
`reset(R)` violates EXP-013 (line 3: the reset edge into `R` is still drawn; AC3). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_dropResets : ¬ EXP_013 exp013_dropResets := by
  intro h
  have := (((h {} (exp013Net (.place "P") ["P", "R"])).1 (by decide) _
    (List.mem_singleton_self _) "R").2.2.1 (by decide) (by decide)).1
  revert this
  decide

/-- A mapper that hands the emitter the reset places of the whole net, not those of the
transition. -/
def exp013_netResets : Exporter :=
  exp013Export refEmit (fun X _ => X.trans.flatMap (·.core.resets)) refStandaloneResets

/-- A two-transition net: `T` outputs to `P`, `U` resets `P`. -/
def exp013NetTU : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"In", .one⟩], [], [], []⟩, out := some (.place "P") },
              { core := ⟨"U", [⟨"In", .one⟩], [], [], ["P"]⟩ }] }

/-- ✗ Combining the edge of `T` into `P` because another transition resets `P` violates EXP-013
(line 4: `T` does not reset `P`, so its edge into `P` is a plain output edge; AC2). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_netResets : ¬ EXP_013 exp013_netResets := by
  intro h
  have := ((h {} exp013NetTU).1 (by decide) _ List.mem_cons_self "P").2.2.2.1 (by decide)
  revert this
  decide

/-- A mapper that draws no edge for a leaf into a reset place: neither a combined edge nor a
plain one, and no standalone reset edge either. -/
def exp013_noEdge : Exporter :=
  exp013Export (exp013Walk fun R par p d l => if p ∈ R then [] else [refLeafEdge R par p d l])
    exp013OwnResets refStandaloneResets

/-- ✗ Drawing nothing into `P` for `Out.Place(P)` with `reset(P)` violates EXP-013 (line 5: one
edge into `P` per leaf; AC1). Every other line holds of this mapper on that net, which is why the
existence line is there. -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_noEdge : ¬ EXP_013 exp013_noEdge := by
  intro h
  have := ((h {} (exp013Net (.place "P") ["P"])).1 (by decide) _ (List.mem_singleton_self _)
    "P").2.2.2.2
  revert this
  decide

/-! ### Wrong exporters found by the mutation review

Each is the reference exporter with its edges rewritten (`exp013Map`) or extended
(`exp013Extra`): the slip one runtime line would make. -/

/-- The reference exporter with every edge rewritten by `f`. -/
def exp013Map (f : ExportNet → XEdge → XEdge) : Exporter := fun cfg X =>
  { refExportFlat cfg X with edges := (refExportFlat cfg X).edges.map (f X) }

/-- The reference exporter with the edges `g X` drawn after its own. -/
def exp013Extra (g : ExportNet → List XEdge) : Exporter := fun cfg X =>
  { refExportFlat cfg X with edges := (refExportFlat cfg X).edges ++ g X }

/-- A mapper that draws the combined edge with arc type reset-output but in the output row. -/
def exp013_comboRow : Exporter :=
  exp013Map fun _ e => if e.arc = .resetOutput then { e with row := .output } else e

/-- ✗ A combined edge in the output row violates EXP-013 on `Out.Place(P)` with `reset(P)`
(line 1: the combined edge is in the reset-output style; AC1). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_comboRow : ¬ EXP_013 exp013_comboRow := by
  intro h
  have := ((h {} (exp013Net (.place "P") ["P"])).1 (by decide) _ (List.mem_singleton_self _)
    "P").1 (by decide)
  revert this
  decide

/-- A mapper that labels the standalone reset edge `reset+out`. The reset and reset-output rows
of the style table draw alike, so the label is what tells AC3's edge from AC1's. -/
def exp013_resetLabel : Exporter :=
  exp013Map fun _ e => if e.arc = .reset then { e with label := some "reset+out" } else e

/-- ✗ A standalone reset edge labelled `reset+out` violates EXP-013 on `Out.Place(Q)` with
`reset(P)` (line 3: the reset edge is labelled `reset`; AC3). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_resetLabel : ¬ EXP_013 exp013_resetLabel := by
  intro h
  have := (((h {} (exp013Net (.place "Q") ["P"])).1 (by decide) _ (List.mem_singleton_self _)
    "P").2.2.1 (by decide) (by decide)).2
  revert this
  decide

/-- A mapper that draws the standalone reset edge from the first `Xor` junction of the
transition instead of from the transition. -/
def exp013_resetFromJunction : Exporter :=
  exp013Map fun _ e =>
    if e.arc = .reset then
      match e.src with
      | .trans u => { e with src := .junction u .xor 0 }
      | _ => e
    else e

/-- ✗ A standalone reset edge drawn from a junction violates EXP-013 on `Out.Xor(Q, R)` with
`reset(P)` (line 3: the reset edge starts at the node of the transition). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_resetFromJunction : ¬ EXP_013 exp013_resetFromJunction := by
  intro h
  have := (((h {} (exp013Net (.xor [.place "Q", .place "R"]) ["P"])).1 (by decide) _
    (List.mem_singleton_self _) "P").2.2.1 (by decide) (by decide)).2
  revert this
  decide

/-- Each element once, at its first occurrence: what iterating an insertion-ordered set of the
reset places gives. -/
def exp013Dedup : List String → List String
  | [] => []
  | p :: ps => p :: (exp013Dedup ps).filter (fun q => q != p)

/-- A mapper whose standalone reset loop iterates the set of reset places (the set the Rust,
Java and TypeScript mappers build for the combined edge) instead of the reset arcs. -/
def exp013_setResets : Exporter :=
  exp013Export refEmit exp013OwnResets fun t =>
    (exp013Dedup t.core.resets).filter fun p => decide (p ∉ t.outLeaves)

/-- ✗ One reset edge for the two reset arcs `reset(P), reset(P)` violates EXP-013 on
`Out.Place(Q)` (line 3: one reset edge per reset arc on `P`, here two). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_setResets : ¬ EXP_013 exp013_setResets := by
  intro h
  have := (((h {} (exp013Net (.place "Q") ["P", "P"])).1 (by decide) _
    (List.mem_singleton_self _) "P").2.2.1 (by decide) (by decide)).1
  revert this
  decide

/-- A mapper that decides the arc type of an output edge per transition but looks its row, dash
and label up in the reset places of the whole net. -/
def exp013_netStyle : Exporter :=
  exp013Map fun X e =>
    match e.arc, e.dst with
    | .output, .place p =>
      if X.trans.any (fun v => v.core.resets.contains p) then
        { e with row := .resetOutput, dashed := false, label := some "reset+out" }
      else e
    | _, _ => e

/-- ✗ An output edge of `T` into `P` drawn like a combined edge because `U` resets `P` violates
EXP-013 (line 4: `T` does not reset `P`, so its edge into `P` is in the output row; AC2). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_netStyle : ¬ EXP_013 exp013_netStyle := by
  intro h
  have := ((h {} exp013NetTU).1 (by decide) _ List.mem_cons_self "P").2.2.2.1 (by decide)
  revert this
  decide

/-- A mapper that draws the edge from the parent into a junction as a combined edge whenever the
transition has a reset arc (testing "the transition resets something" where the leaf edge tests
"this leaf's place is reset"). -/
def exp013_junctionReset : Exporter :=
  exp013Map fun X e =>
    match e.dst with
    | .junction u _ _ =>
      if X.trans.any (fun v => v.name == u && !v.core.resets.isEmpty) then
        { e with arc := .resetOutput, row := .resetOutput, label := some "reset+out" }
      else e
    | _ => e

/-- ✗ A combined edge `t_T → j_T__xor_0` violates EXP-013 on `Out.Xor(P, Q)` with `reset(P)`
(line 6: a reset-output edge ends in a place; AC4: the junction → P edge is the reset-styled
one). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_junctionReset : ¬ EXP_013 exp013_junctionReset := by
  intro h
  have := (h {} (exp013Net (.xor [.place "P", .place "Q"]) ["P"])).2
  revert this
  decide

/-- A mapper that draws each combined edge a second time from the place back to the transition,
as if reset+out were a reset arc in the place to transition direction and an output arc. -/
def exp013_bothWays : Exporter :=
  exp013Extra fun X => X.trans.flatMap fun t =>
    (t.core.resets.filter fun p => decide (p ∈ t.outLeaves)).map fun p =>
      ⟨.place p, .trans t.name, .resetOutput, .resetOutput, false, some "reset+out", none, none⟩

/-- ✗ A second combined edge `p_P → t_T` violates EXP-013 on `Out.Place(P)` with `reset(P)`
(line 6: a reset-output edge starts at a transition or one of its junctions). -/
@[evidence forbids EXP_013]
theorem EXP_013_forbids_bothWays : ¬ EXP_013 exp013_bothWays := by
  intro h
  have := (h {} (exp013Net (.place "P") ["P"])).2
  revert this
  decide

/-! ### Non-vacuity: the acceptance criteria on the reference -/

/-- What the block sees of an edge: source and target IDs, arc type, style row, dash, label. -/
def exp013View (e : XEdge) : (String × String) × (ArcType × EdgeRow × Bool × Option String) :=
  ((nodeId e.src, nodeId e.dst), (e.arc, e.row, e.dashed, e.label))

/-- AC1 to AC4 and the D26 cases on the reference exporter. AC1: `Out.Place(P)` with `reset(P)`
draws one combined edge `T → P` and no reset edge. AC2: `Out.Place(P)` without a reset one plain
output edge. AC3: `reset(P)` without an output to `P` one reset edge labelled `reset`. AC4:
`Out.Xor(P, Q)` with `reset(P)` a combined edge from the junction into `P` and a plain edge
labelled `Q` into `Q`. D26 item 4: `Xor(P, And(P, Q))` with `reset(P)` one combined edge per
leaf. D26 item 3: `Timeout(5, ForwardInput(In, P))` with `reset(P)` an undashed combined edge
labelled `reset+out` alone. -/
@[evidence nonvacuous EXP_013]
theorem EXP_013_nonvacuous :
    (exp013OutInto (refExportFlat {} (exp013Net (.place "P") ["P"])) "T" "P").map exp013View =
      [(("t_T", "p_P"), (.resetOutput, .resetOutput, false, some "reset+out"))] ∧
    exp013ResetInto (refExportFlat {} (exp013Net (.place "P") ["P"])) "T" "P" = [] ∧
    (exp013OutInto (refExportFlat {} (exp013Net (.place "P") [])) "T" "P").map exp013View =
      [(("t_T", "p_P"), (.output, .output, false, none))] ∧
    (exp013ResetInto (refExportFlat {} (exp013Net (.place "Q") ["P"])) "T" "P").map exp013View =
      [(("t_T", "p_P"), (.reset, .reset, false, some "reset"))] ∧
    exp013OutInto (refExportFlat {} (exp013Net (.place "Q") ["P"])) "T" "P" = [] ∧
    (exp013OutInto (refExportFlat {} (exp013Net (.xor [.place "P", .place "Q"]) ["P"])) "T"
        "P").map exp013View =
      [(("j_T__xor_0", "p_P"), (.resetOutput, .resetOutput, false, some "reset+out"))] ∧
    (exp013OutInto (refExportFlat {} (exp013Net (.xor [.place "P", .place "Q"]) ["P"])) "T"
        "Q").map exp013View =
      [(("j_T__xor_0", "p_Q"), (.output, .output, false, some "Q"))] ∧
    (exp013OutInto (refExportFlat {} (exp013Net (.xor [.place "P", .and [.place "P", .place "Q"]])
        ["P"])) "T" "P").map exp013View =
      [(("j_T__xor_0", "p_P"), (.resetOutput, .resetOutput, false, some "reset+out")),
       (("j_T__and_1", "p_P"), (.resetOutput, .resetOutput, false, some "reset+out"))] ∧
    (exp013OutInto (refExportFlat {} (exp013Net (.timeout 5 (.forward "In" "P")) ["P"])) "T"
        "P").map exp013View =
      [(("t_T", "p_P"), (.resetOutput, .resetOutput, false, some "reset+out"))] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Libpetri.Spec
