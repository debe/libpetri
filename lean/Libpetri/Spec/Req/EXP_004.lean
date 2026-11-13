import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster

set_option linter.missingDocs true

/-!
# EXP-004: Arc rendering (`spec/09-export.md`)

How an exporter draws each of the five arc types: the arc type of the drawn edge, its drawn
direction (which node it starts at and which it ends at), its style row of
`spec/petri-net-styles.json` (`Libpetri.Export.EdgeRow`), whether it is drawn dashed in place of
the row's line style, and its fixed label. The requirement is a predicate over an abstract
exporter `E : Exporter` (glossary `GlossaryExport.lean`), one line per arc type. Each line has two
halves: every arc of that type is drawn as such an edge (`exp004InputEdge` and its siblings
below), and every drawn edge of that arc type is the edge of one such arc. Line (output) has a
third part: the edge of every `ForwardInput` leaf into a place the transition does not reset is
drawn dashed and labelled with its source place (`exp004ForwardEdge`).

The witness is the reference exporter `refExportWith S` for every cluster stage `S`
(`EXP_004_any`), recorded on the clustered exporter `refExport` (`EXP_004_reference`). The wrong exporters are the
reference with one kind of edge redrawn: input edges reversed, output edges drawn from the place
to the transition (design mutant), every output edge dashed, the `ForwardInput` edge drawn solid
(the dash flag of the `Place` leaf passed from the `ForwardInput` arm), inhibitor edges in the
input row (design mutant: a normal arrowhead in the input colour), inhibitor edges labelled
`read` (the read loop copied with its label), read edges solid and without label (design
mutant), reset edges drawn from the place to the transition (the glossary's arc direction, which
ruling D20 keeps out of the drawing), no reset edge at all, a standalone reset edge also into
a place a leaf ends in, and the combined edge into a reset place drawn as the dashed
`ForwardInput` output edge it replaces.

"Visually distinct" (AC1) follows from the statement: `EXP_004_distinguishable` shows that two
edges of different types among the five differ in drawn direction or in the row's colour, line
style, arrowhead and pen width, without reading any label.

The sentences are the restatement of ruling D20 (map ruling EXPA-R4, option (a)): the forward
edge and the drawn direction of the reset edge are stated as all three mappers draw them, and the
"or" alternatives give way to the rows of the style table.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export
open Libpetri.Novel.Seam (NInSpec)

/-! ## Block-local vocabulary -/

mutual
/-- The `ForwardInput` leaves of an output tree, as (source place, target place), left to
right. -/
def exp004Forwards : OutTree → List (String × String)
  | .place _ => []
  | .forward s d => [(s, d)]
  | .timeout _ c => exp004Forwards c
  | .and cs => exp004ForwardsL cs
  | .xor cs => exp004ForwardsL cs
/-- `exp004Forwards` of a list of children, concatenated. -/
def exp004ForwardsL : List OutTree → List (String × String)
  | [] => []
  | c :: cs => exp004Forwards c ++ exp004ForwardsL cs
end

/-- The `ForwardInput` leaves of a transition's output spec; none without one. -/
def exp004TransForwards (t : ExportTrans) : List (String × String) :=
  (t.out.map exp004Forwards).getD []

/-- `e` is drawn for input arc `s` of `t` as EXP-004 says: arc type `input`, from the place to the
transition, solid, in the `match-input` row when the place is correlated ([EXP-018]) and in the
`input` row otherwise. -/
def exp004InputEdge (t : ExportTrans) (s : NInSpec String) (e : XEdge) : Prop :=
  e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name ∧ e.dashed = false ∧
    e.row = (if s.place ∈ t.corr then .matchInput else .input)

/-- `e` is an output edge of `t` as EXP-004 says: arc type `output`, `output` row, from the
transition or one of its junction nodes to a place or to a junction node of `t`, and solid unless
it ends in the target `P` of a `ForwardInput` leaf from `F` of `t`, `P` a place `t` does not
reset, and is labelled `⟵F` after some label and a space, or alone. -/
def exp004OutputEdge (t : ExportTrans) (e : XEdge) : Prop :=
  e.arc = .output ∧ e.row = .output ∧ e.src.owner? = some t.name ∧
    (e.dst.place?.isSome ∨ (e.dst.junctionOf t.name).isSome) ∧
    (e.dashed = true →
      ∃ fw ∈ exp004TransForwards t, fw.2 ∉ t.core.resets ∧ e.dst = .place fw.2 ∧
        ∃ l, e.label = some (forwardLabel l fw.1))

/-- `e` is the edge of the `ForwardInput` leaf `fw = (F, P)` of `t` as EXP-004 says: an output
edge of `t` that ends in `P`, is dashed, and is labelled `⟵F` after some label and a space, or
alone. -/
def exp004ForwardEdge (t : ExportTrans) (fw : String × String) (e : XEdge) : Prop :=
  exp004OutputEdge t e ∧ e.dst = .place fw.2 ∧ e.dashed = true ∧
    ∃ l, e.label = some (forwardLabel l fw.1)

/-- `e` is drawn for the inhibitor arc of `t` on `p`: arc type `inhibitor`, from the place to the
transition, `inhibitor` row, solid, without a label. -/
def exp004InhibitorEdge (t : ExportTrans) (p : String) (e : XEdge) : Prop :=
  e.arc = .inhibitor ∧ e.src = .place p ∧ e.dst = .trans t.name ∧ e.row = .inhibitor ∧
    e.dashed = false ∧ e.label = none

/-- `e` is drawn for the read arc of `t` on `p`: arc type `read`, from the place to the
transition, `read` row, labelled `read`. -/
def exp004ReadEdge (t : ExportTrans) (p : String) (e : XEdge) : Prop :=
  e.arc = .read ∧ e.src = .place p ∧ e.dst = .trans t.name ∧ e.row = .read ∧
    e.label = some "read"

/-- `e` is drawn for the reset arc of `t` on `p`: arc type `reset`, from the transition to the
place (the drawing convention), `reset` row (bold), not dashed, labelled `reset`. -/
def exp004ResetEdge (t : ExportTrans) (p : String) (e : XEdge) : Prop :=
  e.arc = .reset ∧ e.src = .trans t.name ∧ e.dst = .place p ∧ e.row = .reset ∧
    e.dashed = false ∧ e.label = some "reset"

/-! ## EXP-004: Arc rendering -/

requirement EXP_004
  id "EXP-004"
  title "Arc Rendering"
  kind F
  scope "every exporter, the input, output, inhibitor, read and reset edges"
  source verbatim "spec/09-export.md"
  quote "Each arc type has a visually distinct rendering."
        "Input arc: solid arrow from place to transition, row `input` (a correlated input of [EXP-018] takes row `match-input`)"
        "Output arc: solid arrow from transition, or from one of its junction nodes ([EXP-012]), to place, row `output`; the edge of a `ForwardInput` leaf is dashed and labelled with its source place ([EXP-012])"
        "Inhibitor arc: arrow with circle arrowhead (standard notation) from place to transition, without a label, row `inhibitor`"
        "Read arc: dashed arrow from place to transition, labelled `read`, row `read`"
        "Reset arc: bold arrow from transition to place, labelled `reset`, row `reset`; a reset arc into a place that a leaf of the output spec also ends in is drawn as the combined edge of [EXP-013]"
        "The reset edge points from the transition to the place it empties. This is a drawing convention: the reset arc itself goes from the place to the transition ([CORE-034])."
        "Visually distinct means that any two edges of different types among these five differ in drawn direction, colour, line style or arrowhead."
        "The mapper *shall* draw each input arc as a solid edge of arc type `input` from its place to its transition, in the `match-input` row where [EXP-018] correlates its place and in the `input` row otherwise."
        "The mapper *shall* draw each output arc of a transition into a place that the transition does not reset as an edge of arc type `output` in the `output` row, from the transition or one of its junction nodes to the place."
        "Every edge of arc type `output` that the mapper draws *shall* run from a transition or one of its junction nodes to a place or to a junction node of that transition, in the `output` row."
        "An edge of arc type `output` *shall* be solid, except the edge of a `ForwardInput` leaf of its transition's output spec from place F to a place P that the transition does not reset, which is dashed, ends in P and is labelled `⟵F`, after another label and a space when it has one."
        "The mapper *shall* draw each inhibitor arc as a solid edge of arc type `inhibitor` from its place to its transition, in the `inhibitor` row and without a label."
        "The mapper *shall* draw each read arc as an edge of arc type `read` from its place to its transition, in the `read` row and labelled `read`."
        "*Where* no leaf of a transition's output spec ends in the place of one of its reset arcs, the mapper *shall* draw that reset arc as an undashed edge of arc type `reset` from the transition to the place, in the `reset` row and labelled `reset`."
        "Every edge of arc type `input`, `inhibitor`, `read` or `reset` that the mapper draws *shall* be the edge of one arc of that type, with the ends, row and line style the sentences above give it and the label they give it where they give one; an edge of arc type `reset` is the edge of a reset arc into a place that no leaf of its transition's output spec ends in."
  reading "For every configuration cfg and net X, in the drawn graph E cfg X:"
          "(input) every input arc s of every transition t of X has an edge drawn for it (exp004InputEdge t s: arc type input, from the place of s to the node of t, solid, row match-input if t correlates the place, else row input), and every edge of arc type input is drawn so for some input arc of some transition of X;"
          "(output) for every transition t of X and every leaf place p of its output spec that t does not reset, some edge into p is an output edge of t (exp004OutputEdge t: arc type output, row output, from the node of t or one of its junctions, into a place or a junction of t, and dashed only if it ends in the target P of a ForwardInput leaf from F of t, with P a place t does not reset, and is labelled forwardLabel l F for some l), for every ForwardInput leaf from F to P of t with P not reset by t, some output edge of t into P is dashed and labelled forwardLabel l F for some l (exp004ForwardEdge t), and every edge of arc type output is an output edge of some transition of X;"
          "(inhibitor) every inhibitor arc of every transition has an edge drawn for it (exp004InhibitorEdge: arc type inhibitor, place to transition, row inhibitor, solid, no label), and every edge of arc type inhibitor is drawn so for some inhibitor arc;"
          "(read) every read arc has an edge drawn for it (exp004ReadEdge: arc type read, place to transition, row read, label read), and every edge of arc type read is drawn so for some read arc;"
          "(reset) every reset arc of t on a place that no leaf of t's output spec ends in has an edge drawn for it (exp004ResetEdge: arc type reset, from the node of t to the place, row reset, not dashed, label reset), and every edge of arc type reset is drawn so for some reset arc of some transition t on a place that no leaf of t's output spec ends in."
  assumes "The model is an exporter E : Exporter (glossary): from a configuration and the export view of a net (ExportNet: declared places, transitions with their core arcs, n-ary output tree, timing, priority and correlated places), the drawn graph (XGraph). An edge (XEdge) has two ends (NodeRef: a transition, a junction of a transition, a place), an arc type, a style row of the edge table (Libpetri.Export.EdgeRow, generated from spec/petri-net-styles.json), a dashed flag that overrides the row's line style, a label and cluster clips. The statement names rows, never colours: the colour, line style, arrowhead and pen width of each row are the generated table (Libpetri.Export.edgeStyle), and the values the runtimes draw are checked against the same JSON by the generator and by tests (kind Q). This is how the second body sentence (each arc type is drawn with the row its bullet names) is read, and why the bullets' words solid, dashed, bold and circle arrowhead are stated as rows: the row input is solid with a normal arrowhead, read dashed, reset bold, inhibitor solid with an odot arrowhead."
          "The five bullets and the eight shall sentences say the same, line by line: the input bullet and the first shall sentence are line (input); the output bullet and the second to fourth are line (output), whose forward part (the edge of a ForwardInput leaf is dashed and labelled with its source place) is the bullet's last clause and the exception of the fourth; the inhibitor bullet and the fifth are line (inhibitor); the read bullet and the sixth are line (read); the reset bullet and the seventh are line (reset). The eighth shall sentence is the second half of lines (input), (inhibitor), (read) and (reset), and its clause on reset edges is the condition p not a leaf of t in the second half of line (reset); the second half of line (output) is the third shall sentence. The label the sentences give is none for an inhibitor edge, read for a read edge and reset for a reset edge; the input sentence gives none, so the label of an input edge is free here (EXP-006, EXP-018)."
          "Drawn direction (AC2) is the ends of each edge: input, inhibitor and read edges start at a place node and end at the node of the arc's transition; output edges start at the transition's node or one of its junction nodes and end at a place or at one of its junction nodes; reset edges start at the transition's node and end at the place. The reset edge's direction is a drawing convention (the two reset sentences of the body): the glossary's reset arc goes from the place to the transition (ResetArc, CORE-034), and drawing it that way violates the block (EXP_004_forbids_resetReversed)."
          "AC1 (each arc type is visually distinguishable) and the body sentence defining visually distinct are EXP_004_distinguishable, proved from the statement alone: for any exporter that meets EXP-004, two drawn edges whose arc types are two different ones of the five have different looks (exp004Look: whether the edge starts at a place, and the row's style with the line style dashed when the edge is drawn dashed), so they differ in drawn direction, colour, line style or arrowhead without reading a label. Input and output edges share the row style (colour, solid, normal arrowhead) and differ in drawn direction; a dashed output edge differs from a read edge in colour. The first body sentence is the same fact."
          "Out of scope here: the combined reset+output edge (arc type resetOutput) is EXP-013's subject, and so are its label reset+out and the leaf edge it replaces (which is why the output existence half and the forward part ask only for places the transition does not reset, and the reset existence half only for places no leaf ends in). The rows reset and reset-output have the same style, so the body sentence on the combined edge (it differs from the reset edge only in its label) is an exception to visually distinct that EXP-013 states; this block reads no label for AC1. That a reset arc into a place a leaf ends in gets no standalone reset edge is stated here as the second half of line (reset) and again by EXP-013. Ghost edges (arc type ghost) are EXP-017's. Which output edges are drawn, from which junction and with which label, is EXP-012's: line (output) fixes only arc type, row, drawn direction, that the edge of each ForwardInput leaf is dashed and labelled with its source place, and that no output edge is dashed unless it ends in the target P of a ForwardInput leaf from F of its transition, P a place the transition does not reset, and is labelled with F (so a dashed output edge into a reset place violates the block, EXP_004_forbids_fwdIntoReset). It does not tie that dash to the leaf's own edge (another output edge of the transition into P with the same label may be dashed too), nor require an output edge to end in a leaf place of its transition: the exact drawing, one edge per leaf from its junction, is EXP-012's, which ExportAgrees carries to the exporter. The labels of input edges (cardinality, EXP-006; the correlation prefix, EXP-018) and EXP-018's choice of correlated places are other blocks'; this block fixes the row of a correlated input edge as the bullet says. That every place and transition has a node is EXP-001's; how many edges an arc gets is EXP-001's line 5 for input, inhibitor and read arcs and EXP-013's for output and reset arcs (this block asks for at least one edge per arc and reads no count)."
          "The test derivation (all five arc types, each with a distinct rendering) is EXP_004_nonvacuous on the reference: a transition with two input arcs (one correlated), an Xor output with a Place leaf and a ForwardInput leaf below a Timeout, an inhibitor, a read and a reset arc, whose drawn edges are listed with their ends, arc types, rows, dash and labels. Line and arrowhead values, pen widths and the DOT text are kind Q."
  signoff "2026-11-13 7d63f79419c27b91 ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, ∃ e ∈ (E cfg X).edges, exp004InputEdge t s e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = .input →
          ∃ t ∈ X.trans, ∃ s ∈ t.core.inputs, exp004InputEdge t s e) ∧
      ((∀ t ∈ X.trans, ∀ p ∈ t.outLeaves, p ∉ t.core.resets →
          ∃ e ∈ (E cfg X).edges, exp004OutputEdge t e ∧ e.dst = .place p) ∧
        (∀ t ∈ X.trans, ∀ fw ∈ exp004TransForwards t, fw.2 ∉ t.core.resets →
          ∃ e ∈ (E cfg X).edges, exp004ForwardEdge t fw e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = .output → ∃ t ∈ X.trans, exp004OutputEdge t e) ∧
      ((∀ t ∈ X.trans, ∀ p ∈ t.core.inhibitors, ∃ e ∈ (E cfg X).edges, exp004InhibitorEdge t p e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = .inhibitor →
          ∃ t ∈ X.trans, ∃ p ∈ t.core.inhibitors, exp004InhibitorEdge t p e) ∧
      ((∀ t ∈ X.trans, ∀ p ∈ t.core.reads, ∃ e ∈ (E cfg X).edges, exp004ReadEdge t p e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = .read →
          ∃ t ∈ X.trans, ∃ p ∈ t.core.reads, exp004ReadEdge t p e) ∧
      ((∀ t ∈ X.trans, ∀ p ∈ t.core.resets, p ∉ t.outLeaves →
          ∃ e ∈ (E cfg X).edges, exp004ResetEdge t p e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = .reset →
          ∃ t ∈ X.trans, ∃ p ∈ t.core.resets, p ∉ t.outLeaves ∧ exp004ResetEdge t p e)

/- The pinned readable form of EXP-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_004 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, ∃ e ∈ (E cfg X).edges, exp004InputEdge t s e) ∧
        ∀ e ∈ (E cfg X).edges, e.arc = ArcType.input → ∃ t ∈ X.trans, ∃ s ∈ t.core.inputs, exp004InputEdge t s e) ∧
      ((∀ t ∈ X.trans,
            ∀ p ∈ t.outLeaves,
              p ∉ t.core.resets → ∃ e ∈ (E cfg X).edges, exp004OutputEdge t e ∧ e.dst = NodeRef.place p) ∧
          (∀ t ∈ X.trans,
              ∀ fw ∈ exp004TransForwards t, fw.2 ∉ t.core.resets → ∃ e ∈ (E cfg X).edges, exp004ForwardEdge t fw e) ∧
            ∀ e ∈ (E cfg X).edges, e.arc = ArcType.output → ∃ t ∈ X.trans, exp004OutputEdge t e) ∧
        ((∀ t ∈ X.trans, ∀ p ∈ t.core.inhibitors, ∃ e ∈ (E cfg X).edges, exp004InhibitorEdge t p e) ∧
            ∀ e ∈ (E cfg X).edges,
              e.arc = ArcType.inhibitor → ∃ t ∈ X.trans, ∃ p ∈ t.core.inhibitors, exp004InhibitorEdge t p e) ∧
          ((∀ t ∈ X.trans, ∀ p ∈ t.core.reads, ∃ e ∈ (E cfg X).edges, exp004ReadEdge t p e) ∧
              ∀ e ∈ (E cfg X).edges, e.arc = ArcType.read → ∃ t ∈ X.trans, ∃ p ∈ t.core.reads, exp004ReadEdge t p e) ∧
            (∀ t ∈ X.trans, ∀ p ∈ t.core.resets, p ∉ t.outLeaves → ∃ e ∈ (E cfg X).edges, exp004ResetEdge t p e) ∧
              ∀ e ∈ (E cfg X).edges,
                e.arc = ArcType.reset → ∃ t ∈ X.trans, ∃ p ∈ t.core.resets, p ∉ t.outLeaves ∧ exp004ResetEdge t p e
-/
#guard_msgs in #print EXP_004

/-! ### The reference -/

mutual
/-- **A dashed edge of the drawing rule** is the edge of a `ForwardInput` leaf: it ends in the
leaf's target and is labelled `⟵<source>` after the inherited label. -/
theorem exp004_drawOut_dashed (t : String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat), ∀ d ∈ drawOut t par l n o, d.dashed = true →
      ∃ fw ∈ exp004Forwards o, d.dst = .place fw.2 ∧ ∃ l', d.label = some (forwardLabel l' fw.1)
  | .place p, n, d, hd, h => by
    simp only [drawOut, List.mem_singleton] at hd; subst hd; simp at h
  | .forward s q, n, d, hd, _ => by
    simp only [drawOut, List.mem_singleton] at hd; subst hd
    exact ⟨(s, q), by simp [exp004Forwards], rfl, l, rfl⟩
  | .timeout ms c, n, d, hd, h => by
    simp only [drawOut] at hd
    simpa only [exp004Forwards] using exp004_drawOut_dashed t par _ c n d hd h
  | .and cs, n, d, hd, h => by
    by_cases hc : 2 ≤ cs.length
    · simp only [drawOut, hc, if_true, List.mem_cons] at hd
      rcases hd with rfl | hd
      · simp at h
      · simpa only [exp004Forwards] using exp004_drawOutL_dashed t _ _ cs (n + 1) d hd h
    · simp only [drawOut, hc, if_false] at hd
      simpa only [exp004Forwards] using exp004_drawOutL_dashed t par _ cs n d hd h
  | .xor cs, n, d, hd, h => by
    by_cases hc : 2 ≤ cs.length
    · simp only [drawOut, hc, if_true, List.mem_cons] at hd
      rcases hd with rfl | hd
      · simp at h
      · simpa only [exp004Forwards] using exp004_drawOutL_dashed t _ _ cs (n + 1) d hd h
    · simp only [drawOut, hc, if_false] at hd
      simpa only [exp004Forwards] using exp004_drawOutL_dashed t par _ cs n d hd h
/-- The list form of `exp004_drawOut_dashed`. -/
theorem exp004_drawOutL_dashed (t : String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat), ∀ d ∈ drawOutL t par u n cs, d.dashed = true →
      ∃ fw ∈ exp004ForwardsL cs, d.dst = .place fw.2 ∧ ∃ l', d.label = some (forwardLabel l' fw.1)
  | [], n, d, hd, _ => by simp [drawOutL] at hd
  | c :: cs, n, d, hd, h => by
    simp only [drawOutL, List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨fw, hfw, h1, h2⟩ := exp004_drawOut_dashed t par _ c n d hd h
      exact ⟨fw, by simp [exp004ForwardsL, hfw], h1, h2⟩
    · obtain ⟨fw, hfw, h1, h2⟩ := exp004_drawOutL_dashed t par u cs _ d hd h
      exact ⟨fw, by simp [exp004ForwardsL, hfw], h1, h2⟩
end

mutual
/-- **Every `ForwardInput` leaf has its dashed edge in the drawing rule**: it ends in the leaf's
target and is labelled `⟵<source>` after the inherited label. -/
theorem exp004_drawOut_forward (t : String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat), ∀ fw ∈ exp004Forwards o,
      ∃ d ∈ drawOut t par l n o, d.dashed = true ∧ d.dst = .place fw.2 ∧
        ∃ l', d.label = some (forwardLabel l' fw.1)
  | .place p, n, fw, hfw => by simp [exp004Forwards] at hfw
  | .forward s q, n, fw, hfw => by
    simp only [exp004Forwards, List.mem_singleton] at hfw; subst hfw
    exact ⟨⟨par, .place q, true, some (forwardLabel l s)⟩, by simp [drawOut], rfl, rfl, l, rfl⟩
  | .timeout ms c, n, fw, hfw => by
    simp only [exp004Forwards] at hfw
    simpa only [drawOut] using exp004_drawOut_forward t par _ c n fw hfw
  | .and cs, n, fw, hfw => by
    simp only [exp004Forwards] at hfw
    by_cases hc : 2 ≤ cs.length
    · obtain ⟨d, hd, h⟩ :=
        exp004_drawOutL_forward t (.junction t .and n) (.junction .and) cs (n + 1) fw hfw
      exact ⟨d, by simp only [drawOut, hc, if_true, List.mem_cons]; exact Or.inr hd, h⟩
    · obtain ⟨d, hd, h⟩ := exp004_drawOutL_forward t par (.pass l) cs n fw hfw
      exact ⟨d, by simp only [drawOut, hc, if_false]; exact hd, h⟩
  | .xor cs, n, fw, hfw => by
    simp only [exp004Forwards] at hfw
    by_cases hc : 2 ≤ cs.length
    · obtain ⟨d, hd, h⟩ :=
        exp004_drawOutL_forward t (.junction t .xor n) (.junction .xor) cs (n + 1) fw hfw
      exact ⟨d, by simp only [drawOut, hc, if_true, List.mem_cons]; exact Or.inr hd, h⟩
    · obtain ⟨d, hd, h⟩ := exp004_drawOutL_forward t par (.pass l) cs n fw hfw
      exact ⟨d, by simp only [drawOut, hc, if_false]; exact hd, h⟩
/-- The list form of `exp004_drawOut_forward`. -/
theorem exp004_drawOutL_forward (t : String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat), ∀ fw ∈ exp004ForwardsL cs,
      ∃ d ∈ drawOutL t par u n cs, d.dashed = true ∧ d.dst = .place fw.2 ∧
        ∃ l', d.label = some (forwardLabel l' fw.1)
  | [], n, fw, hfw => by simp [exp004ForwardsL] at hfw
  | c :: cs, n, fw, hfw => by
    simp only [exp004ForwardsL, List.mem_append] at hfw
    rcases hfw with hfw | hfw
    · obtain ⟨d, hd, h⟩ := exp004_drawOut_forward t par (u.label c) c n fw hfw
      exact ⟨d, by simp only [drawOutL, List.mem_append]; exact Or.inl hd, h⟩
    · obtain ⟨d, hd, h⟩ :=
        exp004_drawOutL_forward t par u cs (n + (OutTree.junctions c).length) fw hfw
      exact ⟨d, by simp only [drawOutL, List.mem_append]; exact Or.inr hd, h⟩
end

/-- The reference realises a dashed edge only from a dashed edge of the rule, keeping its
label. -/
theorem exp004_refRealize_dashed (R : List String) (d : DrawnEdge)
    (h : (refRealize R d).dashed = true) :
    d.dashed = true ∧ (refRealize R d).label = d.label ∧
      ∀ p, (refRealize R d).dst = .place p → p ∉ R := by
  rcases d with ⟨src, dst, dashed, label⟩
  cases dst with
  | place p => by_cases hp : p ∈ R <;> simp_all [refRealize]
  | trans u => simp_all [refRealize]
  | junction u k i => simp_all [refRealize]

/-- A dashed edge of the reference's output side of `t` ends in the target of a `ForwardInput`
leaf of `t`, a place `t` does not reset, and is labelled `⟵<source>` after the inherited
label. -/
theorem exp004_refEmit_dashed {t : ExportTrans} {e : XEdge} (he : e ∈ (refEmit.ofTrans t).edges)
    (h : e.dashed = true) :
    ∃ fw ∈ exp004TransForwards t, fw.2 ∉ t.core.resets ∧ e.dst = .place fw.2 ∧
      ∃ l, e.label = some (forwardLabel l fw.1) := by
  obtain ⟨o, ho, he⟩ := Emitter.mem_ofTrans_edges refEmit he
  rw [refEmit_draws] at he
  simp only [List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨hdd, hl, hnr⟩ := exp004_refRealize_dashed _ d h
  obtain ⟨fw, hfw, h1, l, h2⟩ := exp004_drawOut_dashed _ _ _ o 0 d hd hdd
  have hdst : (refRealize t.core.resets d).dst = .place fw.2 := by rw [refRealize_dst]; exact h1
  refine ⟨fw, by simp [exp004TransForwards, ho, hfw], hnr _ hdst, hdst, l, ?_⟩
  rw [hl, h2]

/-- Every `output` edge of the reference's output side of `t` is an output edge of `t` as EXP-004
says. -/
theorem exp004_refEmit_output {t : ExportTrans} {e : XEdge} (he : e ∈ (refEmit.ofTrans t).edges)
    (ha : e.arc = .output) : exp004OutputEdge t e := by
  have hrow : e.row = .output := by
    rcases (refEmit_ofTrans_arc he).1 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · rw [ha] at h; cases h
  refine ⟨ha, hrow, refEmit_ofTrans_owner he, ?_, exp004_refEmit_dashed he⟩
  rcases (refEmit_ofTrans_ends he).2 with ⟨p, hp⟩ | ⟨k, i, hj, _⟩
  · exact Or.inl (by simp [hp, NodeRef.place?])
  · exact Or.inr (by simp [hj, NodeRef.junctionOf])

/-- The reference's input edge of arc `s` is drawn as EXP-004 says. -/
theorem exp004_refInputEdge (t : ExportTrans) (s : NInSpec String) :
    exp004InputEdge t s (refInputEdge t s) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The reference's inhibitor edge on `p` is drawn as EXP-004 says. -/
theorem exp004_refInhibitorEdge (t : ExportTrans) (p : String) :
    exp004InhibitorEdge t p (refInhibitorEdge t p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The reference draws the edge of every `ForwardInput` leaf of `t` into a place `t` does not
reset as EXP-004 says: the rule's dashed edge, realised as an output edge with its dash and
label. -/
theorem exp004_refForwardEdge {t : ExportTrans} {fw : String × String}
    (hfw : fw ∈ exp004TransForwards t) (hr : fw.2 ∉ t.core.resets) :
    ∃ e ∈ (refEmit.ofTrans t).edges, exp004ForwardEdge t fw e := by
  unfold exp004TransForwards at hfw
  cases ho : t.out with
  | none => simp [ho] at hfw
  | some o =>
    simp only [ho, Option.map_some, Option.getD_some] at hfw
    obtain ⟨d, hd, hdd, hdst, l, hl⟩ := exp004_drawOut_forward t.name (.trans t.name) none o 0 fw hfw
    have hem : refRealize t.core.resets d ∈ (refEmit.ofTrans t).edges := by
      rw [Emitter.ofTrans_some refEmit ho, refEmit_draws]
      exact List.mem_map_of_mem hd
    have ha : (refRealize t.core.resets d).arc = .output := by simp [refRealize, hdst, hr]
    exact ⟨_, hem, exp004_refEmit_output hem ha, by simp [hdst], by simp [refRealize, hdst, hr, hdd],
      l, by simp [refRealize, hdst, hr, hl]⟩

/-- The reference's read edge on `p` is drawn as EXP-004 says. -/
theorem exp004_refReadEdge (t : ExportTrans) (p : String) :
    exp004ReadEdge t p (refReadEdge t p) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The reference's standalone reset edge on `p` is drawn as EXP-004 says. -/
theorem exp004_refResetEdge (t : ExportTrans) (p : String) :
    exp004ResetEdge t p (refResetEdge t p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The reference exporter with any cluster stage satisfies EXP-004: every arc is drawn by
`refTransEdges` of its transition as the line says, and every drawn edge of one of the five arc
types is not a ghost edge, so it is an edge of one transition (`refExportWith_edge_of_ne_ghost`),
whose shape `refTransEdges_input` and its siblings give. -/
theorem EXP_004_any (S : ClusterStage) : EXP_004 (refExportWith S) := by
  intro cfg X
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t ht s hs
    exact ⟨_, refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inl ⟨s, hs, rfl⟩)),
      exp004_refInputEdge t s⟩
  · intro e he ha
    obtain ⟨t, ht, het⟩ := refExportWith_edge_of_ne_ghost he (by rw [ha]; decide)
    obtain ⟨s, hs, rfl⟩ := refTransEdges_input het ha
    exact ⟨t, ht, s, hs, exp004_refInputEdge t s⟩
  · intro t ht p hp hr
    have hm : p ∈ (refEmit.ofTrans t).edges.filterMap XEdge.placeTarget := by
      rw [refEmit_ofTrans_places]; exact hp
    obtain ⟨e, he, hpe⟩ := List.mem_filterMap.mp hm
    have hdst : e.dst = .place p := by
      unfold XEdge.placeTarget at hpe
      cases hd : e.dst <;> simp_all [NodeRef.place?]
    have ha : e.arc = .output := by
      have h2 := (refEmit_ofTrans_arc he).2.1
      rcases (refEmit_ofTrans_arc he).1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · obtain ⟨q, hq, hqd⟩ := h2.mp h
        rw [hdst] at hqd
        cases hqd
        exact absurd hq hr
    exact ⟨e, refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inr (Or.inl he))),
      exp004_refEmit_output he ha, hdst⟩
  · intro t ht fw hfw hr
    obtain ⟨e, he, hf⟩ := exp004_refForwardEdge hfw hr
    exact ⟨e, refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inr (Or.inl he))), hf⟩
  · intro e he ha
    obtain ⟨t, ht, het⟩ := refExportWith_edge_of_ne_ghost he (by rw [ha]; decide)
    exact ⟨t, ht, exp004_refEmit_output (refTransEdges_out het (Or.inl ha)) ha⟩
  · intro t ht p hp
    exact ⟨_, refExportWith_edge_of_trans ht
      (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))), exp004_refInhibitorEdge t p⟩
  · intro e he ha
    obtain ⟨t, ht, het⟩ := refExportWith_edge_of_ne_ghost he (by rw [ha]; decide)
    obtain ⟨p, hp, rfl⟩ := refTransEdges_inhibitor het ha
    exact ⟨t, ht, p, hp, exp004_refInhibitorEdge t p⟩
  · intro t ht p hp
    exact ⟨_, refExportWith_edge_of_trans ht
      (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))),
      exp004_refReadEdge t p⟩
  · intro e he ha
    obtain ⟨t, ht, het⟩ := refExportWith_edge_of_ne_ghost he (by rw [ha]; decide)
    obtain ⟨p, hp, rfl⟩ := refTransEdges_read het ha
    exact ⟨t, ht, p, hp, exp004_refReadEdge t p⟩
  · intro t ht p hp hn
    exact ⟨_, refExportWith_edge_of_trans ht
      (mem_refTransEdges.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hn, rfl⟩))))),
      exp004_refResetEdge t p⟩
  · intro e he ha
    obtain ⟨t, ht, het⟩ := refExportWith_edge_of_ne_ghost he (by rw [ha]; decide)
    obtain ⟨p, hp, hn, rfl⟩ := refTransEdges_reset het ha
    exact ⟨t, ht, p, hp, hn, exp004_refResetEdge t p⟩

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-004 (`EXP_004_any` at the reference cluster stage). -/
@[evidence holds EXP_004]
theorem EXP_004_reference : EXP_004 refExport := EXP_004_any _

/-! ### Visually distinct: AC1, from the statement -/

/-- The five arc types EXP-004 lists. -/
def exp004Five : List ArcType := [.input, .output, .inhibitor, .read, .reset]

/-- What a reader sees of an edge apart from its label: whether it is drawn from a place, and the
colour, line style, arrowhead and pen width of its row, with the line style dashed where the
edge is drawn dashed. -/
def exp004Look (e : XEdge) : Bool × EdgeStyle :=
  (e.src.place?.isSome,
    if e.dashed then { edgeStyle e.row with style := "dashed" } else edgeStyle e.row)

/-- The looks EXP-004 leaves an edge of each of the five arc types. -/
def exp004Looks : ArcType → List (Bool × EdgeStyle)
  | .input => [(true, edgeStyle .input), (true, edgeStyle .matchInput)]
  | .output => [(false, edgeStyle .output), (false, { edgeStyle .output with style := "dashed" })]
  | .inhibitor => [(true, edgeStyle .inhibitor)]
  | .read => [(true, edgeStyle .read)]
  | .reset => [(false, edgeStyle .reset)]
  | _ => []

/-- The looks of two different arc types among the five never meet (a fact of the style
table). -/
theorem exp004_looks_disjoint :
    ∀ k₁ ∈ exp004Five, ∀ k₂ ∈ exp004Five, k₁ ≠ k₂ → ∀ x ∈ exp004Looks k₁, x ∉ exp004Looks k₂ := by
  decide

/-- Under EXP-004, a drawn edge of one of the five arc types has one of the looks of its type. -/
theorem exp004_look_mem {E : Exporter} (h : EXP_004 E) (cfg : ExportCfg) (X : ExportNet)
    {e : XEdge} (he : e ∈ (E cfg X).edges) (hk : e.arc ∈ exp004Five) :
    exp004Look e ∈ exp004Looks e.arc := by
  obtain ⟨⟨-, h1⟩, ⟨-, -, h2⟩, ⟨-, h3⟩, ⟨-, h4⟩, ⟨-, h5⟩⟩ := h cfg X
  simp only [exp004Five, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with ha | ha | ha | ha | ha
  · obtain ⟨t, -, s, -, -, hs, -, hd, hr⟩ := h1 e he ha
    rw [ha]
    by_cases hc : s.place ∈ t.corr <;>
      simp [exp004Look, exp004Looks, hs, hd, hr, hc, NodeRef.place?]
  · obtain ⟨t, -, -, hr, ho, -, -⟩ := h2 e he ha
    have hp : e.src.place? = none := by
      cases hs : e.src <;> simp_all [NodeRef.owner?, NodeRef.place?]
    rw [ha]
    cases hd : e.dashed <;> simp [exp004Look, exp004Looks, hp, hr, hd]
  · obtain ⟨t, -, p, -, -, hs, -, hr, hd, -⟩ := h3 e he ha
    rw [ha]
    simp [exp004Look, exp004Looks, hs, hr, hd, NodeRef.place?]
  · obtain ⟨t, -, p, -, -, hs, -, hr, -⟩ := h4 e he ha
    rw [ha]
    cases hd : e.dashed <;> simp [exp004Look, exp004Looks, hs, hr, hd, NodeRef.place?, edgeStyle]
  · obtain ⟨t, -, p, -, -, -, hs, -, hr, hd, -⟩ := h5 e he ha
    rw [ha]
    simp [exp004Look, exp004Looks, hs, hr, hd, NodeRef.place?]

/-- **AC1, visually distinct.** For every exporter that meets EXP-004, two drawn edges whose arc
types are two different ones of the five differ in drawn direction (from a place or not) or in
the colour, line style, arrowhead or pen width they are drawn with, whatever their labels. -/
@[evidence cites "EXP-004" "AC1 and the sentence defining visually distinct: for every exporter that meets the block, two drawn edges whose arc types are two different ones of input, output, inhibitor, read and reset differ in drawn direction or in the colour, line style, arrowhead or pen width of their row (dashed override included), without reading a label"]
theorem EXP_004_distinguishable {E : Exporter} (h : EXP_004 E) (cfg : ExportCfg) (X : ExportNet)
    {e₁ e₂ : XEdge} (h₁ : e₁ ∈ (E cfg X).edges) (h₂ : e₂ ∈ (E cfg X).edges)
    (k₁ : e₁.arc ∈ exp004Five) (k₂ : e₂.arc ∈ exp004Five) (hne : e₁.arc ≠ e₂.arc) :
    exp004Look e₁ ≠ exp004Look e₂ := by
  intro heq
  have m₁ := exp004_look_mem h cfg X h₁ k₁
  have m₂ := exp004_look_mem h cfg X h₂ k₂
  rw [heq] at m₁
  exact exp004_looks_disjoint _ k₁ _ k₂ hne _ m₁ m₂

/-! ### Wrong exporters, one per line -/

/-- The worked transition: a plain input `A` and a correlated input `M`, the output
`Xor(B, Timeout(5, ForwardInput(A → C)))`, an inhibitor on `I`, a read arc on `R` and a reset arc
on `Z`. -/
def exp004T : ExportTrans :=
  { core := ⟨"T", [⟨"A", .one⟩, ⟨"M", .one⟩], ["I"], ["R"], ["Z"]⟩,
    out := some (.xor [.place "B", .timeout 5 (.forward "A" "C")]),
    corr := ["M"] }

/-- The worked net: the one transition. -/
def exp004Net : ExportNet := { trans := [exp004T] }

/-- The reference with the edges redrawn by `f`, each edge into the list `f` gives it. -/
def exp004Redraw (f : XEdge → List XEdge) : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.flatMap f }

/-- Redraw the edges of arc type `k` by `f`, keep the others. -/
def exp004On (k : ArcType) (f : XEdge → XEdge) : Exporter :=
  exp004Redraw fun e => if e.arc = k then [f e] else [e]

/-- Input edges drawn from the transition to the place. -/
def exp004_inputReversed : Exporter := exp004On .input fun e => { e with src := e.dst, dst := e.src }

/-- ✗ Drawing input edges from the transition to the place violates EXP-004 (line input: every
input edge runs from its place to its transition; AC2). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_inputReversed : ¬ EXP_004 exp004_inputReversed := by
  intro h
  obtain ⟨⟨-, h1⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hs⟩ : ∃ e ∈ (exp004_inputReversed {} exp004Net).edges,
      e.arc = .input ∧ e.src = .trans "T" := by decide
  obtain ⟨t, -, s, -, -, hs', -⟩ := h1 e he ha
  rw [hs'] at hs
  cases hs

/-- Output edges drawn from their place or junction back to the transition side. -/
def exp004_outputReversed : Exporter :=
  exp004On .output fun e => { e with src := e.dst, dst := e.src }

/-- ✗ Drawing output edges from the place to the transition violates EXP-004 (line output: an
output edge starts at the transition or one of its junction nodes; AC2, design mutant). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_outputReversed : ¬ EXP_004 exp004_outputReversed := by
  intro h
  obtain ⟨-, ⟨-, -, h2⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hs⟩ : ∃ e ∈ (exp004_outputReversed {} exp004Net).edges,
      e.arc = .output ∧ e.src = .place "B" := by decide
  obtain ⟨t, -, -, -, ho, -⟩ := h2 e he ha
  rw [hs] at ho
  cases ho

/-- Every output edge drawn dashed. -/
def exp004_outputDashed : Exporter := exp004On .output fun e => { e with dashed := true }

/-- ✗ Drawing every output edge dashed violates EXP-004 (line output: only the edge of a
`ForwardInput` leaf is dashed; the edge into `B` is a `Place` leaf's). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_outputDashed : ¬ EXP_004 exp004_outputDashed := by
  intro h
  obtain ⟨-, ⟨-, -, h2⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hd, hdst⟩ : ∃ e ∈ (exp004_outputDashed {} exp004Net).edges,
      e.arc = .output ∧ e.dashed = true ∧ e.dst = .place "B" := by decide
  obtain ⟨t, ht, -, -, -, -, hf⟩ := h2 e he ha
  obtain ⟨fw, hfw, -, hfd, -⟩ := hf hd
  simp only [exp004Net, List.mem_singleton] at ht
  subst ht
  have hfw' : fw = ("A", "C") := by
    simpa [exp004TransForwards, exp004T, exp004Forwards, exp004ForwardsL] using hfw
  subst hfw'
  rw [hdst] at hfd
  exact absurd hfd (by decide)

/-- A transition whose `ForwardInput` leaf ends in a place it also resets: `ForwardInput(A → P)`
with `reset(P)`. -/
def exp004FwdResetNet : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"A", .one⟩], [], [], ["P"]⟩, out := some (.forward "A" "P") }] }

/-- The combined edge drawn as the dashed `ForwardInput` output edge it replaces: arc type
`output`, `output` row, dashed, labelled `⟵A`. -/
def exp004_fwdIntoReset : Exporter :=
  exp004On .resetOutput fun e =>
    { e with arc := .output, row := .output, dashed := true, label := some (forwardLabel none "A") }

/-- ✗ A dashed output edge into a place the transition resets violates EXP-004 (line output: the
exception for the edge of a `ForwardInput` leaf covers only a target the transition does not
reset). Without that condition the clause would accept the edge: it ends in the target of the
leaf and is labelled `⟵A`. -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_fwdIntoReset : ¬ EXP_004 exp004_fwdIntoReset := by
  intro h
  obtain ⟨-, ⟨-, -, h2⟩, -⟩ := h {} exp004FwdResetNet
  obtain ⟨e, he, ha, hd, hdst⟩ : ∃ e ∈ (exp004_fwdIntoReset {} exp004FwdResetNet).edges,
      e.arc = .output ∧ e.dashed = true ∧ e.dst = .place "P" := by decide
  obtain ⟨t, ht, -, -, -, -, hf⟩ := h2 e he ha
  obtain ⟨fw, hfw, hnr, hfd, -⟩ := hf hd
  simp only [exp004FwdResetNet, List.mem_singleton] at ht
  subst ht
  have hfw' : fw = ("A", "P") := by
    simpa [exp004TransForwards, exp004Forwards] using hfw
  subst hfw'
  exact hnr (by decide)

/-- Inhibitor edges drawn in the input row: a normal arrowhead in the input colour. -/
def exp004_inhibitorAsInput : Exporter := exp004On .inhibitor fun e => { e with row := .input }

/-- ✗ Drawing inhibitor edges in the input row violates EXP-004 (line inhibitor: the
`inhibitor` row, whose arrowhead is the circle; design mutant). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_inhibitorAsInput : ¬ EXP_004 exp004_inhibitorAsInput := by
  intro h
  obtain ⟨-, -, ⟨-, h3⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hr⟩ : ∃ e ∈ (exp004_inhibitorAsInput {} exp004Net).edges,
      e.arc = .inhibitor ∧ e.row = .input := by decide
  obtain ⟨t, -, p, -, -, -, -, hr', -, -⟩ := h3 e he ha
  rw [hr'] at hr
  cases hr

/-- Read edges drawn solid, in the input row, and without the `read` label. -/
def exp004_readPlain : Exporter := exp004On .read fun e => { e with row := .input, label := none }

/-- ✗ Drawing read edges solid and unlabelled violates EXP-004 (line read: the dashed `read` row
and the label `read`; design mutant). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_readPlain : ¬ EXP_004 exp004_readPlain := by
  intro h
  obtain ⟨-, -, -, ⟨-, h4⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hl⟩ : ∃ e ∈ (exp004_readPlain {} exp004Net).edges,
      e.arc = .read ∧ e.label = none := by decide
  obtain ⟨t, -, p, -, -, -, -, -, hl'⟩ := h4 e he ha
  rw [hl'] at hl
  cases hl

/-- Reset edges drawn from the place to the transition, the glossary's arc direction. -/
def exp004_resetReversed : Exporter := exp004On .reset fun e => { e with src := e.dst, dst := e.src }

/-- ✗ Drawing the reset edge from the place to the transition violates EXP-004 (line reset: the
drawing convention is transition to place, ruling D20). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_resetReversed : ¬ EXP_004 exp004_resetReversed := by
  intro h
  obtain ⟨-, -, -, -, ⟨-, h5⟩⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hs⟩ : ∃ e ∈ (exp004_resetReversed {} exp004Net).edges,
      e.arc = .reset ∧ e.src = .place "Z" := by decide
  obtain ⟨t, -, p, -, -, -, hs', -⟩ := h5 e he ha
  rw [hs'] at hs
  cases hs

/-- No standalone reset edge at all. -/
def exp004_noReset : Exporter := exp004Redraw fun e => if e.arc = .reset then [] else [e]

/-- ✗ Drawing no reset edge violates EXP-004 (line reset, first half: a reset arc on a place no
leaf ends in is drawn). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_noReset : ¬ EXP_004 exp004_noReset := by
  intro h
  obtain ⟨-, -, -, -, ⟨h5, -⟩⟩ := h {} exp004Net
  obtain ⟨e, he, hr⟩ := h5 exp004T (by simp [exp004Net]) "Z" (by decide) (by decide)
  have hno : ∀ e ∈ (exp004_noReset {} exp004Net).edges, e.arc ≠ .reset := by decide
  exact hno e he hr.1

/-- Every output edge drawn solid: the edge of a `ForwardInput` leaf loses its dash and keeps its
label (the slip of passing the `Place` leaf's dash flag from the `ForwardInput` arm). -/
def exp004_forwardSolid : Exporter := exp004On .output fun e => { e with dashed := false }

/-- ✗ Drawing the edge of a `ForwardInput` leaf solid violates EXP-004 (line output: the edge of
the `ForwardInput` leaf from `A` to `C` is dashed). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_forwardSolid : ¬ EXP_004 exp004_forwardSolid := by
  intro h
  obtain ⟨-, ⟨-, hf, -⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, -, -, hd, -⟩ := hf exp004T (by simp [exp004Net]) ("A", "C")
    (by simp [exp004TransForwards, exp004T, exp004Forwards, exp004ForwardsL]) (by decide)
  have hno : ∀ e ∈ (exp004_forwardSolid {} exp004Net).edges, e.dashed = false := by decide
  rw [hno e he] at hd
  cases hd

/-- Inhibitor edges labelled `read` (the read loop copied for the inhibitor with its label
kept); the row, the solid line and the ends stay. -/
def exp004_inhibitorLabelled : Exporter :=
  exp004On .inhibitor fun e => { e with label := some "read" }

/-- ✗ Labelling inhibitor edges violates EXP-004 (line inhibitor: an inhibitor edge has no
label). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_inhibitorLabelled : ¬ EXP_004 exp004_inhibitorLabelled := by
  intro h
  obtain ⟨-, -, ⟨-, h3⟩, -⟩ := h {} exp004Net
  obtain ⟨e, he, ha, hl⟩ : ∃ e ∈ (exp004_inhibitorLabelled {} exp004Net).edges,
      e.arc = .inhibitor ∧ e.label = some "read" := by decide
  obtain ⟨t, -, p, -, -, -, -, -, -, hl'⟩ := h3 e he ha
  rw [hl'] at hl
  cases hl

/-- A transition `U` that outputs to `B` and resets `B`: the combined edge of [EXP-013] case. -/
def exp004U : ExportTrans :=
  { core := ⟨"U", [], [], [], ["B"]⟩, out := some (.place "B") }

/-- The net of the one transition `U`. -/
def exp004NetU : ExportNet := { trans := [exp004U] }

/-- A standalone reset edge for every reset arc, also where a leaf ends in the reset place. -/
def exp004_resetEvery : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges ++ X.trans.flatMap fun t => t.core.resets.map (refResetEdge t) }

/-- ✗ Drawing a standalone reset edge into a place a leaf of the transition ends in violates
EXP-004 (line reset, second half: a reset edge is the edge of a reset arc whose place no leaf
ends in). -/
@[evidence forbids EXP_004]
theorem EXP_004_forbids_resetEvery : ¬ EXP_004 exp004_resetEvery := by
  intro h
  obtain ⟨-, -, -, -, ⟨-, h5⟩⟩ := h {} exp004NetU
  obtain ⟨e, he, ha, hd⟩ : ∃ e ∈ (exp004_resetEvery {} exp004NetU).edges,
      e.arc = .reset ∧ e.dst = .place "B" := by decide
  obtain ⟨t, ht, p, -, hn, -, -, hd', -⟩ := h5 e he ha
  simp only [exp004NetU, List.mem_singleton] at ht
  subst ht
  rw [hd] at hd'
  cases hd'
  exact hn (by decide)

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference: the worked transition draws an `input` edge from `A`
and a `match-input` edge from the correlated `M`, the output side (transition to the xor junction,
junction to `B` labelled `B`, junction to `C` dashed and labelled `⏱5ms ⟵A`), an `inhibitor`
edge from `I`, a `read` edge from `R` labelled `read`, and a `reset` edge from the transition to
`Z` labelled `reset`; the eight edges show seven different looks (`exp004Look`): the two output
edges into the junction and into `B` look alike, every other pair differs. -/
@[evidence nonvacuous EXP_004]
theorem EXP_004_nonvacuous :
    (refExportFlat {} exp004Net).edges.map (fun e => (e.src, e.dst, e.arc, e.row)) =
      [(.place "A", .trans "T", .input, .input),
       (.place "M", .trans "T", .input, .matchInput),
       (.trans "T", .junction "T" .xor 0, .output, .output),
       (.junction "T" .xor 0, .place "B", .output, .output),
       (.junction "T" .xor 0, .place "C", .output, .output),
       (.place "I", .trans "T", .inhibitor, .inhibitor),
       (.place "R", .trans "T", .read, .read),
       (.trans "T", .place "Z", .reset, .reset)] ∧
    (refExportFlat {} exp004Net).edges.map (fun e => (e.dashed, e.label)) =
      [(false, none), (false, some "⟨n⟩"), (false, none), (false, some "B"),
       (true, some "⏱5ms ⟵A"), (false, none), (false, some "read"), (false, some "reset")] ∧
    ((refExportFlat {} exp004Net).edges.map exp004Look).dedup.length = 7 := by
  decide

end Libpetri.Spec
