import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_018

set_option linter.missingDocs true

/-!
# EXP-018: ν-match edge decoration (`spec/09-export.md`)

How an exporter draws the input edges of a transition whose ν-net match specification
([NU-020]) correlates some of its input places: the edge of a correlated input arc keeps arc
type `input` and takes the `match-input` style row (`spec/petri-net-styles.json`, colour
`#0d9488`) and the label `⟨n⟩`, followed by one space and the cardinality label of [EXP-006]
when the arc has one (glossary `corrLabel`); the edge of an uncorrelated input arc of the same
transition keeps the `input` row and the cardinality label alone; and no other edge is drawn
with the `match-input` row. Each of the two label lines has a half that holds on every net (some
input edge of the arc is drawn so) and a half for nets with distinct transition names and one
input arc per place (every input edge of the arc is drawn so). The requirement is a predicate over
an abstract exporter `E : Exporter` (glossary `GlossaryExport.lean`).

The witness is the reference exporter `refExportWith S` for every cluster stage `S`
(`Reference/Export.lean`, `refInputEdge` and `refInputLabel`), written as the three runtime
mappers draw an input edge (`map_to_graph` and `input_label` in the Rust crate
`libpetri-export`, `PetriNetGraphMapper.java`, `petri-net-mapper.ts`). `EXP_018_any` proves the
block for every stage; the tagged holds evidence is its instance at the reference cluster stage,
`refExport`, the witness of the joint theorem.

Ruling D41 (a) pins the cardinality label forms to `×n`, `*`, `≥m` (no label for `One`), the
function `refCardLabel` every runtime computes, so the label lines name it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export
open Libpetri.Novel.Seam (NInSpec)

/-! ## EXP-018: ν-Match Edge Decoration -/

requirement EXP_018
  id "EXP-018"
  title "ν-Match Edge Decoration"
  kind F
  scope "every exporter, on the input edges of the graph it draws for a configuration and a net"
  source verbatim "spec/09-export.md"
  covers EXP_018.s1, EXP_018.s2, EXP_018.s3, EXP_018.s4, EXP_018.s5, EXP_018.s6, EXP_018.s7,
        EXP_018.s8, EXP_018.s9
  reading "For the exporter E, every configuration cfg and every net X:"
          "for every transition t of X and every input arc s of t, the graph E cfg X has an edge of arc type input from the place of s to the node of t;"
          "for every input arc s of a transition t whose place t correlates, some such edge has the match-input style row and the label ⟨n⟩, followed by a space and the cardinality label of s when s has one (corrLabel of refCardLabel), and, when the transitions of X have distinct names and no transition has two input arcs on one place, every such edge has that row and that label;"
          "for every input arc s of a transition t whose place t does not correlate, some such edge has the input style row and the cardinality label of s (refCardLabel), none for One, and, under the same condition, every such edge has that row and that label;"
          "every edge of the graph that is not a ghost edge and has the match-input style row is an edge of arc type input from the place of an input arc s of some transition t of X to the node of t, and t correlates the place of s."
  assumes "The model is an exporter E : Exporter (glossary): from an export configuration (glossary ExportCfg) and a net as the exporter reads it (glossary ExportNet), the typed graph the runtimes' mappers build before DOT text (glossary XGraph). An edge (glossary XEdge) carries its ends, its arc type (glossary ArcType), its style row (Libpetri.Export.EdgeRow, generated from spec/petri-net-styles.json) and its label. A transition (glossary ExportTrans) carries in corr the places its ν-net match specification correlates (NU-020), empty without one; NU-020 makes every correlated place an input place of the transition, which is why the lines speak of input arcs only. The DOT text and its attribute syntax are not modelled."
          "Relay targets: corr holds the places of match keys only, never the relay targets of NU-054, as in every runtime: each mapper decorates an input when the correlates test of the match specification holds, and that test checks match keys only, never relay keys. So line 4 forbids drawing a relay edge (an output edge to a relay target) with the match-input row, as it forbids any teal output edge (EXP_018_forbids_outTeal); NU-054's API note is reworded to agree (spec edit NU-054-relay-export)."
          "Colour: the colour bullet (#0d9488, teal, the match-input edge style in spec/petri-net-styles.json, distinguishing the edge from a plain input edge) is read as the match-input style row: an edge names a row of the generated style table and the colour is the row's. EXP_018_nonvacuous decides on the table that the match-input row has colour #0d9488 and that the input row has another colour (#333333). Which hex value the DOT text carries for a row is kind Q (the style generator's gate)."
          "Arc type: all three mappers keep the arc type of a correlated edge as input and change only its style row, so line 1 asks for an edge of arc type input for every input arc, correlated or not, and a mapper that changes the arc type of a correlated edge (EXP_018_forbids_arcRead) or drops the edge (EXP_018_forbids_dropCorr) violates the block. Line 1 overlaps EXP-001's line on input edges and follows from the first halves of lines 2 and 3; it is kept as the line of the first EARS sentence, which states the arc type apart from the decoration, and the two mutants it names also fail the first half of line 2."
          "Labels: the cardinality label is EXP-006's, in the forms ruling D41 (a) pins (×n, *, ≥m, none for One), the function refCardLabel; the correlated label is glossary corrLabel: ⟨n⟩ (U+27E8, n, U+27E9) alone when the cardinality label is none, else ⟨n⟩, one space and the cardinality label. A correlated One edge is therefore labelled ⟨n⟩ and nothing else (EXP_018_forbids_trailingSpace); EXP-006's AC2 ('One cardinality has no cardinality label') names the cardinality label (ruling D41 (a), clash exp-a#6), and ⟨n⟩ is not one, so the ⟨n⟩ label does not contradict it."
          "Lines 2 and 3 have two halves each. The first half holds on every net: some input edge from the place of the arc to the transition has the row and the label. The reference meets it on every net, since it draws refInputEdge t s for every input arc s of every transition t. The second half asks the same of every input edge with those ends, and only on nets whose transitions have distinct names and at most one input arc per place (glossary ExportNet.Distinct): the exporter keys transition nodes by name, so with two transitions of one name, or two input arcs of one transition on one place, two arcs would share the ends of one edge and the half could ask two labels of it. Line 4 needs no such condition."
          "No builder gives ExportNet.Distinct to every net. Distinct transition names are the reading of CORE-020 (a name identifies the transition, see TIME-010); no runtime's net builder rejects two transitions of one name, and only composition does (MOD-025). One input arc per place is CORE-030's transition builder check, with the implementation's own Place equality (CORE-002), and in Java that equality is name-and-type (the MOD-024 divergence note)."
          "On a net that is not Distinct the first halves still bind. A mapper that looks up a transition's match specification by its name, last write wins, draws a correlated input plain when a later transition of the same name has no match; the first half of line 2 rejects it (EXP_018_forbids_lastWinsCorr). With the two transitions in the other order it decorates an uncorrelated input; the first half of line 3 rejects it (EXP_018_forbids_lastWinsUncorr). A Java transition with two input arcs on places of one name and different types, only one of them correlated, is modelled as two input arcs on one place, both correlated, because the exporter names a place node by the place name: the first half of line 2 asks for one decorated edge, which Java draws, and Java's second, plain edge is not ruled out."
          "The second halves are needed on top of the first: an exporter that draws the decorated edge of a correlated input and also a plain copy of it meets the first half of line 2 and violates the second (EXP_018_forbids_dupPlain)."
          "'Non-correlated inputs of the same transition are unaffected' is line 3: the edge keeps the input row and the plain cardinality label, so a mapper that decorates every input of a transition that has a match violates the block (EXP_018_forbids_allInputs), and so does one that keeps the input row of an uncorrelated input but writes ⟨n⟩ before its label (EXP_018_forbids_uncorrPrefix). Line 3 binds every uncorrelated input of every transition, including a transition with no match specification (corr empty), not only the other inputs of a transition with a match. For those it restates the input row of EXP-001 and the cardinality label of EXP-006, so it adds no obligation beyond them; it is what every runtime draws. 'No other edge changes' is line 4 for the style row: no output, inhibitor, read or reset edge, and no input edge of an uncorrelated place, is drawn with the match-input row (EXP_018_forbids_outTeal). Ghost edges (EXP-017) are drawn invisible and their style row is that requirement's, so line 4 excludes them. A label on another edge that happens to start with ⟨n⟩ (an Xor branch label of a place so named) is not ruled out: the label lines speak of input edges only."
          "The sentence 'The decoration is a mapper concern: it is emitted into the DOT by every exporter, so the canonical viewer and all three doc generators render it identically with no viewer change.' is a design note on where the decoration is computed: the block is a predicate over the exporter, which is that mapper, and what the viewer and the doc generators render from the DOT is kind Q."
          "No configuration option changes the decoration in any runtime, so the lines hold for every configuration."
          "AC1 (an input edge to a correlated place has color #0d9488 and a label beginning with ⟨n⟩) is line 2 with the colour reading above; line 2 asks for the whole label, so the literal reading 'begins with ⟨n⟩' is weaker and a mapper that writes ⟨n⟩×2 without the space meets it but not this block (EXP_018_forbids_noSpace). A mapper that writes ⟨n⟩ only when a cardinality label exists draws a correlated One edge with no label and violates line 2 (EXP_018_forbids_optionMap)."
          "AC2 (a non-correlated input edge on the same transition keeps the default color and no ⟨n⟩ prefix) is line 3."
          "AC3 (the label combines with cardinality as ⟨n⟩ ×n, ⟨n⟩ *, ⟨n⟩ ≥m) is line 2 with EXP-006's pinned forms; a mapper that replaces the cardinality label by ⟨n⟩ violates it (EXP_018_forbids_replace)."
          "AC4 (the emitted DOT for a ν-net is byte-identical across the Java, TypeScript and Rust exporters) is kind Q: a Lean function is deterministic and cross-language equality is a property of three programs (ruling D60 (c)); the export corpus EP-2 replays the reference against the runtimes after the migration."
          "The test derivation (a join with match correlating two One inputs, both correlated edges teal and labelled ⟨n⟩, a third non-correlated input unchanged) is EXP_018_nonvacuous on the reference, with a second transition whose correlated Exactly(2), All and AtLeast(3) inputs show ⟨n⟩ ×2, ⟨n⟩ * and ⟨n⟩ ≥3 next to an uncorrelated Exactly(2) input labelled ×2."
  signoff "2026-11-13 8d8e8f61b13cc8dc ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, ∃ e ∈ (E cfg X).edges,
        e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name) ∧
      ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∈ t.corr → ∃ e ∈ (E cfg X).edges,
          e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name ∧
          e.row = .matchInput ∧ e.label = some (corrLabel (refCardLabel s.card))) ∧
        (X.Distinct → ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∈ t.corr →
          ∀ e ∈ (E cfg X).edges, e.arc = .input → e.src = .place s.place → e.dst = .trans t.name →
            e.row = .matchInput ∧ e.label = some (corrLabel (refCardLabel s.card)))) ∧
      ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∉ t.corr → ∃ e ∈ (E cfg X).edges,
          e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name ∧
          e.row = .input ∧ e.label = refCardLabel s.card) ∧
        (X.Distinct → ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∉ t.corr →
          ∀ e ∈ (E cfg X).edges, e.arc = .input → e.src = .place s.place → e.dst = .trans t.name →
            e.row = .input ∧ e.label = refCardLabel s.card)) ∧
      (∀ e ∈ (E cfg X).edges, e.arc ≠ .ghost → e.row = .matchInput →
        e.arc = .input ∧ ∃ t ∈ X.trans, ∃ s ∈ t.core.inputs,
          s.place ∈ t.corr ∧ e.src = .place s.place ∧ e.dst = .trans t.name)

/- The pinned readable form of EXP-018: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_018 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (∀ t ∈ X.trans,
        ∀ s ∈ t.core.inputs,
          ∃ e ∈ (E cfg X).edges, e.arc = ArcType.input ∧ e.src = NodeRef.place s.place ∧ e.dst = NodeRef.trans t.name) ∧
      ((∀ t ∈ X.trans,
            ∀ s ∈ t.core.inputs,
              s.place ∈ t.corr →
                ∃ e ∈ (E cfg X).edges,
                  e.arc = ArcType.input ∧
                    e.src = NodeRef.place s.place ∧
                      e.dst = NodeRef.trans t.name ∧
                        e.row = EdgeRow.matchInput ∧ e.label = some (corrLabel (refCardLabel s.card))) ∧
          (X.Distinct →
            ∀ t ∈ X.trans,
              ∀ s ∈ t.core.inputs,
                s.place ∈ t.corr →
                  ∀ e ∈ (E cfg X).edges,
                    e.arc = ArcType.input →
                      e.src = NodeRef.place s.place →
                        e.dst = NodeRef.trans t.name →
                          e.row = EdgeRow.matchInput ∧ e.label = some (corrLabel (refCardLabel s.card)))) ∧
        ((∀ t ∈ X.trans,
              ∀ s ∈ t.core.inputs,
                s.place ∉ t.corr →
                  ∃ e ∈ (E cfg X).edges,
                    e.arc = ArcType.input ∧
                      e.src = NodeRef.place s.place ∧
                        e.dst = NodeRef.trans t.name ∧ e.row = EdgeRow.input ∧ e.label = refCardLabel s.card) ∧
            (X.Distinct →
              ∀ t ∈ X.trans,
                ∀ s ∈ t.core.inputs,
                  s.place ∉ t.corr →
                    ∀ e ∈ (E cfg X).edges,
                      e.arc = ArcType.input →
                        e.src = NodeRef.place s.place →
                          e.dst = NodeRef.trans t.name → e.row = EdgeRow.input ∧ e.label = refCardLabel s.card)) ∧
          ∀ e ∈ (E cfg X).edges,
            e.arc ≠ ArcType.ghost →
              e.row = EdgeRow.matchInput →
                e.arc = ArcType.input ∧
                  ∃ t ∈ X.trans,
                    ∃ s ∈ t.core.inputs, s.place ∈ t.corr ∧ e.src = NodeRef.place s.place ∧ e.dst = NodeRef.trans t.name
-/
#guard_msgs in #print EXP_018

/-! ### The reference -/

section Reference

variable {S : ClusterStage} {cfg : ExportCfg} {X : ExportNet}

/-- On a net with distinct transition names and at most one input arc per place, the input edge
of the reference exporter from the place of input arc `s` of `t` to the node of `t` is
`refInputEdge t s`, whatever the cluster stage. -/
theorem exp018_inputEdge (hX : X.Distinct) {t : ExportTrans} (ht : t ∈ X.trans)
    {s : NInSpec String} (hs : s ∈ t.core.inputs) {e : XEdge}
    (he : e ∈ (refExportWith S cfg X).edges) (ha : e.arc = .input)
    (hsrc : e.src = .place s.place) (hdst : e.dst = .trans t.name) : e = refInputEdge t s := by
  have hg : e.arc ≠ .ghost := by rw [ha]; exact nofun
  obtain ⟨t', ht', he'⟩ := refExportWith_edge_of_ne_ghost he hg
  obtain ⟨s', hs', rfl⟩ := refTransEdges_input he' ha
  have hname : t'.name = t.name := by simpa [refInputEdge] using hdst
  have htt := ExportNet.eq_of_name hX.1 ht' ht hname
  subst htt
  have hp : s'.place = s.place := by simpa [refInputEdge] using hsrc
  have hss : s' = s := List.inj_on_of_nodup_map (hX.2 t' ht') hs' hs hp
  subst hss
  rfl

/-- The only edge of a transition the reference draws with the `match-input` row is the input
edge of a correlated place. -/
theorem exp018_matchInput {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (hr : e.row = .matchInput) : ∃ s ∈ t.core.inputs, s.place ∈ t.corr ∧ e = refInputEdge t s := by
  rcases mem_refTransEdges.mp he with ⟨s, hs, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · by_cases hc : s.place ∈ t.corr
    · exact ⟨s, hs, hc, rfl⟩
    · simp [refInputEdge, hc] at hr
  · rcases (refEmit_ofTrans_arc h).1 with ⟨_, h1⟩ | ⟨_, h1, _⟩ <;> rw [h1] at hr <;> cases hr
  all_goals simp [refInhibitorEdge, refReadEdge, refResetEdge] at hr

end Reference

/-- The reference exporter satisfies EXP-018 at every cluster stage: each input arc gets the
edge `refInputEdge`, of arc type input, with row `matchInput` and label `corrLabel` of the
cardinality label exactly when the place is correlated; every other edge of a transition has
the row of its own arc type, and the stage adds only ghost edges. -/
theorem EXP_018_any (S : ClusterStage) : EXP_018 (refExportWith S) := by
  intro cfg X
  have hin : ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, refInputEdge t s ∈ (refExportWith S cfg X).edges :=
    fun t ht s hs => refExportWith_edge_of_trans ht (mem_refTransEdges.mpr (Or.inl ⟨s, hs, rfl⟩))
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro t ht s hs
    exact ⟨refInputEdge t s, hin t ht s hs, rfl, rfl, rfl⟩
  · intro t ht s hs hc
    exact ⟨refInputEdge t s, hin t ht s hs, rfl, rfl, rfl, by simp [refInputEdge, hc],
      by simp [refInputEdge, refInputLabel, hc]⟩
  · intro hX t ht s hs hc e he ha hsrc hdst
    rw [exp018_inputEdge hX ht hs he ha hsrc hdst]
    simp [refInputEdge, refInputLabel, hc]
  · intro t ht s hs hc
    exact ⟨refInputEdge t s, hin t ht s hs, rfl, rfl, rfl, by simp [refInputEdge, hc],
      by simp [refInputEdge, refInputLabel, hc]⟩
  · intro hX t ht s hs hc e he ha hsrc hdst
    rw [exp018_inputEdge hX ht hs he ha hsrc hdst]
    simp [refInputEdge, refInputLabel, hc]
  · intro e he hg hr
    obtain ⟨t, ht, he'⟩ := refExportWith_edge_of_ne_ghost he hg
    obtain ⟨s, hs, hc, rfl⟩ := exp018_matchInput he' hr
    exact ⟨rfl, t, ht, s, hs, hc, rfl, rfl⟩

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-018 (`EXP_018_any` at the reference cluster stage). -/
@[evidence holds EXP_018]
theorem EXP_018_reference : EXP_018 refExport := EXP_018_any _

/-! ### Wrong exporters, one per line -/

/-- The edges of transition `t` the reference draws after its input edges: the output side, then
the inhibitor, read and standalone reset edges. -/
def exp018Rest (t : ExportTrans) : List XEdge := (refTransEdges t).drop t.core.inputs.length

/-- The reference exporter with the input edges of each transition drawn by `g` (a list, so that
an edge may be dropped) and every other edge of the transition rewritten by `h`. -/
def exp018Edges (g : ExportTrans → NInSpec String → List XEdge) (h : ExportTrans → XEdge → XEdge) :
    Exporter := fun cfg X =>
  { refExportFlat cfg X with
    edges := X.trans.flatMap fun t => t.core.inputs.flatMap (g t) ++ (exp018Rest t).map (h t) }

/-- The reference exporter with the input edge of each correlated place drawn by `f`. -/
def exp018Corr (f : ExportTrans → NInSpec String → List XEdge) : Exporter :=
  exp018Edges (fun t s => if s.place ∈ t.corr then f t s else [refInputEdge t s]) fun _ e => e

/-- The join of the test derivation: `Join` matches `A` and `B` (two `One` inputs) and also
consumes the uncorrelated `C`. -/
def exp018Join : ExportTrans :=
  { core := ⟨"Join", [⟨"A", .one⟩, ⟨"B", .one⟩, ⟨"C", .one⟩], [], [], []⟩,
    out := some (.place "Out"), corr := ["A", "B"] }

/-- A second join with cardinalities: `Q` (`Exactly(2)`), `R` (`All`) and `S` (`AtLeast(3)`)
correlated, `U` (`Exactly(2)`) not. -/
def exp018Batch : ExportTrans :=
  { core := ⟨"Batch", [⟨"Q", .exactly 2⟩, ⟨"R", .all⟩, ⟨"S", .atLeast 3⟩, ⟨"U", .exactly 2⟩],
      [], [], []⟩,
    out := some (.place "Done"), corr := ["Q", "R", "S"] }

/-- The example net: the two joins. -/
def exp018Net : ExportNet := { trans := [exp018Join, exp018Batch] }

/-- The example net has distinct transition names and one input arc per place. -/
theorem exp018Net_distinct : exp018Net.Distinct := by
  unfold ExportNet.Distinct
  decide

/-- An exporter that draws no edge for a correlated input (the match shown elsewhere). -/
def exp018_dropCorr : Exporter := exp018Corr fun _ _ => []

/-- ✗ Dropping the edge of a correlated input violates EXP-018 (line 1). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_dropCorr : ¬ EXP_018 exp018_dropCorr := by
  intro h
  exact absurd (h {} exp018Net).1 (by decide)

/-- An exporter that gives the edge of a correlated input the arc type read, as if the match
only tested the token. -/
def exp018_arcRead : Exporter :=
  exp018Corr fun t s => [{ refInputEdge t s with arc := .read }]

/-- ✗ Changing the arc type of a correlated edge violates EXP-018 (line 1: no input edge is
left for the arc). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_arcRead : ¬ EXP_018 exp018_arcRead := by
  intro h
  exact absurd (h {} exp018Net).1 (by decide)

/-- An exporter that labels a correlated edge but keeps the `input` row (no teal colour). -/
def exp018_plainRow : Exporter :=
  exp018Corr fun t s => [{ refInputEdge t s with row := .input }]

/-- ✗ Keeping the input row on a correlated edge violates EXP-018 (line 2, first half: no input
edge of `A` is teal). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_plainRow : ¬ EXP_018 exp018_plainRow := by
  intro h
  exact absurd (h {} exp018Net).2.1.1 (by decide)

/-- An exporter that replaces the cardinality label of a correlated edge by `⟨n⟩`. -/
def exp018_replace : Exporter :=
  exp018Corr fun t s => [{ refInputEdge t s with label := some "⟨n⟩" }]

/-- ✗ `⟨n⟩` alone on a correlated `Exactly(2)` edge violates EXP-018 (line 2, second half, AC3). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_replace : ¬ EXP_018 exp018_replace := by
  intro h
  exact absurd ((h {} exp018Net).2.1.2 exp018Net_distinct) (by decide)

/-- The label `⟨n⟩` followed directly by the cardinality label, without the space. -/
def exp018NoSpaceLabel (c : Card) : String := "⟨n⟩" ++ (refCardLabel c).getD ""

/-- The input edge of arc `s` of `t` with the label joined without a space when the place is
correlated, the reference edge otherwise. -/
def exp018NoSpaceEdge (t : ExportTrans) (s : NInSpec String) : XEdge :=
  if s.place ∈ t.corr then { refInputEdge t s with label := some (exp018NoSpaceLabel s.card) }
  else refInputEdge t s

/-- An exporter that joins `⟨n⟩` and the cardinality label without a space: `⟨n⟩×2`. -/
def exp018_noSpace : Exporter := exp018Edges (fun t s => [exp018NoSpaceEdge t s]) fun _ e => e

/-- ✗ `⟨n⟩×2` violates EXP-018 (line 2, second half): the two labels are joined by one space. -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_noSpace : ¬ EXP_018 exp018_noSpace := by
  intro h
  exact absurd ((h {} exp018Net).2.1.2 exp018Net_distinct) (by decide)

/-- An exporter that always writes `⟨n⟩` and a space before the cardinality label, so a
correlated `One` edge reads `⟨n⟩ ` with a trailing space. -/
def exp018_trailingSpace : Exporter :=
  exp018Corr fun t s =>
    [{ refInputEdge t s with label := some ("⟨n⟩ " ++ (refCardLabel s.card).getD "") }]

/-- ✗ A trailing space on a correlated `One` edge violates EXP-018 (line 2, second half: `⟨n⟩`
alone). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_trailingSpace : ¬ EXP_018 exp018_trailingSpace := by
  intro h
  exact absurd ((h {} exp018Net).2.1.2 exp018Net_distinct) (by decide)

/-- The input edge of arc `s` of `t` drawn as a correlated one, whether or not `t` correlates its
place. -/
def exp018Decorated (t : ExportTrans) (s : NInSpec String) : XEdge :=
  { refInputEdge t s with row := .matchInput, label := some (corrLabel (refCardLabel s.card)) }

/-- An exporter that decorates every input of a transition that has a match specification. -/
def exp018_allInputs : Exporter :=
  exp018Edges (fun t s => if t.corr.isEmpty then [refInputEdge t s] else [exp018Decorated t s])
    fun _ e => e

/-- ✗ Decorating the uncorrelated input `C` of `Join` violates EXP-018 (line 3, second
half, AC2). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_allInputs : ¬ EXP_018 exp018_allInputs := by
  intro h
  exact absurd ((h {} exp018Net).2.2.1.2 exp018Net_distinct) (by decide)

/-- An exporter that also draws the output edges of a transition with a match specification
with the `match-input` row. -/
def exp018_outTeal : Exporter :=
  exp018Edges (fun t s => [refInputEdge t s])
    fun t e => if !t.corr.isEmpty && e.arc == .output then { e with row := .matchInput } else e

/-- ✗ A teal output edge violates EXP-018 (line 4). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_outTeal : ¬ EXP_018 exp018_outTeal := by
  intro h
  exact absurd (h {} exp018Net).2.2.2 (by decide)

/-- An exporter that writes `⟨n⟩` only when a cardinality label exists, mapping over the
cardinality label (Rust `input_label(spec).map(|c| format!("⟨n⟩ {c}"))`), so a correlated `One`
edge is teal and has no label. -/
def exp018_optionMap : Exporter :=
  exp018Corr fun t s =>
    [{ refInputEdge t s with label := (refCardLabel s.card).map (fun c => "⟨n⟩ " ++ c) }]

/-- ✗ A correlated `One` edge with no label violates EXP-018 (line 2, first half: `⟨n⟩` alone). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_optionMap : ¬ EXP_018 exp018_optionMap := by
  intro h
  exact absurd (h {} exp018Net).2.1.1 (by decide)

/-- An exporter that keeps the `input` row of an uncorrelated input but writes `⟨n⟩` before its
cardinality label: `Join`'s `C` reads `⟨n⟩`, `Batch`'s `U` reads `⟨n⟩ ×2`. -/
def exp018_uncorrPrefix : Exporter :=
  exp018Edges
    (fun t s => if s.place ∈ t.corr then [refInputEdge t s]
      else [{ refInputEdge t s with label := some (corrLabel (refCardLabel s.card)) }])
    fun _ e => e

/-- ✗ An `⟨n⟩` prefix on an uncorrelated input violates EXP-018 (line 3, first half, the label:
AC2's "no `⟨n⟩` prefix"), although the edge keeps the input row. -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_uncorrPrefix : ¬ EXP_018 exp018_uncorrPrefix := by
  intro h
  exact absurd (h {} exp018Net).2.2.1.1 (by decide)

/-- An exporter that draws the decorated edge of a correlated input and also a plain copy of it. -/
def exp018_dupPlain : Exporter :=
  exp018Corr fun t s =>
    [refInputEdge t s, { refInputEdge t s with row := .input, label := refCardLabel s.card }]

/-- The duplicating exporter meets the first half of line 2 on the example net: each correlated
input has its decorated edge. -/
theorem exp018_dupPlain_first : ∀ t ∈ exp018Net.trans, ∀ s ∈ t.core.inputs, s.place ∈ t.corr →
    ∃ e ∈ (exp018_dupPlain {} exp018Net).edges, e.arc = .input ∧ e.src = .place s.place ∧
      e.dst = .trans t.name ∧ e.row = .matchInput ∧
      e.label = some (corrLabel (refCardLabel s.card)) := by
  decide

/-- ✗ A plain copy of a correlated edge violates EXP-018 (line 2, second half), which the first
half alone would accept (`exp018_dupPlain_first`). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_dupPlain : ¬ EXP_018 exp018_dupPlain := by
  intro h
  exact absurd ((h {} exp018Net).2.1.2 exp018Net_distinct) (by decide)

/-! ### Two transitions of one name -/

/-- The correlation stored under a transition name, last write wins, as a mapper that fills a
map keyed by node id in its transition loop would read it. -/
def exp018CorrOf (X : ExportNet) (n : String) : List String :=
  ((X.trans.reverse.find? (·.name == n)).map (·.corr)).getD []

/-- An exporter that decorates each transition by the correlation stored under its name. On a
net with distinct names it draws what the reference draws. -/
def exp018_lastWins : Exporter := fun cfg X =>
  { refExportFlat cfg X with
    edges := X.trans.flatMap fun t => refTransEdges { t with corr := exp018CorrOf X t.name } }

/-- A transition `T` that consumes `A` and correlates it. -/
def exp018TwinCorr : ExportTrans :=
  { core := ⟨"T", [⟨"A", .one⟩], [], [], []⟩, out := some (.place "O1"), corr := ["A"] }

/-- A second transition `T` that consumes `A` with no match specification. -/
def exp018TwinPlain : ExportTrans :=
  { core := ⟨"T", [⟨"A", .one⟩], [], [], []⟩, out := some (.place "O2") }

/-- Two transitions named `T`, the correlating one first. -/
def exp018Twins : ExportNet := { trans := [exp018TwinCorr, exp018TwinPlain] }

/-- Two transitions named `T`, the correlating one last. -/
def exp018TwinsSwapped : ExportNet := { trans := [exp018TwinPlain, exp018TwinCorr] }

/-- Neither twin net is `Distinct`, so the second halves of lines 2 and 3 say nothing on them. -/
theorem exp018Twins_not_distinct : ¬ exp018Twins.Distinct ∧ ¬ exp018TwinsSwapped.Distinct := by
  unfold ExportNet.Distinct
  decide

/-- ✗ With the correlating `T` first, the mapper draws both `A` edges plain: no input edge of the
correlated `A` is decorated, which violates EXP-018 (line 2, first half). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_lastWinsCorr : ¬ EXP_018 exp018_lastWins := by
  intro h
  exact absurd (h {} exp018Twins).2.1.1 (by decide)

/-- ✗ With the correlating `T` last, the mapper decorates both `A` edges: the uncorrelated `A` of
the first `T` has no plain edge, which violates EXP-018 (line 3, first half). -/
@[evidence forbids EXP_018]
theorem EXP_018_forbids_lastWinsUncorr : ¬ EXP_018 exp018_lastWins := by
  intro h
  exact absurd (h {} exp018TwinsSwapped).2.2.1.1 (by decide)

/-! ### The literal reading of AC1 -/

/-- Mutant of EXP-018 that reads AC1 literally: line 2 asks only that the label of a correlated
edge begins with `⟨n⟩`, not that it is `⟨n⟩` and the cardinality label joined by one space,
in both halves. -/
def EXP_018_mutant_ac1 (E : Exporter) : Prop :=
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, ∃ e ∈ (E cfg X).edges,
      e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name) ∧
    ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∈ t.corr → ∃ e ∈ (E cfg X).edges,
        e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name ∧
        e.row = .matchInput ∧ ∃ l, e.label = some l ∧ "⟨n⟩".toList <+: l.toList) ∧
      (X.Distinct → ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∈ t.corr →
        ∀ e ∈ (E cfg X).edges, e.arc = .input → e.src = .place s.place → e.dst = .trans t.name →
          e.row = .matchInput ∧ ∃ l, e.label = some l ∧ "⟨n⟩".toList <+: l.toList)) ∧
    ((∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∉ t.corr → ∃ e ∈ (E cfg X).edges,
        e.arc = .input ∧ e.src = .place s.place ∧ e.dst = .trans t.name ∧
        e.row = .input ∧ e.label = refCardLabel s.card) ∧
      (X.Distinct → ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs, s.place ∉ t.corr →
        ∀ e ∈ (E cfg X).edges, e.arc = .input → e.src = .place s.place → e.dst = .trans t.name →
          e.row = .input ∧ e.label = refCardLabel s.card)) ∧
    (∀ e ∈ (E cfg X).edges, e.arc ≠ .ghost → e.row = .matchInput →
      e.arc = .input ∧ ∃ t ∈ X.trans, ∃ s ∈ t.core.inputs,
        s.place ∈ t.corr ∧ e.src = .place s.place ∧ e.dst = .trans t.name)

/-- The edges after the input edges are the output side, the inhibitor, read and standalone
reset edges. -/
theorem exp018Rest_eq (t : ExportTrans) :
    exp018Rest t = (refEmit.ofTrans t).edges ++ t.core.inhibitors.map (refInhibitorEdge t) ++
      t.core.reads.map (refReadEdge t) ++ (refStandaloneResets t).map (refResetEdge t) := by
  unfold exp018Rest refTransEdges
  simp only [List.append_assoc]
  exact List.drop_left' (by simp)

/-- No edge after the input edges is an input edge or has the `match-input` row. -/
theorem exp018Rest_arc {t : ExportTrans} {e : XEdge} (he : e ∈ exp018Rest t) :
    e.arc ≠ .input ∧ e.row ≠ .matchInput := by
  rw [exp018Rest_eq] at he
  simp only [List.mem_append, List.mem_map] at he
  rcases he with ((h | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, h2⟩ | ⟨h1, h2, _⟩ <;>
      exact ⟨by rw [h1]; exact nofun, by rw [h2]; exact nofun⟩
  all_goals exact ⟨nofun, nofun⟩

/-- The edges of `exp018Edges g h`: the input edges `g` draws and the rewritten other edges of
each transition. -/
theorem mem_exp018Edges {g : ExportTrans → NInSpec String → List XEdge}
    {h : ExportTrans → XEdge → XEdge} {cfg : ExportCfg} {X : ExportNet} {e : XEdge} :
    e ∈ (exp018Edges g h cfg X).edges ↔
      ∃ t ∈ X.trans, (∃ s ∈ t.core.inputs, e ∈ g t s) ∨ ∃ e' ∈ exp018Rest t, h t e' = e := by
  simp [exp018Edges, List.mem_flatMap, List.mem_map]

/-- The no-space input edge has the ends and arc type of the reference input edge. -/
theorem exp018NoSpaceEdge_ends (t : ExportTrans) (s : NInSpec String) :
    (exp018NoSpaceEdge t s).arc = .input ∧ (exp018NoSpaceEdge t s).src = .place s.place ∧
      (exp018NoSpaceEdge t s).dst = .trans t.name := by
  unfold exp018NoSpaceEdge
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- On a net with distinct names and one input arc per place, the input edge of the no-space
exporter from the place of `s` to `t` is `exp018NoSpaceEdge t s`. -/
theorem exp018_noSpace_inputEdge {cfg : ExportCfg} {X : ExportNet} (hX : X.Distinct)
    {t : ExportTrans} (ht : t ∈ X.trans) {s : NInSpec String} (hs : s ∈ t.core.inputs)
    {e : XEdge} (he : e ∈ (exp018_noSpace cfg X).edges) (ha : e.arc = .input)
    (hsrc : e.src = .place s.place) (hdst : e.dst = .trans t.name) :
    e = exp018NoSpaceEdge t s := by
  obtain ⟨t', ht', ⟨s', hs', he'⟩ | ⟨e', he', rfl⟩⟩ := mem_exp018Edges.mp he
  · rw [List.mem_singleton] at he'
    subst he'
    obtain ⟨_, h2, h3⟩ := exp018NoSpaceEdge_ends t' s'
    have hname : t'.name = t.name := by rw [h3] at hdst; exact NodeRef.trans.inj hdst
    have htt := ExportNet.eq_of_name hX.1 ht' ht hname
    subst htt
    have hp : s'.place = s.place := by rw [h2] at hsrc; exact NodeRef.place.inj hsrc
    rw [List.inj_on_of_nodup_map (hX.2 t' ht') hs' hs hp]
  · exact absurd ha (exp018Rest_arc he').1

/-- The no-space exporter meets the literal reading of AC1: its correlated labels begin with
`⟨n⟩`, and every other line holds as for the reference. -/
theorem exp018_noSpace_ac1 : EXP_018_mutant_ac1 exp018_noSpace := by
  intro cfg X
  have hin : ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs,
      exp018NoSpaceEdge t s ∈ (exp018_noSpace cfg X).edges := fun t ht s hs =>
    mem_exp018Edges.mpr ⟨t, ht, Or.inl ⟨s, hs, List.mem_singleton_self _⟩⟩
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro t ht s hs
    exact ⟨exp018NoSpaceEdge t s, hin t ht s hs, exp018NoSpaceEdge_ends t s⟩
  · intro t ht s hs hc
    obtain ⟨h1, h2, h3⟩ := exp018NoSpaceEdge_ends t s
    refine ⟨exp018NoSpaceEdge t s, hin t ht s hs, h1, h2, h3,
      by simp [exp018NoSpaceEdge, hc, refInputEdge], exp018NoSpaceLabel s.card,
      by simp [exp018NoSpaceEdge, hc], ?_⟩
    simp only [exp018NoSpaceLabel, String.toList_append]
    exact List.prefix_append _ _
  · intro hX t ht s hs hc e he ha hsrc hdst
    rw [exp018_noSpace_inputEdge hX ht hs he ha hsrc hdst]
    refine ⟨by simp [exp018NoSpaceEdge, hc, refInputEdge], exp018NoSpaceLabel s.card,
      by simp [exp018NoSpaceEdge, hc], ?_⟩
    simp only [exp018NoSpaceLabel, String.toList_append]
    exact List.prefix_append _ _
  · intro t ht s hs hc
    obtain ⟨h1, h2, h3⟩ := exp018NoSpaceEdge_ends t s
    exact ⟨exp018NoSpaceEdge t s, hin t ht s hs, h1, h2, h3,
      by simp [exp018NoSpaceEdge, hc, refInputEdge], by simp [exp018NoSpaceEdge, hc, refInputEdge, refInputLabel]⟩
  · intro hX t ht s hs hc e he ha hsrc hdst
    rw [exp018_noSpace_inputEdge hX ht hs he ha hsrc hdst]
    simp [exp018NoSpaceEdge, hc, refInputEdge, refInputLabel]
  · intro e he _ hr
    obtain ⟨t, ht, ⟨s, hs, he'⟩ | ⟨e', he', rfl⟩⟩ := mem_exp018Edges.mp he
    · rw [List.mem_singleton] at he'
      subst he'
      obtain ⟨h1, h2, h3⟩ := exp018NoSpaceEdge_ends t s
      by_cases hc : s.place ∈ t.corr
      · exact ⟨h1, t, ht, s, hs, hc, h2, h3⟩
      · simp [exp018NoSpaceEdge, hc, refInputEdge] at hr
    · exact absurd hr (exp018Rest_arc he').2

/-- The no-space exporter kills the AC1-literal mutant: `⟨n⟩×2` begins with `⟨n⟩`, but EXP-018
asks for `⟨n⟩ ×2`. -/
@[evidence mutant EXP_018]
theorem EXP_018_mutant_ac1_killed : EXP_018_mutant_ac1 exp018_noSpace ∧ ¬ EXP_018 exp018_noSpace :=
  ⟨exp018_noSpace_ac1, EXP_018_forbids_noSpace⟩

/-! ### Non-vacuity -/

/-- The test derivation on the reference: the correlated `One` inputs `A` and `B` of `Join` are
drawn with the `match-input` row and labelled `⟨n⟩`, the uncorrelated `C` with the `input` row
and no label; the correlated inputs of `Batch` read `⟨n⟩ ×2`, `⟨n⟩ *` and `⟨n⟩ ≥3`, its
uncorrelated `Exactly(2)` input `×2`; the output edges keep the output row. The style table
gives the `match-input` row the colour `#0d9488` and the `input` row another colour. -/
@[evidence nonvacuous EXP_018]
theorem EXP_018_nonvacuous :
    (edgeStyle .matchInput).color = "#0d9488" ∧ (edgeStyle .input).color = "#333333" ∧
    (refExportFlat {} exp018Net).edges.map (fun e => (nodeId e.src, nodeId e.dst, e.arc, e.row, e.label)) =
      [("p_A", "t_Join", .input, .matchInput, some "⟨n⟩"),
       ("p_B", "t_Join", .input, .matchInput, some "⟨n⟩"),
       ("p_C", "t_Join", .input, .input, none),
       ("t_Join", "p_Out", .output, .output, none),
       ("p_Q", "t_Batch", .input, .matchInput, some "⟨n⟩ ×2"),
       ("p_R", "t_Batch", .input, .matchInput, some "⟨n⟩ *"),
       ("p_S", "t_Batch", .input, .matchInput, some "⟨n⟩ ≥3"),
       ("p_U", "t_Batch", .input, .input, some "×2"),
       ("t_Batch", "p_Done", .output, .output, none)] := by
  decide

end Libpetri.Spec
