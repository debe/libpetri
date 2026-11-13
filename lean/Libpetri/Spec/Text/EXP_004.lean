import Libpetri.Spec.Text

requirement_text EXP_004
  id "EXP-004"
  title "Arc Rendering"
  priority MUST
  kind F
  body r#"⟦s1|Each arc type has a visually distinct rendering.⟧ Its colour, line style, arrowhead and pen width are those of the row its bullet names in the `edge` table of `spec/petri-net-styles.json`:
- ⟦s2|**Input arc**: solid arrow from place to transition, row `input` (a correlated input of [EXP-018] takes row `match-input`)⟧
- ⟦s3|**Output arc**: solid arrow from transition, or from one of its junction nodes ([EXP-012]), to place, row `output`; the edge of a `ForwardInput` leaf is dashed and labelled with its source place ([EXP-012])⟧
- ⟦s4|**Inhibitor arc**: arrow with circle arrowhead (standard notation) from place to transition, without a label, row `inhibitor`⟧
- ⟦s5|**Read arc**: dashed arrow from place to transition, labelled `read`, row `read`⟧
- ⟦s6|**Reset arc**: bold arrow from transition to place, labelled `reset`, row `reset`; a reset arc into a place that a leaf of the output spec also ends in is drawn as the combined edge of [EXP-013]⟧

⟦s7|The reset edge points from the transition to the place it empties. This is a drawing convention: the reset arc itself goes from the place to the transition ([CORE-034]).⟧

⟦s8|Visually distinct means that any two edges of different types among these five differ in drawn direction, colour, line style or arrowhead.⟧ The combined edge of [EXP-013] has the style of the reset edge and differs from it only in its label.

⟦s9|The mapper *shall* draw each input arc as a solid edge of arc type `input` from its place to its transition, in the `match-input` row where [EXP-018] correlates its place and in the `input` row otherwise.⟧

⟦s10|The mapper *shall* draw each output arc of a transition into a place that the transition does not reset as an edge of arc type `output` in the `output` row, from the transition or one of its junction nodes to the place.⟧

⟦s11|Every edge of arc type `output` that the mapper draws *shall* run from a transition or one of its junction nodes to a place or to a junction node of that transition, in the `output` row.⟧

⟦s12|An edge of arc type `output` *shall* be solid, except the edge of a `ForwardInput` leaf of its transition's output spec from place F to a place P that the transition does not reset, which is dashed, ends in P and is labelled `⟵F`, after another label and a space when it has one.⟧

⟦s13|The mapper *shall* draw each inhibitor arc as a solid edge of arc type `inhibitor` from its place to its transition, in the `inhibitor` row and without a label.⟧

⟦s14|The mapper *shall* draw each read arc as an edge of arc type `read` from its place to its transition, in the `read` row and labelled `read`.⟧

⟦s15|*Where* no leaf of a transition's output spec ends in the place of one of its reset arcs, the mapper *shall* draw that reset arc as an undashed edge of arc type `reset` from the transition to the place, in the `reset` row and labelled `reset`.⟧

⟦s16|Every edge of arc type `input`, `inhibitor`, `read` or `reset` that the mapper draws *shall* be the edge of one arc of that type, with the ends, row and line style the sentences above give it and the label they give it where they give one; an edge of arc type `reset` is the edge of a reset arc into a place that no leaf of its transition's output spec ends in.⟧

**Acceptance Criteria:**
1. Each arc type is visually distinguishable.
2. Arc direction reflects flow (place→transition for input, transition→place for output).

**Test derivation:** Build net with all 5 arc types; export; verify each arc type has distinct rendering."#
