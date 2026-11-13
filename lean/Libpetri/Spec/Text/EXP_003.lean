import Libpetri.Spec.Text

requirement_text EXP_003
  id "EXP-003"
  title "Visual Semantics — Transitions"
  priority MUST
  kind F
  body r#"⟦s1|Transitions are rendered as rectangles or bars (following Petri net convention).⟧ ⟦s2|Transition names are displayed as labels.⟧

The transition category is the `transition` row of the node table in `spec/petri-net-styles.json`; its shape is `box`, a rectangle, so the export draws rectangles and does not use bars. No place row, no junction row and not the `interface-port` row has that shape. The `sync-channel` row is also `box`; a place node never has it, since [EXP-002] draws every place node with a place row. Transitions and places are therefore told apart by this requirement together with [EXP-002]. The timing interval and the priority that may follow the name in a transition's label are given by [EXP-007].

⟦s3|The export *shall* draw a node for every transition of the net.⟧

⟦s4|The export *shall* draw no node that stands for a transition the net does not have.⟧

⟦s5|The export *shall* give a node the transition category exactly when the node stands for a transition.⟧

⟦s6|The export *shall* label the node of a transition with a text that starts with the transition's name as written in the net.⟧

⟦s7|*Where* the configuration hides the timing interval and the priority, the export *shall* label the node of a transition with the transition's name alone.⟧

**Acceptance Criteria:**
1. Transitions are visually distinguishable from places.
2. Transition names are readable.

**Test derivation:** Export net; verify transition nodes use correct shape syntax."#
