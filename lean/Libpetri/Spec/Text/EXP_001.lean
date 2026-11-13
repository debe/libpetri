import Libpetri.Spec.Text

requirement_text EXP_001
  id "EXP-001"
  title "Graph Export Format"
  priority MUST
  kind F
  body r#"⟦s1|The engine MUST support exporting the net structure to at least one standard graph format suitable for visualization.⟧ The canonical format is DOT (Graphviz), a widely-supported, text-based format.

In this chapter the node of a place or a transition is the node that stands for it in the exported graph, whatever its DOT ID ([EXP-014]). A place that the net declares and on which no transition has an arc may have a node or none; a node for it is the intended end state.

⟦s2|The export *shall* draw exactly one node for each place on which some transition has an input, output, inhibitor, read or reset arc.⟧

⟦s3|*Where* the transitions of a net have pairwise distinct names, the export *shall* draw exactly one node for each transition.⟧

⟦s4|The export *shall* draw a place node only for a place that the net declares or on which some transition has an arc, and a transition node only for a transition of the net.⟧

⟦s5|The export *shall* draw, for each input arc, inhibitor arc and read arc, an edge of the arc's type from the node of its place to the node of its transition.⟧

⟦s6|*Where* the transitions of a net have pairwise distinct names, the export *shall* draw as many input, inhibitor and read edges from the node of a place to the node of a transition as the transition has arcs of that type on that place.⟧

⟦s7|The export *shall* draw into each place that a transition's output spec names an edge from that transition or from one of its junctions, of type output or, where the transition also has a reset arc on that place, of the combined reset+output type of [EXP-013].⟧

⟦s8|The export *shall* draw into each place on which a transition has a reset arc an edge from that transition or from one of its junctions, of type reset or, where the transition's output spec also names that place, of the combined reset+output type of [EXP-013].⟧

**Acceptance Criteria:**
1. Export produces valid, parseable output in the chosen format.
2. All places and transitions in the net are represented.
3. All arcs (input, output, inhibitor, read, reset) are represented.

**Implementation notes:**
- Java: DOT (Graphviz) format
- TypeScript: DOT (Graphviz) format
- Rust: DOT (Graphviz) format

**Test derivation:** Build net with all arc types; export; verify output parses correctly."#
