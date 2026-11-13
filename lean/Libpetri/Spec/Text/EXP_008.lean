import Libpetri.Spec.Text

requirement_text EXP_008
  id "EXP-008"
  title "Styling"
  priority SHOULD
  kind F
  body r#"⟦s1|The export applies visual styling to distinguish node categories:⟧
- **Start places** (no incoming arcs): highlighted (e.g., green)
- **End places** (no outgoing arcs): highlighted (e.g., blue)
- **Transitions**: distinct color (e.g., yellow)

Each place category names a row of the node table in `spec/petri-net-styles.json`: terminal, environment, start, end, or the regular `place` row. In this section an ordinary place is a place that is neither a terminal place ([EXEC-042]) nor an environment place ([ENV-001]). In the bullets above, an incoming arc of a place is an output arc on it (some transition's output spec names it), and an input arc on it is an outgoing arc; inhibitor arcs and reset arcs are neither, and whether a read arc is an outgoing arc is left open in this version (see the last two sentences below). The category of a place is the one the export's mapper gives it; a documentation generator that afterwards redraws the interface ports of a subnet body with the `interface-port` row ([EXP-011]) is outside this requirement.

⟦s2|The export *shall* give a terminal place the terminal category.⟧

⟦s3|The export *shall* give an environment place that is not a terminal place the environment category.⟧

⟦s4|The export *shall* give an ordinary place the start category exactly when no transition's output spec names it.⟧

⟦s5|The export *shall* give the end category to an ordinary place that some transition's output spec names and on which no transition has an input arc or a read arc.⟧

⟦s6|The export *shall not* give the end category to an ordinary place on which some transition has an input arc.⟧

⟦s7|The export *shall* give an ordinary place the start, the end or the regular place category.⟧

An ordinary place that some transition's output spec names, and on which some transition has a read arc and none has an input arc, may have the end or the regular place category in this version; the regular place category is the intended one.

⟦s8|The export *shall* give the same category to all ordinary places, in one net or in different nets, that some transition's output spec names, on which some transition has a read arc and on which no transition has an input arc.⟧

**Acceptance Criteria:**
1. Start places are visually distinct from other places.
2. End places are visually distinct from other places.

**Test derivation:** Net with start and end places; export; verify styling applied."#
