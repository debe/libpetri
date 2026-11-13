import Libpetri.Spec.Text

requirement_text EXP_002
  id "EXP-002"
  title "Visual Semantics — Places"
  priority MUST
  kind F
  body r#"⟦s1|Places are rendered as distinct shapes from transitions:⟧
- ⟦s2|Places: circles, ellipses, or stadium-shaped nodes (following Petri net convention)⟧
- ⟦s3|Place names are displayed as labels⟧

⟦s4|The mapper *shall* give every place node a place category, which is the place, start, end, environment or terminal row of the style table, and *shall* give no transition node and no junction node a place category (a transition node gets the transition category, see [EXP-003]).⟧

⟦s5|The mapper *shall* draw every place node for a place of the net (one that the net declares or on which some transition has an arc), show the name of that place, as written and not sanitized, as the external label (`xlabel`) of the node, and give the node an empty label, so that nothing is drawn inside it.⟧

**Acceptance Criteria:**
1. Places are visually distinguishable from transitions.
2. Place names are readable.

**Test derivation:** Export net; verify place nodes use correct shape syntax."#
