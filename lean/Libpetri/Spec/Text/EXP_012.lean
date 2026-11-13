import Libpetri.Spec.Text

requirement_text EXP_012
  id "EXP-012"
  title "XOR/AND Junction Nodes"
  priority MUST
  kind F
  body r#"⟦s1|For every `Out.Xor` or `Out.And` group with **two or more children**, the mapper MUST insert a synthetic *junction node* between the transition and the children.⟧ ⟦s2|A group with fewer than two children MUST NOT produce a junction (it is a pass-through).⟧

**Junction node attributes** (gateway convention — diamond + single heavy glyph):
- **XOR junction**: shape `diamond`, fill `#FFFFFF`, stroke `#333333`, penwidth `1.0`, width `0.3`, height `0.3`, label `"✕"` (U+2715 Multiplication X), fontsize `14`, fixedsize `true`. Style category `xor-junction`.
- **AND junction**: shape `diamond`, fill `#FFFFFF`, stroke `#333333`, penwidth `1.0`, width `0.3`, height `0.3`, label `"✚"` (U+271A Heavy Greek Cross), fontsize `14`, fixedsize `true`. Style category `and-junction`.

The two kinds share a shape and color family; the inline heavy glyph (`✕` for exclusive choice, `✚` for parallel split) is the discriminator. Heavy dingbat variants are used (instead of the lightweight `×` U+00D7 / `+` U+002B) so the symbol stays legible at the small junction size where the diamonds read as scaffolding rather than first-class entities.

**Edge routing:**
- Edge `transition → junction`: output style, no label (or the timeout label `⏱<n>ms` if the group is wrapped in `Out.Timeout`).
- Edge `junction → child` for an XOR junction: output style, label = the inferred branch label (place name for `Place`, `⏱<n>ms` for `Timeout`, or none if the child is itself a group).
- Edge `junction → child` for an AND junction: output style, no label of its own.
- A `Timeout` node puts its label `⏱<n>ms` on the edge that enters its child, wherever the `Timeout` sits.
- A `ForwardInput` leaf edge is dashed and labelled `⟵<from>`, after the label the edge would otherwise carry and a space when it has one.
- Where [EXP-013] combines a leaf edge into a reset place, its arc type, label and style are those of [EXP-013].

⟦s3|The mapper *shall* draw one junction node for each `And` or `Xor` group of an output spec that has two or more children, of the group's kind, and no other junction node.⟧

⟦s4|*Where* an `And` or `Xor` group has fewer than two children, the mapper *shall* draw its child, if it has one, from the group's parent and with the label the edge into the group would carry.⟧

⟦s5|The mapper *shall* draw exactly one solid output edge into each junction node, into the place of each `Place` leaf and into the target place of each `ForwardInput` leaf, from the nearest junction node above it, or from the transition when there is none, and no other edge for the output spec.⟧

⟦s6|The edge into a child of an `Xor` junction *shall* carry the child's branch label: the place name of a `Place` child, `⏱<n>ms` for a `Timeout` child of n ms, and no label for an `And` or `Xor` child.⟧

⟦s7|The edge into a child of an `And` junction, and the edge from the transition into the output spec, *shall* carry no label of their own.⟧

⟦s8|*Where* a `Timeout` node of n ms is in an output spec, the edge drawn into its child *shall* carry `⏱<n>ms` in place of the label the edge into the `Timeout` would carry.⟧

⟦s9|*Where* a leaf is a `ForwardInput` from place F to place P, the mapper *shall* draw its edge as the edge of a `Place` leaf for P at the same position, dashed instead of solid, and with `⟵F` after its label and a space, or as its only label when it has none.⟧

⟦s10|*Where* [EXP-013] combines a leaf edge into a reset place, that edge *shall* take the arc type, label and style [EXP-013] gives it in place of the ones above.⟧

**Acceptance Criteria:**
1. Net with `XOR(P_a, P_b)` exports one diamond junction labelled `"✕"` and two edges junction→{P_a, P_b}.
2. Net with `AND(P_c, P_d)` exports one diamond junction labelled `"✚"` and two edges junction→{P_c, P_d}.
3. Net with `AND(P_a)` (single child) exports a direct edge transition→P_a, no junction.
4. Nested groups (e.g. `XOR(AND(P_a, P_b), P_c)`) produce nested junctions.
5. Java, TypeScript, and Rust mappers produce byte-identical junction nodes and edges for the same input net (modulo deterministic ordering already in place).

**Test derivation:** For each language, build a net with `XOR(A, B)`, `AND(C, D)`, `AND(A)`, and a nested case; export; assert junction node count, shape, and edge wiring."#
