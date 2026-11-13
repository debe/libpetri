import Libpetri.Spec.Text

requirement_text EXP_014
  id "EXP-014"
  title "Junction ID Format and Layout Stability"
  priority MUST
  kind F
  body r#"⟦s1|Synthetic junction nodes MUST use IDs of the form `j_<transitionSanitized>__<kind>_<idx>`, where:⟧
- ⟦s2|`transitionSanitized` is the transition's name with non-`[A-Za-z0-9_]` characters replaced by `_` (the same `sanitize` function used for place and transition IDs).⟧
- ⟦s3|`<kind>` is `xor` or `and`.⟧
- ⟦s4|`<idx>` is a non-negative integer. Junctions in a single transition's `Out` tree are numbered in depth-first pre-order, with the counter starting at `0` and incrementing once per emitted junction. Single-child XOR/AND groups collapse (per EXP-012) and consume no counter slot. Example: `t_Nested` with output `AND(XOR(a,b), XOR(c,d))` produces three junctions in the order `j_Nested__and_0`, `j_Nested__xor_1`, `j_Nested__xor_2`.⟧

The flat counter (rather than a hierarchical path-encoded index) keeps junction IDs short and human-scannable while still being uniquely determined by the depth-first traversal of the `Out` tree, which is what cross-language byte-equality requires.

This guarantees:
1. ⟦s5|Junction IDs do not collide with place IDs (`p_…`) or transition IDs (`t_…`).⟧
2. Repeated exports of the same net produce byte-identical DOT (required for stable Graphviz `dot` layouts across reloads in debug-ui and reproducible doc-generated SVGs).
3. Cross-language byte-equality of DOT output for the same input net.

⟦s6|*Where* a node's name (the place's, the transition's, or for a junction its transition's) holds only ASCII characters, the mapper *shall* give the node the ID `p_<s>`, `t_<s>` or `j_<s>__<kind>_<idx>` according to what it stands for, with `<s>` that name with each character outside `[A-Za-z0-9_]` replaced by `_`, `<kind>` the kind of the junction and `<idx>` its index written in decimal without leading zeros.⟧

⟦s7|The ID of a node whose name holds a character outside ASCII is implementation-defined, within the rule of the next sentence.⟧

⟦s8|The mapper *shall* give no junction node the ID of a place node or a transition node, whatever the names.⟧

⟦s9|*Where* the transition names of a net are pairwise distinct, the mapper *shall* draw for each transition one junction node for each group with two or more children in its output spec, of the kind of that group, and no other junction node for the transition.⟧

⟦s10|*Where* the transition names of a net are pairwise distinct, the mapper *shall* give the junction node of a group with two or more children the index of that group in the depth-first pre-order of such groups in the transition's output spec, counting from 0, with one counter for both kinds.⟧

⟦s11|*Where* the transition names of a net are pairwise distinct, the mapper *shall* draw as the output edges of a transition, compared by their ends, exactly the edges [EXP-012] draws for its output spec, each as often as [EXP-012] draws it, with each junction numbered by the index of its group.⟧

⟦s12|The mapper *shall* draw no edge that starts or ends at a junction node it does not draw.⟧

⟦s13|The mapper *shall* draw no junction node for a transition the net does not have.⟧

⟦s14|The mapper *shall* give a junction node of kind `xor` the `xor-junction` category of the node table and a junction node of kind `and` the `and-junction` category.⟧

⟦s15|*Where* the transition names of a net are pairwise distinct, its place and transition names hold only ASCII characters, and no two different place names, nor two different transition names, become equal when each character outside `[A-Za-z0-9_]` is replaced by `_`, the mapper *shall* give no two nodes of the graph the same ID.⟧

⟦s16|AC1 covers the junctions of transitions whose name is not empty and holds only ASCII characters.⟧

**Acceptance Criteria:**
1. All junction IDs match the regex `j_[A-Za-z0-9_]+__(xor|and)_[0-9]+`.
2. Two consecutive exports of the same net produce byte-equal DOT.
3. Java, TypeScript, and Rust exports of the same net produce byte-equal DOT.

**Test derivation:** Export same net twice in same language; diff. Export same net across all three languages; diff."#
