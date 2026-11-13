<!-- Generated from lean/Libpetri/Spec/Text/Chapter/Ch09.lean and the requirement texts it lists, by lean/spec-tools/Render.lean. Do not edit: edit the Lean source, then run `lake env lean spec-tools/Render.lean` from lean/. -->
# 09 — Export

This document specifies graph export formats for visualization and formal analysis interchange.

---

## Graph Export

#### EXP-001: Graph Export Format

**Priority:** MUST
**Kind:** F

The engine MUST support exporting the net structure to at least one standard graph format suitable for visualization. The canonical format is DOT (Graphviz), a widely-supported, text-based format.

In this chapter the node of a place or a transition is the node that stands for it in the exported graph, whatever its DOT ID ([EXP-014]). A place that the net declares and on which no transition has an arc may have a node or none; a node for it is the intended end state.

The export *shall* draw exactly one node for each place on which some transition has an input, output, inhibitor, read or reset arc.

*Where* the transitions of a net have pairwise distinct names, the export *shall* draw exactly one node for each transition.

The export *shall* draw a place node only for a place that the net declares or on which some transition has an arc, and a transition node only for a transition of the net.

The export *shall* draw, for each input arc, inhibitor arc and read arc, an edge of the arc's type from the node of its place to the node of its transition.

*Where* the transitions of a net have pairwise distinct names, the export *shall* draw as many input, inhibitor and read edges from the node of a place to the node of a transition as the transition has arcs of that type on that place.

The export *shall* draw into each place that a transition's output spec names an edge from that transition or from one of its junctions, of type output or, where the transition also has a reset arc on that place, of the combined reset+output type of [EXP-013].

The export *shall* draw into each place on which a transition has a reset arc an edge from that transition or from one of its junctions, of type reset or, where the transition's output spec also names that place, of the combined reset+output type of [EXP-013].

**Acceptance Criteria:**
1. Export produces valid, parseable output in the chosen format.
2. All places and transitions in the net are represented.
3. All arcs (input, output, inhibitor, read, reset) are represented.

**Implementation notes:**
- Java: DOT (Graphviz) format
- TypeScript: DOT (Graphviz) format
- Rust: DOT (Graphviz) format

**Test derivation:** Build net with all arc types; export; verify output parses correctly.

---

#### EXP-002: Visual Semantics — Places

**Priority:** MUST
**Kind:** F

Places are rendered as distinct shapes from transitions:
- Places: circles, ellipses, or stadium-shaped nodes (following Petri net convention)
- Place names are displayed as labels

The mapper *shall* give every place node a place category, which is the place, start, end, environment or terminal row of the style table, and *shall* give no transition node and no junction node a place category (a transition node gets the transition category, see [EXP-003]).

The mapper *shall* draw every place node for a place of the net (one that the net declares or on which some transition has an arc), show the name of that place, as written and not sanitized, as the external label (`xlabel`) of the node, and give the node an empty label, so that nothing is drawn inside it.

**Acceptance Criteria:**
1. Places are visually distinguishable from transitions.
2. Place names are readable.

**Test derivation:** Export net; verify place nodes use correct shape syntax.

---

#### EXP-003: Visual Semantics — Transitions

**Priority:** MUST
**Kind:** F

Transitions are rendered as rectangles or bars (following Petri net convention). Transition names are displayed as labels.

The transition category is the `transition` row of the node table in `spec/petri-net-styles.json`; its shape is `box`, a rectangle, so the export draws rectangles and does not use bars. No place row, no junction row and not the `interface-port` row has that shape. The `sync-channel` row is also `box`; a place node never has it, since [EXP-002] draws every place node with a place row. Transitions and places are therefore told apart by this requirement together with [EXP-002]. The timing interval and the priority that may follow the name in a transition's label are given by [EXP-007].

The export *shall* draw a node for every transition of the net.

The export *shall* draw no node that stands for a transition the net does not have.

The export *shall* give a node the transition category exactly when the node stands for a transition.

The export *shall* label the node of a transition with a text that starts with the transition's name as written in the net.

*Where* the configuration hides the timing interval and the priority, the export *shall* label the node of a transition with the transition's name alone.

**Acceptance Criteria:**
1. Transitions are visually distinguishable from places.
2. Transition names are readable.

**Test derivation:** Export net; verify transition nodes use correct shape syntax.

---

#### EXP-004: Arc Rendering

**Priority:** MUST
**Kind:** F

Each arc type has a visually distinct rendering. Its colour, line style, arrowhead and pen width are those of the row its bullet names in the `edge` table of `spec/petri-net-styles.json`:
- **Input arc**: solid arrow from place to transition, row `input` (a correlated input of [EXP-018] takes row `match-input`)
- **Output arc**: solid arrow from transition, or from one of its junction nodes ([EXP-012]), to place, row `output`; the edge of a `ForwardInput` leaf is dashed and labelled with its source place ([EXP-012])
- **Inhibitor arc**: arrow with circle arrowhead (standard notation) from place to transition, without a label, row `inhibitor`
- **Read arc**: dashed arrow from place to transition, labelled `read`, row `read`
- **Reset arc**: bold arrow from transition to place, labelled `reset`, row `reset`; a reset arc into a place that a leaf of the output spec also ends in is drawn as the combined edge of [EXP-013]

The reset edge points from the transition to the place it empties. This is a drawing convention: the reset arc itself goes from the place to the transition ([CORE-034]).

Visually distinct means that any two edges of different types among these five differ in drawn direction, colour, line style or arrowhead. The combined edge of [EXP-013] has the style of the reset edge and differs from it only in its label.

The mapper *shall* draw each input arc as a solid edge of arc type `input` from its place to its transition, in the `match-input` row where [EXP-018] correlates its place and in the `input` row otherwise.

The mapper *shall* draw each output arc of a transition into a place that the transition does not reset as an edge of arc type `output` in the `output` row, from the transition or one of its junction nodes to the place.

Every edge of arc type `output` that the mapper draws *shall* run from a transition or one of its junction nodes to a place or to a junction node of that transition, in the `output` row.

An edge of arc type `output` *shall* be solid, except the edge of a `ForwardInput` leaf of its transition's output spec from place F to a place P that the transition does not reset, which is dashed, ends in P and is labelled `⟵F`, after another label and a space when it has one.

The mapper *shall* draw each inhibitor arc as a solid edge of arc type `inhibitor` from its place to its transition, in the `inhibitor` row and without a label.

The mapper *shall* draw each read arc as an edge of arc type `read` from its place to its transition, in the `read` row and labelled `read`.

*Where* no leaf of a transition's output spec ends in the place of one of its reset arcs, the mapper *shall* draw that reset arc as an undashed edge of arc type `reset` from the transition to the place, in the `reset` row and labelled `reset`.

Every edge of arc type `input`, `inhibitor`, `read` or `reset` that the mapper draws *shall* be the edge of one arc of that type, with the ends, row and line style the sentences above give it and the label they give it where they give one; an edge of arc type `reset` is the edge of a reset arc into a place that no leaf of its transition's output spec ends in.

**Acceptance Criteria:**
1. Each arc type is visually distinguishable.
2. Arc direction reflects flow (place→transition for input, transition→place for output).

**Test derivation:** Build net with all 5 arc types; export; verify each arc type has distinct rendering.

---

#### EXP-005: XOR Branch Labels

**Priority:** SHOULD
**Kind:** F

XOR output branches should be labeled to indicate the branching structure. Each branch of a XOR should be visually identifiable.

The mapper *shall* draw each `Xor` group with two or more children in an output spec as an `Xor` junction node with exactly one edge out of it for each child, in the order of the children.

The mapper *shall* draw the edges below the edge into a child of an `Xor` junction so that following them down reaches the places of that child's leaves, one path into a place for each leaf, and no other place.

The edge into a `Place`, `ForwardInput` or `Timeout` child of an `Xor` junction *shall* carry the label [EXP-012] gives it, and be dashed exactly when [EXP-012] draws it dashed.

*Where* [EXP-013] combines that edge into a reset place, the edge *shall* carry a label that is not empty in place of the one above.

**Acceptance Criteria:**
1. XOR branches have labels or visual grouping.
2. The viewer can identify which outputs belong to which XOR branch.

**Test derivation:** Net with XOR output; export; verify branches are labeled.

---

#### EXP-006: Cardinality Labels

**Priority:** SHOULD
**Kind:** F

Multi-token arcs (Exactly(n), All, AtLeast(m)) display count notation on the arc label:
- Exactly(n): label shows "×n"
- All: label shows "*"
- AtLeast(m): label shows "≥m"

The export *shall* give an input arc with cardinality `One` no cardinality label.

The export *shall* give an input arc with cardinality `Exactly(n)` the cardinality label `×n`.

The export *shall* give an input arc with cardinality `All` the cardinality label `*`.

The export *shall* give an input arc with cardinality `AtLeast(m)` the cardinality label `≥m`.

The export *shall* draw the cardinality label of an input arc on the edge of the arc.

**Acceptance Criteria:**
1. Non-One cardinality is displayed on the arc.
2. One cardinality has no cardinality label (default).

**Test derivation:** Net with Exactly(3) and AtLeast(5) inputs; export; verify labels show counts.

---

#### EXP-007: Export Configuration

**Priority:** SHOULD
**Kind:** F

The export supports configuration options:
- **Layout direction**: top-to-bottom, left-to-right, etc.
- **Show/hide timing**: toggle timing interval display on transitions
- **Show/hide priority**: toggle priority display on transitions

*Where* the configuration hides timing and priority, the export *shall* label a transition node with the transition's name alone.

*Where* the configuration shows timing and hides priority, the export *shall* label a transition node with the transition's name, a space and `[e, l]ms`, where e is `earliest()` and l is `latest()` of the transition's timing, in milliseconds and in decimal, and l is written `∞` when `hasDeadline()` is false ([TIME-001]).

*Where* the configuration shows priority and the transition's priority n is not 0, the export *shall* label the transition's node with the label it would have if the configuration hid priority, followed by a space and `prio=n`, with n in decimal.

*Where* a transition's priority is 0, the export *shall* label its node with the label it would have if the configuration hid priority.

The export *shall* lay out the drawing in the layout direction the configuration names.

The export *shall* draw the same graph, apart from its layout direction and the label drawn inside each transition node, under two configurations that differ only in the layout direction and the show options.

*Where* a configuration carries a show-types option, the export *shall* draw the same graph whichever value the option has.

The default configuration names the top-to-bottom layout direction and shows timing and priority.

**Acceptance Criteria:**
1. Configuration controls what information is displayed.
2. Default configuration shows all information.
3. Minimal configuration hides timing and priority.

**Test derivation:** Export with default config; export with minimal config; verify difference.

---

#### EXP-008: Styling

**Priority:** SHOULD
**Kind:** F

The export applies visual styling to distinguish node categories:
- **Start places** (no incoming arcs): highlighted (e.g., green)
- **End places** (no outgoing arcs): highlighted (e.g., blue)
- **Transitions**: distinct color (e.g., yellow)

Each place category names a row of the node table in `spec/petri-net-styles.json`: terminal, environment, start, end, or the regular `place` row. In this section an ordinary place is a place that is neither a terminal place ([EXEC-042]) nor an environment place ([ENV-001]). In the bullets above, an incoming arc of a place is an output arc on it (some transition's output spec names it), and an input arc on it is an outgoing arc; inhibitor arcs and reset arcs are neither, and whether a read arc is an outgoing arc is left open in this version (see the last two sentences below). The category of a place is the one the export's mapper gives it; a documentation generator that afterwards redraws the interface ports of a subnet body with the `interface-port` row ([EXP-011]) is outside this requirement.

The export *shall* give a terminal place the terminal category.

The export *shall* give an environment place that is not a terminal place the environment category.

The export *shall* give an ordinary place the start category exactly when no transition's output spec names it.

The export *shall* give the end category to an ordinary place that some transition's output spec names and on which no transition has an input arc or a read arc.

The export *shall not* give the end category to an ordinary place on which some transition has an input arc.

The export *shall* give an ordinary place the start, the end or the regular place category.

An ordinary place that some transition's output spec names, and on which some transition has a read arc and none has an input arc, may have the end or the regular place category in this version; the regular place category is the intended one.

The export *shall* give the same category to all ordinary places, in one net or in different nets, that some transition's output spec names, on which some transition has a read arc and on which no transition has an input arc.

**Acceptance Criteria:**
1. Start places are visually distinct from other places.
2. End places are visually distinct from other places.

**Test derivation:** Net with start and end places; export; verify styling applied.

---

## Formal Analysis Export

#### EXP-010: Formal Interchange Format

**Priority:** MAY
**Kind:** Q

The engine MAY support exporting to formal analysis interchange formats suitable for external tools (e.g., PNML for Petri net tools, STTT format for Sirio timing analysis).

**Acceptance Criteria:**
1. Export produces valid output in the target format.
2. Places, transitions, arcs, and timing are represented.

**Implementation notes:**
- Not yet implemented in any language

**Test derivation:** Export to interchange format; validate against schema.

---

#### EXP-011: Compile-Time Diagram Generation

**Priority:** MAY
**Kind:** Q

The engine MAY support generating diagrams from net structure annotations at compile time, embedding them in documentation or source comments.

**Acceptance Criteria:**
1. Net structure annotations are processed at compile time.
2. Diagrams are generated without running the net.

**Implementation notes:**
- Java: `@NetStructure` annotation processed by `@petrinet` Javadoc taglet to embed DOT in `data-dot` attributes
- TypeScript: `@petrinet` TypeDoc plugin resolves net definitions and embeds DOT in `data-dot` attributes
- Rust: `libpetri-docgen` build-dependency crate emits DOT-in-HTML via `SvgGenerator` / `generate_svg()`

All three generators emit self-contained HTML pages that inline the canonical `LibpetriViewer` IIFE bundle (with `@viz-js/viz` Graphviz WASM baked in). DOT → SVG conversion happens client-side at view time. No external tooling (`dot`, `node`, etc.) is required on the doc-generation host.

**Test derivation:** Annotated net structure; build project; verify diagram generated.

---

## Visualization Rules — junctions and combined edges

The following requirements specify the *visualization* layer that the mapper applies on top of the raw arc set, so XOR/AND fork structure and reset+output coupling are visible to a reader. They are mandatory for all language implementations so Java/TS/Rust mappers (and their doc generators) produce visually identical diagrams.

#### EXP-012: XOR/AND Junction Nodes

**Priority:** MUST
**Kind:** F

For every `Out.Xor` or `Out.And` group with **two or more children**, the mapper MUST insert a synthetic *junction node* between the transition and the children. A group with fewer than two children MUST NOT produce a junction (it is a pass-through).

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

The mapper *shall* draw one junction node for each `And` or `Xor` group of an output spec that has two or more children, of the group's kind, and no other junction node.

*Where* an `And` or `Xor` group has fewer than two children, the mapper *shall* draw its child, if it has one, from the group's parent and with the label the edge into the group would carry.

The mapper *shall* draw exactly one solid output edge into each junction node, into the place of each `Place` leaf and into the target place of each `ForwardInput` leaf, from the nearest junction node above it, or from the transition when there is none, and no other edge for the output spec.

The edge into a child of an `Xor` junction *shall* carry the child's branch label: the place name of a `Place` child, `⏱<n>ms` for a `Timeout` child of n ms, and no label for an `And` or `Xor` child.

The edge into a child of an `And` junction, and the edge from the transition into the output spec, *shall* carry no label of their own.

*Where* a `Timeout` node of n ms is in an output spec, the edge drawn into its child *shall* carry `⏱<n>ms` in place of the label the edge into the `Timeout` would carry.

*Where* a leaf is a `ForwardInput` from place F to place P, the mapper *shall* draw its edge as the edge of a `Place` leaf for P at the same position, dashed instead of solid, and with `⟵F` after its label and a space, or as its only label when it has none.

*Where* [EXP-013] combines a leaf edge into a reset place, that edge *shall* take the arc type, label and style [EXP-013] gives it in place of the ones above.

**Acceptance Criteria:**
1. Net with `XOR(P_a, P_b)` exports one diamond junction labelled `"✕"` and two edges junction→{P_a, P_b}.
2. Net with `AND(P_c, P_d)` exports one diamond junction labelled `"✚"` and two edges junction→{P_c, P_d}.
3. Net with `AND(P_a)` (single child) exports a direct edge transition→P_a, no junction.
4. Nested groups (e.g. `XOR(AND(P_a, P_b), P_c)`) produce nested junctions.
5. Java, TypeScript, and Rust mappers produce byte-identical junction nodes and edges for the same input net (modulo deterministic ordering already in place).

**Test derivation:** For each language, build a net with `XOR(A, B)`, `AND(C, D)`, `AND(A)`, and a nested case; export; assert junction node count, shape, and edge wiring.

---

#### EXP-013: Combined reset+output Edge

**Priority:** MUST
**Kind:** F

When a transition has both an output arc and a reset arc to the same place P, the mapper MUST draw every output edge to P as a combined edge, styled as the reset-output category (color `#fd7e14`, style `bold`, penwidth `2.0`, arrowhead `normal`) and labelled `"reset+out"`. The standalone output edge to P MUST be suppressed in this case. The standalone reset edge to P MUST be suppressed in this case. When the output spec names P in more than one leaf (for example `Xor(P, And(P, Q))`), each such leaf gives one combined edge.

If a transition resets place P but does not output to P, the standalone reset edge with label `"reset"` MUST still be emitted (existing behavior preserved).

If a transition outputs to P but does not reset P, the standalone output edge MUST be emitted (existing behavior preserved).

The combination applies regardless of whether the output edge originates at the transition directly or at an XOR/AND junction underneath the transition (per EXP-012). When the output is a leaf under a junction, the *junction → P* edge is the one that becomes reset-styled with the `"reset+out"` label.

The combined edge carries the label `"reset+out"` alone and is never dashed: it replaces the branch label, the timeout label and the `ForwardInput` label and dash the leaf edge would carry under [EXP-012].

*Where* the transitions of a net have pairwise distinct names and a transition of the net resets place P, each edge the mapper draws for a `Place` leaf for P or a `ForwardInput` leaf into P of its output spec *shall* be an undashed edge of arc type reset-output, in the reset-output style and labelled `reset+out`, whether it starts at the transition or at a junction node.

*Where* the transitions of a net have pairwise distinct names, a transition of the net resets place P and its output spec has a `Place` leaf for P or a `ForwardInput` leaf into P, the mapper *shall* draw no reset edge from that transition to P.

*Where* the transitions of a net have pairwise distinct names, a transition of the net resets place P and its output spec has no `Place` leaf for P and no `ForwardInput` leaf into P, the mapper *shall* draw one undashed reset edge from the transition to P for each reset arc of the transition on P, in the reset style and labelled `reset`.

*Where* the transitions of a net have pairwise distinct names and a transition of the net does not reset place P, each edge the mapper draws for a `Place` leaf for P or a `ForwardInput` leaf into P of its output spec *shall* be of arc type output, in the output style.

*Where* the transitions of a net have pairwise distinct names, for each transition and place P the mapper *shall* draw exactly as many edges of arc type output or reset-output from the transition and its junction nodes into P as the transition's output spec has `Place` leaves for P and `ForwardInput` leaves into P.

The mapper *shall* draw every edge of arc type reset-output from a transition or one of its junction nodes into a place that transition resets.

**Acceptance Criteria:**
1. Transition with `Out.Place(P)` and `reset(P)` exports one orange-bold edge T→P labelled `"reset+out"`. No black output edge to P. No standalone reset edge labelled `"reset"`.
2. Transition with `Out.Place(P)` and no reset exports one black output edge.
3. Transition with reset(P) and no output to P exports one orange-bold edge labelled `"reset"`.
4. Transition with `Out.Xor(P, Q)` and `reset(P)` exports a junction; junction→P is reset-styled with label `"reset+out"`; junction→Q is plain output style.
5. Java, TypeScript, and Rust mappers produce byte-identical edges for the same input.

**Test derivation:** Build nets covering each acceptance case; assert exactly the expected edges (count, color, label) per language.

**Worked DOT:** for a transition `Try` with `Out.Xor(P_Ok, P_Fail)` and `reset(P_Fail)` plus a transition `RefreshCache` with `Out.Place(P_Cache)` and `reset(P_Cache)`:

```
t_RefreshCache -> p_Cache       [color="#fd7e14", style="bold", arrowhead="normal", label="reset+out", penwidth=2];
t_Try -> j_Try__xor_0           [color="#333333", style="solid", arrowhead="normal"];
j_Try__xor_0 -> p_Ok            [color="#333333", style="solid", arrowhead="normal", label="Ok"];
j_Try__xor_0 -> p_Fail          [color="#fd7e14", style="bold", arrowhead="normal", label="reset+out", penwidth=2];
```

Note that the through-junction case (line 4) is identical in style to the direct case (line 1); only the source node differs.

---

#### EXP-014: Junction ID Format and Layout Stability

**Priority:** MUST
**Kind:** F

Synthetic junction nodes MUST use IDs of the form `j_<transitionSanitized>__<kind>_<idx>`, where:
- `transitionSanitized` is the transition's name with non-`[A-Za-z0-9_]` characters replaced by `_` (the same `sanitize` function used for place and transition IDs).
- `<kind>` is `xor` or `and`.
- `<idx>` is a non-negative integer. Junctions in a single transition's `Out` tree are numbered in depth-first pre-order, with the counter starting at `0` and incrementing once per emitted junction. Single-child XOR/AND groups collapse (per EXP-012) and consume no counter slot. Example: `t_Nested` with output `AND(XOR(a,b), XOR(c,d))` produces three junctions in the order `j_Nested__and_0`, `j_Nested__xor_1`, `j_Nested__xor_2`.

The flat counter (rather than a hierarchical path-encoded index) keeps junction IDs short and human-scannable while still being uniquely determined by the depth-first traversal of the `Out` tree, which is what cross-language byte-equality requires.

This guarantees:
1. Junction IDs do not collide with place IDs (`p_…`) or transition IDs (`t_…`).
2. Repeated exports of the same net produce byte-identical DOT (required for stable Graphviz `dot` layouts across reloads in debug-ui and reproducible doc-generated SVGs).
3. Cross-language byte-equality of DOT output for the same input net.

*Where* a node's name (the place's, the transition's, or for a junction its transition's) holds only ASCII characters, the mapper *shall* give the node the ID `p_<s>`, `t_<s>` or `j_<s>__<kind>_<idx>` according to what it stands for, with `<s>` that name with each character outside `[A-Za-z0-9_]` replaced by `_`, `<kind>` the kind of the junction and `<idx>` its index written in decimal without leading zeros.

The ID of a node whose name holds a character outside ASCII is implementation-defined, within the rule of the next sentence.

The mapper *shall* give no junction node the ID of a place node or a transition node, whatever the names.

*Where* the transition names of a net are pairwise distinct, the mapper *shall* draw for each transition one junction node for each group with two or more children in its output spec, of the kind of that group, and no other junction node for the transition.

*Where* the transition names of a net are pairwise distinct, the mapper *shall* give the junction node of a group with two or more children the index of that group in the depth-first pre-order of such groups in the transition's output spec, counting from 0, with one counter for both kinds.

*Where* the transition names of a net are pairwise distinct, the mapper *shall* draw as the output edges of a transition, compared by their ends, exactly the edges [EXP-012] draws for its output spec, each as often as [EXP-012] draws it, with each junction numbered by the index of its group.

The mapper *shall* draw no edge that starts or ends at a junction node it does not draw.

The mapper *shall* draw no junction node for a transition the net does not have.

The mapper *shall* give a junction node of kind `xor` the `xor-junction` category of the node table and a junction node of kind `and` the `and-junction` category.

*Where* the transition names of a net are pairwise distinct, its place and transition names hold only ASCII characters, and no two different place names, nor two different transition names, become equal when each character outside `[A-Za-z0-9_]` is replaced by `_`, the mapper *shall* give no two nodes of the graph the same ID.

AC1 covers the junctions of transitions whose name is not empty and holds only ASCII characters.

**Acceptance Criteria:**
1. All junction IDs match the regex `j_[A-Za-z0-9_]+__(xor|and)_[0-9]+`.
2. Two consecutive exports of the same net produce byte-equal DOT.
3. Java, TypeScript, and Rust exports of the same net produce byte-equal DOT.

**Test derivation:** Export same net twice in same language; diff. Export same net across all three languages; diff.

---

#### EXP-015: Doc Generator Parity

**Priority:** MUST
**Kind:** Q

The compile-time diagram generators (EXP-011) MUST embed DOT sources reflecting the visualization rules above. Specifically, `mvn javadoc:javadoc`, `cargo doc`, and the TypeDoc plugin MUST emit DOT that includes junction nodes (per EXP-012) and combined reset+output edges (per EXP-013) for any net that uses XOR/AND outputs or reset+output coupling. Rendering of that DOT into SVG happens client-side at view time via the bundled `LibpetriViewer` IIFE (per EXP-011).

This is achieved by having all three doc generators delegate to their language's mapper; no doc-generator-specific code is required.

**Acceptance Criteria:**
1. Building Java docs for a net with `XOR(A, B)` includes a `data-dot` attribute whose DOT source declares a diamond-shaped junction node (the XOR junction).
2. Building Rust docs for the same net produces a DOT source that, modulo whitespace, matches the Java DOT.
3. Building TypeScript docs for the same net produces a DOT source that matches.

**Depends on:** [EXP-011], [EXP-012], [EXP-013]
**Test derivation:** Build docs in each language for a small net with `XOR(A, B)` and `Out.Place(P) + reset(P)`; extract the embedded DOT (the `data-dot` attribute) and assert content via grep for the expected shape/color signatures.

---

#### EXP-016: Subnet Instance Cluster Subgraphs

**Priority:** SHOULD
**Kind:** F

DOT export of a net produced by modular composition (per [MOD-020]) SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping each subnet's nodes. The cluster key is drawn from one of two sources, per [MOD-040]:

- **Subnet-membership metadata** ([MOD-026]) carried by a directly-composed net — a node mapped to subnet `S` clusters under `cluster_<sanitize(S)>`; a shared (multi-subnet) place has no entry and is not grouped by metadata.
- **Instance-prefix detection** — a node whose name begins with `<prefix>/` (the separator established by [MOD-010]) clusters under `cluster_<sanitize(prefix)>`. Nested instance prefixes (per [MOD-013]) MUST produce nested cluster subgraphs.

When the net carries membership metadata the exporter SHOULD prefer it and fall back to instance-prefix detection for any node without an entry, so direct and instance composition coexist. The cluster source MAY be caller-selectable (metadata-only, prefix-only, or no clustering); the default SHOULD be metadata-when-present.

The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`). The cluster `label` attribute SHOULD carry the original (un-sanitized) key string for human readability.

This requirement does NOT alter the styling, junction, or arc rendering rules of EXP-002..EXP-015; it adds grouping structure only. A net with neither composed instances nor membership metadata (no `/` in any node name) MUST produce no cluster subgraphs.

The SHOULD priority is whether an exporter draws cluster subgraphs at all. For an exporter that draws them, every MAY, SHOULD and MUST sentence of this requirement reads as *shall*: it lets the caller select each cluster source named above, takes the default source when the caller selects none, and follows the sentences below.

Under the default cluster source the cluster key of a place or a transition is its membership entry when it has one and otherwise its instance prefix; under the metadata-only source it is the membership entry alone, under the prefix-only source the instance prefix alone, and under no clustering there is none. The instance prefix of a name is the part before its last `/`; a name without `/`, or whose only `/` is its first character, has none. A junction node has the cluster key of its transition. A node without a cluster key is a top-level node. A `/`-prefix of a key is the non-empty beginning of the key up to, and not including, one of its `/` characters.

These sentences cover nets whose place names and transition names are ASCII, in which no two place names and no two transition names become equal under the sanitization of [EXP-014], and in which every cluster key of a place or transition name is ASCII, non-empty and has no empty `/`-segment: it neither starts nor ends with `/` and holds no `//`. On other nets the clustering, and whether it changes the nodes and edges drawn, is implementation-defined.

Known limit: the Java, TypeScript and Rust mappers look a node's cluster key up by its DOT ID, so two names that sanitize to one ID, such as `b1/x` and `b1_x`, become one node in one cluster. The name assumption above keeps such nets out of these sentences.

The mapper *shall* make each node that has a cluster key a direct member of the cluster of that key and of no other cluster, and a top-level node a member of no cluster.

The mapper *shall* list as a member of a cluster only a node it draws, and, on a net whose transition names are pairwise distinct, list each such node at most once.

The mapper *shall* draw exactly one cluster for each cluster key of a drawn node and for each `/`-prefix of such a key, and no other cluster.

The mapper *shall* nest each cluster directly in the cluster whose key is the part of its own key before the last `/`, and draw a cluster whose key has no `/` at the top level.

The mapper *shall* give the cluster of key K the ID `cluster_` followed by K with each character outside `[A-Za-z0-9_]` replaced by `_`, and the label K.

The mapper *shall* draw, in any order, the same nodes, and the same edges other than the ghost edges of [EXP-017], as it draws for the same net and configuration under no clustering.

**Acceptance Criteria:**
1. A net composed from two top-level instances with prefixes `b1` and `b2` exports DOT containing `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by `/`, and the junction nodes of those transitions.
3. Nested instances produce nested cluster subgraphs (e.g., `cluster_outer` containing `cluster_outer_inner`).
4. A net with no `/` in any node name and no membership metadata produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` and are deterministic across repeated exports.
6. Java, TypeScript, and Rust mappers produce byte-identical cluster blocks (subject to MOD support in each language) for the same composed input.
7. A directly-composed net carrying [MOD-026] metadata exports one `subgraph cluster_<subnetName>` block per subnet, with each subnet's private nodes inside and shared places whose names carry no instance prefix at the top level.

**Depends on:** [EXP-001], [EXP-014], [MOD-010], [MOD-026], [MOD-040]
**Test derivation:** Compose two instances with prefixes `b1` and `b2`; export DOT; assert cluster blocks present, members correct, IDs sanitized. Compose nested instances; assert nested cluster subgraphs. Direct-compose two subnets; assert one `cluster_<subnetName>` block per subnet.

---

#### EXP-017: Compound Cluster Layout Hints

**Priority:** SHOULD
**Kind:** F

DOT export SHOULD set `compound=true` at the digraph level unconditionally so Graphviz honours `lhead` and `ltail` attributes on edges that cross cluster boundaries. This is a no-op for flat (uncomposed) nets but keeps the digraph header uniform across all exports.

In this requirement the cluster key of a node is its key under [EXP-016], so a node with a key lies in the deepest cluster of that key, and an orphan is a node with no key, which is drawn at the top level. An edge is an edge of the exported graph other than a ghost edge, of any arc type, in the direction it is drawn, and either end of it may be a junction node ([EXP-012]). A bridge for an ordered pair of distinct keys (X, Y) is an orphan `o` together with an edge `a → o` from a node `a` with key X and an edge `o → b` to a node `b` with key Y, so one orphan with several such pairs of edges gives several bridges. A cluster and a cluster nested in it, such as `outer` and `outer/inner`, have two distinct keys, so an orphan between them bridges them.

For every ordered pair of distinct cluster keys (X, Y) that at least one bridge connects, the exporter MUST emit exactly one invisible ghost edge with:

- `style = invis` (no visible artifact; pure layout constraint)
- `arrowhead = none`
- `ltail = "cluster_" + sanitize(X)` (matches the cluster id defined by [EXP-016])
- `lhead = "cluster_" + sanitize(Y)`

The ghost edge's source and target node ids MUST be the `a` and the `b` of the first bridge for (X, Y) in this scan order: the nodes in the order they are drawn, for each orphan the edges into it in the order they are drawn, and for each of those the edges out of it in the order they are drawn. Graphviz then has a real cluster-to-cluster connection to constrain layout, while the visible flow still passes through the orphan via the original real edges.

Because every drawn edge counts, a reset edge into an orphan place and a read edge out of it bridge two clusters although no token moves between them. An orphan transition whose output spec has a junction bridges nothing through that junction, since the junction is itself an orphan.

Multiple orphans bridging the same ordered cluster pair `(X, Y)` collapse to one ghost edge (dedup by ordered pair). The reverse direction `(Y, X)` is a separate ghost edge when its own 1-hop path exists. Orphan paths that fall entirely inside a single cluster (`X == Y`) or that only touch one clustered neighbour MUST NOT produce a ghost edge.

This requirement does NOT change [EXP-016] cluster membership, the visible edge set, or styling rules. It only adds the `compound=true` graph attribute and the synthesized ghost edges.

Apart from the `compound` attribute, these sentences cover the nets that the sentences of [EXP-016] cover; on other nets the ghost edges, and whether clustering changes the other edges drawn, are implementation-defined.

The exporter *shall* set the graph attribute `compound` to true in every export.

*Where* a bridge connects an ordered pair of distinct cluster keys (X, Y), an exporter that clusters *shall* draw a ghost edge from the `a` to the `b` of the first bridge for (X, Y), with `ltail` the cluster ID of X and `lhead` the cluster ID of Y.

Each ghost edge that an exporter that clusters draws *shall* run from the `a` to the `b` of the first bridge for some ordered pair of distinct cluster keys (X, Y), with `ltail` the cluster ID of X and `lhead` the cluster ID of Y.

An exporter that clusters *shall* draw at most one ghost edge for each ordered pair of cluster keys.

The exporter *shall* draw the same edges other than ghost edges as it draws for the same net with no clustering.

**Acceptance Criteria:**
1. Every DOT export contains `compound="true"` as a top-level graph attribute.
2. A net where `cluster_left` and `cluster_right` are bridged by a single orphan transition produces exactly one ghost edge with `style=invis`, `arrowhead=none`, `ltail="cluster_left"`, `lhead="cluster_right"`.
3. Three orphans bridging the same `(left, right)` pair still produce exactly one ghost edge (dedup by ordered pair).
4. Bidirectional bridging (`left → o1 → right` and `right → o2 → left`) produces two ghost edges, one per direction.
5. An orphan with `X → o → X` (same cluster on both sides) produces no ghost edge.
6. An orphan with only one clustered neighbour produces no ghost edge.
7. A flat net (no instance prefixes) produces no ghost edges but still emits `compound="true"`.
8. Anchor node selection is deterministic and matches across Java, TypeScript, and Rust exporters byte-for-byte for the same composed input.

**Depends on:** [EXP-012], [EXP-014], [EXP-016]
**Test derivation:** Build a composed net with two instances and an orphan transition between them; export DOT in each language; assert one `style="invis"` edge with matching `ltail`/`lhead`. Add bidirectional and multi-orphan variants. Verify `compound="true"` on a flat net.

---

#### EXP-018: ν-Match Edge Decoration

**Priority:** SHOULD
**Kind:** F

When a transition declares a ν-net join correlation ([NU-020]), each **input
edge** to a correlated place is decorated to mark it as a name-matched input:

- **Color** `#0d9488` (teal, the `match-input` edge style in
  `spec/petri-net-styles.json`), distinguishing it from a plain input edge.
- **Label** prefixed with the bound-name variable `⟨n⟩` (U+27E8 `n` U+27E9). When
  the input also carries a cardinality label ([EXP-006]), the two are joined with
  a single space: `⟨n⟩ ×2`, `⟨n⟩ *`, `⟨n⟩ ≥3`. A correlated `One` input shows
  `⟨n⟩` alone.

Non-correlated inputs of the same transition are unaffected. The decoration is a
mapper concern: it is emitted into the DOT by every exporter, so the canonical
viewer and all three doc generators render it identically with no viewer change.

The export *shall* draw each input arc of a transition as an edge of arc type input from the arc's place to the transition, whether or not the transition correlates the place.

*Where* the match specification of a transition ([NU-020]) correlates the place of one of its input arcs, the export *shall* draw the edge of that arc with the `match-input` style row and label it `⟨n⟩` if the arc's cardinality is `One`, and otherwise `⟨n⟩`, one space and the arc's cardinality label ([EXP-006]).

*Where* a transition does not correlate the place of one of its input arcs, the export *shall* draw the edge of that arc with the `input` style row and give it the arc's cardinality label alone, or no label if the cardinality is `One`.

Apart from ghost edges ([EXP-017]), the export *shall* draw only the input edges of correlated places with the `match-input` style row.

**Acceptance Criteria:**
1. An input edge to a correlated place has color `#0d9488` and a label beginning
   with `⟨n⟩`.
2. A non-correlated input edge on the same transition keeps the default color and
   no `⟨n⟩` prefix.
3. The label combines with cardinality as `⟨n⟩ ×n` / `⟨n⟩ *` / `⟨n⟩ ≥m`.
4. The emitted DOT for a ν-net is byte-identical across the Java, TypeScript, and
   Rust exporters.

**Depends on:** [EXP-006], [EXP-017], [NU-020]
**Test derivation:** Build a join with `match` correlating two `one` inputs;
export; verify both correlated edges are teal and labeled `⟨n⟩`, and a third
non-correlated input is unchanged.
