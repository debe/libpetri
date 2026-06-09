# 09 — Export

This document specifies graph export formats for visualization and formal analysis interchange.

---

## Graph Export

#### EXP-001: Graph Export Format

**Priority:** MUST

The engine MUST support exporting the net structure to at least one standard graph format suitable for visualization. The canonical format is DOT (Graphviz), a widely-supported, text-based format.

**Acceptance Criteria:**
1. Export produces valid, parseable output in the chosen format.
2. All places and transitions in the net are represented.
3. All arcs (input, output, inhibitor, read, reset) are represented.

**Implementation notes:**
- Java: DOT (Graphviz) format
- TypeScript: DOT (Graphviz) format
- Rust: Not yet implemented

**Test derivation:** Build net with all arc types; export; verify output parses correctly.

---

#### EXP-002: Visual Semantics — Places

**Priority:** MUST

Places are rendered as distinct shapes from transitions:
- Places: circles, ellipses, or stadium-shaped nodes (following Petri net convention)
- Place names are displayed as labels

**Acceptance Criteria:**
1. Places are visually distinguishable from transitions.
2. Place names are readable.

**Test derivation:** Export net; verify place nodes use correct shape syntax.

---

#### EXP-003: Visual Semantics — Transitions

**Priority:** MUST

Transitions are rendered as rectangles or bars (following Petri net convention). Transition names are displayed as labels.

**Acceptance Criteria:**
1. Transitions are visually distinguishable from places.
2. Transition names are readable.

**Test derivation:** Export net; verify transition nodes use correct shape syntax.

---

#### EXP-004: Arc Rendering

**Priority:** MUST

Each arc type has a visually distinct rendering:
- **Input arc**: solid arrow from place to transition
- **Output arc**: solid arrow from transition to place
- **Inhibitor arc**: arrow with circle arrowhead (standard notation)
- **Read arc**: dashed arrow or bidirectional arrow (test arc notation)
- **Reset arc**: double-line arrow or distinctive marking

**Acceptance Criteria:**
1. Each arc type is visually distinguishable.
2. Arc direction reflects flow (place→transition for input, transition→place for output).

**Test derivation:** Build net with all 5 arc types; export; verify each arc type has distinct rendering.

---

#### EXP-005: XOR Branch Labels

**Priority:** SHOULD

XOR output branches should be labeled to indicate the branching structure. Each branch of a XOR should be visually identifiable.

**Acceptance Criteria:**
1. XOR branches have labels or visual grouping.
2. The viewer can identify which outputs belong to which XOR branch.

**Test derivation:** Net with XOR output; export; verify branches are labeled.

---

#### EXP-006: Cardinality Labels

**Priority:** SHOULD

Multi-token arcs (Exactly(n), All, AtLeast(m)) display count notation on the arc label:
- Exactly(n): label shows "×n" or "n"
- All: label shows "*" or "all"
- AtLeast(m): label shows "≥m"

**Acceptance Criteria:**
1. Non-One cardinality is displayed on the arc.
2. One cardinality has no label (default).

**Test derivation:** Net with Exactly(3) and AtLeast(5) inputs; export; verify labels show counts.

---

#### EXP-007: Export Configuration

**Priority:** SHOULD

The export supports configuration options:
- **Layout direction**: top-to-bottom, left-to-right, etc.
- **Show/hide types**: toggle token type annotations
- **Show/hide timing**: toggle timing interval display on transitions
- **Show/hide priority**: toggle priority display on transitions

**Acceptance Criteria:**
1. Configuration controls what information is displayed.
2. Default configuration shows all information.
3. Minimal configuration hides types, timing, and priority.

**Test derivation:** Export with default config; export with minimal config; verify difference.

---

#### EXP-008: Styling

**Priority:** SHOULD

The export applies visual styling to distinguish node categories:
- **Start places** (no incoming arcs): highlighted (e.g., green)
- **End places** (no outgoing arcs): highlighted (e.g., blue)
- **Transitions**: distinct color (e.g., yellow)

**Acceptance Criteria:**
1. Start places are visually distinct from other places.
2. End places are visually distinct from other places.

**Test derivation:** Net with start and end places; export; verify styling applied.

---

## Formal Analysis Export

#### EXP-010: Formal Interchange Format

**Priority:** MAY

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

For every `Out.Xor` or `Out.And` group with **two or more children**, the mapper MUST insert a synthetic *junction node* between the transition and the children. Single-child XOR/AND groups MUST NOT produce a junction (they are semantically pass-through).

**Junction node attributes** (gateway convention — diamond + single heavy glyph):
- **XOR junction**: shape `diamond`, fill `#FFFFFF`, stroke `#333333`, penwidth `1.0`, width `0.3`, height `0.3`, label `"✕"` (U+2715 Multiplication X), fontsize `14`, fixedsize `true`. Style category `xor-junction`.
- **AND junction**: shape `diamond`, fill `#FFFFFF`, stroke `#333333`, penwidth `1.0`, width `0.3`, height `0.3`, label `"✚"` (U+271A Heavy Greek Cross), fontsize `14`, fixedsize `true`. Style category `and-junction`.

The two kinds share a shape and color family; the inline heavy glyph (`✕` for exclusive choice, `✚` for parallel split) is the discriminator. Heavy dingbat variants are used (instead of the lightweight `×` U+00D7 / `+` U+002B) so the symbol stays legible at the small junction size where the diamonds read as scaffolding rather than first-class entities.

**Edge routing:**
- Edge `transition → junction`: output style, no label (or the timeout label `⏱<n>ms` if the group is wrapped in `Out.Timeout`).
- Edge `junction → child` for an XOR junction: output style, label = the inferred branch label (place name for `Place`, target name for `ForwardInput`, `⏱<n>ms` for `Timeout`, or none if the child is itself a junction).
- Edge `junction → child` for an AND junction: output style, no label.

**Acceptance Criteria:**
1. Net with `XOR(P_a, P_b)` exports one diamond junction labelled `"✕"` and two edges junction→{P_a, P_b}.
2. Net with `AND(P_c, P_d)` exports one diamond junction labelled `"✚"` and two edges junction→{P_c, P_d}.
3. Net with `XOR(P_a)` (single child) exports a direct edge transition→P_a, no junction.
4. Nested groups (e.g. `XOR(AND(P_a, P_b), P_c)`) produce nested junctions.
5. Java, TypeScript, and Rust mappers produce byte-identical junction nodes and edges for the same input net (modulo deterministic ordering already in place).

**Test derivation:** For each language, build a net with `XOR(A, B)`, `AND(C, D)`, `XOR(A)`, and a nested case; export; assert junction node count, shape, and edge wiring.

---

#### EXP-013: Combined reset+output Edge

**Priority:** MUST

When a transition has both an output arc and a reset arc to the same place P, the mapper MUST emit **exactly one** edge to P, styled as the reset-output category (color `#fd7e14`, style `bold`, penwidth `2.0`, arrowhead `normal`) and labelled `"reset+out"`. The standalone output edge to P MUST be suppressed in this case. The standalone reset edge to P MUST be suppressed in this case.

If a transition resets place P but does not output to P, the standalone reset edge with label `"reset"` MUST still be emitted (existing behavior preserved).

If a transition outputs to P but does not reset P, the standalone output edge MUST be emitted (existing behavior preserved).

The combination applies regardless of whether the output edge originates at the transition directly or at an XOR/AND junction underneath the transition (per EXP-012). When the output is a leaf under a junction, the *junction → P* edge is the one that becomes reset-styled with the `"reset+out"` label.

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

Synthetic junction nodes MUST use IDs of the form `j_<transitionSanitized>__<kind>_<idx>`, where:
- `transitionSanitized` is the transition's name with non-`[A-Za-z0-9_]` characters replaced by `_` (the same `sanitize` function used for place and transition IDs).
- `<kind>` is `xor` or `and`.
- `<idx>` is a non-negative integer. Junctions in a single transition's `Out` tree are numbered in depth-first pre-order, with the counter starting at `0` and incrementing once per emitted junction. Single-child XOR/AND groups collapse (per EXP-012) and consume no counter slot. Example: `t_Nested` with output `AND(XOR(a,b), XOR(c,d))` produces three junctions in the order `j_Nested__and_0`, `j_Nested__xor_1`, `j_Nested__xor_2`.

The flat counter (rather than a hierarchical path-encoded index) keeps junction IDs short and human-scannable while still being uniquely determined by the depth-first traversal of the `Out` tree, which is what cross-language byte-equality requires.

This guarantees:
1. Junction IDs do not collide with place IDs (`p_…`) or transition IDs (`t_…`).
2. Repeated exports of the same net produce byte-identical DOT (required for stable Graphviz `dot` layouts across reloads in debug-ui and reproducible doc-generated SVGs).
3. Cross-language byte-equality of DOT output for the same input net.

**Acceptance Criteria:**
1. All junction IDs match the regex `j_[A-Za-z0-9_]+__(xor|and)_[0-9]+`.
2. Two consecutive exports of the same net produce byte-equal DOT.
3. Java, TypeScript, and Rust exports of the same net produce byte-equal DOT.

**Test derivation:** Export same net twice in same language; diff. Export same net across all three languages; diff.

---

#### EXP-015: Doc Generator Parity

**Priority:** MUST

The compile-time diagram generators (EXP-011) MUST embed DOT sources reflecting the visualization rules above. Specifically, `mvn javadoc:javadoc`, `cargo doc`, and the TypeDoc plugin MUST emit DOT that includes junction nodes (per EXP-012) and combined reset+output edges (per EXP-013) for any net that uses XOR/AND outputs or reset+output coupling. Rendering of that DOT into SVG happens client-side at view time via the bundled `LibpetriViewer` IIFE (per EXP-011).

This is achieved by having all three doc generators delegate to their language's mapper; no doc-generator-specific code is required.

**Acceptance Criteria:**
1. Building Java docs for a net with `XOR(A, B)` includes a `data-dot` attribute whose DOT source declares a diamond-shaped junction node (the XOR junction).
2. Building Rust docs for the same net produces a DOT source that, modulo whitespace, matches the Java DOT.
3. Building TypeScript docs for the same net produces a DOT source that matches.

**Test derivation:** Build docs in each language for a small net with `XOR(A, B)` and `Out.Place(P) + reset(P)`; extract the embedded DOT (the `data-dot` attribute) and assert content via grep for the expected shape/color signatures.

---

#### EXP-016: Subnet Instance Cluster Subgraphs

**Priority:** SHOULD

DOT export of a net produced by modular composition (per [MOD-020]) SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping each subnet's nodes. The cluster key is drawn from one of two sources, per [MOD-040]:

- **Subnet-membership metadata** ([MOD-026]) carried by a directly-composed net — a node mapped to subnet `S` clusters under `cluster_<sanitize(S)>`; a shared (multi-subnet) place has no entry and stays top-level.
- **Instance-prefix detection** — a node whose name begins with `<prefix>/` (the separator established by [MOD-010]) clusters under `cluster_<sanitize(prefix)>`. Nested instance prefixes (per [MOD-013]) MUST produce nested cluster subgraphs.

When the net carries membership metadata the exporter SHOULD prefer it and fall back to instance-prefix detection for any node without an entry, so direct and instance composition coexist. The cluster source MAY be caller-selectable (metadata-only, prefix-only, or no clustering); the default SHOULD be metadata-when-present.

The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`). The cluster `label` attribute SHOULD carry the original (un-sanitized) key string for human readability.

This requirement does NOT alter the styling, junction, or arc rendering rules of EXP-002..EXP-015; it adds grouping structure only. A net with neither composed instances nor membership metadata (no `/` in any node name) MUST produce no cluster subgraphs.

**Acceptance Criteria:**
1. A net composed from two top-level instances with prefixes `b1` and `b2` exports DOT containing `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains exactly the nodes whose names begin with the corresponding prefix.
3. Nested instances produce nested cluster subgraphs (e.g., `cluster_outer` containing `cluster_outer_inner`).
4. A net with no `/` in any node name and no membership metadata produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` and are deterministic across repeated exports.
6. Java, TypeScript, and Rust mappers produce byte-identical cluster blocks (subject to MOD support in each language) for the same composed input.
7. A directly-composed net carrying [MOD-026] metadata exports one `subgraph cluster_<subnetName>` block per subnet, with each subnet's private nodes inside and shared places at the top level.

**Depends on:** [EXP-001], [EXP-014], [MOD-010], [MOD-026], [MOD-040]
**Test derivation:** Compose two instances with prefixes `b1` and `b2`; export DOT; assert cluster blocks present, members correct, IDs sanitized. Compose nested instances; assert nested cluster subgraphs. Direct-compose two subnets; assert one `cluster_<subnetName>` block per subnet.

---

#### EXP-017: Compound Cluster Layout Hints

**Priority:** SHOULD

DOT export SHOULD set `compound=true` at the digraph level unconditionally so Graphviz honours `lhead` and `ltail` attributes on edges that cross cluster boundaries. This is a no-op for flat (uncomposed) nets but keeps the digraph header uniform across all exports.

For every ordered pair of distinct subnet-instance clusters `(cluster_X, cluster_Y)` that are bridged by at least one top-level orphan node via a single-hop path — i.e. there exists some node `a` in `cluster_X`, some top-level orphan node `o` (no instance prefix per [EXP-016]), and some node `b` in `cluster_Y` such that the edges `a → o` and `o → b` both exist — the exporter MUST emit exactly one invisible ghost edge with:

- `style = invis` (no visible artifact; pure layout constraint)
- `arrowhead = none`
- `ltail = "cluster_" + sanitize(X)` (matches the cluster id defined by [EXP-016])
- `lhead = "cluster_" + sanitize(Y)`

The ghost edge's source and target node ids MUST be the first-witness anchor pair: the `a` from the first encountered `a → o` edge and the `b` from the first encountered `o → b` edge, in input iteration order (nodes scanned in their original input order; for each orphan, incoming edges then outgoing edges scanned in their original input order). Graphviz then has a real cluster-to-cluster connection to constrain layout, while the visible flow still passes through the orphan via the original real edges.

Multiple orphans bridging the same ordered cluster pair `(X, Y)` collapse to one ghost edge (dedup by ordered pair). The reverse direction `(Y, X)` is a separate ghost edge when its own 1-hop path exists. Orphan paths that fall entirely inside a single cluster (`X == Y`) or that only touch one clustered neighbour MUST NOT produce a ghost edge.

This requirement does NOT change [EXP-016] cluster membership, the visible edge set, or styling rules. It only adds the `compound=true` graph attribute and the synthesized ghost edges.

**Acceptance Criteria:**
1. Every DOT export contains `compound="true"` as a top-level graph attribute.
2. A net where `cluster_left` and `cluster_right` are bridged by a single orphan transition produces exactly one ghost edge with `style=invis`, `arrowhead=none`, `ltail="cluster_left"`, `lhead="cluster_right"`.
3. Three orphans bridging the same `(left, right)` pair still produce exactly one ghost edge (dedup by ordered pair).
4. Bidirectional bridging (`left → o1 → right` and `right → o2 → left`) produces two ghost edges, one per direction.
5. An orphan with `X → o → X` (same cluster on both sides) produces no ghost edge.
6. An orphan with only one clustered neighbour produces no ghost edge.
7. A flat net (no instance prefixes) produces no ghost edges but still emits `compound="true"`.
8. Anchor node selection is deterministic and matches across Java, TypeScript, and Rust exporters byte-for-byte for the same composed input.

**Depends on:** [EXP-016], [EXP-014]
**Test derivation:** Build a composed net with two instances and an orphan transition between them; export DOT in each language; assert one `style="invis"` edge with matching `ltail`/`lhead`. Add bidirectional and multi-orphan variants. Verify `compound="true"` on a flat net.

---

#### EXP-018: ν-Match Edge Decoration

**Priority:** SHOULD

When a transition declares a ν-net join correlation ([NU-020]), each **input
edge** to a correlated place is decorated to mark it as a name-matched input:

- **Color** `#0d9488` (teal — the `match-input` edge style in
  `spec/petri-net-styles.json`), distinguishing it from a plain input edge.
- **Label** prefixed with the bound-name variable `⟨n⟩` (U+27E8 `n` U+27E9). When
  the input also carries a cardinality label ([EXP-006]), the two are joined with
  a single space: `⟨n⟩ ×2`, `⟨n⟩ *`, `⟨n⟩ ≥3`. A correlated `One` input shows
  `⟨n⟩` alone.

Non-correlated inputs of the same transition are unaffected. The decoration is a
mapper concern: it is emitted into the DOT by every exporter, so the canonical
viewer and all three doc generators render it identically with no viewer change.

**Acceptance Criteria:**
1. An input edge to a correlated place has color `#0d9488` and a label beginning
   with `⟨n⟩`.
2. A non-correlated input edge on the same transition keeps the default color and
   no `⟨n⟩` prefix.
3. The label combines with cardinality as `⟨n⟩ ×n` / `⟨n⟩ *` / `⟨n⟩ ≥m`.
4. The emitted DOT for a ν-net is byte-identical across the Java, TypeScript, and
   Rust exporters.

**Depends on:** [EXP-006], [NU-020]
**Test derivation:** Build a join with `match` correlating two `one` inputs;
export; verify both correlated edges are teal and labeled `⟨n⟩`, and a third
non-correlated input is unchanged.
