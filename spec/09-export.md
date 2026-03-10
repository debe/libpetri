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
- Java: `@NetStructure` annotation processed by `@petrinet` Javadoc taglet to generate DOT→SVG diagrams
- TypeScript: `@petrinet` TypeDoc plugin resolves net definitions and generates embedded SVG diagrams
- Rust: `libpetri-docgen` build-dependency crate generates DOT→SVG diagrams via `SvgGenerator` / `generate_svg()`

**Test derivation:** Annotated net structure; build project; verify diagram generated.
