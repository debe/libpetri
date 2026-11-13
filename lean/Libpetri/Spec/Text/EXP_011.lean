import Libpetri.Spec.Text

requirement_text EXP_011
  id "EXP-011"
  title "Compile-Time Diagram Generation"
  priority MAY
  kind Q
  body r#"The engine MAY support generating diagrams from net structure annotations at compile time, embedding them in documentation or source comments.

**Acceptance Criteria:**
1. Net structure annotations are processed at compile time.
2. Diagrams are generated without running the net.

**Implementation notes:**
- Java: `@NetStructure` annotation processed by `@petrinet` Javadoc taglet to embed DOT in `data-dot` attributes
- TypeScript: `@petrinet` TypeDoc plugin resolves net definitions and embeds DOT in `data-dot` attributes
- Rust: `libpetri-docgen` build-dependency crate emits DOT-in-HTML via `SvgGenerator` / `generate_svg()`

All three generators emit self-contained HTML pages that inline the canonical `LibpetriViewer` IIFE bundle (with `@viz-js/viz` Graphviz WASM baked in). DOT → SVG conversion happens client-side at view time. No external tooling (`dot`, `node`, etc.) is required on the doc-generation host.

**Test derivation:** Annotated net structure; build project; verify diagram generated."#
