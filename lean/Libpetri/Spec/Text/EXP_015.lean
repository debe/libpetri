import Libpetri.Spec.Text

requirement_text EXP_015
  id "EXP-015"
  title "Doc Generator Parity"
  priority MUST
  kind Q
  body r#"The compile-time diagram generators (EXP-011) MUST embed DOT sources reflecting the visualization rules above. Specifically, `mvn javadoc:javadoc`, `cargo doc`, and the TypeDoc plugin MUST emit DOT that includes junction nodes (per EXP-012) and combined reset+output edges (per EXP-013) for any net that uses XOR/AND outputs or reset+output coupling. Rendering of that DOT into SVG happens client-side at view time via the bundled `LibpetriViewer` IIFE (per EXP-011).

This is achieved by having all three doc generators delegate to their language's mapper; no doc-generator-specific code is required.

**Acceptance Criteria:**
1. Building Java docs for a net with `XOR(A, B)` includes a `data-dot` attribute whose DOT source declares a diamond-shaped junction node (the XOR junction).
2. Building Rust docs for the same net produces a DOT source that, modulo whitespace, matches the Java DOT.
3. Building TypeScript docs for the same net produces a DOT source that matches.

**Test derivation:** Build docs in each language for a small net with `XOR(A, B)` and `Out.Place(P) + reset(P)`; extract the embedded DOT (the `data-dot` attribute) and assert content via grep for the expected shape/color signatures."#
