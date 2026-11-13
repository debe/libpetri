import Libpetri.Spec.Text

requirement_text EXP_010
  id "EXP-010"
  title "Formal Interchange Format"
  priority MAY
  kind Q
  body r#"The engine MAY support exporting to formal analysis interchange formats suitable for external tools (e.g., PNML for Petri net tools, STTT format for Sirio timing analysis).

**Acceptance Criteria:**
1. Export produces valid output in the target format.
2. Places, transitions, arcs, and timing are represented.

**Implementation notes:**
- Not yet implemented in any language

**Test derivation:** Export to interchange format; validate against schema."#
