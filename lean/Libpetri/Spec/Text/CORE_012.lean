import Libpetri.Spec.Text

requirement_text CORE_012
  id "CORE-012"
  title "Unit Token"
  priority MUST
  kind Q
  body r#"A unit token is a special token with no meaningful payload value, used for pure control flow signaling. The engine provides a canonical way to create unit tokens.

**Acceptance Criteria:**
1. A unit token can be created.
2. A unit token can be added to a place that accepts the unit type.
3. Unit tokens are identifiable as such.

**Test derivation:** Create a unit token; verify it is recognized as a unit token by the engine."#
