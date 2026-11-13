import Libpetri.Spec.Text

requirement_text EVT_001
  id "EVT-001"
  title "Event Immutability"
  priority MUST
  kind Q
  body r#"All events are immutable value objects. Once created, no field can be modified. Collections within events (e.g., consumed tokens) are defensive copies.

**Acceptance Criteria:**
1. Event fields are read-only.
2. Collections within events are immutable copies (not live references).

**Test derivation:** Create event with list; modify original list; verify event's list unchanged."#
