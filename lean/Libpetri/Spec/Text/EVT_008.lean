import Libpetri.Spec.Text

requirement_text EVT_008
  id "EVT-008"
  title "TransitionFailed Event"
  priority MUST
  kind B
  body r#"Emitted when a firing fails ([EXEC-021], [EXEC-030]): its action throws an exception or returns an error, or output validation or the join-relay check of [NU-054] rejects its outcome. Contains:
- Timestamp
- Transition name
- Error message
- Exception type name (Java and TypeScript)

⟦s1|*If* a firing fails, because its action throws an exception or returns an error or because output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021], [EXEC-030]), *then* the executor *shall* emit exactly one TransitionFailed event naming the firing's transition, and *shall not* emit a TransitionCompleted event or a TokenAdded event when it settles that firing.⟧

⟦s2|The executor *shall* emit TransitionFailed events only when a firing fails.⟧

Each TransitionFailed event *shall* carry the error message of the failure.

*Where* the TransitionFailed event carries the exception type (Java and TypeScript), it *shall* carry the name of the exception type of the failure.

**Acceptance Criteria:**
1. Emitted when action fails.
2. The error message is captured, and the exception type name where the event carries it (Java and TypeScript).

**Depends on:** [EXEC-030], [EXEC-021], [NU-054]
**Test derivation:** Action throws; verify TransitionFailed with error details."#
