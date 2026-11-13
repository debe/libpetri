import Libpetri.Spec.Text

requirement_text EXEC_031
  id "EXEC-031"
  title "No Rollback"
  priority MUST
  kind B
  body r#"⟦s1|The engine does not provide transaction rollback.⟧ ⟦s2|Once tokens are consumed by a firing transition, they are not restored if the action fails.⟧ This is a deliberate design choice — rollback would require complex compensation logic and conflicts with the async nature of actions.

⟦s3|A firing fails when its action throws or returns an error ([EXEC-030]), when its produced tokens fail output validation ([EXEC-021]), or when its produced tokens or its timeout outcome fail the join-relay check ([NU-054]).⟧

⟦s4|*If* a firing fails, *then* the executor *shall not* restore the tokens the firing consumed.⟧

⟦s5|*If* a firing fails, *then* the executor *shall not* later deposit a completion or a timeout outcome of that firing.⟧

**Acceptance Criteria:**
1. Failed action → consumed tokens permanently removed.

**Depends on:** [EXEC-021], [EXEC-030], [NU-054]
**Test derivation:** Fire transition consuming token; action fails; verify token not in any place."#
