import Libpetri.Spec.Text

requirement_text TIME_002
  id "TIME-002"
  title "Immediate Timing"
  priority MUST
  kind T
  body r#"`Immediate` — the transition can fire as soon as it is enabled, with no deadline.

- Interval: `[0, ∞)`
- `earliest()` = 0
- `latest()` = maximum duration
- `hasDeadline()` = false

⟦s1|*While* a transition with `Immediate` timing is armed, its timing *shall not* stop it from being ready ([TIME-010]).⟧

⟦s2|The executor *shall not* reap a transition with `Immediate` timing ([TIME-013]).⟧

**Acceptance Criteria:**
1. Transition fires immediately when enabled.
2. No deadline enforcement.

**Test derivation:** Transition with Immediate timing; enable it; verify it fires on next cycle."#
