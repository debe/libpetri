import Libpetri.Spec.Text

requirement_text TIME_004
  id "TIME-004"
  title "Delayed Timing"
  priority MUST
  kind T
  body r#"`Delayed(after)` — the transition must wait at least `after` time units before firing.

- Interval: `[after, ∞)`
- `earliest()` = after
- `latest()` = maximum duration
- `hasDeadline()` = false
- Construction: `0 <= after <= maximum duration` ([TIME-001] AC4)

⟦s1|*While* a transition with `Delayed(after)` timing is armed and its elapsed time is less than `after`, the transition *shall not* fire.⟧

⟦s2|*While* a transition with `Delayed(after)` timing is armed and its elapsed time is at least `after`, its timing *shall not* stop it from being ready.⟧

⟦s3|The executor *shall not* reap a transition with `Delayed` timing ([TIME-013]).⟧

**Acceptance Criteria:**
1. Transition cannot fire before `after` time has elapsed since enablement.
2. After `after`, the transition can fire at any time.

**Test derivation:** Delayed(3s); enable at T=0; attempt fire at T=2s → not ready; fire at T=3s → ready."#
