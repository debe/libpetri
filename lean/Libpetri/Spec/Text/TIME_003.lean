import Libpetri.Spec.Text

requirement_text TIME_003
  id "TIME-003"
  title "Deadline Timing"
  priority MUST
  kind T
  body r#"`Deadline(by)` — the transition can fire immediately but must fire within `by` time units, plus the deadline tolerance ([TIME-013]).

- Interval: `[0, by]`
- `earliest()` = 0
- `latest()` = by
- `hasDeadline()` = true
- Construction: `0 < by <= maximum duration` ([TIME-001] AC4)

⟦s1|*While* a transition with `Deadline(by)` timing is armed, its timing *shall not* stop it from being ready until it is expired.⟧

⟦s2|*If* a transition with `Deadline(by)` timing is armed and its elapsed time exceeds `by` plus the deadline tolerance, *then* the executor *shall* reap it ([TIME-013]).⟧

**Acceptance Criteria:**
1. Transition can fire immediately after enablement.
2. A transition still armed past `by` plus the deadline tolerance does not fire after that
   bound. If it is still armed on the first cycle whose elapsed time is strictly greater than the
   bound, it is reaped in that cycle and a `TransitionTimedOut` event is emitted ([EVT-009]).

**Depends on:** [EVT-009]
**Test derivation:** Deadline(5s); enable transition; let 6s pass without firing; verify transition disabled."#
