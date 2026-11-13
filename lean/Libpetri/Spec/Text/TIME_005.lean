import Libpetri.Spec.Text

requirement_text TIME_005
  id "TIME-005"
  title "Window Timing"
  priority MUST
  kind T
  body r#"`Window(earliest, latest)` — the transition can fire within the specified time window.

- Interval: `[earliest, latest]`
- Construction: `0 <= earliest <= latest <= maximum duration` ([TIME-001] AC4)
- `hasDeadline()` = true

⟦s1|*While* a transition with `Window(earliest, latest)` timing is armed and its elapsed time is less than `earliest`, the transition *shall not* fire.⟧

⟦s2|*While* a transition with `Window(earliest, latest)` timing is armed and its elapsed time is at least `earliest`, its timing *shall not* stop it from being ready until it is expired.⟧

⟦s3|*If* a transition with `Window(earliest, latest)` timing is armed and its elapsed time exceeds `latest` plus the deadline tolerance, *then* the executor *shall* reap it ([TIME-013]).⟧

**Acceptance Criteria:**
1. Cannot fire before `earliest`.
2. A transition still armed past `latest` plus the deadline tolerance does not fire after that
   bound. If it is still armed on the first cycle whose elapsed time is strictly greater than the
   bound, it is reaped in that cycle ([TIME-013]).
3. Construction with latest < earliest is rejected.
4. Construction with earliest or latest above the maximum duration is rejected ([TIME-001] AC4).

**Depends on:** [TIME-001], [TIME-003]
**Test derivation:** Window(1s, 5s); attempt fire at 0.5s → not ready; fire at 2s → ready; at 6s → expired."#
