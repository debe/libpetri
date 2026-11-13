import Libpetri.Spec.Text

requirement_text TIME_006
  id "TIME-006"
  title "Exact Timing"
  priority MUST
  kind T
  body r#"`Exact(at)` — the transition targets the specified time.

- Interval: `[at, at]`
- `earliest()` = `latest()` = at
- `hasDeadline()` = true
- Construction: `0 <= at <= maximum duration` ([TIME-001] AC4)

The interval `[at, at]` is the precise value used for **verification and simulation** (logical
time). Under **wall-clock execution** a zero-width window cannot be hit exactly — the executor
observes the clock at discrete cycle points, so it invariably lands at `at + ε`. Exact timing is
therefore enforced **softly**: the transition fires at the first opportunity at or after `at`
(delayed-style liveness) and is **never** force-disabled for overrunning `at`. Real-time callers
that want a plain lower bound SHOULD use `Delayed(at)`; those wanting a hard bounded window SHOULD
use `Window(at, at + slack)`.

The requirements below describe the executor. The verification reading of `[at, at]` belongs to
[VER-002] and [VER-012].

⟦s1|*While* a transition with `Exact(at)` timing is armed and its elapsed time is less than `at`, the transition *shall not* fire.⟧

⟦s2|*While* a transition with `Exact(at)` timing is armed and its elapsed time is at least `at`, its timing *shall not* stop it from being ready.⟧

⟦s3|The executor *shall not* reap a transition with `Exact` timing, however late it observes it ([TIME-013]).⟧

**Acceptance Criteria:**
1. Cannot fire before `at`.
2. Fires at the first opportunity at or after `at` and is not force-disabled for being observed
   late (see [TIME-013]); exactness is observable from the firing event, not enforced destructively.

**Test derivation:** Exact(50ms) under a busy executor that cannot run a cycle until well past
50ms; verify it still fires and emits no `TransitionTimedOut`."#
