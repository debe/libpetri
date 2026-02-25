# 03 — Timing

This document specifies firing interval semantics based on classical Time Petri Net (TPN) theory.

---

## Timing Variants

#### TIME-001: Timing Specification

**Priority:** MUST

Each transition has an associated timing specification that defines when it can and must fire relative to its enablement time. The timing is expressed as an interval `[earliest, latest]` where:
- The transition CANNOT fire before `earliest` time units after enablement
- The transition SHOULD be disabled after `latest` time units (deadline enforcement)

A maximum duration constant (e.g., ~100 years) represents "no constraint" on the upper bound.

**Acceptance Criteria:**
1. Each transition has a timing specification (defaults to Immediate).
2. `earliest()` and `latest()` are queryable.
3. `hasDeadline()` returns true when latest < maximum duration.

**Test derivation:** Create each timing variant; verify earliest(), latest(), hasDeadline().

---

#### TIME-002: Immediate Timing

**Priority:** MUST

`Immediate` — the transition can fire as soon as it is enabled, with no deadline.

- Interval: `[0, ∞)`
- `earliest()` = 0
- `latest()` = maximum duration
- `hasDeadline()` = false

**Acceptance Criteria:**
1. Transition fires immediately when enabled.
2. No deadline enforcement.

**Test derivation:** Transition with Immediate timing; enable it; verify it fires on next cycle.

---

#### TIME-003: Deadline Timing

**Priority:** MUST

`Deadline(by)` — the transition can fire immediately but must fire within `by` time units.

- Interval: `[0, by]`
- `earliest()` = 0
- `latest()` = by
- `hasDeadline()` = true
- Construction: `by` must be positive (> 0)

**Acceptance Criteria:**
1. Transition can fire immediately after enablement.
2. If not fired within `by`, the transition should be disabled and a timeout event emitted.

**Depends on:** [EVT-008]
**Test derivation:** Deadline(5s); enable transition; let 6s pass without firing; verify transition disabled.

---

#### TIME-004: Delayed Timing

**Priority:** MUST

`Delayed(after)` — the transition must wait at least `after` time units before firing.

- Interval: `[after, ∞)`
- `earliest()` = after
- `latest()` = maximum duration
- `hasDeadline()` = false

**Acceptance Criteria:**
1. Transition cannot fire before `after` time has elapsed since enablement.
2. After `after`, the transition can fire at any time.

**Test derivation:** Delayed(3s); enable at T=0; attempt fire at T=2s → not ready; fire at T=3s → ready.

---

#### TIME-005: Window Timing

**Priority:** MUST

`Window(earliest, latest)` — the transition can fire within the specified time window.

- Interval: `[earliest, latest]`
- Construction: `latest` >= `earliest`, both >= 0
- `hasDeadline()` = true

**Acceptance Criteria:**
1. Cannot fire before `earliest`.
2. Must fire by `latest` or be disabled.
3. Construction with latest < earliest is rejected.

**Test derivation:** Window(1s, 5s); attempt fire at 0.5s → not ready; fire at 2s → ready; at 6s → expired.

---

#### TIME-006: Exact Timing

**Priority:** MUST

`Exact(at)` — the transition fires at exactly the specified time.

- Interval: `[at, at]`
- `earliest()` = `latest()` = at
- `hasDeadline()` = true

**Acceptance Criteria:**
1. Cannot fire before `at`.
2. Must fire at `at` (or be disabled immediately after).

**Test derivation:** Exact(3s); verify fires at exactly 3s.

---

## Clock Semantics

#### TIME-010: Clock Starts on Enablement

**Priority:** MUST

The timing clock starts when the transition first becomes enabled (all preconditions met). The elapsed time for timing decisions is measured from this enablement moment.

**Acceptance Criteria:**
1. Transition enabled at T=10; earliest=3s; transition ready at T=13.
2. Transition enabled at T=10; disabled at T=11; re-enabled at T=15; ready at T=18 (clock restarted).

**Test derivation:** Enable transition; track elapsed time; verify firing window is relative to enablement.

---

#### TIME-011: Clock Restarts on Re-enablement

**Priority:** MUST

If a transition becomes disabled and then re-enabled, the clock restarts from zero. The previous elapsed time is discarded.

**Acceptance Criteria:**
1. Transition enabled with Delayed(5s); at 3s it becomes disabled; re-enabled later; must wait another 5s.

**Test derivation:** Enable, partially wait, disable, re-enable; verify full delay applies again.

---

#### TIME-012: Clock Restart on Reset Arc

**Priority:** MUST

If a transition is enabled and a reset arc fires on one of its input places (removing tokens, then new tokens arrive), the transition's clock restarts. A `TransitionClockRestarted` event is emitted.

**Acceptance Criteria:**
1. Transition T reads/inputs from place P; T is enabled; another transition resets P; new token arrives in P; T's clock restarts.
2. TransitionClockRestarted event emitted.

**Depends on:** [CORE-034], [EVT-004]
**Test derivation:** Setup two transitions sharing a place via reset arc; verify clock restart event.

---

#### TIME-013: Deadline Enforcement

**Priority:** MUST

When a transition exceeds its latest bound (deadline), the executor disables it and emits a `TransitionTimedOut` event. Implementations MAY apply a small tolerance (e.g., 1ms) for timer resolution jitter.

**Acceptance Criteria:**
1. Transition with Deadline(5s); not fired within 5s + tolerance → disabled + event emitted.
2. Tolerance is implementation-defined but documented.

**Depends on:** [EVT-008]
**Test derivation:** Create transition with tight deadline; delay firing; verify timeout event and disablement.

---

#### TIME-014: Competitive Scheduling with Timing

**Priority:** MUST

When multiple transitions compete for the same tokens, timing interacts with priority:
- Higher priority transitions are preferred.
- Among equal priority, Immediate transitions fire before Delayed ones (since Delayed transitions are not ready until their earliest bound).
- A Delayed transition with low priority can serve as a fallback when the high-priority immediate transition fires first.

**Acceptance Criteria:**
1. Two transitions on same input: T1 (P=10, Immediate) and T2 (P=-10, Delayed(3s)); T1 fires first.
2. If T1 does not fire within 3s, T2 becomes ready and fires.

**Depends on:** [EXEC-003]
**Test derivation:** Event-driven workflow pattern: PrimaryAction (P=10, immediate) vs FallbackAction (P=-10, 3s delay).
