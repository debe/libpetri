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

`Exact(at)` — the transition targets the specified time.

- Interval: `[at, at]`
- `earliest()` = `latest()` = at
- `hasDeadline()` = true

The interval `[at, at]` is the precise value used for **verification and simulation** (logical
time). Under **wall-clock execution** a zero-width window cannot be hit exactly — the executor
observes the clock at discrete cycle points, so it invariably lands at `at + ε`. Exact timing is
therefore enforced **softly**: the transition fires at the first opportunity at or after `at`
(delayed-style liveness) and is **never** force-disabled for overrunning `at`. Real-time callers
that want a plain lower bound SHOULD use `Delayed(at)`; those wanting a hard bounded window SHOULD
use `Window(at, at + slack)`.

**Acceptance Criteria:**
1. Cannot fire before `at`.
2. Fires at the first opportunity at or after `at` and is not force-disabled for being observed
   late (see [TIME-013]); exactness is observable from the firing event, not enforced destructively.

**Test derivation:** Exact(50ms) under a busy executor that cannot run a cycle until well past
50ms; verify it still fires and emits no `TransitionTimedOut`.

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

#### TIME-012: Clock Restart on Intermediate Disablement

**Priority:** MUST

A firing of transition `t` has two halves: its inputs are consumed and its reset places drained, then its outputs are deposited. The marking between the halves is the intermediate marking `M - Pre(t)` of Berthomieu and Diaz. Any other transition that was enabled before `t` fired and is not enabled in the intermediate marking is newly enabled when it is enabled again afterwards, so its clock restarts from zero ([TIME-011]). This holds even when `t`'s own outputs refill the place, and it holds whether `t`'s action completes synchronously or asynchronously: a synchronous action MUST NOT hide the gap. The intermediate marking comes from the marking `t` fires from, so tokens an earlier firing already deposited count, while outputs of an asynchronous action still in flight do not.

- Removing tokens disables a transition only through input arcs, read arcs, cardinality requirements and ν-join bindings, never through inhibitor arcs.
- A reset arc is a consumption that drains its place, so every enabled transition that consumes or reads from a reset place starts a fresh clock when it is enabled again.
- Surplus tokens keep the clock. If `P` holds two tokens, `t` takes one and `t'` needs one, `t'` stays enabled in the intermediate marking and its clock continues.
- The fired transition itself always starts a fresh clock when it is enabled again.

The state class graph applies the same rule to persistence ([VER-010]). A transition that stays marked enabled across the firing announces its fresh clock with `TransitionClockRestarted` ([EVT-005]). If the executor observed it disabled in between, for example while an asynchronous action was in flight, its re-enablement emits `TransitionEnabled` instead ([EVT-004]).

**Acceptance Criteria:**
1. T consumes from place P and is enabled. Another transition consumes P's token and deposits a token into P in one firing, with a synchronous action. T's clock restarts: with `delayed(d)`, T fires no earlier than `d` after the refill.
2. As AC1, but T only reads P. T's clock restarts.
3. As AC1, but the other transition drains P through a reset arc and deposits a new token. T's clock restarts.
4. As AC1, but P holds two tokens and the other transition takes one and returns it. T's clock continues, and neither `TransitionClockRestarted` nor `TransitionEnabled` is emitted for T after the refresh.
5. AC1 with an asynchronous action restarts T's clock as well.
6. Each restart emits exactly one of `TransitionClockRestarted` or `TransitionEnabled`.

**Depends on:** [TIME-011], [CORE-034], [EXEC-013], [EVT-004]
**Test derivation:** A timer place P feeds a delayed transition T. An injected activity token fires a refresh transition that takes P's token and puts one back: through an input arc, with T only reading P, through a reset arc, and with a surplus token in P. Repeat the input-arc case with an asynchronous action. Assert a lower bound on T's firing time and the fresh-clock event, or its absence in the surplus case.

---

#### TIME-013: Deadline Enforcement

**Priority:** MUST

When a transition with a **hard deadline** (`Deadline` / `Window`) exceeds its latest bound, the executor disables it and emits a `TransitionTimedOut` event. Implementations MUST apply a deadline tolerance — a grace band beyond `latest` (default 5ms) that absorbs timer-resolution and scheduling jitter — and SHOULD expose it as a configurable per-executor option (e.g. `deadlineTolerance` / `deadline_tolerance_ms`); a value of `0` gives strict enforcement.

`Exact` timing is **not** subject to destructive enforcement: it is enforced softly per [TIME-006] (fires at the first opportunity at/after its target, never force-disabled). Only `Deadline` and `Window` transitions are reaped here.

**Acceptance Criteria:**
1. Transition with Deadline(5s); not fired within 5s + tolerance → disabled + `TransitionTimedOut`.
2. The tolerance is documented and configurable; the default is 5ms across implementations.
3. An `Exact` transition observed past its target is **not** disabled (see [TIME-006]).

**Depends on:** [EVT-008]
**Test derivation:** Create a `Window`/`Deadline` transition; block the executor past `latest + tolerance`; verify timeout event and disablement. Separately, verify an `Exact` transition under the same conditions still fires.

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

---

#### TIME-015: Injectable Clock

**Priority:** SHOULD

An implementation SHOULD let a host supply the executor's time source. The seam is **per
executor**, not per net: a net is immutable and shared across composition ([MOD-010]), so a
clock attached to one would have to be merged at every compose, and a host that runs two
executors in one process — comparing an engine against a reference, or testing one net under
virtual time while another runs live — needs them on independent clocks.

**Two time bases, not one.** An executor reads time from two distinct sources, and a single
injected `now` cannot serve both:

- the **firing clock** — a monotonic source from which enablement stamps ([TIME-010]),
  elapsed-time decisions ([TIME-004], [TIME-005], [TIME-006]), deadline enforcement
  ([TIME-013]) and the wake-up interval are computed;
- the **epoch clock** — a wall-clock source stamping token creation times ([CORE-011]) and
  the timestamps events carry.

Their origins are unrelated and MUST NOT be conflated. A host MAY derive both from one
logical source, and SHOULD when it needs the two to agree across a replay.

**Reading time is not enough — the seam MUST own the wait.** If a host supplies only a
`now` while the executor still sleeps on the real timer, the stamps are virtual and the
waiting is real: a `delayed(d)` still costs `d` of wall time and a timed test is no more
deterministic than before. The seam MUST therefore also own the executor's wait for the next
timing boundary ([EXEC-001] step 6).

**Contract on an injected clock.** All five hold; none of them is an error condition today,
and each is silent when violated:

1. **Non-decreasing, and not assumed strictly increasing.** The firing clock MUST NOT go
   backwards: elapsed time is a difference from an enablement stamp, so a backwards step
   yields a negative elapsed value, which re-opens the earliest bound of an already-due
   transition and can stall the net indefinitely without surfacing an error. Equally, the
   executor MUST NOT assume the clock *advances* between two reads. A host clock is commonly
   derived from a coarser source — millisecond-resolution wall time, or a replay log — and
   returns the **same** value across many cycles; that is normal, not a fault. Any logic that
   requires a non-zero delta between reads, or that treats a clock reading as a unique key,
   breaks under such a host, and breaks intermittently.
2. **Suspend or advance — and where there is no boundary, suspend.** Given a finite interval the
   wait MUST either suspend until that boundary or advance the clock to it; a host clock that
   advances only on demand, paired with a wait that does neither, spins forever with elapsed time
   never reaching the bound.

   **An infinite interval is not a boundary, and neither disjunct applies to it.** The executor
   passes an infinite interval whenever nothing timed is pending — which is most of the time: the
   orchestrator is parked on an in-flight action, or waiting on external events. There is no
   instant to advance to, so the wait MUST **suspend until woken**. Returning immediately is
   non-conforming: the executor re-enters the wait at once and the loop becomes a spin. On a
   single-threaded runtime that spin starves the very work the wait exists for, so the net does not
   merely burn a core — it stops making progress, and no enclosing timeout can rescue it because
   nothing yields. The failure *surface* differs by runtime and neither
   form is benign. Where the per-cycle wake-up primitive is registered on a queue that starvation
   never drains it is retained, so memory grows without bound and the process fails on memory at
   whatever heap it was given; where the runtime drops it when the wait completes, allocation
   churns at a constant steady state and the process does not fail at all. Both were observed on
   the same defect in two implementations — one an out-of-memory failure in a bounded test worker,
   the other resident memory flat to the kilobyte over forty seconds. Neither observation
   generalises to the other runtime, and an implementation SHOULD NOT assume its own failure
   surface from a sibling's.

   The second is the reason **a test MUST NOT be bounded by patience**. An enclosing timeout cannot
   fire when nothing yields — measured at 36.9 s of CPU with a 5 s inner timeout that never ran —
   so a test written that way wedges CI instead of failing it. Bound the test by the number of
   times the wait is **entered** instead: that fails in milliseconds and names the defect.

   This is the failure the requirement is least likely to survive a first reading, so
   implementations SHOULD test a clock against an interval of `Infinity` explicitly, and SHOULD
   pin any clock that appears in their own documentation by transcribing it into that test — a
   documented clock is the one a host copies.

   A wait offered as **asynchronous** MUST NOT complete synchronously on first poll, and MUST NOT
   block the calling thread: the first defeats suspension exactly as returning early does, and the
   second parks a worker that the runtime needs for the action being waited on. An implementation
   whose asynchronous wait defaults to running its synchronous one MUST document that the default
   suits only a clock that *advances*, and MUST NOT ship a suspending clock that inherits it.

   With (1) these are the liveness failures an injected clock introduces.
3. **Spurious completion permitted.** The wait MAY complete early and for no reason. The
   executor MUST re-check its boundary conditions and MUST NOT treat "the wait completed" as
   "the boundary is reached".
4. **Abort completes, not fails.** Where the seam hands the wait an abort signal, the executor
   raises it **when the wait is over or the executor is closing** ([ENV-013]) — not only on
   shutdown. A wait is over as soon as the executor stops waiting on it, which is usually because
   the *other* half of "signal or timeout" won: an action completed, an event arrived. On abort
   the wait MUST complete normally rather than failing, and MUST release whatever it registered
   to hear the abort. Shutdown is precisely the path on which a failing wait is most likely to
   escape unobserved.

   The signal is scoped to **one wait** because the alternative leaks. A suspended wait
   (contract 2: an infinite interval) that loses to a wake-up is abandoned still suspended; if
   the only signal it listens to is one that fires at close, its registration — and everything
   the registration retains — outlives it, once per idle period, for the life of the executor.
   A host MUST therefore not read abort as teardown: it says *this wait* is finished, and the
   clock will be asked to wait again. An implementation whose abandoned wait is simply dropped
   or cancelled by the runtime owes nothing here; one that hands out a listener-style signal
   owes a per-wait one, and MUST still keep the no-clock path free of the allocation (AC#9).
5. **Any readiness signal is time-free.** A host-visible readiness predicate the wait
   consults MUST be cheap, repeatable and side-effect free, and MUST NOT itself consult a
   clock — a time-based predicate reintroduces the real clock behind the seam.

**The wait is "signal or timeout", never a bare sleep.** Every implementation's wait already
completes on *either* an elapsed interval *or* a wake-up raised by a completing action, an
injected external event, or a close ([CONC-010], [ENV-005], [ENV-013]) — realised as a
semaphore acquire with timeout, a race against a wake-up promise, or a channel receive with
timeout. The seam MUST carry **both halves**. A seam expressed purely as a duration cannot
express the wake-up and is non-conforming: under an injected clock a completing action would
stop waking the orchestrator and the net would stall, while the default path kept working —
precisely the silent, injection-only failure this requirement exists to prevent. A seam taking
*both* a readiness predicate and an interval is the conforming shape; it is only a bare
interval that is not.

**When the host owns the wait, it owns the wake-up's visibility.** An implementation MAY stop
raising its own internal wake-up while a host clock is installed, delegating entirely to the
readiness predicate. Doing so makes the predicate the **sole carrier** of every reason the
executor might need to stop waiting, and it MUST then cover all of them.

Two distinct obligations follow, and the second is the one most easily missed:

1. **Visibility.** The predicate MUST observe work published by any thread that can complete an
   action or inject an event. In practice either the host serializes all access to the executor,
   or the predicate reads that state with the memory visibility publication requires.
2. **Completeness.** The predicate MUST also observe every **lifecycle** change that can make the
   run terminable — a drain ([ENV-011]), a close ([ENV-013]), a stop request — and not merely the
   arrival of work. A lifecycle change typically has no queue behind it, so a predicate written
   around the work queues omits it silently: the flag is set, nothing enqueues, the host is never
   woken, and the net parks forever *under an injected clock only* while the default path keeps
   working. A predicate that is false whenever the run can no longer make progress also cannot
   spin, so the two properties are satisfiable together.

An implementation that silences its internal wake-up without meeting both leaves a host free to
complete an action on a foreign thread, or to drain the executor, and never be noticed.

**Whether silencing is even a choice depends on the shape of the seam.** Where the wait composes
**non-blockingly** — a race over promises, a `select!` over channel arms — the implementation's own
wake-up can sit alongside the host's interval in a single construct. It then carries both halves by
construction and owes neither obligation; that is the simpler design and SHOULD be preferred where
the runtime allows it. Where the host's wait is instead a **synchronous call on the orchestrator's
own thread**, it is not available: while that thread is inside host code it cannot also be blocked
on the implementation's own wake-up primitive, so a signal raised during the wait has no waiter and
never will — it accumulates unread, or is simply lost. At that shape the readiness predicate is the
sole carrier **by construction rather than by choice**, and both obligations above are
unconditional. A binding that rides another implementation's runtime inherits whichever shape it
exposes, so one that later offers a synchronous host wait acquires the stricter obligation with it.

**Admission from inside the wait.** A host that owns the wait may be the only thing running
while the executor is parked, so `inject()` ([ENV-003]) MUST be legal to call from inside the
wait — reentrantly, from a host callback the executor itself invoked. Such an injection MUST
only *enqueue*: the tokens MUST be admitted in the executor's own external-events phase
([EXEC-001] step 2) on a following cycle, and MUST NOT be applied at the point of injection.
This keeps a host-driven run's admission order identical to a default run's, and it matters
because a host that installs a clock and nothing else has no other admission path.

The same holds for the other admission path, an action's result. A host that executes actions
itself — a workflow runtime's activities, a discrete-event simulator, a deterministic test harness —
MAY complete an action's future (or promise, or task) from inside the wait. Completion MUST only
enqueue: the result is admitted in the executor's completion phase ([EXEC-001] step 1) of a
following cycle, never at the call. Where the runtime runs a future's dependents inline on the
completing thread, whatever the completion runs there is bound by the same rules as the host: it
may inject or complete, but it MUST NOT await an admission signal and MUST NOT block.

**The admission signal MUST NOT be awaited there.** `inject()` reports admission through a
completion signal that the **orchestrator** completes once the event reaches its phase
([ENV-004]) — and inside the wait the orchestrator *is* the caller. Awaiting that signal there
deadlocks the executor against itself: the thread or task that would complete it is the one
blocked waiting for it, so there is no error, no timeout from the executor's own machinery, and
nothing to indicate what happened. A host must inject and return. This follows from the design
rather than from any one runtime, so it holds wherever the orchestrator is a single logical
thread of control — a blocked thread, a suspended async loop, or a parked task alike. An
implementation SHOULD make the hazard hard to hit rather than merely documented: where it can
tell that an injection came from its own orchestrator context, it SHOULD offer, or steer the
caller to, a form whose result cannot be awaited.

**Default behaviour is unchanged.** Absent an injected clock an implementation MUST behave
exactly as before: this requirement adds a seam, not a semantic change, and every existing
timing conformance test MUST pass unchanged.

**Boundary short-circuit preserved.** When the next boundary is already due and there is
nothing else to wait for, the executor MUST return and let the next cycle act on it rather
than waiting. Implementations reach this differently — a zero-length sleep, or an early
return on a non-positive interval — and an injected clock MUST NOT make them diverge
([EXEC-001], [CONC-010]).

**Token stamping boundary.** The epoch clock stamps tokens the **executor** produces. Tokens
a host mints in its own code are outside this requirement and no seam can reach them; an
implementation MUST therefore offer construction of a token at an explicit timestamp
([CORE-011]) so a host can keep those replay-safe without one.

**The line is drawn by who chooses the timestamp, not who supplies the value.** An action calling
`ctx.output(place, value)` supplies a *value*; the implementation constructs the token and
therefore chooses its `created_at`. Such a token is **executor-produced** and MUST be stamped
through the injected epoch clock — as MUST every token the implementation synthesises during a
firing, including the recovery outputs it produces when an action timeout fires ([IO-013]) and
tokens minted from a raw value on injection. Only a token the **host itself** constructs, and
whose timestamp the host therefore already chose, falls outside. Reading the boundary the other
way — treating anything an action had a hand in as host-side — leaves the bulk of a run's tokens
carrying wall-clock time under a virtual clock, which defeats the requirement while appearing to
satisfy it.

Seed tokens are the sharp edge. An initial marking ([CORE-072]) is built by the host *before*
any executor exists, so no seam can reach it and the obvious constructor stamps wall-clock
time — which under replay differs per attempt, inside the marking itself. The executor MUST NOT
silently re-stamp host-supplied tokens: that would defeat [CORE-073], whose restore
deliberately preserves `created_at`. An implementation SHOULD instead offer a construction path
that stamps *fresh* seed tokens through the injected epoch clock, and MUST document that its
default token constructor is non-deterministic under a host clock and unsuitable for a seed
marking. Left undocumented the failure is invisible: a replay diverges, and the cause is a
timestamp minted before the run began.

> **Note (non-normative).** Mixed time bases are also visible to one firing decision: the
> [NU-022] tie-break orders correlation names by their oldest token's `created_at`. Host-stamped
> seed tokens and restored tokens ([CORE-073]) carry the stamps of whatever clock made them, and a
> virtual epoch clock that starts near zero sorts every token the run produces ahead of all of
> them. A host injecting an epoch clock over such a marking — a resumed execution above all —
> should seed the clock at or above the marking's maximum `created_at`; below it, the tie-break
> order between the pre-existing and the fresh groups is unspecified. The engine does not
> re-stamp and the tie-break key does not change.

**Scope limit: action timeouts are not virtualized.** An action timeout ([IO-013]) — the
`timeout(after, recovery)` branch of an output spec — *is* a timing decision the net declares, but
it is enforced by a **per-action** wait, whereas this seam owns only the executor's single
orchestrator wait. It is therefore **out of scope** for this requirement: under an injected clock
the recovery tokens are stamped from the epoch clock (AC#13), but the timeout interval itself
still elapses in real time. A net declaring `timeout(…)` is consequently not fully virtualizable,
and a host replaying one waits the real interval. An implementation MUST document this limit
rather than let a host infer from the rest of the requirement that all net-declared timing is
virtualized.

This is a known boundary, not an oversight: bringing action timeouts under the seam requires the
clock to mediate every in-flight action's wait rather than one orchestrator wait, which is a
larger change than adding a seam. An implementation MUST NOT route the timeout interval through
the injected clock while leaving the action's own wait on real time — that would fire the recovery
branch at a virtual instant the action never reached, producing a recovery for work that is still
running.

**A run budget is not net timing.** A wall-clock budget passed to a run-with-timeout is a limit on
the *host's* patience, not a firing decision, and an implementation SHOULD leave it on real time
even when a clock is installed: routing it through a host-driven clock makes a virtual-time run
unkillable, since the only thing that would advance the clock is the run it is meant to bound. A
host driving virtual time SHOULD therefore pass a generous or unbounded budget. One consequence
worth stating: a host that violates the admission rule above then fails at its budget rather than
hanging forever, which is bounded but still silent as to why.

**Identifiers MUST NOT be clock readings.** Any identifier an implementation derives for a run —
an execution id carried on lifecycle events, for example — MUST NOT be derived solely from a clock
reading. Contract point 1 already forbids treating a reading as a unique key, and a run identifier
is the likeliest place to violate it: under a host clock, two executors seeded from the same
virtual instant, or one run replayed, produce the same reading and therefore the same identifier.
Such an identifier MUST be unique among executors that can be observed together, and SHOULD remain
reproducible for a fixed clock and firing order.

A run identifier is deliberately **not** the default minting scope of [NU-011]. That scope MUST
differ between two processes that did nothing differently; a reproducible identifier is one that
does not. The two are separate values, and an implementation MUST NOT derive either from the
other.

**Interactions.**

- [TIME-013]'s deadline tolerance exists to absorb real timer and scheduling jitter. Under an
  injected clock that jitter is under host control, so a host verifying deadline behaviour
  SHOULD set the tolerance to `0`; left at its default it masks exactly the deadline
  discrepancies a virtual clock is introduced to expose.
- [EXEC-002] AC4 becomes newly observable. Under wall time, two transitions becoming due in
  the same instant is rare, and the all-immediate fast path's declaration order is hard to
  distinguish from the general path's enablement order. A virtual clock makes both
  reproducible. This does not change [EXEC-002] — the tie-break is already specified — but a
  conformance suite running on a virtual clock MUST NOT pin fast-path order for a net that
  takes the general path, or the reverse.

**Acceptance Criteria:**
1. With no clock supplied, every existing timing test passes unchanged.
2. Two executors in one process on two independent injected clocks do not observe each
   other's time; advancing one does not advance the other.
3. A net containing `delayed(d)` driven by a host-advanced clock reaches quiescence without
   `d` elapsing in real time.
4. A wait that completes spuriously does not cause a transition to fire before its earliest
   bound.
5. A wait aborted during shutdown completes rather than failing, and the executor terminates
   per [ENV-013] with no escaping failure. Where the seam carries an abort signal, a wait that
   *loses* to a wake-up is aborted too: after many idle waits on a suspending clock, the number
   of registrations that clock holds on the executor's signals does not grow.
6. Under an injected clock with deadline tolerance `0`, a `Deadline` transition is reaped at
   exactly its bound.
7. A net with a boundary already due and nothing in flight advances on the next cycle rather
   than waiting, under an injected clock as under the default one, in every backend.
8. **The wake-up path survives injection.** Under an injected clock, each of a completing
   in-flight action, an injected external event, a **drain** and a close wakes the wait without
   the interval being waited out — as each does by default. An implementation that silences its
   own wake-up satisfies this only if its readiness predicate observes every one of them,
   lifecycle changes included.
9. **The default path pays nothing measurable.** With no clock supplied, the executor's
   hot-path benchmarks ([PERF-020], [PERF-021], [PERF-041]) show no regression beyond noise
   against the same net before the seam existed. The firing clock is read on every
   orchestrator cycle, so an unconditional indirection through a host-supplied abstraction is
   not an acceptable default; the no-clock path MUST stay as direct as it was, in the spirit
   of [PERF-010].
10. **A coarse clock is not a broken clock.** A host clock whose readings are constant across
    several consecutive cycles — millisecond-derived, or replay-derived — drives a net
    containing `delayed`, `window` and `deadline` transitions to the same outcome as a
    strictly increasing clock.
11. **Reentrant admission.** With a clock installed, `inject()` called from inside the wait
    enqueues without being applied there, and the tokens appear in the following cycle's
    external-events phase in the order a default run would have admitted them. A host that
    injects and returns proceeds normally; the run does not deadlock, and the hazard of
    awaiting the admission signal in that position is stated on the API rather than left to be
    discovered. Likewise, an in-flight action's future completed from inside the wait is admitted
    in the following cycle's completion phase, and its outputs appear there, not at the call.
12. **Seed determinism is reachable and documented.** Two replays on the same host clock,
    seeded through the implementation's clock-stamped seed path, produce identical token
    timestamps in the initial marking; the documentation states that the default token
    constructor does not give this.
13. **Every executor-stamped token follows the clock.** Under an injected clock, tokens produced
    by `ctx.output`, by a raw-value injection, and by an action-timeout recovery output all carry
    timestamps from the injected epoch clock, not from wall time.
14. **Run identifiers survive a coarse or repeated clock.** Two executors constructed at the same
    injected instant carry different run identifiers — that half is the MUST. Reproducibility is
    the SHOULD: where an implementation meets it, a run replayed from the same construction order
    carries the same identifier. A per-process counter satisfies the MUST unconditionally and the
    SHOULD within a process; the two are not jointly satisfiable *across* processes by a counter
    alone, and this criterion does not ask for that.
15. **An absent boundary suspends.** A clock given an *infinite* interval suspends rather than
    returning, on the synchronous and asynchronous paths alike, and a net whose orchestrator is
    parked on an in-flight action reaches quiescence on a **single-threaded** runtime without the
    executor spinning. Every clock the implementation itself ships, and every clock in its own
    documentation, satisfies this.

**Depends on:** [TIME-010], [TIME-011], [TIME-013], [CORE-011], [CORE-072], [EXEC-001],
[EXEC-002], [CONC-010], [ENV-003], [ENV-004], [ENV-005], [ENV-013], [IO-013], [MOD-010], [PERF-010], [PERF-020],
[PERF-021]
**Implementation status:** The contract is settled; the host-facing API is **not yet frozen** and
its names and signatures may still move. **Java** (`ExecutionEnvironment`: `nanoTime` / `now` /
`awaitWork`, both executors), **TypeScript** (`Clock`: `now` / `epochNow` / `sleep`, plus
`systemClock()` and `seedToken()`, both executors) and **Rust** (`ExecutorClock`: `now_ms` / `epoch_ms` /
`await_work` / `await_work_async`, plus `SystemClock`, `ManualClock`, `seed_token()` and
`ExecutorOptions::clock`, both backends) expose the seam; the default path in each reads the real
clocks directly, with no indirection. Signatures and units differ by idiom (nanoseconds, float
milliseconds, `Instant` versus a number); the semantics above are what is held in common. Only
**TypeScript**'s seam carries a listener-style abort signal, so only it owes contract 4's per-wait
scope: each wait gets its own `AbortController`, aborted when the race settles and on `close()`,
and the no-clock fast path allocates none. Java's wait is a call that returns and Rust's a future
that is dropped, so neither retains anything for an abandoned wait. For Rust that is checked, not
assumed: the clock's async wait is one arm of the idle-cycle `select!`, built fresh each cycle
and dropped in place when it loses, the executor keeps no other reference to it, and there is no
listener list for a wait to be forgotten on; a test on both backends counts live wait futures —
each holding the waker it was polled with — across repeated idle cycles and finds none surviving
into the next. **Java**'s `awaitWork` cannot throw `InterruptedException`, so its interrupt
contract is on the flag ([EXEC-041]): the executor calls it with the flag clear and reads the
flag when it returns, a host that blocks interruptibly catches, re-interrupts and returns, and a
flag set on return ends the run `INTERRUPTED`. **Python** deliberately
exposes no seam: a Python-implemented clock would put a GIL acquisition on every orchestrator
cycle, so a Rust-side replay clock configured from Python is the intended shape if one is ever
wanted.

AC#13 is the criterion most easily missed on a partial implementation: an executor may route
`ctx.output` and raw-value injection through the epoch clock and still mint action-timeout recovery
tokens ([IO-013]) at wall time, because that path often constructs tokens somewhere other than the
output collector. An implementation claiming this requirement SHOULD carry a test for all three
origins.
**Test derivation:** Drive a net containing `delayed`, `window` and `deadline` transitions
from a host clock that advances only when asked; assert firing order and deadline reaping
match a wall-clock run of the same net, and that the run completes in negligible real time.
Run two such executors concurrently on independent clocks and assert neither observes the
other's advances. Assert a spurious wait completion fires nothing early, and that aborting
mid-wait terminates cleanly per [ENV-013].
