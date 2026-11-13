import Libpetri.Spec.Text

requirement_text TIME_015
  id "TIME-015"
  title "Injectable Clock"
  priority SHOULD
  kind A
  body r#"An implementation SHOULD let a host supply the executor's time source. The seam is **per
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

The core of the contract below, in the terms of the glossary:

⟦s1|*While* an executor runs on an injected clock, successive readings of its firing clock *shall* be non-decreasing.⟧

⟦s2|*When* the executor's wait completes, the executor *shall* re-check its boundary conditions before it fires any transition, so an armed transition *shall not* fire before its earliest bound because a wait completed early ([TIME-010]).⟧

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
3. **Spurious completion permitted.** The wait MAY complete early and for no reason. ⟦s3|The
   executor MUST re-check its boundary conditions and MUST NOT treat "the wait completed" as
   "the boundary is reached".⟧
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
firing, including the recovery outputs it mints when an action timeout fires ([IO-013]) and
tokens minted from a raw value on injection. A token a `ForwardInput` deposits on that path is not
synthesised: it is the consumed token itself and keeps its `created_at` ([IO-014]). Only a token the **host itself** constructs, and
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
6. Under an injected clock with deadline tolerance `0`, a `Deadline` transition is reaped on the
   first cycle whose elapsed time is strictly greater than its bound, and not on a cycle that
   observes exactly its bound ([TIME-013]).
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
    several consecutive cycles (millisecond-derived, or replay-derived) drives a net
    containing `delayed`, `window` and `deadline` transitions to the same outcome as the same
    clock with each repeated reading taken once: a repeated reading is not a time step. The
    criterion claims no more than that. A clock that advances in steps wider than a window can
    pass the window unseen, so a coarse clock is not claimed to reach the outcome of a finer one.
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
    by `ctx.output`, by a raw-value injection, and by a minted action-timeout recovery output all
    carry timestamps from the injected epoch clock, not from wall time. A forwarded recovery token
    keeps the `created_at` of the token it forwards ([IO-014]).
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
mid-wait terminates cleanly per [ENV-013]."#
