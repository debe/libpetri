# 06 — Environment Places

This document specifies external event injection via environment places, implicit long-running behavior, and executor lifecycle (drain/close).

---

## Environment Place Declaration

#### ENV-001: Environment Place Wrapper

**Priority:** MUST

An environment place is a marker wrapper around a regular place that designates it as an external event injection point. Tokens can be injected into environment places from outside the executor.

**Acceptance Criteria:**
1. An environment place wraps a regular place.
2. The underlying place's name and type are accessible.
3. Environment places are registered with the executor at construction time.

**Note (orthogonality with interface places):** Environment places (per this requirement) and interface places (ports per [MOD-003]) are **orthogonal concepts**. An environment place marks a *world boundary* — the seam where the engine accepts injections from outside the executor. An interface place marks a *composition boundary* — the seam where two net fragments are wired together at build time. A single underlying place MAY simultaneously be an environment place and a port: the resulting flat net (after composition per [MOD-020]) treats it as a regular place that the executor accepts injections into and that arcs from both fragments reference. Where this dual role is used (e.g., a subnet's input port is also the host's external event injection point), the environment-place registration applies after composition, on the post-composition place identity.

**Test derivation:** Create environment place wrapping place "UserInput"; verify name and type accessible.

---

#### ENV-002: Environment Place Registration

**Priority:** MUST

Environment places must be registered with the executor before execution begins. The executor maintains a set of registered environment places.

**Acceptance Criteria:**
1. Executor builder accepts environment place registrations.
2. Only registered environment places accept injections.
3. Attempting to inject into a non-environment place returns an error.

**Test derivation:** Register 3 environment places; inject into registered one → success; inject into unregistered → error.

---

## Token Injection

#### ENV-003: inject() Thread Safety

**Priority:** MUST

The inject operation is safe to call from any thread, task, or coroutine — not just the orchestrator thread. It enqueues the token for processing on the next orchestrator cycle.

**Acceptance Criteria:**
1. inject() can be called from a different thread than the orchestrator.
2. Multiple concurrent inject() calls do not cause data races.
3. Injected tokens are eventually processed by the orchestrator.

**Test derivation:** Spawn 10 threads; each injects a token; verify all 10 tokens processed.

---

#### ENV-004: inject() Completion Semantics

**Priority:** MUST

The inject operation returns a future/promise that completes when the token has been added to the marking and enablement has been recalculated. The return value indicates whether the injection was accepted.

**Acceptance Criteria:**
1. Future completes with true/success when token is in marking.
2. Future completes with false/error if executor is closed or draining.

**Test derivation:** Inject token; await future; verify token in marking after future resolves.

---

#### ENV-005: inject() Wake-Up

**Priority:** MUST

Injecting a token wakes the orchestrator from idle immediately. The orchestrator does not need to wait for a timer or poll.

**Acceptance Criteria:**
1. Orchestrator is idle (no ready transitions).
2. External inject() call wakes orchestrator.
3. Token is processed promptly (within one cycle).

**Depends on:** [CONC-010]
**Test derivation:** Start executor with environment places; wait for quiescence; inject token; verify processing within milliseconds.

---

#### ENV-006: inject() Rejection on Closed or Draining Executor

**Priority:** MUST

If the executor has been closed, is draining, or execution has completed, inject() returns an error or false rather than silently dropping the token.

**Acceptance Criteria:**
1. After executor closes, inject() returns error/false.
2. After drain(), inject() returns error/false.
3. No token is silently lost.

**Test derivation:** Run executor to completion; call inject(); verify error returned. Call drain(); inject(); verify error returned.

---

## Implicit Long-Running Behavior

#### ENV-010: Implicit Long-Running Behavior

**Priority:** MUST

When environment places are registered with the executor, the executor does NOT terminate at quiescence (when no transitions are enabled and none are in-flight). Instead, it waits for external events that may enable new transitions. This behavior is derived from the presence of environment places — no explicit flag is needed.

When no environment places are registered, the executor terminates at quiescence per [EXEC-040].

**Acceptance Criteria:**
1. Registering environment places causes executor to wait at quiescence instead of terminating.
2. No explicit long-running flag exists on the executor API.
3. Executor with environment places does not terminate at quiescence.
4. Executor without environment places terminates at quiescence.
5. Injecting a token resumes execution from quiescence.

**Test derivation:** Executor with environment places; all transitions fire; verify executor still running; inject token; verify new transition fires; drain executor; verify termination.

---

## Executor Lifecycle

#### ENV-011: Graceful Drain

**Priority:** MUST

The executor provides a `drain()` method that signals graceful shutdown. After `drain()` is called:
1. New `inject()` calls are rejected (return error/false).
2. Already-queued external events are processed normally.
3. In-flight actions are allowed to complete.
4. The executor terminates when quiescent (no enabled transitions, no in-flight, no pending events).

For executors without environment places, `drain()` is a no-op since the executor already terminates at quiescence.

**Acceptance Criteria:**
1. `drain()` method is available on the executor.
2. After `drain()`, `inject()` returns error/false.
3. Already-queued events are processed before termination.
4. In-flight actions complete before termination.
5. Executor terminates when quiescent after drain.

**Depends on:** [ENV-010]
**Test derivation:** Executor with env places; inject tokens; call drain(); verify queued events processed; verify new inject rejected; verify termination at quiescence.

---

#### ENV-012: Event-Driven Workflow Pattern

**Priority:** SHOULD

The engine supports event-driven workflow patterns where ~10 environment places represent external event sources (activity signals, data streams, tool requests, state changes, etc.) and the executor runs indefinitely, processing events as they arrive.

**Acceptance Criteria:**
1. 10+ environment places can be registered simultaneously.
2. Injection from multiple concurrent sources works correctly.
3. The net reacts to each injection by enabling relevant transitions.

**Depends on:** [ENV-001], [ENV-002], [ENV-010]
**Test derivation:** Build a net with 10 environment places; inject events from multiple sources; verify correct transition firing.

---

#### ENV-013: Immediate Close

**Priority:** MUST

The executor provides a `close()` method for immediate shutdown. After `close()` is called:
1. New `inject()` calls are rejected (return error/false).
2. Queued external events are discarded (completed with false).
3. In-flight actions are allowed to complete.
4. The executor terminates after in-flight actions complete.

Calling `close()` after `drain()` escalates from graceful to immediate shutdown.

**Acceptance Criteria:**
1. `close()` signals immediate shutdown.
2. Queued events are drained with false (not processed).
3. In-flight actions complete before termination.
4. `inject()` returns error/false after close.

**Depends on:** [ENV-010]
**Test derivation:** Executor with in-flight action; call close(); verify action completes; verify queued events discarded; verify executor terminates.

---

#### ENV-014: Mid-Execution Marking Snapshot

**Priority:** SHOULD

The executor exposes a `snapshot()` operation that returns a point-in-time copy of the current
marking **without affecting lifecycle** — unlike `drain()` ([ENV-011]) and `close()` ([ENV-013]),
it neither stops nor pauses execution. The request is serviced within one orchestrator cycle and
the returned marking is an owned, independent copy. This backs observation and checkpoint-saver
patterns (e.g. periodic external persistence of the marking) without interrupting the run.

**Observation is not a restore point.** A marking taken while any work is in flight is a valid
*observation* but is **not** sufficient to resume from. **Work in flight** means either of two
things: an **action** that has started and not completed, or an **external event the executor has
accepted but not yet injected** ([ENV-003], [ENV-004]). Three reasons, of different severity:

1. A firing whose action is in flight has already consumed its inputs ([EXEC-031], no rollback)
   and has not yet deposited its outputs. The snapshot captures neither, so those tokens are
   simply absent from it.
2. More fundamentally, the correspondence between an in-flight action and the **external work it
   started** — a remote call, a task handle, a cancellation scope — has no representation in the
   marking at all. A snapshot can therefore restore every token faithfully and still resume a net
   that has forgotten it has work outstanding. No amount of fidelity in the marking closes this;
   it is outside the marking by construction.
3. An accepted external event is the same conservation gap from the other side. The host has
   handed the token over — `inject()` returned, or was never going to be awaited ([TIME-015]'s
   admission rule forbids awaiting it from inside a host wait) — and the executor has not yet
   reached the external-events phase that places it ([EXEC-001] step 2). The token is in neither
   the host's hands nor the marking. A host that persists such a snapshot as a restore point and
   shuts down has lost it, and nothing in the snapshot says so.

Consequently a snapshot offered as a restore point for [CORE-073] MUST be taken at a moment when
no work is in flight — no action, and no accepted external event still awaiting injection. An
implementation MUST make that condition visible to the caller rather than leaving it implicit:
either by refusing a restore-point snapshot while work is in flight, by reporting alongside the
returned marking whether it was taken with none, or by offering a mode that defers servicing
until the executor next reaches that state. Which of the three is an implementation choice;
silently returning a marking the caller cannot tell is unusable for restore is not. Whichever is
chosen MUST cover **both** kinds of work and MUST be decided at the same instant the marking is
captured: an indication computed from the actions alone reports a restore point across exactly
the gap in (3).

**Two conforming shapes for the pending-event half.** An implementation whose `snapshot()` reads
the marking without passing through the orchestrator's event queue MUST fold "an accepted event
is still queued" into its indication. An implementation whose snapshot request travels the *same
ordered channel* as injections serves every injection accepted before it first, so at the moment
the marking is captured no earlier-accepted event can still be pending: it conforms by
construction, with the token **in** the marking rather than flagged. The two differ in what the
snapshot contains and agree on the property that matters — a token the executor has accepted is
never absent from a snapshot that reports itself a restore point.

**A snapshot requested from inside an action is a snapshot with work in flight.** The firing that
is running the caller has consumed its inputs and not deposited its outputs, which is reason (1)
exactly. A firing therefore counts as in flight **from the moment its inputs are consumed** — not
from the moment its action first suspends — so the window covers the action's synchronous prefix
and any event-store callback the firing triggers, and the indication MUST report work in flight
throughout it. Where actions are invoked inline on the orchestrator's own thread, such a request
additionally cannot be queued for the orchestrator to service, because the orchestrator *is* the
caller and would park waiting for itself — with no error, no timeout and nothing to indicate what
happened, the same self-deadlock [TIME-015] describes for an awaited `inject()`. An
implementation with that shape MUST detect the case and capture directly on the calling thread,
after whatever synchronisation of internal token storage any other marking read performs.

**Acceptance Criteria:**
1. `snapshot()` may be called at any time while the executor is running.
2. The executor services the request within one orchestrator cycle and keeps running afterwards.
3. The returned marking is an owned copy, independent of subsequent executor state.
4. `snapshot()` is rejected (error / `None`) once the executor has been drained or closed.
5. A snapshot taken while an action is in flight is distinguishable by the caller from one taken
   with none in flight — by refusal, by an accompanying indication, or by the operation having
   waited for quiescence.
6. A net whose only marked place feeds a transition with an in-flight action yields a snapshot in
   which those consumed tokens are absent, and the caller can determine that the snapshot is not
   a valid restore point.
7. **An accepted event is never silently absent.** A snapshot requested after an external event
   has been accepted and before it has been injected either contains that event's token or is
   distinguishable as not a valid restore point. It never omits the token while reporting one.
8. **From inside an action.** `snapshot()` requested by a running action — from its synchronous
   prefix as well as after it has suspended — does not park the orchestrator against itself. Its
   result is either distinguishable as not a valid restore point, or **deferred until that firing
   has settled**, in which case it describes the settled instant — outputs deposited, no token
   missing — and may truthfully be a restore point. What it MUST NOT be is a result that omits the
   firing's consumed inputs *and* reports a restore point. An implementation that defers MUST NOT
   be blocked on from the orchestrator's own thread of control, since the reply cannot arrive until
   the action returns.

**Depends on:** [ENV-003], [ENV-004], [ENV-010], [EXEC-001], [EXEC-031], [EXEC-040], [CORE-073],
[TIME-015]
**Implementation status:** AC1–AC8 in all four. `snapshot()` returns a result carrying the marking
**and** an in-flight indication, read in the same operation that captures the marking — a
separately-queryable flag would be read at a different instant, which is the race AC5 closes. The
field keeps its name (`actionInFlight` / `action_in_flight`) and means **work in flight: an action,
or an accepted but un-injected external event**. **TypeScript** and **Java** read the marking
outside the event queue, so they OR a pending-external-queue check into the flag at the instant
of capture; **TypeScript** counts a firing as in flight from consumption, and **Java**, whose
actions run inline, captures directly when called on the orchestrator thread (the precompiled
executor synchronising its ring buffers first, as its `marking()` does) and reports the flag
true. A Java request from a *foreign* thread waits for the orchestrator to serve it, bounded by a
2 s best-effort cap so a caller is never parked behind a blocking inline action; a request that
was **not served** within the cap returns the last published marking with the flag **forced
true**, whatever flag that older marking was published with — since then an accepted event may
have been injected and consumed by the very firing that is blocking, so an unserved request is
never a restore point (AC7). Both Java executors compute the published flag with one shared
expression, and an event that will be *refused* — queued behind a run that has already
terminated or closed, so `inject` answers `false` and the host keeps the token — was never
accepted and does not count. **Rust** and **Python** need neither: injections and the snapshot request share one FIFO
channel, so every earlier injection is already in the marking when the snapshot is served, and a
request is a non-blocking send whose reply arrives from the orchestrator's next cycle — an
**asynchronous** action that awaits it is, correctly, reported in flight, from its first statement
as well as after it has suspended (in Python the awaitable binds to the loop `start_async` /
`run_async` captured, since an action's thread has no running loop). As with `inject()` under
[TIME-015], that reply MUST NOT be *blocked on* from the orchestrator's own thread of control,
and there are two such places: an `ExecutorClock` wait, and a **synchronous** action under
`run_async` / `start_async`, which runs inline in the orchestrator loop. Such an action may send
the request, but the orchestrator cannot serve it until the action returns, so blocking on the
reply hangs the run; and the reply, once it comes, describes the instant *after* that firing
settled — outputs deposited, no token missing, and therefore possibly a restore point. That is
AC8's deferred arm: in Rust and Python an asynchronous action gets the flagged result, and an
inline synchronous one gets the deferred one. Under `run_sync` there is no signal channel and the
case does not arise.

**Test derivation:** Start a long-running net; call `snapshot()` mid-execution; verify the returned
marking reflects current state and the executor continues; call after `close()` and verify rejection.
For AC5/AC6, gate a transition's action open, snapshot while it is in flight, and assert the caller
can tell the result apart from a snapshot taken at quiescence — then release the gate, snapshot
again at quiescence, and assert that one restores to an equivalent marking per [CORE-073]. For
AC7, inject without awaiting admission and snapshot in the same turn; assert the token is present
or the result is flagged, on every executor. Where a foreign caller's wait for the orchestrator
is bounded, also hold an inline action past that bound with an accepted event already consumed by
it, and assert the unserved result is flagged. For AC8, call `snapshot()` from an action's first
synchronous statement and assert it returns flagged; bound the test by the call returning, not by
patience, since the failure mode is a self-deadlock.

---

#### ENV-015: Immediate Termination

**Priority:** MAY

An implementation MAY provide an immediate-termination operation (`terminateNow()`) that stops the
orchestrator loop **without** waiting for in-flight actions, unlike `close()` ([ENV-013]) which lets
them complete. After it is invoked:
1. New `inject()` calls are rejected (return error / false), as after [ENV-013].
2. Queued external events are discarded (completed with false).
3. The loop stops at the end of its current cycle; it does NOT wait for in-flight actions, and their
   results are discarded rather than admitted to the marking.
4. In-flight actions keep running where the runtime cannot cancel them ([IO-013]); their consumed
   tokens are lost ([EXEC-031]).

It is an explicit escape hatch and MUST NOT be invoked implicitly by `close()`.

**Acceptance Criteria:**
1. `terminateNow()` stops the loop without awaiting an outstanding in-flight action.
2. The in-flight action's eventual output is not admitted to the marking.
3. `inject()` after `terminateNow()` returns error / false, does not hang.

**Depends on:** [ENV-013]
**Status:** Proposed
**Implementation status:** Java implemented; Rust/TypeScript/Python pending.
**Test derivation:** Start a net with a gated in-flight action; call `terminateNow()`; verify the loop
terminates without releasing the gate and the action's output never reaches the marking.

---

#### ENV-016: Observable Termination

**Priority:** MAY

An implementation MAY provide `awaitTermination(timeout)`, which blocks until the orchestrator loop
has finished its termination bookkeeping (pending `inject()` futures completed, `ExecutionCompleted`
emitted), returning whether termination was observed within the timeout. It returns promptly when the
loop was never started, and it MUST NOT itself be defeated by a failure in that bookkeeping (for
example a throwing event store).

Independently, run-with-timeout ([EXEC] `run(timeout)`) MAY expose a policy for what happens to the
loop when the caller's timeout expires: *abandon* (leave the loop running — the historical default,
rarely desirable) or *close* (stop it per [ENV-013]). The expiry of the caller's timeout MUST NOT
complete the loop's own result: an abandoned loop can still report its real final marking.

**Acceptance Criteria:**
1. `awaitTermination` returns false while the loop is still running, true once it has stopped.
2. `awaitTermination` returns promptly (true) if the loop was never started.
3. Under a *close* policy the loop is stopped on timeout; under *abandon* it keeps running.

**Depends on:** [ENV-013]
**Status:** Proposed
**Implementation status:** Java implemented; Rust/TypeScript/Python pending.
**Test derivation:** Run a net that will not quiesce with a short timeout under each policy; verify the
loop is stopped under *close* and still live under *abandon*, and that `awaitTermination` reports the
transition.
