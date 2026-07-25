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
the returned marking is an owned, independent copy. This backs checkpoint-saver patterns (e.g. a
periodic external persistence of in-flight state) without interrupting the run.

**Acceptance Criteria:**
1. `snapshot()` may be called at any time while the executor is running.
2. The executor services the request within one orchestrator cycle and keeps running afterwards.
3. The returned marking is an owned copy, independent of subsequent executor state.
4. `snapshot()` is rejected (error / `None`) once the executor has been drained or closed.

**Depends on:** [ENV-010]
**Status:** Proposed
**Implementation status:** Rust (`ExecutorSignal::Snapshot` + `ExecutorHandle::snapshot`) and Python
(`ExecutorHandle.snapshot`) implemented; Java/TypeScript pending.
**Test derivation:** Start a long-running net; call `snapshot()` mid-execution; verify the returned
marking reflects current state and the executor continues; call after `close()` and verify rejection.

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
