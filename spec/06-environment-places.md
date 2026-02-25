# 06 — Environment Places

This document specifies external event injection via environment places and long-running mode.

---

## Environment Place Declaration

#### ENV-001: Environment Place Wrapper

**Priority:** MUST

An environment place is a marker wrapper around a regular place that designates it as an external event injection point. Tokens can be injected into environment places from outside the executor.

**Acceptance Criteria:**
1. An environment place wraps a regular place.
2. The underlying place's name and type are accessible.
3. Environment places are registered with the executor at construction time.

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
2. Future completes with false/error if executor is closed.

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
**Test derivation:** Start executor in long-running mode; wait for quiescence; inject token; verify processing within milliseconds.

---

#### ENV-006: inject() Rejection on Closed Executor

**Priority:** MUST

If the executor has been closed (execution completed or explicitly shut down), inject() returns an error or false rather than silently dropping the token.

**Acceptance Criteria:**
1. After executor closes, inject() returns error/false.
2. No token is silently lost.

**Test derivation:** Run executor to completion; call inject(); verify error returned.

---

## Long-Running Mode

#### ENV-010: Long-Running Mode

**Priority:** MUST

In long-running mode, the executor does NOT terminate at quiescence (when no transitions are enabled and none are in-flight). Instead, it waits for external events that may enable new transitions.

**Acceptance Criteria:**
1. Long-running flag is set at executor construction.
2. Executor reaches quiescence but does not terminate.
3. Injecting a token resumes execution.
4. Executor terminates only when explicitly closed.

**Test derivation:** Long-running executor; all transitions fire; verify executor still running; inject token; verify new transition fires; close executor; verify termination.

---

#### ENV-011: Explicit Close

**Priority:** MUST

A long-running executor can be explicitly closed, causing it to terminate after processing any remaining in-flight actions.

**Acceptance Criteria:**
1. close() method signals the executor to shut down.
2. In-flight actions are allowed to complete before termination.
3. After close(), inject() returns error/false.

**Test derivation:** Long-running executor with in-flight action; call close(); verify action completes; verify executor terminates.

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
