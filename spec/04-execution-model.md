# 04 — Execution Model

This document specifies the orchestrator loop, scheduling, token consumption, output validation, failure handling, and quiescence detection.

---

## Orchestrator Loop

#### EXEC-001: Orchestrator Loop Steps

**Priority:** MUST

The executor runs a loop with the following steps, in order:

1. **Process completions** — collect outputs from actions that have finished; validate against output specs; deposit produced tokens into marking; emit events.
2. **Process external events** — dequeue and apply externally injected tokens (see [ENV-003]).
3. **Update enablement** — re-evaluate which transitions are enabled based on current marking. Only transitions affected by token changes need re-evaluation (see [CONC-004]).
4. **Enforce deadlines** — check enabled transitions with finite deadlines; disable those past their latest bound.
5. **Fire ready transitions** — among enabled transitions whose elapsed time >= earliest bound, sort by priority (then FIFO), and fire in order.
6. **Await work** — if no transitions are ready and none are in-flight, wait for a completion, external event, or timer.

**Acceptance Criteria:**
1. Steps execute in the specified order each cycle.
2. No transition fires before completions are processed.
3. External events are applied before enablement updates.

**Test derivation:** Trace execution of a simple net; verify step ordering via event log.

---

## Scheduling

#### EXEC-002: Priority-Based Firing Order

**Priority:** MUST

When multiple transitions are ready to fire (enabled and timing satisfied), they are sorted by:
1. **Priority** — descending (higher priority fires first)
2. **Enablement time** — ascending (FIFO; earliest enabled fires first among equal priority)

**All-immediate fast path.** When every transition is `Immediate` and all priorities are equal, backends fire straight from the enablement bitmap in ascending declaration order and do not read the enablement timestamp at all — including when two ready transitions carry different timestamps because one was held across cycles while in flight. This is deliberate, and every backend takes the path under the same condition. The sort above describes the general path.

**Acceptance Criteria:**
1. Transition with priority 10 fires before transition with priority 5.
2. Two transitions with equal priority on the general path: the one enabled first fires first.
3. Equal priority **and** equal enablement time (transitions enabled in the same
   orchestrator cycle share one enablement timestamp): the tie breaks by ascending
   declaration order, so the order is fully deterministic.
4. Every executor backend produces the **identical** ready order for the same net
   and marking. Enablement-time order is the general-path order; on the
   all-immediate single-priority fast path every backend fires in declaration
   order instead. Backends MUST NOT differ in which order they use, nor in the
   condition that selects it.

**Test derivation:** Three transitions with priorities 5, 10, 5; enable all simultaneously; verify firing order: P10, then P5 (first enabled), then P5 (second enabled). For AC4, on a net that takes the general path (two priority levels, or one non-`Immediate` transition), enable two equal-priority transitions in different cycles with declaration order opposite to enablement order and verify every backend follows enablement order; on an all-immediate single-priority net, verify every backend fires in declaration order.

---

#### EXEC-003: Competitive Conflict Resolution

**Priority:** MUST

When multiple transitions compete for the same input tokens, the highest-priority ready transition fires first and consumes the tokens. Lower-priority transitions become disabled if their inputs are no longer satisfied.

**Acceptance Criteria:**
1. Two transitions sharing input place P; T1 (P=10) and T2 (P=5); one token in P; T1 fires; T2 disabled.
2. If T1 is not ready (timing not satisfied), T2 may fire.

**Test derivation:** Two competing transitions; verify only highest priority fires when only 1 token available.

---

## Token Consumption

#### EXEC-010: FIFO Token Consumption

**Priority:** MUST

When a transition fires, it consumes tokens from the oldest-first (FIFO) end of each input place's queue. The number of tokens consumed is determined by the input cardinality's `consumptionCount(available)`.

**Acceptance Criteria:**
1. Tokens added in order A, B, C; One consumes A.
2. Exactly(2) consumes A, B.
3. All consumes A, B, C.

**Depends on:** [CORE-013], [IO-007]
**Test derivation:** Add tokens with identifiable values; fire transition; verify consumed tokens match FIFO order.

---

#### EXEC-011: ~~Guarded Token Consumption~~ (Removed)

**Status:** Removed

Guarded consumption was removed together with the guard predicate itself (see
[IO-006]). With no per-token value predicate in the input specification, token
selection is purely positional: [EXEC-010] (FIFO order) and [IO-007]
(`consumptionCount`) fully determine which tokens a firing consumes. The one
remaining per-token selection rule is the ν-name correlation of [NU-020], which is
specified there and is structural, not a value predicate.

Retained as a tombstone for traceability; excluded from the active requirement count.

---

#### EXEC-012: Read Arc Peek

**Priority:** MUST

When a transition fires, read arc values are provided to the action without consuming the tokens. The oldest token in the read place is peeked.

**Acceptance Criteria:**
1. Read place has tokens A, B; action receives A; both A and B remain after firing.

**Depends on:** [CORE-032]
**Test derivation:** Read place with 2 tokens; fire transition; verify both tokens remain; verify action received first.

---

#### EXEC-013: Reset Arc Execution

**Priority:** MUST

When a transition fires, all tokens are removed from each reset place. This happens during the firing step, before the action executes. The removal is tracked for clock restart detection (see [TIME-012]).

**Acceptance Criteria:**
1. Reset place with 5 tokens → all removed.
2. Reset place empty → no error.
3. If the reset place is also an input place for another enabled transition, that transition's clock restarts.
4. Reset draining occurs **after** read-arc peeking within the same firing: a
   transition with a read arc and a reset arc on the same place observes the
   pre-reset front token via `ctx.read()` (see [EXEC-012], [CORE-032]). The
   overall in-firing order is: input consumption, then read peeks, then reset
   draining.

**Depends on:** [CORE-034], [EXEC-012], [CORE-032]
**Test derivation:** Transition with reset on place with 3 tokens; verify all removed; verify clock restart for affected transitions.

---

## Output Handling

#### EXEC-020: Output Token Deposition

**Priority:** MUST

After an action completes, the executor deposits produced tokens into the marking according to the output specification. Each token is added to the end of the target place's FIFO queue.

**Acceptance Criteria:**
1. Action produces token with value V to place P; V appears at end of P's queue.
2. Multiple tokens to same place are added in order.

**Test derivation:** Action produces 3 tokens to P; verify all 3 appear in order.

---

#### EXEC-021: Output Spec Validation

**Priority:** MUST

After depositing tokens, the executor validates that the produced tokens satisfy the declared output specification (see [IO-015]).

**Acceptance Criteria:**
1. And: all children received tokens → valid.
2. Xor: exactly one child received tokens → valid; when several overlapping branches match, the subsumption tie-break of [IO-015] resolves them before a violation is raised.
3. Violation → failure event emitted.
4. Validation is applied by every executor backend a language ships, not only the reference one.

**Depends on:** [IO-011], [IO-012], [IO-015]
**Test derivation:** Xor output with tokens to 2 branches → violation event.

---

#### EXEC-022: Action Timeout Handling

**Priority:** MUST

When a transition's output specification includes a Timeout node, the executor races the action against the timeout duration:
- Action completes first → normal output validation.
- Timeout fires first → the firing is abandoned (the action is stopped where the runtime can; see [IO-013]); the timeout child output receives tokens; ActionTimedOut event emitted.

**Acceptance Criteria:**
1. Action completes in 50ms with 100ms timeout → normal completion.
2. Action takes 200ms with 100ms timeout → timeout branch activated; ActionTimedOut event.
3. ForwardInput in timeout child → **every** token consumed from the `from` place is forwarded to the `to` place, one output token per consumed token, in consumption order ([IO-014]).
4. Output the action wrote before the budget expired is discarded, not merged with the timeout branch ([IO-013] AC5).

**Depends on:** [IO-013], [IO-014], [EVT-009]
**Test derivation:** Slow action with timeout; verify timeout branch tokens and event.

---

## Failure Handling

#### EXEC-030: Action Failure

**Priority:** MUST

If an action throws an exception or returns an error, the executor:
1. Emits a TransitionFailed event with error details.
2. Does NOT restore consumed input tokens (no rollback).
3. The transition is no longer in-flight.
4. Execution continues with remaining transitions.

**Acceptance Criteria:**
1. Failing action → TransitionFailed event with error message and type.
2. Consumed tokens are lost (not returned to input places).
3. Other transitions continue to fire.

**Depends on:** [EVT-007]
**Test derivation:** Action throws; verify failure event; verify consumed tokens not restored; verify net continues.

---

#### EXEC-031: No Rollback

**Priority:** MUST

The engine does not provide transaction rollback. Once tokens are consumed by a firing transition, they are not restored if the action fails. This is a deliberate design choice — rollback would require complex compensation logic and conflicts with the async nature of actions.

**Acceptance Criteria:**
1. Failed action → consumed tokens permanently removed.

**Test derivation:** Fire transition consuming token; action fails; verify token not in any place.

---

## Quiescence

#### EXEC-040: Standard Quiescence

**Priority:** MUST

When no environment places are registered, the executor terminates when ALL of the following hold:
1. No transitions are enabled.
2. No transitions are in-flight (executing actions).
3. No external events are pending.

The final marking is returned.

**Acceptance Criteria:**
1. Simple chain A→B→C: executor runs to completion; returns marking with token in C.
2. Parallel branches: waits for all in-flight actions before terminating.

**Test derivation:** Linear chain of 5 transitions; verify executor returns marking with token at end.

---

#### EXEC-041: Execution Result

**Priority:** MUST

When execution completes, the executor returns the final marking (token distribution across all places).

**Acceptance Criteria:**
1. Return value contains the token state after quiescence.
2. All places with tokens are represented.

**Test derivation:** Run net; inspect returned marking; verify expected token distribution.

---

## Stale Detection Pattern

#### EXEC-050: Timestamp-Based Stale Detection

**Priority:** SHOULD

Transitions can implement stale detection by comparing timestamps. A transition reads a "latest search timestamp" via a read arc and compares it with the consumed token's timestamp to determine if the data is still current.

This is a **usage pattern**, not a built-in feature — the engine provides the primitives (read arcs, token timestamps) and the action logic performs the comparison.

**Acceptance Criteria:**
1. Read arc provides timestamp from shared state.
2. Action can compare consumed token timestamp with read value.
3. Stale data detected → action can route to discard branch (via XOR output).

**Depends on:** [CORE-032], [CORE-010]
**Test derivation:** CommitProductList pattern: read LATEST_SEARCH_TIMESTAMP; compare with consumed token; discard if stale.
