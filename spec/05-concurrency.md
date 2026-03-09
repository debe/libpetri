# 05 — Concurrency

This document specifies the concurrency model: single-threaded orchestrator, async action dispatch, bitmap executor optimization, precompiled flat-array executor, and wake-up mechanisms.

---

## Single-Threaded Orchestrator

#### CONC-001: Orchestrator Thread Ownership

**Priority:** MUST

All marking state (token queues, enablement flags, enabled-at timestamps) is owned and mutated exclusively by a single logical orchestrator thread. No locking or synchronization is needed for marking access.

**Acceptance Criteria:**
1. Marking has no locks, mutexes, or atomic operations.
2. Only the orchestrator thread reads/writes the marking.
3. Action completion results are communicated back via a thread-safe mechanism, then applied on the orchestrator thread.

**Test derivation:** Inspect marking implementation for absence of synchronization primitives.

---

#### CONC-002: Action Execution on Separate Task Pool

**Priority:** MUST

Transition actions execute asynchronously on a separate task pool (virtual threads, tokio tasks, or promise microtasks). The orchestrator never blocks waiting for an action to complete.

**Acceptance Criteria:**
1. Action execution does not block the orchestrator loop.
2. Multiple actions can execute concurrently.
3. The orchestrator continues processing other transitions while actions run.

**Test derivation:** Two transitions fire; both actions sleep 100ms; verify total time ~100ms, not ~200ms.

---

#### CONC-003: Happens-Before Guarantee

**Priority:** MUST

All writes performed by an action (output tokens, side effects) are visible to the orchestrator after the action's future/promise completes. The completion mechanism provides a happens-before edge.

**Acceptance Criteria:**
1. Action writes to output context; orchestrator reads output after completion; values are visible.
2. No stale reads possible.

**Test derivation:** Action stores complex object in output; verify orchestrator sees complete object.

---

## Bitmap Executor

#### CONC-004: Bitmap-Based Enablement Check

**Priority:** MUST

The primary executor uses precomputed bitmasks for O(1) enablement checking per transition (proportional to the number of machine words needed to represent all places).

Each transition has precomputed masks:
- **needs-mask**: bits set for all input + read places (all must have tokens)
- **inhibitor-mask**: bits set for all inhibitor places (none may have tokens)

Enablement check: `(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0`

**Acceptance Criteria:**
1. Enablement is checked via bitwise operations, not by iterating over arcs.
2. A transition with 3 inputs and 2 reads requires only 1-2 bitwise operations.
3. The check is O(W) where W = ceil(numPlaces / word_size).

**Test derivation:** Net with 100 places; verify enablement check performance is constant per transition.

---

#### CONC-005: Dirty Set Optimization

**Priority:** MUST

When tokens are added or removed from a place, only transitions affected by that place need re-evaluation. A precomputed reverse index maps each place to the set of transitions that reference it.

The dirty set is maintained as a bitmap: when a place changes, the executor sets the bits for all affected transitions. Each cycle, only dirty transitions are re-evaluated.

**Acceptance Criteria:**
1. Adding a token to place P only marks transitions connected to P as dirty.
2. Transitions not connected to P are not re-evaluated.
3. After re-evaluation, dirty bits are cleared.

**Test derivation:** Net with 50 transitions; add token to place connected to 3 transitions; verify only 3 transitions re-evaluated.

---

#### CONC-006: Lock-Free Completion Signaling

**Priority:** MUST

Action completions are communicated to the orchestrator via a lock-free mechanism (lock-free queue, mpsc channel, or similar). The hot path avoids contention on shared locks.

**Acceptance Criteria:**
1. Multiple actions completing simultaneously do not contend on a single lock.
2. Completion notification is O(1) per completion.

**Test derivation:** 10 actions complete near-simultaneously; verify no lock contention (measured via timing, not exceeding linear overhead).

---

#### CONC-007: Compiled Net Representation

**Priority:** MUST

The bitmap executor compiles the net into an integer-indexed representation where places and transitions are assigned stable numeric IDs (0-based). This enables array-based access instead of hash map lookups.

Precomputed data includes:
- Per-transition: needs-mask, inhibitor-mask, reset-mask
- Per-place: list of affected transition IDs (reverse index)
- Per-transition: cardinality checks (for Exactly/All/AtLeast requiring token count verification beyond presence)
- Per-transition: guard presence flags

**Acceptance Criteria:**
1. Places and transitions have stable numeric IDs.
2. All masks are precomputed at compilation time, not at each enablement check.

**Test derivation:** Compile a net; verify masks match expected bit patterns.

---

#### CONC-008: Multi-Phase Enablement

**Priority:** MUST

Enablement checking is a multi-phase process:
1. **Phase 1 — Bitmap presence check**: O(W) bitwise check against needs-mask and inhibitor-mask. Fast reject for most transitions.
2. **Phase 2 — Cardinality check**: For transitions with Exactly(n)/All/AtLeast(m), verify actual token counts meet thresholds.
3. **Phase 3 — Guard check**: For transitions with guard predicates, scan tokens for matching values.

Phases 2 and 3 are only reached if Phase 1 passes, minimizing work for most transitions.

**Acceptance Criteria:**
1. A transition with only One inputs and no guards is fully checked in Phase 1.
2. A transition with Exactly(5) input requires Phase 2 to verify token count.
3. A transition with a guard requires Phase 3 to scan tokens.

**Test derivation:** Mix of simple and complex transitions; verify correct enablement with minimal re-evaluation.

---

## Precompiled Flat-Array Executor

#### CONC-020: Precompiled Net Representation

**Priority:** SHOULD

The precompiled net extends the compiled net [CONC-007] by further compiling the net topology into flat arrays and operation sequences that eliminate virtual dispatch and hash map lookups from the hot path. The precompiled representation includes:
- Flat arrays of length T (transition count) for per-transition data: timing, priorities, enablement masks, operation sequences
- Opcode-based consume operation sequences per transition [CONC-021]
- Ring buffer token storage indexed by place ID [CONC-022]
- Priority-partitioned ready queues [CONC-023]
- Precomputed timing arrays [CONC-024]
- Sparse enablement masks [PERF-042]

The precompiled net is immutable after construction.

**Acceptance Criteria:**
1. Precompiled net is constructed from a compiled net or directly from a symbolic net.
2. All per-transition data is stored in parallel arrays indexed by transition ID.
3. No hash map lookups occur during execution.
4. The precompiled net is immutable — no mutation after compile().

**Depends on:** [CONC-007]
**Test derivation:** Compile a net; verify all arrays are correctly populated and match the symbolic net.

---

#### CONC-021: Opcode-Based Consume Operations

**Priority:** SHOULD

Each transition's input and reset arcs are compiled into a flat integer array of opcodes. During firing, the executor iterates the opcode array instead of pattern-matching on sealed arc types. Read arcs are compiled into a separate place-ID array.

Opcodes:
- `CONSUME_ONE(0) placeId` — consume one token from place
- `CONSUME_N(1) placeId count` — consume exactly N tokens
- `CONSUME_ALL(2) placeId` — consume all tokens
- `CONSUME_ATLEAST(3) placeId minimum` — consume at least N tokens (takes all)
- `RESET(4) placeId` — clear all tokens from place

**Acceptance Criteria:**
1. Each transition has a precompiled consume operation array.
2. Read arcs are compiled into a separate place-ID array (reads do not consume).
3. Firing a transition iterates the opcode array without type dispatch.
4. All five opcodes produce the same observable behavior as the corresponding arc types.

**Test derivation:** Compile a net with all arc types; fire transitions; verify token consumption matches bitmap executor.

---

#### CONC-022: Flat-Array Token Storage

**Priority:** SHOULD

Token storage uses ring buffers indexed by place ID for O(1) access. Each place has a dedicated ring buffer that preserves FIFO ordering [CORE-013] and grows dynamically when capacity is exceeded.

**Acceptance Criteria:**
1. Token access is O(1) by place ID — no hashing or map lookup.
2. FIFO ordering is preserved (oldest token consumed first).
3. Ring buffers grow dynamically when capacity is exceeded.
4. Token count per place is available in O(1).

**Depends on:** [CORE-013]
**Test derivation:** Add and consume tokens in various orders; verify FIFO ordering and correct counts.

---

#### CONC-023: Priority-Partitioned Ready Queues

**Priority:** SHOULD

Distinct priority values are sorted descending at compile time. Each priority level has its own FIFO queue. Transition selection scans priority levels in descending order and picks the first non-empty queue, giving O(L) selection where L is the number of distinct priority levels (typically 1–3).

Each transition maps to a priority index for O(1) ready-queue insertion.

**Acceptance Criteria:**
1. Distinct priority levels are precomputed and sorted descending.
2. Each priority level has a separate FIFO queue.
3. Transition selection is O(L) where L = distinct priority levels.
4. Within the same priority, FIFO ordering by enablement time is preserved.

**Depends on:** [EXEC-002]
**Test derivation:** Net with 3 priority levels; verify transitions fire in correct priority order with FIFO within each level.

---

#### CONC-024: Precomputed Timing Arrays

**Priority:** SHOULD

Timing constraints are precomputed into flat arrays at compile time to avoid virtual dispatch on timing types during execution:
- `earliestNanos[]` / `earliestMillis[]` — earliest firing time per transition
- `latestNanos[]` / `latestMillis[]` — latest firing time (MAX_VALUE if no deadline)
- `hasDeadline[]` — boolean flag per transition
- `allImmediate` — global flag: true if all transitions are immediate
- `anyDeadlines` — global flag: true if any transition has a deadline

Millisecond arrays are precomputed to avoid nanosecond-to-millisecond division on the hot path.

**Acceptance Criteria:**
1. Timing arrays are populated at compile time, not computed per cycle.
2. `allImmediate` flag allows skipping timing checks entirely for immediate-only nets.
3. `anyDeadlines` flag allows skipping deadline enforcement when no deadlines exist.
4. Precomputed millisecond values match the nanosecond values (within rounding).

**Test derivation:** Compile nets with various timing configurations; verify array values and global flags.

---

#### CONC-025: Lazy Marking Synchronization

**Priority:** SHOULD

The executor maintains token state internally in ring buffers [CONC-022] and materializes a Marking object lazily — only when needed for events [EVT-014], debug inspection, or the execution result [EXEC-041]. During normal execution cycles, no Marking object is created or updated.

**Acceptance Criteria:**
1. Normal execution cycles do not create or update a Marking object.
2. Marking is materialized on demand for event emission, debug, or result.
3. The materialized Marking accurately reflects the current ring buffer state.

**Test derivation:** Execute a net with noop event store; verify no Marking object is created until result is requested.

---

#### CONC-026: Optional Output Validation Skip

**Priority:** MAY

The executor MAY support an opt-in builder option to skip XOR/AND output specification validation [EXEC-021] for known-correct nets. When enabled, output tokens are deposited without verifying that exactly one XOR branch or all AND branches produced output.

This is a performance optimization for production use where nets have been verified at development time.

**Acceptance Criteria:**
1. The option is opt-in (validation is on by default).
2. When enabled, output tokens are deposited without validation.
3. When disabled, output validation behaves identically to the bitmap executor.

**Test derivation:** Enable skip; fire transition with XOR output; verify tokens deposited without validation error.

---

## Wake-Up Mechanism

#### CONC-010: Orchestrator Wake-Up

**Priority:** MUST

When the orchestrator is idle (no transitions ready, waiting for work), it can be woken by:
1. **Action completion** — a completion is enqueued.
2. **External event injection** — a token is injected via an environment place.
3. **Timer expiry** — a delayed transition becomes ready.

The wake-up mechanism is implementation-specific (semaphore, notify, promise resolution) but must be responsive (no polling).

**Acceptance Criteria:**
1. Injecting a token into an environment place wakes the orchestrator immediately.
2. Action completion wakes the orchestrator.
3. Timer-based delayed transitions fire on time (within timer resolution).

**Test derivation:** Inject token while orchestrator is idle; measure latency to processing.

---

#### CONC-011: Inline Synchronous Execution

**Priority:** SHOULD

When an action completes synchronously (returns an immediately-resolved future or signals inline execution support), the executor SHOULD avoid task pool dispatch entirely and run the action inline on the orchestrator thread. This eliminates scheduling overhead for pure-compute workflows.

**Acceptance Criteria:**
1. Passthrough actions execute inline without task dispatch.
2. Synchronous transform actions execute inline when the action signals inline support.
3. Async actions are dispatched to the task pool as normal.

**Test derivation:** Chain of 10 passthrough transitions; measure overhead; verify no task dispatch.

---

#### CONC-012: Concurrent Action Limit

**Priority:** MAY

The executor MAY support limiting the number of concurrently executing actions to prevent resource exhaustion in systems with many enabled transitions.

**Acceptance Criteria:**
1. If a limit is set, no more than N actions execute simultaneously.
2. Excess transitions wait until in-flight count drops below the limit.

**Test derivation:** Set limit to 3; enable 10 transitions; verify max 3 in-flight at any time.
