# 05 — Concurrency

This document specifies the concurrency model: single-threaded orchestrator, async action dispatch, bitmap executor optimization, precompiled flat-array executor, and wake-up mechanisms.

---

## Single-Threaded Orchestrator

#### CONC-001: Orchestrator Thread Ownership

**Priority:** MUST
**Kind:** B

All marking state (token queues, enablement flags, enabled-at timestamps) is owned and mutated exclusively by a single logical orchestrator thread. No locking or synchronization is needed for marking access.

A step that the orchestrator does not take (an action writing, flushing a batch ([IO-015]) or returning, the budget of an action expiring, a caller requesting an injection or draining, closing or terminating the executor, or the firing clock advancing) *shall not* change the clock status of a transition (its enablement flag, its enabled-at timestamp, its restart flag or its reaped mark) or the orchestrator's current cycle (its phase, its clock reading, the transitions its firing pass has still to try, whether the pass has started one, and the tokens the pass has deposited).

A step that neither starts a firing nor deposits the outcome of a firing, a flushed batch or an injected event *shall not* change the token queues.

The orchestrator *shall not* deposit the produced tokens of a firing before the firing's action has returned, deposit its timeout outcome before its budget has expired, or settle it without a deposit before either has happened.

The orchestrator *shall not* deposit a flushed batch of a firing before the firing's action has flushed a batch.

The orchestrator *shall not* inject an event before a caller's request to inject it has been accepted.

**Acceptance Criteria:**
1. Marking has no locks, mutexes, or atomic operations.
2. Only the orchestrator thread writes the marking; a thread other than the orchestrator reads it only as [ENV-014] allows.
3. Action completion results are communicated back via a thread-safe mechanism, then applied on the orchestrator thread.

**Test derivation:** Inspect marking implementation for absence of synchronization primitives.

---

#### CONC-002: Non-Blocking Action Dispatch

**Priority:** MUST
**Kind:** B

An action returns a future/promise/task; the orchestrator does not *await* its completion inline before continuing. Concurrency is provided by whatever drives that returned handle — a virtual-thread pool, tokio tasks, or promise microtasks. Where the action *body* is invoked is implementation-defined: an implementation MAY invoke it inline on the orchestrator thread (delegating the dispatch decision to the action, which supplies its own executor for any work it wants to run off-thread), or MAY submit it to a task pool itself. In an inline-invoking implementation an action that blocks before returning its handle blocks the whole net; concurrency there comes from the action returning a handle backed by its own thread/pool.

*When* the executor starts a transition, it *shall not* deposit any token; the outputs of the firing are deposited in a later step ([CONC-003]).

*When* the executor starts a transition, it *shall* add a firing of that transition, its action not yet completed, to the firings in flight, and *shall* leave every other firing in flight as it was.

From its termination test ([EXEC-040]) the executor *shall* either begin a firing pass or finish the run; it *shall not* wait at the test for a firing in flight to complete.

The executor *shall* pass over a transition of the ready order without starting it only when the transition holds no clock or is not enabled on the marking the firing pass judges ([EXEC-003]), whatever firings are in flight.

*When* the executor updates enablement ([TIME-010]), it *shall* leave every enabled transition that is not reaped ([TIME-013]) holding a clock, whatever firings are in flight, unless the executor is not re-entrant and a firing of that transition is in flight.

*Where* the executor is not re-entrant (Java, TypeScript), it *shall not* arm ([TIME-010]) or start a transition while a firing of that transition is in flight.

**Acceptance Criteria:**
1. The orchestrator does not await an action's completion inline; it continues once the action returns its handle.
2. Multiple actions whose handles are backed by concurrent work execute concurrently.
3. The orchestrator continues processing other transitions while such actions run.

While an action runs its inputs are consumed and its outputs not yet deposited, and other
transitions fire. Verification models that for every transition it splits in two ([VER-004]):
one whose output another transition tests with an inhibitor, reset or drain, one that marks a
terminal place, and the extra transitions a lower-bound `QuiescentCount` beside a terminal
place and conflict priority ([NU-052]) require. Whether an executor starts a transition again
while an earlier firing of it is in flight is not specified: a re-entrant executor does (Rust,
Python), one that is not re-entrant does not (Java, TypeScript). The verification model allows it, which is sound for every
implementation. When a counterexample
starts a transition again while its earlier firing is in flight, the report says so, since on
Java and TypeScript that trace may be a false alarm. Conflict priority does not rely on the
restart: a pruner pre-empts nothing while its own action is in flight.

**Test derivation:** Two transitions fire; both actions return handles backed by a 100ms async sleep; verify total time ~100ms, not ~200ms.

---

#### CONC-003: Happens-Before Guarantee

**Priority:** MUST
**Kind:** B

All writes performed by an action (output tokens, side effects) are visible to the orchestrator after the action's future/promise completes. The completion mechanism provides a happens-before edge.

*When* the executor deposits the produced tokens of an admitted completion ([EXEC-020]), it *shall* deposit exactly the tokens the action wrote after its last publication, if any ([IO-015]), and before it returned, each at the tail of its place, in the order the action wrote them.

*When* the executor deposits a batch an action published before it completed ([IO-015]), it *shall* deposit the earliest publication of that action it has not yet deposited, as exactly the tokens the action wrote before that publication and after the one before it, each at the tail of its place, in the order the action wrote them.

The executor *shall* keep the batches an action published queued, in the order the action published them, until it deposits each one, unless a terminal place or an immediate termination stops the run ([EXEC-042], [ENV-015]).

**Acceptance Criteria:**
1. Action writes to output context; orchestrator reads output after completion; values are visible.
2. No stale reads possible.

**Test derivation:** Action stores complex object in output; verify orchestrator sees complete object.

---

## Bitmap Executor

#### CONC-004: Bitmap-Based Enablement Check

**Priority:** MUST
**Kind:** F

The primary executor uses precomputed bitmasks for O(1) enablement checking per transition (proportional to the number of machine words needed to represent all places).

Each transition has precomputed masks:
- **needs-mask**: bits set for all input + read places (all must have tokens)
- **inhibitor-mask**: bits set for all inhibitor places (none may have tokens)

Enablement check: `(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0`

The presence check of a transition *shall* pass on a bitmap exactly when every bit of its needs-mask is set in the bitmap and no bit of its inhibitor-mask is set.

**Acceptance Criteria:**
1. Enablement is checked via bitwise operations, not by iterating over arcs.
2. A transition with 3 inputs and 2 reads requires only 1-2 bitwise operations.
3. The check is O(W) where W = ceil(numPlaces / word_size).

**Test derivation:** Net with 100 places; verify enablement check performance is constant per transition.

---

#### CONC-005: Dirty Set Optimization

**Priority:** MUST
**Kind:** B

When tokens are added or removed from a place, only transitions affected by that place need re-evaluation. A precomputed reverse index maps each place to the set of transitions that reference it.

*When* a firing or an injected token writes one of a transition's arc places, the executor *shall* re-run the transition's enablement check.

The executor *shall* re-run a transition's enablement check only when a firing or an injected token writes one of its arc places, or when the transition itself fires.

*If* the consumption of a firing, the deposit of a firing or an injected token writes none of a transition's arc places, *then* the transition's enablement check *shall* pass after it exactly when it passed before it.

*While* a transition is reaped ([TIME-013]), the executor *shall not* re-run its enablement check, and only a firing or an injected token that writes one of its arc places *shall* end its reaped state.

The dirty set is maintained as a bitmap: when a place changes, the executor sets the bits for all affected transitions. Each cycle, only dirty transitions are re-evaluated.

**Acceptance Criteria:**
1. Adding a token to place P only marks transitions connected to P as dirty.
2. Transitions not connected to P are not re-evaluated.
3. After re-evaluation, dirty bits are cleared.

**Test derivation:** Net with 50 transitions; add token to place connected to 3 transitions; verify only 3 transitions re-evaluated.

---

#### CONC-006: Lock-Free Completion Signaling

**Priority:** MUST
**Kind:** Q

Action completions are communicated to the orchestrator via a lock-free mechanism (lock-free queue, mpsc channel, or similar). The hot path avoids contention on shared locks.

**Acceptance Criteria:**
1. Multiple actions completing simultaneously do not contend on a single lock.
2. Completion notification is O(1) per completion.

**Test derivation:** 10 actions complete near-simultaneously; verify no lock contention (measured via timing, not exceeding linear overhead).

---

#### CONC-007: Compiled Net Representation

**Priority:** MUST
**Kind:** F

The bitmap executor compiles the net into an integer-indexed representation where places and transitions are assigned stable numeric IDs (0-based). This enables array-based access instead of hash map lookups.

Precomputed data includes:
- Per-transition: needs-mask, inhibitor-mask, consumption places (the IDs of its input and reset places)
- Per-place: list of affected transition IDs (reverse index)
- Per-transition: cardinality check (needed for a transition with an input that requires more than one token)
- Per-transition: match presence flag (whether the transition carries a ν-match specification, [NU-020])

Stable means that the IDs stay fixed for the life of the compiled net. The order in which places are numbered is not specified; transitions are numbered in declaration order.

The compiled net *shall* number the places of the net from 0 to P-1, where P is the number of places of the net, so that each place has exactly one ID and each ID names exactly one place.

The compiled net *shall* give each transition its declaration position as its ID, numbering the transitions from 0 in the order the net declares them.

The needs-mask of a transition *shall* hold exactly the IDs of its input and read places, and its inhibitor-mask exactly the IDs of its inhibitor places.

The consumption places of a transition *shall* be exactly the IDs of its input and reset places.

The reverse index *shall* map the ID of each place to exactly the IDs of the transitions that have an input, read, inhibitor or reset arc on that place.

*If* a transition has no cardinality check, *then* each of its inputs *shall* require at most one token.

Each entry of a cardinality check *shall* be the ID of an input place of the transition with the required count of that input, and each input that requires more than one token *shall* have an entry.

The compiled net *shall* set the match presence flag of a transition exactly when the transition carries a match specification ([NU-020]).

**Acceptance Criteria:**
1. Places and transitions have stable numeric IDs.
2. All masks are precomputed at compilation time, not at each enablement check.

**Test derivation:** Compile a net; verify masks match expected bit patterns.

---

#### CONC-008: Multi-Phase Enablement

**Priority:** MUST
**Kind:** F

Enablement checking is a multi-phase process:
1. **Phase 1 — Bitmap presence check**: O(W) bitwise check against needs-mask and inhibitor-mask. Fast reject for most transitions.
2. **Phase 2 — Cardinality check**: For transitions with Exactly(n)/All/AtLeast(m), verify actual token counts meet thresholds.
3. **Phase 3 — ν-match check**: For transitions carrying a match specification ([NU-020]), scan the correlated inputs for a name of which every correlated input holds at least its required count of tokens of that name. This is the only per-token phase; there is no value-predicate phase (guards were removed, [IO-006]).

Phases 2 and 3 are only reached if Phase 1 passes, minimizing work for most transitions.

*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, and its presence check passes on the presence bitmap of the marking, its cardinality check *shall* pass exactly when every input place holds at least its required count.

*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking and the cardinality check passes.

*When* a transition that builds has no match specification and no `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking.

*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when the transition is enabled ([CORE-022]).

*When* a transition that builds has a match specification and phases 1 and 2 pass on the token counts of the marking, its ν-match check *shall* pass exactly when the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name ([NU-020]).

*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking and its ν-match check passes.

*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking.

*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when the transition without its match specification is enabled on the token counts of the marking ([CORE-022]), the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name.

**Acceptance Criteria:**
1. A transition with only One inputs and no match specification is fully checked in Phase 1.
2. A transition with Exactly(5) input requires Phase 2 to verify token count.
3. A transition with a match specification requires Phase 3 to scan tokens for a name of which every correlated input holds at least its required count of tokens of that name.

**Test derivation:** Mix of simple and complex transitions; verify correct enablement with minimal re-evaluation.

---

## Precompiled Flat-Array Executor

#### CONC-020: Precompiled Net Representation

**Priority:** SHOULD
**Kind:** Q

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
**Kind:** F

Each transition's input and reset arcs are compiled into a flat integer array of opcodes. During firing, the executor iterates the opcode array instead of pattern-matching on sealed arc types, except for a transition with a match specification, whose inputs are consumed through the match path (its correlated inputs by name, [NU-020]). Read arcs are compiled into a separate place-ID array.

Opcodes:
- `CONSUME_ONE(0) placeId`: consume one token from place
- `CONSUME_N(1) placeId count`: consume exactly N tokens
- `CONSUME_ALL(2) placeId`: consume all tokens the firing may drain ([EXEC-003] AC5)
- `CONSUME_ATLEAST(3) placeId minimum`: consume at least N tokens (takes all tokens the firing may drain, [EXEC-003] AC5)
- `RESET(4) placeId`: clear from the place all tokens the firing may drain ([EXEC-003] AC5)

*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action from each input place the oldest tokens the place holds, as many as the consumption count of the input arc ([IO-007]) for the number of tokens the firing may drain ([EXEC-003] AC5), in queue order, and nothing from any other place.

*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action for each read arc the head of the read place's queue as it is after the input operations and before the reset operations.

*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* remove from each reset place every token the firing may drain ([EXEC-003] AC5), leave each other input place its queue without the tokens handed to the action, leave the queue of every other place unchanged, and hold a queue for every place the token storage held and for no other place.

**Acceptance Criteria:**
1. Each transition has a precompiled consume operation array.
2. Read arcs are compiled into a separate place-ID array (reads do not consume).
3. Firing a transition iterates the opcode array without type dispatch, except for a transition with a match specification, whose inputs are consumed through the match path (its correlated inputs by name, [NU-020]).
4. All five opcodes produce the same observable behavior as the corresponding arc types.

**Test derivation:** Compile a net with all arc types; fire transitions; verify token consumption matches bitmap executor.

---

#### CONC-022: Flat-Array Token Storage

**Priority:** SHOULD
**Kind:** F

Token storage uses ring buffers indexed by place ID for O(1) access. Each place has a dedicated ring buffer that preserves FIFO ordering [CORE-013] and grows dynamically when capacity is exceeded.

The precompiled executor's token storage *shall* hold a dedicated queue for each place of the net it is built for.

*When* a token is added to a place the token storage holds a queue for, the token storage *shall* append it at the tail of the place's queue whatever the capacity of the place's storage, *shall* keep holding a queue for every place it held, and *shall* leave the queue of every other place unchanged.

*When* the first token of a marked place the token storage holds a queue for is removed, the token storage *shall* return the head of the place's queue, keep the rest of that queue in queue order, keep holding a queue for every place it held, and leave the queue of every other place unchanged.

*When* the first token of a place the token storage holds a queue for is read without removing it, the token storage *shall* return the head of the place's queue, or nothing when the place is not marked.

The token storage *shall* report as the token count of a place it holds a queue for the length of the place's queue.

**Acceptance Criteria:**
1. Token access is O(1) by place ID — no hashing or map lookup.
2. FIFO ordering is preserved (oldest token consumed first, except on a correlated input of a match specification, [NU-020]).
3. Ring buffers grow dynamically when capacity is exceeded.
4. Token count per place is available in O(1).

**Depends on:** [CORE-013]
**Test derivation:** Add and consume tokens in various orders; verify FIFO ordering and correct counts.

---

#### CONC-023: Priority-Partitioned Ready Queues

**Priority:** SHOULD
**Kind:** F

Distinct priority values are sorted descending at compile time. Each priority level has its own FIFO queue. Transition selection scans priority levels in descending order and picks the first non-empty queue, giving O(L) selection where L is the number of distinct priority levels (typically 1–3).

*Where* the net does not take the all-immediate fast path, the ready order *shall* be the ready transitions grouped by priority level, at most one group per priority level, with the groups in descending order of priority.

*Where* the net does not take the all-immediate fast path, the ready order *shall* offer the ready transitions of one priority level in ascending order of stamp.

The ready order *shall* hold every ready transition exactly once and no other transition, on the all-immediate fast path as well.

The ready order *shall* offer ready transitions of one priority level with equal stamps in ascending declaration order, also when they were armed in different cycles and on the all-immediate fast path.

Each transition maps to a priority index for O(1) ready-queue insertion.

**Acceptance Criteria:**
1. Distinct priority levels are precomputed and sorted descending.
2. Each priority level has a separate FIFO queue.
3. Transition selection is O(L) where L = distinct priority levels.
4. Within the same priority, FIFO ordering by enablement time is preserved.
   Feeding a level's queue in declaration order is NOT sufficient: transitions
   enabled in different cycles must drain in enablement order even when it
   disagrees with declaration order, and equal enablement timestamps break by
   ascending declaration order — the identical order [EXEC-002] AC3/AC4
   requires of every backend. The all-immediate single-priority fast path is
   exempt: it bypasses the ready queues and fires in declaration order, which
   [EXEC-002] AC4 requires of every backend alike.

**Depends on:** [EXEC-002]
**Test derivation:** Net with 3 priority levels; verify transitions fire in correct priority order with FIFO within each level.

---

#### CONC-024: Precomputed Timing Arrays

**Priority:** SHOULD
**Kind:** F

Timing constraints are precomputed into flat arrays at compile time to avoid virtual dispatch on timing types during execution:
- `earliestNanos[]` / `earliestMillis[]` — earliest firing time per transition
- `latestNanos[]` / `latestMillis[]` — latest firing time (MAX_VALUE if no deadline)
- `hasDeadline[]` — boolean flag per transition
- `allImmediate` — global flag: true if all transitions are immediate
- `anyDeadlines` — global flag: true if any transition has a deadline

Millisecond arrays are precomputed to avoid nanosecond-to-millisecond division on the hot path.

*When* a net is precompiled, the timing arrays *shall* hold, for each transition, the `earliest()` of its timing in the array's unit and the `hasDeadline()` of its timing ([TIME-001]).

*When* a net is precompiled, the timing arrays *shall* hold, for each transition whose timing's `hasDeadline()` is true, the `latest()` of its timing in the array's unit.

*When* a net is precompiled, `allImmediate` *shall* be true exactly when every transition of the net has the timing `Immediate`.

*When* a net is precompiled, `anyDeadlines` *shall* be true exactly when some transition of the net has a timing whose `hasDeadline()` is true.

**Acceptance Criteria:**
1. Timing arrays are populated at compile time, not computed per cycle.
2. `allImmediate` flag allows skipping timing checks entirely for immediate-only nets.
3. `anyDeadlines` flag allows skipping deadline enforcement when no deadlines exist.
4. Precomputed millisecond values match the nanosecond values (within rounding).

**Test derivation:** Compile nets with various timing configurations; verify array values and global flags.

---

#### CONC-025: Lazy Marking Synchronization

**Priority:** SHOULD
**Kind:** B

The executor maintains token state internally in ring buffers [CONC-022] and materializes a Marking object lazily — only when needed for events [EVT-014], debug inspection, or the execution result [EXEC-041]. During normal execution cycles, no Marking object is created or updated.

*When* the executor materializes a Marking, it *shall* give each place the token storage holds a queue for exactly the tokens of that queue at that moment, in queue order.

**Acceptance Criteria:**
1. Normal execution cycles do not create or update a Marking object.
2. Marking is materialized on demand for event emission, debug, or result.
3. The materialized Marking accurately reflects the current ring buffer state.

**Test derivation:** Execute a net with noop event store; verify no Marking object is created until result is requested.

---

#### CONC-026: Optional Output Validation Skip

**Priority:** MAY
**Kind:** N

The executor MAY support an opt-in builder option to skip output validation ([IO-015], [EXEC-021]) for known-correct nets. This is a performance optimization for production use where nets have been verified at development time.

*While* the option is enabled, the executor *shall* deposit the tokens an action wrote without validating them against the transition's output spec. The skip covers the whole spec, its `Place` and `ForwardInput` leaves included: a transition whose output spec is a single leaf is not checked for a write to that place either. It also covers the join-relay check of [NU-054] and the multiplicity warning of [IO-016] AC4, both of which run as part of validation.

[IO-010], [IO-011] and [IO-012], the per-firing check of [IO-015] and the last two firing lines of [CORE-036] for a firing that ends with its action are requirements on an executor with output validation enabled, which is the default. While the option is enabled they do not apply: a firing that ends with its action deposits the action's write whether or not it equals an output branch.

The option skips nothing else. A write to a place the transition does not declare as an output still fails ([CORE-063]). A firing that ends with the timeout outcome deposits what [IO-013] and [IO-014] say. The build-time checks of [IO-011], [IO-012], [IO-013] and [IO-014] run when the transition is built, before any executor exists, and no executor option reaches them.

**Acceptance Criteria:**
1. The option is opt-in (validation is on by default).
2. When enabled, output tokens are deposited without validation.
3. When disabled, output validation behaves identically to the bitmap executor.
4. When enabled, a transition with output spec `Place(P)` whose action writes nothing completes
   without a validation error and deposits nothing, and a transition with `And(A, B)` whose
   action writes only `A` deposits the `A` token.
5. When enabled, a token in a relay target that does not carry the matched name is deposited
   without the [NU-054] diagnostic, and a write of two tokens into one claimed place emits no
   [IO-016] AC4 warning.
6. When enabled, a write to an undeclared place still fails ([CORE-063]), and building a
   transition whose output spec [IO-012] rejects still fails.

**Implementation notes:** the option is offered by the production executor of each language:
Java `PrecompiledNetExecutor.Builder.skipOutputValidation`, TypeScript's
`PrecompiledNetExecutor` option `skipOutputValidation`, Rust's `PrecompiledNetExecutor` and
`OwnedPrecompiledNet` builders (`skip_output_validation`), and Python's
`ExecutorOptions(skip_output_validation=...)`, which sets the Rust one. All four skip the leaf
check, the relay check and the warning alike. The reference executors offer no option.

**Depends on:** [IO-015], [EXEC-021], [NU-054]
**Test derivation:** Enable skip; fire transition with XOR output; verify tokens deposited without validation error. With the skip enabled, fire the AC4 and AC5 transitions and verify the deposits and the absence of any violation, relay diagnostic or warning; with it disabled, verify each fails or warns as [IO-010], [IO-011], [NU-054] and [IO-016] say. Build the AC6 transition with the skip enabled and verify it is rejected.

---

## Wake-Up Mechanism

#### CONC-010: Orchestrator Wake-Up

**Priority:** MUST
**Kind:** B

When the orchestrator is idle (no transitions ready, waiting for work), it must be woken by each of these causes:
1. **Action completion:** an action returns, or its timeout expires ([EXEC-022]), and its outcome is queued for the orchestrator.
2. **External event injection:** `inject()` accepts a token for an environment place ([ENV-003]).
3. **Timer expiry:** the timer the wait set for a timing boundary of an armed transition runs out.
4. **Lifecycle:** the executor is drained ([ENV-011]), closed ([ENV-013]) or terminated immediately ([ENV-015]).
5. **Publication:** an action's flush queues a batch of outputs before the action returns ([IO-015]), in an implementation with mid-action publication. A flush that the join-relay check rejects ([NU-054]) queues nothing and is no wake cause; the firing then ends with an error when its action returns.

The wait may also end for no reason, such as a spurious wake-up or a periodic re-check behind the direct wake-up ([TIME-015]). A snapshot request ([ENV-014]) may be answered from the wait without ending it. The wake-up mechanism is implementation-specific (semaphore, notify, promise resolution, channel select) but must be responsive: a wake-up does not depend on a poll interval.

A drain, a close or an immediate termination that comes after the cycle's termination test and before the block is not lost either: the runtimes keep the signal until the wait reads it (Rust's signal channel, Java's semaphore permit, TypeScript's latched wake-up), and the wait then ends at once. The rules below do not state this case yet, so it is tested, not proven.

A timing boundary of an armed transition is its earliest bound, while its elapsed time has not reached it, and, for a reapable transition, the reading at which it becomes expired ([TIME-013]). The orchestrator judges Ready, Expired and the timing boundaries for its wait at the firing-clock reading its deadline step took in the current cycle ([EXEC-001] step 4), which is not earlier than the reading of its enablement update ([TIME-010]). Judging them at a later reading of the same cycle parks less often and sets an earlier timer, which the rules below also allow.

*While* the outcome of an action, a flushed publication or an accepted injection is queued and not yet processed, the executor *shall not* block in its wait ([EXEC-001] step 6).

*While* a transition is Ready or Expired at the reading of the cycle's deadline step, the executor *shall not* block in its wait.

*When* an action's outcome is queued, an action's flush queues a publication, `inject()` accepts a token, or the executor is drained, closed or terminated immediately, the executor *shall* end any block of its wait at once and be ready to leave the wait for the start of its loop ([EXEC-001] step 1) without waiting for a timer.

*When* the executor blocks in its wait while an armed transition has a timing boundary ahead, it *shall* set a timer no longer than the time from the reading of the cycle's deadline step to the nearest such boundary, plus the timer resolution.

*When* an action returns or its timeout expires, the executor *shall* queue the action's outcome for the orchestrator.

So no queued work waits for a timer or a poll, and a wait with a timing boundary ahead carries a timer that runs out no later than that boundary, within timer resolution, counted from the reading of the cycle's deadline step. Ending the wait when that timer runs out is the work of the host timer ([TIME-015]).

**Acceptance Criteria:**
1. Injecting a token into an environment place wakes the orchestrator immediately.
2. Action completion wakes the orchestrator.
3. A wait with a timing boundary of an armed transition ahead sets a timer of at most the time to that boundary plus the timer resolution, counted from the reading of the cycle's deadline step, so that, if the transition is still armed, the cycle the timer starts finds it ready ([TIME-010]) or reaps it ([TIME-013]) without another cause.
4. A drain, a close or an immediate termination ends a block of the wait at once.

**Test derivation:** Inject token while orchestrator is idle; measure latency to processing.

---

#### CONC-011: Inline Synchronous Execution

**Priority:** SHOULD
**Kind:** Q

When an action completes synchronously (returns an immediately-resolved future or signals inline execution support), the executor SHOULD avoid task pool dispatch entirely and run the action inline on the orchestrator thread. This eliminates scheduling overhead for pure-compute workflows.

**Acceptance Criteria:**
1. Passthrough actions execute inline without task dispatch.
2. Synchronous transform actions execute inline when the action signals inline support.
3. The orchestrator never dispatches actions itself; an async action returns a handle backed by its own executor, and the orchestrator continues once the handle is returned ([CONC-002]).

**Test derivation:** Chain of 10 transitions bound to trivial synchronous actions; measure overhead; verify no task dispatch.

---

#### CONC-012: ~~Concurrent Action Limit~~ (Removed)

**Status:** Removed

No implementation offers an executor-level limit on in-flight actions, and a permit place bounds concurrency inside the net, where verification can see it. The former text and the permit-place pattern are kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count.
