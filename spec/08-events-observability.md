# 08 — Events & Observability

This document specifies the event types emitted during execution, the event store interface, and observability features.

---

## Event Hierarchy

#### EVT-001: Event Immutability

**Priority:** MUST

All events are immutable value objects. Once created, no field can be modified. Collections within events (e.g., consumed tokens) are defensive copies.

**Acceptance Criteria:**
1. Event fields are read-only.
2. Collections within events are immutable copies (not live references).

**Test derivation:** Create event with list; modify original list; verify event's list unchanged.

---

#### EVT-002: ExecutionStarted Event

**Priority:** MUST

Emitted when the executor begins running. Contains:
- Timestamp
- Net name
- Execution ID (unique per run)

**Acceptance Criteria:**
1. Emitted exactly once per execution run, before any transitions fire.
2. Execution ID is unique across runs.

**Test derivation:** Run net; verify first event is ExecutionStarted with correct net name.

---

#### EVT-003: ExecutionCompleted Event

**Priority:** MUST

Emitted when the executor reaches quiescence and terminates (or is explicitly closed). Contains:
- Timestamp
- Net name
- Execution ID
- Total duration

**Acceptance Criteria:**
1. Emitted exactly once per execution run, after all transitions complete.
2. Total duration reflects wall-clock time from start to completion.

**Test derivation:** Run net; verify last event is ExecutionCompleted; verify duration > 0.

---

#### EVT-004: TransitionEnabled Event

**Priority:** MUST

Emitted when a transition becomes enabled (all preconditions met for the first time, or re-enabled after being disabled).

**Acceptance Criteria:**
1. Emitted each time a transition transitions from disabled to enabled.
2. Not emitted if transition was already enabled.

**Test derivation:** Add token enabling transition T; verify TransitionEnabled event for T.

---

#### EVT-005: TransitionClockRestarted Event

**Priority:** MUST

Emitted when a transition's timing clock is restarted because one of its input/read places was affected by a reset arc, while the transition remains enabled (see [TIME-012]).

**Acceptance Criteria:**
1. Emitted only when transition remains enabled but clock restarts.
2. Not emitted on initial enablement (that's TransitionEnabled).

**Depends on:** [TIME-012]
**Test derivation:** Transition T enabled; reset arc clears its input place; new token arrives; verify TransitionClockRestarted for T.

---

#### EVT-006: TransitionStarted Event

**Priority:** MUST

Emitted when a transition begins firing (tokens consumed, action dispatched). Contains:
- Timestamp
- Transition name
- List of consumed tokens (defensive copy)

**Acceptance Criteria:**
1. Emitted after token consumption, before action execution.
2. Consumed tokens list matches actual consumed tokens.

**Test derivation:** Fire transition consuming 2 tokens; verify TransitionStarted with 2 tokens listed.

---

#### EVT-007: TransitionCompleted Event

**Priority:** MUST

Emitted when a transition's action completes successfully. Contains:
- Timestamp
- Transition name
- List of produced tokens (defensive copy)
- Duration of action execution

**Acceptance Criteria:**
1. Emitted after successful action completion and output deposition.
2. Duration reflects action execution time.

**Test derivation:** Fire transition; verify TransitionCompleted with produced tokens and positive duration.

---

#### EVT-008: TransitionFailed Event

**Priority:** MUST

Emitted when a transition's action throws an exception or returns an error. Contains:
- Timestamp
- Transition name
- Error message
- Exception type name

**Acceptance Criteria:**
1. Emitted when action fails.
2. Error message and type are captured.

**Depends on:** [EXEC-030]
**Test derivation:** Action throws; verify TransitionFailed with error details.

---

#### EVT-009: TransitionTimedOut Event

**Priority:** MUST

Emitted when a transition exceeds its timing deadline (latest bound) without firing. Contains:
- Timestamp
- Transition name
- Deadline duration
- Actual elapsed duration since enablement

**Acceptance Criteria:**
1. Emitted when elapsed time exceeds latest bound.
2. Transition is disabled after this event.

**Depends on:** [TIME-013]
**Test derivation:** Transition with Deadline(100ms); delay firing 200ms; verify TransitionTimedOut event.

---

#### EVT-010: ActionTimedOut Event

**Priority:** MUST

Emitted when a transition's action exceeds the Out.Timeout duration (distinct from the transition's timing deadline). Contains:
- Timestamp
- Transition name
- Timeout duration

**Acceptance Criteria:**
1. Emitted when action exceeds Out.Timeout, not the transition's timing deadline.
2. Timeout branch is activated after this event.

**Depends on:** [IO-013], [EXEC-022]
**Test derivation:** Action sleeps 500ms; Out.Timeout at 100ms; verify ActionTimedOut event.

---

#### EVT-011: TokenAdded Event

**Priority:** MUST

Emitted when a token is added to a place (whether from initial marking, action output, or external injection). Contains:
- Timestamp
- Place name
- The token

**Acceptance Criteria:**
1. Emitted for every token addition.
2. Place name identifies the target place.

**Test derivation:** Add token to place; verify TokenAdded event with correct place name.

---

#### EVT-012: TokenRemoved Event

**Priority:** MUST

Emitted when a token is removed from a place (consumed by input arc or cleared by reset arc). Contains:
- Timestamp
- Place name
- The token

**Acceptance Criteria:**
1. Emitted for every token removal.
2. Place name identifies the source place.

**Test derivation:** Fire transition consuming token; verify TokenRemoved event.

---

#### EVT-013: LogMessage Event

**Priority:** SHOULD

Emitted when a transition action produces log output. The engine captures log statements from within actions and wraps them as events. Contains:
- Timestamp
- Transition name
- Logger name
- Log level
- Message
- Error/throwable details (optional)

**Acceptance Criteria:**
1. Log statements within actions are captured as LogMessage events.
2. Log level (INFO, WARN, ERROR, etc.) is preserved.
3. Exception details are included when present.

**Implementation notes:**
- Java: Captures SLF4J output via LogCaptureScope
- TypeScript: Captures via context.log() method
- Rust: Not yet implemented

**Test derivation:** Action logs a warning; verify LogMessage event with correct level and message.

---

#### EVT-014: MarkingSnapshot Event

**Priority:** SHOULD

Emitted at specific points during execution to capture the full marking state. Contains:
- Timestamp
- Map of place name → list of tokens

**Acceptance Criteria:**
1. Emitted at least at execution start (initial marking) and before execution completion.
2. Snapshot is a deep defensive copy (not a live reference).
3. Only non-empty places are included.

**Test derivation:** Run net; verify MarkingSnapshot at start and end; verify snapshot accuracy.

---

## Event Store Interface

#### EVT-020: EventStore Interface

**Priority:** MUST

The event store provides:
- `append(event)` — thread-safe event addition
- `events()` — snapshot of all events
- `isEnabled()` — whether event capture is active

**Acceptance Criteria:**
1. append() is safe to call from any thread.
2. events() returns a consistent snapshot.
3. isEnabled() controls whether the executor creates event objects.

**Test derivation:** Append events from multiple threads; verify events() returns all of them.

---

#### EVT-021: InMemoryEventStore

**Priority:** MUST

A thread-safe in-memory event store that retains all events in chronological order.

**Acceptance Criteria:**
1. Events are stored in insertion order.
2. Thread-safe append (concurrent callers do not lose events).
3. events() returns a snapshot copy (not a live reference).
4. Provides clear() for test reuse.

**Test derivation:** Append 100 events; verify events() returns 100 in order.

---

#### EVT-022: NoopEventStore

**Priority:** MUST

A zero-cost event store that discards all events. When used, the executor skips event object creation entirely.

**Acceptance Criteria:**
1. append() is a no-op.
2. events() returns empty.
3. isEnabled() returns false.
4. The executor does not allocate event objects when the noop store is used.

**Test derivation:** Run net with noop store; verify no events captured; verify no allocation overhead (benchmark).

---

#### EVT-023: LoggingEventStore

**Priority:** SHOULD

An event store decorator that logs events to the platform's logging framework at appropriate levels before delegating to a wrapped store.

**Acceptance Criteria:**
1. Failure events logged at WARN level.
2. Lifecycle events logged at INFO level.
3. Transition events logged at DEBUG level.
4. Token events logged at TRACE level.
5. Delegates to wrapped store after logging.

**Implementation notes:**
- Java: Full implementation with SLF4J
- TypeScript: Not implemented
- Rust: Not implemented

**Test derivation:** Run net with logging store; verify log output at correct levels.

---

#### EVT-024: DebugEventStore

**Priority:** SHOULD

An event store with live tailing support for debug UIs. Supports:
- Subscriptions (consumers notified of new events)
- Capacity management (eviction of old events)
- Session tracking

**Acceptance Criteria:**
1. Subscribers receive new events in FIFO order.
2. Old events are evicted when capacity is exceeded.
3. Multiple subscribers can be active simultaneously.

**Implementation notes:**
- Java: Full implementation with virtual-thread broadcast
- TypeScript: Full implementation with microtask broadcast
- Rust: Not implemented

**Test derivation:** Subscribe to debug store; append event; verify subscriber receives it.

---

#### EVT-025: Session Archive Format

**Priority:** SHOULD

Completed debug sessions can be serialized to a length-prefixed compressed archive (LZ4
for Java, gzip for TypeScript and Rust) for later replay. The archive has a versioned
header followed by one length-prefixed JSON record per event.

Three header versions exist; readers MUST accept all three and dispatch into the matching
sealed variant (`V1`/`V2`/`V3`) so callers can pattern-match on writer guarantees.

**Header format** (identical across languages):

| Header | First shipped | Adds over previous |
|---|---|---|
| v1 | libpetri 1.5.x | baseline: `sessionId`, `netName`, `dotDiagram`, `startTime`, `eventCount`, `structure` |
| v2 | libpetri 1.7.x | `endTime`, `tags`, pre-computed `metadata` (event-type histogram, first/last, hasErrors) |
| v3 | libpetri 1.8.0 | same fields as v2; bump signals typed-token event bodies |

**Event body format** (per-language, because each implementation serializes its
own event shape — Java serializes the `NetEvent` record directly, TypeScript and Rust
serialize a `NetEventInfo` debug-protocol projection). Archive bodies are therefore not
byte-compatible across languages — only headers are. All languages agree on *semantic*
content, not wire layout.

- **Java (v3):** `token: {valueType: <FQN>, v: <structured JSON>, createdAt: <iso>}`.
  Special cases: `{valueType: "void", createdAt}` for unit tokens (no `v`);
  `{valueType, text, createdAt}` fallback when Jackson cannot structure the value;
  legacy `{value, valueType: simpleName, createdAt}` from v1/v2 also accepted.
- **TypeScript (v3):** `token: {id, type, value: <String(value)>, structured?: <JSON>, timestamp}`.
  The `value` string is retained alongside the new optional `structured` field so the
  bundled debug UI keeps rendering without change. `type` is `value.constructor.name`
  (simple name — TypeScript has no portable FQN).
- **Rust (v3):** `token: {id, type, value, structured?, timestamp}` — wire-identical to
  TypeScript via a shared `NetEventInfo` camelCase serde contract. `type` is
  `std::any::type_name::<T>()` at token-erasure time; `structured` is populated by
  [`TokenProjectorRegistry`](../rust/libpetri-debug/src/token_projector_registry.rs)
  when the token's inner `T` is registered, else falls back to
  `{"type": <type_name>, "text": <Debug repr>}` — parallel to Java's `{valueType, text}`
  shape.

**Acceptance Criteria:**
1. Each language's v3-capable writer defaults to emitting v3; `writeV1` / `writeV2` still
   exist and emit the corresponding header. The event body is always the writer's current
   token shape regardless of header version — byte-identical 1.7.x event bodies are not
   producible from 1.8.0+.
2. Each v3-capable reader reads v1, v2, and v3 archives; an archive with an unknown
   version is rejected with an error/exception that names the encountered version and
   the supported range.
3. Record, enum, boxed primitive, and unit tokens written under Java v3 round-trip with
   their original concrete type when the class is on the reader's classpath.
4. When a Java-side `valueType` FQN cannot be resolved (class not on classpath, shaded,
   cross-language write), the token hydrates as `Token<JsonNode>` — the deserializer
   never throws on unknown types.
5. TypeScript + Rust archives preserve the `structured` JSON payload across a full
   write→read round-trip; replay consumers receive `TokenInfo.structured` (TS) or a
   `ReplayedTokenPayload` on `NetEvent::TokenAdded`/`TokenRemoved` (Rust) carrying the
   same JSON shape the writer emitted.
6. Legacy (`{value, valueType: simpleName}`) tokens continue to hydrate as string-valued
   tokens on any v3-capable reader.
7. TypeScript archives omit the `structured` field entirely when it would be empty or
   unprojectable (wire size is neutral for unstructurable tokens).
8. The header `eventCount` field MUST equal the number of event records that follow in
   the body. Implementations MUST NOT populate `eventCount` from a cumulative lifetime
   counter on the event store; the value reflects retained body length only. After a
   write→read round-trip, `archive.eventCount() == archive.events().size()` for all
   three header versions and across all three language implementations. The writer
   MUST take exactly one snapshot of the event store; header `eventCount`, V2/V3
   metadata, and the event body MUST all derive from that single snapshot.

**Implementation notes:**
- Java: Full implementation — default writer emits v3, deserializer reconstructs original
  token types via `Class.forName`.
- TypeScript: Full implementation — default writer emits v3, `structured` projection via
  `JSON.parse(JSON.stringify(value))`.
- Rust: Full implementation — default writer emits v3 via a user-supplied
  `TokenProjectorRegistry`; reader hydrates into a `ReplayedTokenPayload` exposing the
  `structured` JSON without attempting to revive the original `T` (Rust has no
  `Class.forName` equivalent).

**Cross-language replay:** Java → Java reconstructs typed tokens. TypeScript ↔ Rust
archives are wire-compatible at the event body level (shared `NetEventInfo` contract);
both preserve `structured` across a round-trip. Java archive bodies use a different shape
(`NetEvent` direct serialization) and are not interchangeable at the body level — use
language-native archives for full-fidelity replay.

**Security note:** Java v3 deserialization resolves the archive-supplied `valueType`
FQN via `Class.forName`. TypeScript's `structuredValue` uses
`JSON.parse(JSON.stringify(v))` — safe against code execution and prototype pollution,
but respects any `toJSON()` method on the value. Rust's `TokenProjectorRegistry`
projects only user-registered types; unregistered values fall back to `Debug` repr and
never execute arbitrary code. Archives are a trust boundary: **do not deserialize
archives from untrusted network sources** without a guard — in Java because of
static-initializer side effects, in TypeScript because a hostile `toJSON()` override
could return misleading data, and in Rust because a hostile archive could claim any
`type_name` string.

**Test derivation:**
- Java: `SessionArchiveV3Test` (record/enum/primitive/unit round-trip, v2-on-v3
  back-compat, unknown-version rejection) and `NetEventConverterTest.TokenInfoConversion`
  (structured field projection).
- TypeScript: `session-archive-v3.test.ts` (analogous round-trip) and
  `session-archive-v2.test.ts` (explicit v2 emission remains possible).
- Rust: `session_archive_reader::tests::v3_roundtrip_preserves_structured_token` (end-to-end
  writer→reader through `TokenProjectorRegistry`),
  `reader_accepts_v3_archives` (third-party v3 archive hydration), and
  `read_rejects_unsupported_version`.

---

## Event Query Helpers

#### EVT-030: Event Filtering

**Priority:** SHOULD

The event store or helper functions support:
- Filter by event type
- Filter by transition name
- Filter for failure events
- Count events

**Acceptance Criteria:**
1. `eventsOfType(TransitionCompleted)` returns only completed events.
2. `transitionEvents("MyTransition")` returns all events for that transition.
3. `failures()` returns TransitionFailed, TransitionTimedOut, and ActionTimedOut events.

**Test derivation:** Run net with mixed events; verify each filter returns correct subset.
