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

Emitted when a transition's timing clock restarts while the transition stays marked enabled: another transition's firing left it disabled in the intermediate marking, and the marking enabled it again before the executor observed the gap (see [TIME-012]).

**Acceptance Criteria:**
1. Emitted only when the transition stays marked enabled but its clock restarts.
2. Not emitted on initial enablement, nor on re-enablement after an observed disablement (both are `TransitionEnabled`).

**Depends on:** [TIME-012]
**Test derivation:** Transition T enabled; another transition consumes T's input token, and a synchronous action deposits a new one before the executor re-evaluates T; verify TransitionClockRestarted for T. An executor that re-evaluates between consumption and deposit reports TransitionEnabled instead ([TIME-012] AC6).

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
- Transition name — **absent when the diagnostic is not attributable to a transition** (see below)
- Logger name
- Log level
- Message
- Error/throwable details (optional)

**The engine may also emit diagnostics of its own** through this event rather than adding an event
type per diagnostic — an unknown place in an initial marking ([CORE-072]), a repeated output place,
and similar. Such an event carries **no transition name**, because none is responsible for it.
Consumers MUST therefore treat the transition name as optional and MUST NOT key, filter or group on
it without handling its absence.

An engine diagnostic SHOULD be emitted only where it reports something the caller did not ask for
and would otherwise not learn. A diagnostic on a path the caller explicitly requested — a `close()`
it called itself ([ENV-013]) — is a false positive: it fires on every run of a net whose normal
ending is a shutdown ([ENV-012]), and a warning that always fires trains its reader to ignore the
level. Where a queryable result already carries the information ([EXEC-041] AC3), the event is an
addition to it and MUST NOT be the only signal.

**Acceptance Criteria:**
1. Log statements within actions are captured as LogMessage events.
2. Log level (INFO, WARN, ERROR, etc.) is preserved.
3. Exception details are included when present.
4. An engine-emitted diagnostic carries no transition name, and every consumer of the event
   tolerates its absence.
5. No engine diagnostic is emitted on a caller-requested termination path.

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

A marking snapshot carried on this event is the snapshot form of [CORE-073], and [CORE-073]'s
canonical place-order rule applies to it: where an implementation emits this event, the places of
the marking it carries MUST appear in ascending code-point order of the place name. The event is
an ordered, in-process value, so the order is both meetable and observable there, and it is one
of the two places a host takes a snapshot from.

The order is **not** promised past the event. A JSON session archive ([EVT-025]) and the JSON
debug protocol are unordered media, and code-point order is deliberately not required of them.
What is required of any rendering of this event — those two included — is **reproducibility
across runs of the same implementation**: two runs over identical data MUST produce identical
output, so a rendering MUST NOT pass the marking through a container whose iteration order is
randomised per process ([CORE-073]).

Emitting this event MUST NOT fail the run. In particular the refusal [CORE-073] requires for two
same-named places belongs to the host-facing snapshot and restore operations, not to this event.

**Acceptance Criteria:**
1. Emitted at least at execution start (initial marking) and before execution completion.
2. Snapshot is a deep defensive copy (not a live reference).
3. Only non-empty places are included.
4. The places of the marking carried on the event appear in ascending code-point order of the
   place name ([CORE-073] AC12), on every executor, including for a place name above U+FFFF.
5. Rendering the same event stream twice with one implementation — into an archive or onto the
   debug protocol — yields identical output.

**Depends on:** [CORE-073]
**Implementation status:** **Java** and **TypeScript** emit the event at start and before
completion, on both executors, in canonical order. **Rust** — and **Python**, which rides it —
declares the event and consumes it (debug converter, marking cache, archive metadata) but has **no
producer**: no executor emits it, so AC1–AC4 are unmet there and a test that constructs the event
by hand is not coverage of them. AC5 holds in all four. Rust's tests cite this requirement for
AC5 alone — the `libpetri-debug` rendering-order tests over debug frames, the marking cache, the
net structure and archive headers, each of which failed on the per-process-randomised map they
replaced. A converter-level test of event-to-JSON order would prove nothing (`serde_json`'s map is
ordered unless `preserve_order` is enabled, and it is not), so there is deliberately none.

**Test derivation:** Run net; verify MarkingSnapshot at start and end; verify snapshot accuracy.
For AC4, run a net whose place names include one above U+FFFF and one in U+E000–U+FFFF and assert
the order on the emitted event. For AC5, render one recorded stream twice — in two processes where
the implementation's default map is randomised per process — and compare the output.

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
- Rust: Implemented (`libpetri-debug::DebugEventStore`, crossbeam-channel subscriptions)

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

**Key order in an archive is not guaranteed, and [CORE-073]'s canonical order does not reach it.**
A JSON object is an *unordered* collection by definition, so an archive that renders a marking as
one carries no order regardless of what the producer did. Some implementations preserve insertion
order incidentally; JavaScript cannot, because it orders integer-like keys numerically ahead of
every other key whatever the insertion order — a net with a place named `2` reorders itself. The
JSON debug protocol is the same medium and is bound the same way.

This is a bound on the medium, not a defect to fix: canonical order is guaranteed **on the snapshot
form and on the event** ([CORE-073], [EVT-014]), which is where a host that hashes, diffs or
content-addresses should take it. A host needing a byte-stable archive artefact *across
implementations* MUST canonicalise at its own serialization boundary rather than relying on the
object's key order.

What the medium does not excuse is **irreproducibility**. An archive written twice by the same
implementation from identical run data MUST NOT differ ([CORE-073], [EVT-014] AC5). JavaScript's
numeric-first key order is arbitrary but fixed, so it satisfies this; a marking copied through a
per-process-randomised map does not, and an implementation MUST NOT put one on the path to the
archive or the debug protocol. This asks for no change of archive format.

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
- Filter by place name (for token events)
- Pagination (offset / limit) over the filtered result
- Filter for failure events
- Count events, and an event-type histogram (counters)

**Acceptance Criteria:**
1. `eventsOfType(TransitionCompleted)` returns only completed events.
2. `transitionEvents("MyTransition")` returns all events for that transition.
3. Place filtering returns only token events for the named place(s); offset/limit page the result.
4. `failures()` returns TransitionFailed, TransitionTimedOut, and ActionTimedOut events.
5. `counters()` returns a `{eventType: count}` histogram whose values sum to the total event count.

**Test derivation:** Run net with mixed events; verify each filter, pagination, and the counters
histogram return correct subsets / totals.

---

## Live Streaming & Replay

#### EVT-031: EventStore Live Subscriptions

**Priority:** SHOULD

An event store may expose a live subscription that streams events as they are appended — distinct
from the post-hoc snapshot reads of [EVT-020]. A subscription:
- delivers only events matching its server-side filters (by type, transition, and place);
- is forward-only — events appended **before** the subscription was created are not replayed;
- batches delivery by a caller-chosen `batch_size` and `batch_timeout_ms` (a `batch_size = 1`,
  `batch_timeout_ms = 0` "unary" mode delivers one event at a time for low latency);
- is bounded — it uses a finite channel capacity with a documented back-pressure / drop policy;
- terminates cleanly on explicit close or when the store is dropped.

This differs from [EVT-024] (DebugEventStore live tailing for debug UIs): EVT-031 governs
subscriptions over the ordinary observability store, with server-side filtering and batching.

**Acceptance Criteria:**
1. A subscriber receives only events matching its filters, in append order.
2. Events appended before the subscription are not delivered (forward-only).
3. Unary mode delivers one event per batch; batched mode delivers up to `batch_size`, flushing
   early after `batch_timeout_ms`.
4. Explicit close ends iteration cleanly; a full channel applies the documented policy.

**Depends on:** [EVT-020], [EVT-021]
**Status:** Proposed
**Implementation status:** Rust binding + Python (`InMemoryEventStore.subscribe(...)`,
`async for batch in ...`) implemented; Java/TypeScript pending.
**Test derivation:** Run an async net feeding environment events; subscribe with a transition
filter; verify batched forward-only delivery and clean close.

---

#### EVT-032: Marking Replay Cache

**Priority:** SHOULD

A replay cache reconstructs execution state at an arbitrary event index from a recorded event
stream, for debug-protocol seek / step. `compute_at(events, index)` returns a `ComputedState`
— the marking (token counts per place), enabled transitions, and in-flight transitions — replayed
from the nearest periodically-cached snapshot rather than from the start of the stream.

**Acceptance Criteria:**
1. `compute_at(events, 0)` is the initial/empty state; `compute_at(events, len)` matches the final
   marking shape.
2. An index beyond the stream length is clamped to the end (no panic).
3. Repeated calls reuse cached snapshots and return state structurally equal to a from-scratch
   replay.
4. The marking in `ComputedState` carries token counts; replayed tokens need not carry value
   payloads (events carry type + structured metadata, not live objects).

**Depends on:** [EVT-021], [CONC-025]
**Implementation status:** Implemented in all four: Rust (`libpetri-debug::MarkingCache`), Python
(`MarkingCache`, `ComputedState`), Java (`org.libpetri.debug.MarkingCache.computeAt`) and
TypeScript (`MarkingCache.computeAt` in `libpetri/debug`).
**Test derivation:** Record a multi-firing run; `compute_at` at 0, an intermediate index, the end,
and beyond-end; verify clamping and snapshot reuse.
