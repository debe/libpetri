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

Emitted when the executor reaps a transition: a reapable transition whose elapsed time is strictly greater than its latest bound plus the deadline tolerance, without firing ([TIME-013]). Contains:
- Timestamp
- Transition name
- Deadline duration
- Actual elapsed duration since enablement

**Acceptance Criteria:**
1. Emitted when elapsed time is strictly greater than the latest bound plus the deadline
   tolerance.
2. After this event the transition is reaped: it stays enabled but is not armed, and does not
   fire until one of its arc places is written ([TIME-013]).

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
**Kind:** F

The event store provides:
- `append(event)` — thread-safe event addition
- `events()` — a subsequence of the appended events, in append order
- `isEnabled()` — whether event capture is active

The list `events()` returns *shall* be a subsequence of the events appended to the store: only appended events, in the order they were appended, each append at most once. A store that keeps token payloads only for some places (the Python binding's `capture_tokens` filter) is compared with the appended events after the same payloads are removed from them. Which appended events the list leaves out, and whether it is a copy or a live view of the store, is up to each store ([EVT-021], [EVT-022], [EVT-024]).

Events reach a store through the executor, which appends them only while the store reports itself as enabled (`isEnabled()` returns true; in Rust, the store type's `ENABLED` constant is true).

**Acceptance Criteria:**
1. append() is safe to call from any thread.
2. events() returns a subsequence of the appended events, in append order; whether that list is a copy or a live view is not specified.
3. isEnabled() controls whether the executor appends events to the store.

**Test derivation:** Append events from multiple threads; verify events() returns only appended events, each at most once, in the order the appends took effect (on the in-memory store, all of them, [EVT-021]).

---

#### EVT-021: InMemoryEventStore

**Priority:** MUST
**Kind:** F

A thread-safe in-memory event store that retains all events in the order they were appended.

A new in-memory event store *shall* return no event from `events()`.

*When* an event is appended to the in-memory event store, a call of `events()` made right after the append *shall* return the events that a call made right before the append returns, with that event added at the end.

*Where* the in-memory event store provides `clear()`, a call of `events()` made right after `clear()` *shall* return no event.

The in-memory event store *shall* report itself as enabled, so that an executor appends every event it emits to it (see [EVT-020]): `isEnabled()` returns true in Java and TypeScript, the store type's `ENABLED` constant is true in Rust, and the Python binding's store is written through a Rust store whose `ENABLED` constant is true.

A call of `events()` changes nothing that a later call of `events()` returns, so the sentences above speak of what a call returns after the appends and clears made so far.

**Acceptance Criteria:**
1. Events are stored in insertion order.
2. Thread-safe append (concurrent callers do not lose events).
3. events() returns the events appended since the last clear() (every appended event where the store has no clear()), in the order they were appended; what a returned list shows after later operations, whether it is a copy or a live view, is not specified.
4. Where the store provides clear() (TypeScript; in Java only on the package-private InMemoryEventStore class, which EventStore.inMemory() returns as the EventStore interface), clear() empties it for test reuse.

**Test derivation:** Append 100 events; verify events() returns 100 in order.

---

#### EVT-022: NoopEventStore

**Priority:** MUST
**Kind:** F

A zero-cost event store that discards all events. When used, the executor skips event object creation entirely.

The noop event store *shall* return no event from `events()`, whatever was appended to it, and the list it returns *shall* stay empty whatever is appended to it later.

*When* an event is appended to the noop event store, the store *shall* discard it.

The noop event store *shall* report itself as not enabled (`isEnabled()` returns false; in Rust, the store type's `ENABLED` constant is false).

**Acceptance Criteria:**
1. append() is a no-op.
2. events() returns empty.
3. isEnabled() returns false.
4. The executor does not allocate event objects when the noop store is used.

**Test derivation:** Run net with noop store; verify no events captured; verify no allocation overhead (benchmark).

---

#### EVT-023: LoggingEventStore

**Priority:** SHOULD
**Kind:** F

An event store decorator that logs events to the platform's logging framework at appropriate levels before delegating to a wrapped store.

*When* an event is appended to the logging event store, the store *shall* log the event once, at the level of the event's kind, *shall* then pass the event once to the wrapped store, and *shall* log no other record and pass no other event, whatever store it wraps.

The logging event store *shall* make the logging call of an event whenever the logging framework has the call's level enabled, and *may* skip the call when the framework has that level disabled.

The logging event store *shall* log TransitionFailed, TransitionTimedOut and ActionTimedOut events at WARN level.

The logging event store *shall* log ExecutionStarted and ExecutionCompleted events at INFO level.

The logging event store *shall* log TransitionEnabled, TransitionClockRestarted, TransitionStarted and TransitionCompleted events at DEBUG level.

The logging event store *shall* log TokenAdded, TokenRemoved, MarkingSnapshot and LogMessage events at TRACE level.

The logging event store *shall* return from `events()` what the wrapped store returns.

The logging event store *shall* report itself as enabled, whatever the wrapped store reports (`isEnabled()` returns true).

**Acceptance Criteria:**
1. Failure events (TransitionFailed, TransitionTimedOut, ActionTimedOut) logged at WARN level.
2. Lifecycle events (ExecutionStarted, ExecutionCompleted) logged at INFO level.
3. The other transition events (TransitionEnabled, TransitionClockRestarted, TransitionStarted, TransitionCompleted) logged at DEBUG level.
4. Token events (TokenAdded, TokenRemoved), MarkingSnapshot and LogMessage logged at TRACE level.
5. Delegates to wrapped store after logging; `events()` returns the wrapped store's events.
6. Reports itself as enabled whatever store it wraps.

**Implementation notes:**
- Java: Full implementation with `java.lang.System.Logger`
- TypeScript: Not implemented
- Rust: Not implemented
- Python: Not implemented

**Test derivation:** Run net with logging store; verify log output at correct levels.

---

#### EVT-024: DebugEventStore

**Priority:** SHOULD
**Kind:** F

An event store with live tailing support for debug UIs. Supports:
- Subscriptions (consumers notified of new events)
- Capacity management (eviction of old events)
- Session tracking

A debug event store has a capacity: a positive number of events, 10,000 unless the caller gives another. A debug event store is open until its `close()` is called.

*When* events have been appended to a debug event store one after the other, a call of `events()` *shall* return the newest of them, as many as the store's capacity allows, in the order they were appended.

*When* an event is appended to an open debug event store, the append *shall* complete without waiting for any subscriber to receive the event.

Each subscriber of a debug event store *shall* receive only events appended to the store, each at most once and, for appends that do not overlap in time, in the order they were appended. A subscriber may receive an event after the append that added it has returned.

*While* a debug event store is open, a caller *shall* be able to add a further subscriber, whatever subscribers the store already has.

*While* a debug event store is open, each subscriber that has not cancelled its subscription *shall* still be able to receive every event appended since it subscribed, whatever the other subscribers have received.

**Acceptance Criteria:**
1. While the store is open, each subscriber that has not cancelled can receive the events appended since it subscribed, each at most once and, for appends that do not overlap in time, in the order they were appended.
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
**Kind:** F

Completed debug sessions can be serialized to a length-prefixed compressed archive (LZ4
for Java, gzip for TypeScript and Rust) for later replay. The archive has a versioned
header followed by one length-prefixed JSON record per event.

Three header versions exist; readers MUST accept all three and dispatch into the matching
sealed variant (`V1`/`V2`/`V3`) so callers can pattern-match on writer guarantees.

**Header format** (the same field names and JSON types in every language; the encoding of time values differs, see below):

| Header | First shipped | Adds over previous |
|---|---|---|
| v1 | libpetri 1.5.x | baseline: `sessionId`, `netName`, `dotDiagram`, `startTime`, `eventCount`, `structure` |
| v2 | libpetri 1.7.x | `endTime`, `tags`, pre-computed `metadata` (event-type histogram, first/last, hasErrors) |
| v3 | libpetri 1.8.0 | same fields as v2; bump signals typed-token event bodies |

**Event body format** (per-language, because each implementation serializes its
own event shape — Java serializes the `NetEvent` record directly, TypeScript and Rust
serialize a `NetEventInfo` debug-protocol projection). Archive bodies are therefore not
byte-compatible across languages, and neither are whole archives: Java compresses with LZ4 and
the others with gzip, and every time value (the header's `startTime` and `endTime`, the event and
token timestamps of the body) is ISO-8601 text in Java and TypeScript and decimal epoch
milliseconds in Rust and Python. The Rust reader rejects an archive whose event timestamps are
ISO-8601 text, and the TypeScript reader reads decimal epoch milliseconds as invalid dates, so an
archive is read correctly only by an implementation of the language that wrote it. All languages
agree on *semantic* content, not wire layout.

- **Java (v3):** `token: {valueType: <FQN>, v: <structured JSON>, createdAt: <iso>}`.
  Special cases: `{valueType: "void", createdAt}` for unit tokens (no `v`);
  `{valueType, text, createdAt}` fallback when Jackson cannot structure the value;
  legacy `{value, valueType: simpleName, createdAt}` from v1/v2 also accepted.
- **TypeScript (v3):** `token: {id, type, value: <String(value)>, structured?: <JSON>, timestamp}`.
  The `value` string is retained alongside the new optional `structured` field so the
  bundled debug UI keeps rendering without change. `type` is `value.constructor.name`
  (simple name — TypeScript has no portable FQN).
- **Rust (v3):** `token: {id, type, value, structured?, timestamp}`, with the field names and
  JSON shapes of TypeScript via a shared `NetEventInfo` camelCase serde contract; the
  `timestamp` is decimal epoch milliseconds where TypeScript writes ISO-8601 text. `type` is
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

*Where* an implementation provides session archives, *when* its reader reads a well-formed archive of header version 1, 2 or 3 in its own implementation's format (one whose `eventCount` and metadata are those of its body, as its writer writes them), the reader *shall* return the header variant of that version (`V1`, `V2` or `V3`).

*Where* an implementation provides session archives, *if* its reader reads an archive in its own implementation's format whose header version is not 1, 2 or 3, *then* the reader *shall* reject the archive with the error `Unsupported archive version: <version> (reader supports 1..3)`, which names the version it found and the supported range.

*Where* an implementation provides session archives, *when* its reader accepts a well-formed archive in its own implementation's format, it *shall* return the header's `eventCount` unchanged, the header's session fields and metadata as written, and one event for each record of the body, in body order.

*Where* an implementation provides session archives, *when* its writer writes an archive of a session for header version 1, 2 or 3 (`writeV1`, `writeV2`, or `write` for version 3), the header *shall* carry that version and the session's own header fields.

*Where* an implementation provides session archives, *when* its writer writes an archive, the writer *shall* take one snapshot of the event store, the header's `eventCount` *shall* be the number of events in that snapshot, a V1 header *shall* carry no metadata, the V2 and V3 metadata *shall* be computed from that snapshot, and the body *shall* hold one record for each event of that snapshot, in the order of the snapshot.

*Where* an implementation provides session archives, two archives its writer writes for the same header version from identical run data *shall* be identical.

*Where* an implementation provides session archives, its writer *shall* write an archive of any session for each of the header versions 1, 2 and 3 (`writeV1`, `writeV2`, and `write` for version 3), whatever the session's event store holds.

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
  token types via `Class.forName`. Known gap: the V2 and V3 header builds the tags and the
  metadata histogram with `Map.copyOf`, whose iteration order changes from one JVM to the next,
  so two JVMs write different headers for the same run data ([runtime-defects.md](runtime-defects.md) RD-17).
- TypeScript: Full implementation — default writer emits v3, `structured` projection via
  `JSON.parse(JSON.stringify(value))`.
- Rust: Full implementation — default writer emits v3 via a user-supplied
  `TokenProjectorRegistry`; reader hydrates into a `ReplayedTokenPayload` exposing the
  `structured` JSON without attempting to revive the original `T` (Rust has no
  `Class.forName` equivalent).
- Python: `write_from_store` writes through the Rust writer. Known gap: it copies the store into
  a debug store that keeps at most 10,000 events, so a larger store is archived without its
  oldest events (RD-18). Known gap: it writes version 3 only and offers no `writeV1` or `writeV2`
  (RD-19). Known gap: for an empty store it takes the start and end times from the wall clock, so
  two archives of the same empty session differ (RD-20).

**Cross-language replay:** Java → Java reconstructs typed tokens. TypeScript and Rust
archive bodies share field names and JSON shapes (shared `NetEventInfo` contract) but not the
time encoding, so neither reader reads the other's archives correctly; both preserve `structured` across
a round-trip. Java archive bodies use a different shape
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
**Kind:** F

The event store or helper functions support:
- Filter by event type
- Filter by transition name
- Filter by place name (for token events)
- Pagination (offset / limit) over the filtered result
- Filter for failure events
- Count events, and an event-type histogram (counters)

*Where* an implementation provides a query over the events of an event store, the query without offset and limit *shall* return exactly the events that `events()` returns and that match every filter the query gives, in the order `events()` returns them, for every query whose transition filter does not name the empty name.

A filter by event type *shall* match the events of the given types, a filter by transition name *shall* match the events that carry one of the given transition names, and a filter by place name *shall* match the events that carry one of the given place names.

An event that carries no transition name *shall* match no filter by transition name, and its presence in the store *shall not* change which other events such a filter returns.

*Where* an implementation provides offset and limit on a query, the query *shall* skip the first `offset` matching events and return the first `limit` of the matching events that follow (all of them when no limit is given), so that the page is taken over the filtered result and not over the store.

*Where* an implementation provides `failures()`, it *shall* return exactly the TransitionFailed, TransitionTimedOut and ActionTimedOut events that `events()` returns, in the order `events()` returns them.

*Where* an implementation provides `counters()`, it *shall* name each event type that occurs among the events `events()` returns exactly once, with the number of those events of that type, and *shall* name no other event type.

*Where* an implementation provides a count of events, the count *shall* be the number of events that `events()` returns whose type is one of the given types, or the number of all of them when no type is given.

**Acceptance Criteria:**
1. `eventsOfType(TransitionCompleted)` returns only completed events.
2. `transitionEvents("MyTransition")` returns all events that carry that transition name, also when the store holds events that carry no transition name.
3. Place filtering returns only token events for the named place(s); offset/limit page the result.
4. `failures()` returns TransitionFailed, TransitionTimedOut, and ActionTimedOut events.
5. `counters()` returns a `{eventType: count}` histogram whose values sum to the total event count.

**Implementation status:** the helpers differ per language. Filter by type: Java and TypeScript (`eventsOfType`), Python (`events(types=...)`); the Rust store has none. Filter by transition name: Java and TypeScript (`transitionEvents`), Rust (`transition_events`), Python (`events(transitions=...)`). Filter by place name, offset/limit and `counters()`: Python only. Count: all four count every event (`size()` in Java, TypeScript and Rust, `len()` in Python), and Python also counts by type (`count(types=...)`). `failures()`: all four. Every implementation marks the missing transition name of an engine diagnostic at the initial-marking seam by the empty name, so a filter for the empty name returns those diagnostics; such a filter is outside this requirement. Java's `transitionEvents` throws on a store that holds a log message with no transition name (an engine diagnostic of an interrupted run); this is a known gap in Java.
**Test derivation:** Run net with mixed events; verify each filter, pagination, and the counters
histogram return correct subsets / totals.

---

## Live Streaming & Replay

#### EVT-031: EventStore Live Subscriptions

**Priority:** SHOULD
**Kind:** B

An event store may expose a live subscription that streams events as they are appended, distinct
from the post-hoc snapshot reads of [EVT-020]. A subscription:
- delivers only events matching its server-side filters (by type, transition, and place);
- is forward-only: events appended **before** the subscription was created are not replayed;
- batches delivery by a caller-chosen `batch_size` and `batch_timeout_ms` (a `batch_size = 1`,
  `batch_timeout_ms = 0` "unary" mode delivers one event at a time for low latency);
- is bounded: it uses a finite channel capacity, and an append of a matching event that finds the channel full ends that subscription instead of waiting for room;
- terminates cleanly on explicit close, when the store is dropped, or when its channel overflows.

This differs from [EVT-024] (DebugEventStore live tailing for debug UIs): EVT-031 governs
subscriptions over the ordinary observability store, with server-side filtering and batching.

*Where* an event store provides live subscriptions, the events a subscription has received at any point, taken over all its batches in the order it received them, *shall* be events that match its filters and were appended to the store after the subscription was created and before that point, in append order, each at most once.

Each batch a subscription receives *shall* hold at least one event and at most `batch_size` events, so that with `batch_size = 1` it receives one event per batch.

Each subscription *shall* have a finite channel capacity.

*When* a receive has taken the first event of its batch, it *shall* add further events until the batch holds `batch_size` events, `batch_timeout_ms` have elapsed since it took that first event, or no further event can arrive, and *shall* then return the batch; with `batch_timeout_ms = 0` it *shall* add only the events already in the channel.

*When* an append of an event that matches the filters of a subscription finds its channel full, the store *shall* end that subscription: the subscription *shall* receive no event appended from then on, and, if none of its receives is pending at that append, its receives *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.

Until the store is dropped, an append *shall* be accepted at every point; in particular it *shall not* wait for room in the channel of a subscription.

*When* a subscription is closed while none of its receives is pending, it *shall* receive no further event, and its next receive *shall* report the end of the stream.

*When* the store is dropped, the receives of each of its subscriptions that has no receive pending *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.

**Acceptance Criteria:**
1. A subscriber receives only events matching its filters, in append order.
2. Events appended before the subscription are not delivered (forward-only).
3. Unary mode delivers one event per batch; batched mode delivers up to `batch_size`, flushing
   early after `batch_timeout_ms`.
4. Explicit close with no receive pending ends iteration cleanly; a full channel ends the subscription: it receives no later event, the append does not wait, and with no receive pending its receives report the end after they have taken the events its channel holds.

**Depends on:** [EVT-020], [EVT-021], [EVT-030]
**Status:** Proposed
**Implementation status:** Rust binding + Python (`InMemoryEventStore.subscribe(...)`,
`async for batch in ...`, and `subscribe_stream(...)`, which is `batch_size = 1` without the list wrapper) implemented; Java/TypeScript pending. Python's defaults are `batch_size = 64`, `batch_timeout_ms = 10` and `channel_capacity = 4096`, and a `batch_size` or `channel_capacity` of 0 is rejected with `ValueError`. In Python, `close()` called while a receive is pending does nothing, so the pending receive keeps waiting; this case is outside the requirement. A receive pending when an append finds its channel full is outside the requirement too. The end of the stream is reported the same way after a close, a drop and an overflow.
**Test derivation:** Run an async net feeding environment events; subscribe with a transition
filter; verify batched forward-only delivery and clean close.

---

#### EVT-032: Marking Replay Cache

**Priority:** SHOULD
**Kind:** F

A replay cache reconstructs execution state at an arbitrary event index from a recorded event
stream, for debug-protocol seek / step. `compute_at(events, index)` returns a `ComputedState`
— the marking (token counts per place), enabled transitions, and in-flight transitions — replayed
from the nearest periodically-cached snapshot rather than from the start of the stream.

*While* every snapshot in the replay cache is at an index no greater than the length of `events` and is the replay of `events` up to that index, `compute_at(events, index)` *shall* return the replay of the first `index` events of `events`, or of all of `events` when `index` is beyond its length.

*When* `compute_at(events, index)` returns, every snapshot it leaves in the replay cache *shall* be at an index no greater than the length of `events` and be the replay of `events` up to that index, provided every snapshot in the cache met both conditions before the call.

The replay of an event stream *shall* start from the empty state (no token in any place, no enabled and no in-flight transition) and apply its events in order, each as follows: a `MarkingSnapshot` sets the token count of every place it carries to the count it carries and of every other place to zero; a `TokenAdded` adds one token to its place; a `TokenRemoved` removes one token from its place, and does nothing if the place has none; a `TransitionEnabled` adds its transition to the enabled transitions; a `TransitionStarted` removes its transition from the enabled transitions and adds it to the in-flight transitions; a `TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut` or `ActionTimedOut` removes its transition from the in-flight transitions; any other event (`ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted`, `LogMessage`) leaves the state unchanged.

The enabled transitions are those with a `TransitionEnabled` event and no later `TransitionStarted` event, so they over-approximate the transitions enabled at that point of the run: a transition whose tokens another firing took, or a reaped transition, stays listed. The in-flight transitions are a set of names, so a transition with two firings in flight at once leaves it when its first firing ends. The replayed token counts include the initial marking only for a stream that reports it: a Java or TypeScript stream reports the initial marking in a `MarkingSnapshot` right after its `ExecutionStarted` event, while a Rust or Python stream reports no initial token. The two transition lists of a `ComputedState` are sets: their order is not specified.

**Acceptance Criteria:**
1. `compute_at(events, 0)` is the empty state; `compute_at(events, len)` is the replay of the whole
   stream.
2. An index beyond the stream length is clamped to the end (no panic).
3. Repeated calls on a stream that only grows at its end return state equal to a from-scratch
   replay: the same token count per place and the same sets of enabled and in-flight transitions,
   in an unspecified order. A stream that changed otherwise, for example by the eviction of its
   oldest events ([EVT-024]), needs `invalidate()` before the next call. Reusing cached snapshots
   is expected for speed only: it does not change the state returned.
4. The marking in `ComputedState` carries token counts; replayed tokens need not carry value
   payloads (events carry type + structured metadata, not live objects).

**Depends on:** [EVT-021], [EVT-004], [EVT-006], [EVT-007], [EVT-008], [EVT-009], [EVT-010], [EVT-011], [EVT-012], [EVT-014]
**Implementation status:** Implemented in all four: Rust (`libpetri-debug::MarkingCache`), Python
(`MarkingCache`, `ComputedState`), Java (`org.libpetri.debug.MarkingCache.computeAt`) and
TypeScript (`MarkingCache.computeAt` in `libpetri/debug`). Known gap: Java's `computeAt` does not
clamp an index beyond the stream length and throws `IndexOutOfBoundsException` (AC2). Known gap:
no debug protocol handler calls `invalidate()` when its debug store evicts events ([EVT-024]), so a
seek after an eviction can return a state that is not the replay (AC3).
**Test derivation:** Record a multi-firing run; `compute_at` at 0, an intermediate index, the end,
and beyond-end; verify clamping and snapshot reuse.
