# Changelog

## 1.7.0

### Archive format v2 (all three languages)

`SessionArchive` is now a sealed hierarchy (`V1` / `V2`) — Java sealed interface + records,
TypeScript discriminated union keyed on `version: 1 | 2`, Rust enum. The v2 header adds:

- `endTime` — the `complete()` timestamp, preserving session duration across archival.
- `tags` — the user-defined tag snapshot at write time.
- `metadata` (new `SessionMetadata`) — single-pass aggregates: event-type histogram
  (PascalCase keys, alphabetical, identical wire format across languages), first/last event
  times, and `hasErrors` (true for any `TransitionFailed`, `TransitionTimedOut`,
  `ActionTimedOut`, or `LogMessage` at level `ERROR`, case-insensitive).

v2 lets listing/sampling tools answer "which sessions had errors" or "how many events of
type X" without decompressing the body. Per-event wire format is identical to v1.

### Backward compatibility

- Readers peek `version` via a probe DTO and deserialize into the matching variant. v1
  archives from libpetri ≤ 1.6.1 remain fully readable; mixed v1/v2 buckets coexist.
- v2-only accessors (`tags()`, `endTime()`, `metadata()`) return safe defaults on v1 archives.
- `writeV1()` / `write_v1()` escape hatch for producing archives consumable by older readers.
  Default `write()` emits v2.
- Shared metadata helpers usable on live sessions or v1 reads:
  Java `SessionMetadata.fromEvents`, TypeScript `computeMetadata`, Rust `compute_metadata`.
- Rust adds `NetEvent::has_error_signal()` — superset of `is_failure()` that also catches
  `LogMessage` at `ERROR`. `is_failure()` is unchanged.

### Performance

- v2 overhead vs v1: **+0.8%** on a 1000-event session (20,872 vs 20,703 bytes LZ4).
  LZ4/gzip frame dedup absorbs the repeated header strings; v2's value is at read time, not
  on disk.

### Compatibility

- **Java** binary-incompatible for code pattern-matching on the old `SessionArchive` record —
  recompile against 1.7.0.
- **Rust** `imported.metadata.session_id` (field) → `session_id()` (method). No in-workspace
  consumers affected.
- **TypeScript** source-compatible; the discriminated union narrows existing
  `version === CURRENT_VERSION` checks.
- Archive envelopes still differ by language (Java LZ4, TS/Rust gzip; Java/TS ISO-8601,
  Rust u64-ms). Cross-language read is future work.
- No spec changes for the archive format — it is implementation-defined.

### Bulk token output on `TransitionContext` (all three languages)

Transition actions can now push multiple tokens to the same output place in one call,
avoiding the `for v in values { ctx.output(...) }` loop that previously incurred per-element
place-declaration validation:

- **Java**: `@SafeVarargs public final <T> TransitionContext output(Place<T>, T...)` and
  `<T> TransitionContext output(Place<T>, Iterable<? extends T>)`. Strict-match overload
  resolution (JLS §15.12.2.5) keeps the existing single-value `output(Place<T>, T)` call
  path unchanged.
- **TypeScript**: `ctx.output<T>(place, ...values: T[])` and
  `ctx.outputToken<T>(place, ...tokens)` now accept rest parameters. Single-arg call sites
  continue to type-check.
- **Rust**: new `ctx.output_many<T>(place_name, impl IntoIterator<Item = T>)`. Accepts
  arrays, `Vec`, slice iterators, and iterator adaptors. The existing single-value
  `output()` is untouched.

All three implementations validate the output place **once** before iterating, share a
single timestamp across the produced tokens (matching "fired at time T" semantics), and
fail fast on undeclared places without leaving partial output. See [CORE-062].

### Spec Changes

- **CORE-062 updated.** Extended the acceptance criteria to cover the bulk-form API, the
  validate-once-fail-fast contract, and the empty-bulk-is-a-no-op degenerate case.

## 1.6.1

### Session tags (all three languages)

`DebugSessionRegistry` sessions now carry arbitrary `Map<String,String>` tags
(e.g. `{channel: "voice", env: "staging"}`). Storage lives on the `DebugSession` itself —
no shadow map, no cleanup coordination. Java uses `ConcurrentHashMap` for lock-free updates;
TS/Rust mutate in place. New APIs across languages: `register(id, net, tags)`,
`tag(id, key, value)`, `tagsFor(id)`, and an optional `tagFilter` on `listSessions` /
`listActiveSessions`.

### Session endTime

`complete(sessionId)` stamps an `endTime` once (first-completion semantics). `duration()`
returns `Optional<Duration>` / `undefined | number` / `Option<u64>` ms.

### Wire protocol

- `DebugResponse.SessionSummary` adds optional `tags`, `endTime`, `durationMs`. Older clients
  tolerate the new fields.
- `registerImported` overload accepts `endTime` + `tags` for archive round-trips.

### Breaking changes (Rust internal wire format)

- `DebugCommand` / `DebugResponse` inline enum-variant fields now serialize in **camelCase**
  to match Java/TypeScript (`sessionId`, `activeOnly`, `tagFilter`, `netName`, `dotDiagram`,
  `eventCount`, `startIndex`, `hasMore`, `currentMarking`, `enabledTransitions`,
  `inFlightTransitions`, `currentIndex`, `breakpointId`, `eventIndex`, `fromIndex`, `fileName`,
  `storageAvailable`). Previously snake_case, which prevented the TypeScript debug-ui from
  connecting to a Rust backend. Inner struct types were already correct. Update any Rust-only
  client code that hardcoded JSON keys.

### Compatibility

Otherwise additive and source-compatible. Archive v1 format untouched; v2 with tags +
histograms ships in 1.7.0. No spec changes.

## 1.5.3

### Dependency Updates

- **lz4-java**: changed groupId from `org.lz4` to `at.yawk.lz4` (upstream artifact relocation).

## 1.5.2

### Bug Fixes

- **Fixed CPU spin in `drain()` with enabled timed transitions (Java, Rust).** Calling `drain()`
  on an executor with environment places while timed transitions were enabled but not yet ready
  (nothing in-flight) caused the orchestrator to spin at 100% CPU. In Java, `awaitWork()` fell
  through without blocking because `hasEnvironmentPlaces && !draining.get()` was false and no
  other branch applied. In Rust, the same condition caused premature termination (dropping
  enabled timed transitions). With 20 concurrent nets on 4 cores, total CPU burned was ~5,600ms
  for a 400ms wall-clock window. Affects `BitmapNetExecutor` and `NetExecutor` (Java),
  `BitmapNetExecutor` and `PrecompiledNetExecutor` (Rust async). Java `PrecompiledNetExecutor`
  and TypeScript were already correct. Regression introduced in 1.5.0.

## 1.5.1

### Bug Fixes

- **Fixed CPU spin in `close()` with in-flight async actions (Java).** Calling `close()` while
  async transition actions were running caused the orchestrator thread to spin at 100% CPU until
  those actions completed. The `awaitCompletionOrEvent()` poll loop now blocks with 50ms polling
  intervals instead of exiting immediately when `closed` is set. Affects all three Java executors:
  `BitmapNetExecutor`, `NetExecutor`, `PrecompiledNetExecutor`. TypeScript and Rust were not
  affected (event-driven architectures). Regression introduced in 1.5.0.

## 1.5.0

### Breaking Changes

- **Removed `longRunning` flag.** Long-running behavior is now implicit when environment places
  are registered — no explicit flag needed. Remove `.longRunning(true)` / `long_running: true`
  from all executor builders/options.

- **`close()` is now immediate shutdown (ENV-013).** Queued events are discarded; in-flight
  actions complete; executor terminates. Use the new `drain()` for graceful behavior.

- **Rust: channel type `ExternalEvent` → `ExecutorSignal`.** The async channel now carries
  lifecycle signals (`Drain`, `Close`) alongside events. Wrap events:
  `tx.send(ExecutorSignal::Event(event))`.

### New Features

- **`drain()` — graceful shutdown (ENV-011).** Rejects new `inject()` calls, processes
  queued events, completes in-flight actions, terminates at quiescence.

- **`close()` — immediate shutdown (ENV-013).** Discards queued events, completes in-flight,
  terminates. `close()` after `drain()` escalates from graceful to immediate.

- **Rust: `ExecutorHandle`** — RAII lifecycle wrapper with typed `inject()`/`drain()`/`close()`
  and auto-drain on drop. Re-exported from umbrella crate under `tokio` feature.

### Spec Changes

| Requirement | Change |
|---|---|
| ENV-006 | Reject `inject()` on closed **or draining** executor |
| ENV-010 | Rewritten: implicit long-running from environment places |
| ENV-011 | Rewritten: graceful `drain()` (was "explicit close") |
| ENV-013 | **New**: immediate `close()` |
| Total | 155 → 156 requirements |
