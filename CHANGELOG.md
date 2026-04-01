# Changelog

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
