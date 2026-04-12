# Changelog

## Unreleased

### New Features

- **Bulk token output on `TransitionContext` (all three implementations).** Transition
  actions can now push multiple tokens to the same output place in a single call,
  avoiding the `for v in values { ctx.output(...) }` loop that previously incurred
  per-element place-declaration validation:
  - **Java**: added `@SafeVarargs public final <T> TransitionContext output(Place<T>, T...)`
    and `<T> TransitionContext output(Place<T>, Iterable<? extends T>)`. Strict-match
    overload resolution (JLS §15.12.2.5) keeps the existing single-value
    `output(Place<T>, T)` call path unchanged.
  - **TypeScript**: `ctx.output<T>(place, ...values: T[])` and `ctx.outputToken<T>(place, ...tokens)`
    now accept rest parameters. Single-arg call sites continue to type-check.
  - **Rust**: new `ctx.output_many<T>(place_name, impl IntoIterator<Item = T>)` method.
    Accepts arrays, `Vec`, slice iterators, and iterator adaptors. The existing
    single-value `output()` is untouched.

  All three implementations validate the output place **once** before iterating, share
  a single timestamp across the produced tokens (matching "fired at time T" semantics),
  and fail fast on undeclared places without leaving partial output. See [CORE-062].

### Spec Changes

- **CORE-062 updated.** Extended the acceptance criteria to cover the bulk-form API,
  the validate-once-fail-fast contract, and the empty-bulk-is-a-no-op degenerate case.

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
