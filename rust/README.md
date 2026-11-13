# libpetri for Rust

[![crates.io](https://img.shields.io/crates/v/libpetri)](https://crates.io/crates/libpetri)
[![Rust](https://img.shields.io/badge/Rust-1.88%2B-orange)](Cargo.toml)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](../LICENSE)

The Rust 2024 implementation of libpetri. This directory is a Cargo workspace containing the typed model, execution backends, events, verification, export, debug support, documentation tooling, benchmarks, and Python bindings.

The [project README](../README.md) walks through one agent turn as a net: reading it, running it, and checking it with the verifier. The published umbrella crate has a separate [crates.io-facing guide](libpetri/README.md).

## Install

```bash
cargo add libpetri --features tokio
```

Rust 1.88 or newer is required. The `tokio` feature enables asynchronous execution and external event injection; synchronous execution works without it.

## Quick start

```rust
use libpetri::*;

let input = Place::<String>::new("input");
let output = Place::<String>::new("output");

let copy = Transition::builder("copy")
    .input(one(&input))
    .output(out_place(&output))
    .action(fork())
    .build();

let net = PetriNet::builder("example").transition(copy).build();
let mut marking = Marking::new();
marking.add(&input, Token::at("hello".to_owned(), 0));

let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
    &net, marking, ExecutorOptions::default(),
);
executor.run_sync();

assert_eq!(&*executor.marking().peek(&output).unwrap(), "hello");
```

## Execution and concurrency

`BitmapNetExecutor` is the reference backend. `PrecompiledNetExecutor` uses a compiled opcode program, ring-buffer token storage, dirty sets, and priority queues while preserving the same semantics.

With the `tokio` feature, transition futures can overlap while the orchestrator alone updates the marking. Actions receive owned context and return it with their outputs, preventing concurrent mutation of runtime state.

`termination_reason()` tells a completed run (`Quiescent`, `Terminal`, see `is_complete()`) from a truncated one (`Closed`, `Stopped`). A synchronous action's outputs are deposited inside the firing pass, so the pass stops at the deposit that marks a terminal place.

## Checkpoint and resume

```rust
let snap = handle.snapshot().expect("running").await?;   // does not stop the net
if snap.is_restore_point() { save(&snap.marking); }       // MarkingSnapshot

let resumed = Marking::from_snapshot(&saved);             // pass as the initial marking
```

A `MarkingSnapshot` is a `BTreeMap` from place name to tokens and carries `created_at` through untouched. Persist one only when `is_restore_point()` is true; otherwise an action had consumed inputs whose outputs had not landed. Timing clocks restart on resume, so a `deadline` gets a fresh full budget. Minted ν-names are `<transition>#<scope>:<n>` with a random scope per executor; pin `execution_scope(...)` when a replay must reproduce them, fresh per run segment. The default scope is 128 bits of the platform's randomness. An invalid scope panics at construction, so check untrusted input with `validate_execution_scope` first.

Injections and snapshot requests share one FIFO channel, so every earlier injection is in the marking a snapshot reports. An asynchronous action that awaits `snapshot()` is reported in flight. A synchronous action under `run_async` runs inside the orchestrator loop: it may send the request but must not block on the reply, which arrives after the firing has settled. `run_sync` has no signal channel.

## Clocks

`ExecutorOptions::clock` (or the `clock(...)` builder method) drives a run from a host clock implementing `ExecutorClock` (`now_ms`, `epoch_ms`, `await_work`, `await_work_async`). The crate ships `SystemClock`, `ManualClock`, which jumps to each timing boundary, and `SteppedClock`, which moves only when the host advances it (`settle`, `settle_after`). `seed_token()` stamps an initial token from the clock's epoch. Without a clock the executor reads the real clocks directly. The contract is settled, but the names and signatures of this API may still change.

## Events

The Rust events, which Python also uses, carry less than the Java and TypeScript ones:

- `TransitionCompleted` and `TransitionTimedOut` carry the transition name and a timestamp only.
- `TransitionFailed` carries one `error` text and no exception type.
- `ActionTimedOut` carries `timeout_ms`. It is emitted when the executor settles the timeout outcome, and no `TransitionCompleted` follows it.

## Workspace crates

| Crate | Purpose |
|---|---|
| `libpetri` | Umbrella package and top-level re-exports |
| `libpetri-core` | Places, tokens, transitions, arcs, timing, and composition |
| `libpetri-runtime` | Bitmap and precompiled executors |
| `libpetri-event` | Events and event stores |
| `libpetri-verification` | Structural, timed, and SMT verification |
| `libpetri-export` | DOT export |
| `libpetri-debug` | Debug protocol and archives |
| `libpetri-docgen` | Rustdoc diagram generation |
| `libpetri-py` | PyO3 extension used by the Python package |

## Features

| Feature | Effect |
|---|---|
| `tokio` | Async executor and environment-event APIs |
| `z3` | Enables the SMT verification surface; a `z3` executable (4.8.0 or newer, on `PATH` or named by `LIBPETRI_Z3`) is required at runtime |
| `debug` | WebSocket debug protocol |
| `archive` | Debug support plus session archives |

## Build and test

```bash
cargo build --workspace --exclude libpetri-py --all-features
cargo test --workspace --exclude libpetri-py --all-features
cargo test -p libpetri-runtime
cargo bench
```

`libpetri-py` is intentionally excluded from the normal workspace command because Python-extension linkage is provided by maturin.

## Project links

- [Language-agnostic specification](../spec/00-index.md)
- [Lean soundness and backend-refinement proofs](../lean/README.md)
- [Changelog](../CHANGELOG.md)
- [Apache License 2.0](../LICENSE)
