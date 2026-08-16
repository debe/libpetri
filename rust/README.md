# libpetri for Rust

[![crates.io](https://img.shields.io/crates/v/libpetri)](https://crates.io/crates/libpetri)
[![Rust](https://img.shields.io/badge/Rust-1.88%2B-orange)](Cargo.toml)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](../LICENSE)

The Rust 2024 implementation of libpetri. This directory is a Cargo workspace containing the typed model, execution backends, events, verification, export, debug support, documentation tooling, benchmarks, and Python bindings.

For the motivation and the all-arcs concurrent timeout example, see the [project README](../README.md#why-a-petri-net). The published umbrella crate has a separate [crates.io-facing guide](libpetri/README.md).

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
| `z3` | Enables the SMT verification surface; the `z3` executable is required at runtime |
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
