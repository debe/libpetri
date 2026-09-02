# libpetri for Rust

[![crates.io](https://img.shields.io/crates/v/libpetri)](https://crates.io/crates/libpetri)
[![docs.rs](https://img.shields.io/docsrs/libpetri)](https://docs.rs/libpetri)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](https://github.com/debe/libpetri/blob/main/LICENSE)

The umbrella crate for libpetri's Rust 2024 Coloured Time Petri Net engine. It re-exports the model, runtime, events, verification, and DOT export APIs from one package.

See the [project README](https://github.com/debe/libpetri#why-a-petri-net) for the motivation and a workflow demonstrating every arc type, concurrent actions, and timeout routing. Contributors should use the [Rust workspace guide](https://github.com/debe/libpetri/blob/main/rust/README.md).

## Install

```bash
cargo add libpetri
# Add async execution and external events when needed:
cargo add libpetri --features tokio
```

Requires Rust 1.88 or newer.

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

## What is included

- Typed places and tokens; input, output, read, inhibitor, and reset arcs.
- Immediate, deadline, delayed, window, and exact transition timing.
- AND, XOR, timeout, and input-forwarding output routes.
- Open subnet composition, port/channel binding, place fusion, and action overrides.
- Bitmap reference and precompiled production executors.
- Environment events, event stores, DOT export, and ν-net identity correlation.
- Structural analysis, timed state classes, and feature-gated SMT verification.

Transition futures may overlap, but one orchestrator owns the marking. This keeps token movement deterministic and makes concurrency visible in the net rather than hidden inside shared mutable state.

## Features

| Feature | Effect |
|---|---|
| `tokio` | Async execution and environment-event APIs |
| `z3` | SMT verification API; requires a `z3` executable (4.8.0 or newer, on `PATH` or `LIBPETRI_Z3`) at runtime |
| `debug` | Debug protocol module |
| `archive` | Debug module and session archive support |

## Executors

Use `BitmapNetExecutor` while developing semantics and `PrecompiledNetExecutor` for hot production paths. Both consume the same immutable `PetriNet` and are kept aligned by differential tests; the Lean development proves agreement for the untimed immediate fragment.

## Links

- [Documentation](https://docs.rs/libpetri)
- [Specification](https://github.com/debe/libpetri/blob/main/spec/00-index.md)
- [Lean proofs](https://github.com/debe/libpetri/blob/main/lean/README.md)
- [Changelog](https://github.com/debe/libpetri/blob/main/CHANGELOG.md)
- [Apache License 2.0](https://github.com/debe/libpetri/blob/main/LICENSE)
