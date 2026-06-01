//! # libpetri-runtime — Petri Net Executors
//!
//! Provides two executors for running Coloured Time Petri Nets defined with
//! [`libpetri-core`](https://docs.rs/libpetri-core).
//!
//! ## BitmapNetExecutor
//!
//! The general-purpose executor. Single-threaded orchestrator with concurrent
//! async actions.
//!
#![doc = include_str!(concat!(env!("OUT_DIR"), "/executor_example.svg"))]
//!
//! ### Execution Loop (6 steps per cycle, per spec EXEC-001)
//!
//! 1. **Process completed** — collect outputs from finished async actions
//! 2. **Process events** — inject tokens from environment places
//! 3. **Update dirty** — re-evaluate enablement via bitmap masks (O(W) where W = ceil(places/64))
//! 4. **Enforce deadlines** — force-disable transitions past their deadline
//! 5. **Fire ready** — sorted by priority, then FIFO by enablement time
//! 6. **Await work** — sleep until an action completes, a timer fires, or an event arrives
//!
//! (The synchronous path runs steps 3–5; steps 1, 2, and 6 are async-only.)
//!
//! ### Key types
//!
//! - [`BitmapNetExecutor`](executor::BitmapNetExecutor) — the executor
//! - [`CompiledNet`](compiled_net::CompiledNet) — precomputed bitmap masks and reverse indexes
//! - [`ExecutorOptions`](executor::ExecutorOptions) — configuration (e.g. time source override)
//!
//! ## PrecompiledNetExecutor
//!
//! A high-performance alternative optimized for throughput-critical workloads.
//!
#![doc = include_str!(concat!(env!("OUT_DIR"), "/precompiled_example.svg"))]
//!
//! Additional optimizations over BitmapNetExecutor:
//! - Ring buffer token storage (flat `Vec<Option<ErasedToken>>` pool)
//! - Opcode-based consume dispatch (CONSUME_ONE, CONSUME_N, CONSUME_ALL, RESET)
//! - Two-level summary bitmaps for dirty/enabled iteration
//! - Reusable `HashMap` buffers reclaimed via `take_inputs()`/`take_reads()`
//! - Priority-partitioned ready queues
//!
//! ### Key types
//!
//! - [`PrecompiledNetExecutor`](precompiled_executor::PrecompiledNetExecutor) — the executor
//! - [`PrecompiledNet`](precompiled_net::PrecompiledNet) — borrows `&CompiledNet`, zero-cost reuse
//! - [`OwnedPrecompiledNet`](owned_precompiled::OwnedPrecompiledNet) — owned helper for FFI and long-lived callers
//!
//! ## Compilation Pipeline
//!
//! ```text
//! PetriNet ──► CompiledNet ──► PrecompiledNet (optional)
//!              (bitmap masks)   (ring buffers, opcodes)
//! ```
//!
//! ## Marking
//!
//! [`Marking`](marking::Marking) holds the mutable token state — type-erased
//! FIFO queues per place, with typed access via `Place<T>` references.
//!
//! ## Async Support
//!
//! Enable the `tokio` feature for `run_async()` on both executors. This allows
//! transition actions to be async (`CompletableFuture`-style) with external
//! event injection via environment places.

#[cfg(test)]
mod backend_suite_tests;
pub mod bitmap;
pub mod bitmap_backend;
pub mod compiled_net;
pub mod environment;
pub mod executor;
pub mod executor_core;
#[cfg(feature = "tokio")]
pub mod executor_handle;
pub mod marking;
pub mod owned_precompiled;
pub mod precompiled_backend;
pub mod precompiled_executor;
pub mod precompiled_net;
