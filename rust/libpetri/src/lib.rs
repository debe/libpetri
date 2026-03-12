//! # libpetri — Coloured Time Petri Net Engine
//!
//! A high-performance Petri net engine with formal verification support.
//!
//! ## Quick Start
//!
//! ```rust
//! use libpetri::*;
//!
//! let p1 = Place::<i32>::new("input");
//! let p2 = Place::<i32>::new("output");
//!
//! let t = Transition::builder("process")
//!     .input(one(&p1))
//!     .output(out_place(&p2))
//!     .action(fork())
//!     .build();
//!
//! let net = PetriNet::builder("example").transition(t).build();
//!
//! let mut marking = Marking::new();
//! marking.add(&p1, Token::at(42, 0));
//!
//! let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
//!     &net, marking, ExecutorOptions::default(),
//! );
//! executor.run_sync();
//!
//! assert_eq!(*executor.marking().peek(&p2).unwrap(), 42);
//! ```
//!
//! ## Example: Basic Chain
//!
#![doc = include_str!(concat!(env!("OUT_DIR"), "/basic_chain.svg"))]
//!
//! ## Example: Racing LLM Agent Pipeline
//!
//! An agent orchestration net with three environment inputs (keystroke activity,
//! submitted messages, topic-change triggers), demonstrating all arc types
//! (input, output, read, inhibitor, reset), all timing modes (immediate, window,
//! deadline, delayed, exact), AND-fork, priority, dump semantics, the
//! optional-dependency pattern (GatherContext vs GatherFresh), and coloured
//! tokens (`String` messages + `()` control signals).
//!
#![doc = include_str!(concat!(env!("OUT_DIR"), "/showcase.svg"))]
//!
//! ## Crate Structure
//!
//! - [`core`] — Places, tokens, transitions, timing, actions
//! - [`event`] — Event store for recording execution events
//! - [`runtime`] — Bitmap-based executor (sync + async)
//! - [`export`] — DOT/Graphviz export pipeline
//! - [`verification`] — Formal verification (P-invariants, state class graphs, SMT)
//!
//! ## Executors
//!
//! Two executors are available:
//! - [`BitmapNetExecutor`] — General-purpose, bitmap-based enablement checks
//! - [`PrecompiledNetExecutor`] — High-performance alternative with ring buffers,
//!   opcode dispatch, and two-level summary bitmaps
//!
//! ## Feature Flags
//!
//! | Feature | Effect |
//! |---------|--------|
//! | `tokio` | Enables `run_async()` on both executors (external event injection) |
//! | `z3` | Enables SMT-based IC3/PDR model checking in [`verification`] |
//! | `debug` | Enables the `debug` module (WebSocket debug protocol) |

pub use libpetri_core as core;
#[cfg(feature = "debug")]
pub use libpetri_debug as debug;
pub use libpetri_event as event;
pub use libpetri_export as export;
pub use libpetri_runtime as runtime;
pub use libpetri_verification as verification;

// Re-export commonly used types at the top level
pub use libpetri_core::action::{
    ActionError, BoxedAction, async_action, fork, passthrough, produce, sync_action, transform,
};
pub use libpetri_core::arc::{Inhibitor, Read, Reset, inhibitor, read, reset};
pub use libpetri_core::context::TransitionContext;
pub use libpetri_core::input::{In, all, at_least, exactly, one};
pub use libpetri_core::output::{
    Out, and, and_places, forward_input, out_place, timeout, timeout_place, xor, xor_places,
};
pub use libpetri_core::petri_net::PetriNet;
pub use libpetri_core::place::{EnvironmentPlace, Place, PlaceRef};
pub use libpetri_core::timing::{Timing, deadline, delayed, exact, immediate, window};
pub use libpetri_core::token::Token;
pub use libpetri_core::transition::Transition;

pub use libpetri_event::event_store::{EventStore, InMemoryEventStore, NoopEventStore};
pub use libpetri_event::net_event::NetEvent;

pub use libpetri_export::dot_exporter::dot_export;

pub use libpetri_runtime::compiled_net::CompiledNet;
pub use libpetri_runtime::executor::{BitmapNetExecutor, ExecutorOptions};
pub use libpetri_runtime::marking::Marking;
pub use libpetri_runtime::precompiled_executor::{
    PrecompiledExecutorBuilder, PrecompiledNetExecutor,
};
pub use libpetri_runtime::precompiled_net::PrecompiledNet;
