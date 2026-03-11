//! # libpetri-core — Core Types for Coloured Time Petri Nets
//!
//! This crate defines the structural model: places, tokens, transitions, arcs,
//! and timing constraints. It contains no execution logic — see
//! [`libpetri-runtime`](https://docs.rs/libpetri-runtime) for that.
//!
//! ## Concepts
//!
//! | Type | Description |
//! |------|-------------|
//! | [`Place<T>`](place::Place) | Typed, named token container. Identity by name. |
//! | [`Token<T>`](token::Token) | Immutable value + timestamp. |
//! | [`Transition`](transition::Transition) | Consumes/produces tokens via arcs. Optional timing and priority. |
//! | [`PetriNet`](petri_net::PetriNet) | Immutable net definition built via builder pattern. |
//!
//! ## Arc Types
//!
#![doc = include_str!("../doc/arc_types.svg")]
//!
//! | Arc | Module | Semantics |
//! |-----|--------|-----------|
//! | **Input** | [`input`] | Consume tokens (one, exactly N, at least N, all) |
//! | **Output** | [`output`] | Produce tokens (single, AND-fork, XOR-split, timeout) |
//! | **Inhibitor** | [`arc`] | Block firing when place has tokens |
//! | **Read** | [`arc`] | Require token without consuming |
//! | **Reset** | [`arc`] | Clear all tokens from place on firing |
//!
//! ## Timing Modes
//!
#![doc = include_str!("../doc/timing_modes.svg")]
//!
//! | Mode | Interval | Factory |
//! |------|----------|---------|
//! | Immediate | \[0, ∞) | [`timing::immediate()`] |
//! | Deadline | \[0, d\] | [`timing::deadline(ms)`](timing::deadline) |
//! | Delayed | \[d, ∞) | [`timing::delayed(ms)`](timing::delayed) |
//! | Window | \[a, b\] | [`timing::window(a, b)`](timing::window) |
//! | Exact | \[t, t\] | [`timing::exact(ms)`](timing::exact) |
//!
//! ## Quick Example
//!
//! ```rust
//! use libpetri_core::place::Place;
//! use libpetri_core::token::Token;
//! use libpetri_core::transition::Transition;
//! use libpetri_core::petri_net::PetriNet;
//! use libpetri_core::input::one;
//! use libpetri_core::output::out_place;
//! use libpetri_core::action::fork;
//! use libpetri_core::timing::delayed;
//!
//! let inbox = Place::<String>::new("inbox");
//! let outbox = Place::<String>::new("outbox");
//!
//! let send = Transition::builder("send")
//!     .input(one(&inbox))
//!     .output(out_place(&outbox))
//!     .timing(delayed(100))
//!     .action(fork())
//!     .build();
//!
//! let net = PetriNet::builder("mailer")
//!     .transition(send)
//!     .build();
//!
//! assert_eq!(net.transitions().len(), 1);
//! ```

pub mod action;
pub mod arc;
pub mod context;
pub mod input;
pub mod output;
pub mod petri_net;
pub mod place;
pub mod timing;
pub mod token;
pub mod transition;
