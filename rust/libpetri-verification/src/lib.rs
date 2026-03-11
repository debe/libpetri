//! # libpetri-verification — Formal Verification
//!
//! Verifies safety and liveness properties of Petri nets defined with
//! [`libpetri-core`](https://docs.rs/libpetri-core).
//!
//! ## Example: Mutual Exclusion
//!
//! A classic mutual exclusion net where two processes compete for a shared
//! mutex token. Verification proves that `critical_a` and `critical_b` can
//! never both hold tokens simultaneously.
//!
#![doc = include_str!(concat!(env!("OUT_DIR"), "/mutex_example.svg"))]
//!
//! ## State Class Graph
//!
//! The [`state_class_graph`] module implements the Berthomieu-Diaz state class
//! method. Time is abstracted using Difference-Bound Matrices ([`dbm`]),
//! producing a finite graph even for dense-time nets. BFS exploration covers
//! all reachable state classes.
//!
//! ## P-Invariants
//!
//! The [`p_invariant`] module computes P-invariants via the Farkas method —
//! weighted sums over place markings that remain constant across all reachable
//! states. Used to prove mutual exclusion, place bounds, and conservation.
//!
//! ## Structural Analysis
//!
//! The [`structural_check`] module performs siphon/trap analysis and applies
//! Commoner's theorem as pre-checks before more expensive exploration.
//!
//! ## Analyzer
//!
//! The [`analyzer`] module provides the main entry point for verification.
//! It combines structural pre-checks with state class graph exploration and
//! returns detailed [`result`]s with optional counterexample traces.
//!
//! ## SMT Verification
//!
//! With the `z3` feature enabled, `smt_encoder` and `smt_verifier` provide
//! IC3/PDR-based model checking. Supported properties
//! ([`SmtProperty`](property::SmtProperty)):
//!
//! - **DeadlockFree** — no reachable deadlock state
//! - **MutualExclusion** — at most one token across given places
//! - **PlaceBound** — upper bound on tokens in a place
//! - **Unreachable** — given places cannot all be simultaneously marked

pub mod analyzer;
pub mod counterexample;
pub mod dbm;
pub mod environment;
pub mod incidence_matrix;
pub mod marking_state;
pub mod net_flattener;
pub mod p_invariant;
pub mod property;
pub mod result;
pub mod scc;
#[cfg(feature = "z3")]
pub mod smt_encoder;
pub mod state_class;
pub mod state_class_graph;
pub mod structural_check;

#[cfg(feature = "z3")]
pub mod smt_verifier;
