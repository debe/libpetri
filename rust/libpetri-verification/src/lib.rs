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
//! IC3/PDR-based model checking through the `z3` executable ([`z3_process`]:
//! `z3` on `PATH` or `LIBPETRI_Z3`, version 4.8.0 or newer). Supported properties
//! ([`SmtProperty`](property::SmtProperty)):
//!
//! - **DeadlockFree** — no reachable deadlock state
//! - **MutualExclusion** — at most one token across given places
//! - **PlaceBound** — upper bound on tokens in a place
//! - **Unreachable** — given places cannot all be simultaneously marked
//!
//! `DeadlockFree` reads a quiescent marking against the places where a token may
//! rest ([`rest_set`]): the declared sinks (`sink_places`) and, under [VER-014],
//! the conditional sinks (`sink_places_when(marker, places)`) that are excused
//! while their marker holds a token. A reachability-safety property is first
//! tried against the [`linear_bound`] of [VER-015] (`linear_bound(true)`, the
//! default) — one `QF_LIA` query re-checked in exact arithmetic that proves the
//! property structurally when a decreasing conservation law excludes every
//! violating marking — before the IC3/PDR fixpoint query. `state_equation(true)`
//! ([VER-016], off by default) makes the flat CHC encoding carry one firing
//! counter per transition and the marking equation in every rule body, which is
//! what a quiescence proof on a pipeline-shaped net needs.
//!
//! Before any of that, an untimed net with no ν-joins and no environment places
//! is tried against the [`scg_verifier`] route of [VER-017]: when the
//! state-class graph closes within `enumeration_max_classes` (default 50 000,
//! `0` disables it) the property is decided exactly, with no solver at all — the
//! answer for the narrow, deep state spaces a workflow net produces, where IC3
//! needs a frame per pipeline stage. On truncation the SMT pipeline runs
//! unchanged, so the route can only add verdicts. It and the ν name-partition
//! route of [VER-012] decide the SAME predicate, stated once in
//! [`graph_decision`] ([VER-002] AC7).
//!
//! [`VerificationResult::route`](result::VerificationResult::route) names which
//! route answered ([VER-003] AC4). Read it before concluding anything from an
//! **empty** invariant list: off the SMT route that means "not computed", never
//! "the net has none". `semiflow_invariants` takes
//! [`SemiflowMode`](smt_verifier::SemiflowMode) — `Auto` unions the semiflows
//! exactly when the basis lost a law to the H1 guard, and skips the (worst-case
//! exponential) enumeration otherwise.

pub mod abstract_replay;
pub mod analyzer;
#[cfg(feature = "z3")]
pub mod certificate_check;
pub mod counterexample;
pub mod dbm;
pub mod environment;
pub mod graph_decision;
pub mod harness;
pub mod incidence_matrix;
pub mod marking_state;
#[cfg(feature = "z3")]
pub mod name_coloured_encoder;
pub mod name_fragment;
pub mod name_marking;
pub mod name_state_class;
pub mod name_state_class_graph;
pub mod net_flattener;
pub mod nu_scg_verifier;
pub mod p_invariant;
pub mod priority_semantics;
pub mod property;
pub mod rest_set;
pub mod result;
pub mod scc;
pub mod scg_verifier;
#[cfg(feature = "z3")]
pub mod smt_encoder;
pub mod state_class;
pub mod state_class_graph;
pub mod structural_check;

#[cfg(feature = "z3")]
pub mod linear_bound;
#[cfg(feature = "z3")]
pub mod smt_verifier;
#[cfg(feature = "z3")]
pub mod z3_process;
