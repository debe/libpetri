//! # libpetri-event — Execution Event System
//!
//! Records observable events during Petri net execution for debugging,
//! testing, and live inspection.
//!
//! ## Event Store
//!
//! The [`EventStore`](event_store::EventStore) trait defines event recording.
//! Two implementations are provided:
//!
//! - [`NoopEventStore`](event_store::NoopEventStore) — Production use. All
//!   methods are no-ops, fully eliminated at compile time.
//! - [`InMemoryEventStore`](event_store::InMemoryEventStore) — Testing and
//!   debugging. Stores all events in a `Vec<NetEvent>`.
//!
//! ## Zero-Cost Design
//!
//! The `ENABLED` associated constant on `EventStore` enables compile-time
//! elimination. The executor guards every `append()` call with
//! `if E::ENABLED { ... }` — when `E = NoopEventStore`, the compiler
//! removes the entire branch (including argument construction) as dead code.
//!
//! ## Event Types
//!
//! [`NetEvent`](net_event::NetEvent) is a 13-variant enum:
//!
//! | Category | Events |
//! |----------|--------|
//! | **Lifecycle** | `ExecutionStarted`, `ExecutionCompleted` |
//! | **Transitions** | `TransitionEnabled`, `TransitionStarted`, `TransitionCompleted` |
//! | **Timing** | `TransitionClockRestarted`, `TransitionTimedOut`, `ActionTimedOut` |
//! | **Failures** | `TransitionFailed` |
//! | **Tokens** | `TokenAdded`, `TokenRemoved` |
//! | **Diagnostics** | `LogMessage`, `MarkingSnapshot` |

pub mod event_store;
pub mod net_event;
