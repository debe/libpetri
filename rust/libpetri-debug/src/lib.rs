//! # libpetri-debug — Debug Protocol for Petri Net Inspection
//!
//! Provides a framework-agnostic debug protocol for live inspection,
//! replay, breakpoints, and event filtering of Petri net executions.
//!
//! ## Architecture
//!
//! - [`DebugAwareEventStore`] wraps a primary `EventStore` and an `Arc<DebugEventStore>`,
//!   forwarding events to both. The executor owns the wrapper; the protocol handler
//!   shares the `Arc<DebugEventStore>`.
//! - [`DebugProtocolHandler`] dispatches commands from clients, manages subscriptions,
//!   and sends responses via the [`ResponseSink`] trait.
//! - [`DebugSessionRegistry`] tracks sessions, generates DOT diagrams, and extracts
//!   net structure.
//!
//! ## Feature Flags
//!
//! - `archive` — Enables gzip-compressed session archive read/write.

pub mod archive;
pub mod debug_aware_event_store;
pub mod debug_command;
pub mod debug_event_store;
pub mod debug_protocol_handler;
pub mod debug_response;
pub mod debug_session_registry;
pub mod marking_cache;
pub mod net_event_converter;
pub mod place_analysis;
pub mod token_projector_registry;

// Re-exports for convenience
pub use debug_aware_event_store::DebugAwareEventStore;
pub use debug_command::{
    BreakpointConfig, BreakpointType, DebugCommand, EventFilter, SubscriptionMode,
};
pub use debug_event_store::DebugEventStore;
pub use debug_protocol_handler::{DebugProtocolHandler, ResponseSink};
pub use debug_response::{
    DebugResponse, NetEventInfo, NetStructure, PlaceInfo, SessionSummary, TokenInfo, TransitionInfo,
};
pub use debug_session_registry::{DebugSession, DebugSessionRegistry};
pub use marking_cache::ComputedState;
pub use place_analysis::PlaceAnalysis;
pub use token_projector_registry::TokenProjectorRegistry;
