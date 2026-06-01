use std::sync::Arc;

use libpetri_core::token::ErasedToken;

/// An external event to inject into the executor.
#[derive(Debug, Clone)]
pub struct ExternalEvent {
    pub place_name: Arc<str>,
    pub token: ErasedToken,
}

/// Signal sent to a running executor via the control channel.
///
/// Merges external events and lifecycle commands into a single enum,
/// avoiding separate channels or atomic flags. The executor's async loop
/// pattern-matches on these variants with O(1) overhead per iteration.
///
/// # Lifecycle signals
///
/// - [`Drain`](Self::Drain) — graceful shutdown per \[ENV-011\]: reject new events,
///   process already-queued events, complete in-flight actions, terminate at quiescence.
/// - [`Close`](Self::Close) — immediate shutdown per \[ENV-013\]: discard queued events,
///   complete in-flight actions, terminate.
/// - [`Snapshot`](Self::Snapshot) — mid-execution marking snapshot: the executor
///   materializes its current marking and sends it through the provided
///   oneshot. Does not affect lifecycle. Used by checkpoint-saver patterns
///   (e.g. `langgraph-libpetri`'s `PetriCheckpointSaver`).
///
/// Use [`ExecutorHandle`](crate::executor_handle::ExecutorHandle) for RAII-managed
/// lifecycle with automatic drain on drop.
#[cfg(feature = "tokio")]
#[derive(Debug)]
pub enum ExecutorSignal {
    /// External event injection (existing behavior).
    Event(ExternalEvent),
    /// Batched external event injection — one signal carries N events.
    /// Processed atomically: all events deposit before the next signal
    /// is observed. Lets Python `handle.inject_many(...)` cross the FFI
    /// once for any number of tokens.
    EventBatch(Vec<ExternalEvent>),
    /// Graceful drain: reject new events, process queued, terminate at quiescence.
    Drain,
    /// Immediate close: discard queued events, complete in-flight, terminate.
    Close,
    /// Mid-execution snapshot request: executor replies with the current
    /// owned [`Marking`](crate::Marking) on the provided oneshot.
    Snapshot(tokio::sync::oneshot::Sender<crate::marking::Marking>),
}
