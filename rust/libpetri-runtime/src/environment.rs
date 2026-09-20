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
/// - [`Snapshot`](Self::Snapshot) — mid-execution snapshot per \[ENV-014\]: the
///   executor materializes its current marking and replies on the provided
///   oneshot with a [`SnapshotResult`](crate::marking::SnapshotResult) — the
///   marking **and** whether work was in flight at that instant. Does not
///   affect lifecycle. The reply is always a valid *observation*; it is a
///   valid *restore point* only when
///   [`is_restore_point`](crate::marking::SnapshotResult::is_restore_point)
///   says so, because a firing in flight has consumed its inputs and not yet
///   deposited its outputs. A checkpoint saver must check it before
///   persisting. Events sent before this signal are already in the marking
///   it reports (one FIFO channel, applied on receipt).
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
    /// Mid-execution snapshot request: executor replies on the provided
    /// oneshot with the marking in the \[CORE-073\] form **plus** whether an
    /// action was in flight when it was taken (\[ENV-014\] AC5/AC6). Sending
    /// is non-blocking and legal from anywhere, an action included; the reply
    /// MUST NOT be *blocked on* from the orchestrator's own thread of control
    /// — see [`ExecutorHandle::snapshot`](crate::executor_handle::ExecutorHandle::snapshot).
    Snapshot(tokio::sync::oneshot::Sender<crate::marking::SnapshotResult>),
}
