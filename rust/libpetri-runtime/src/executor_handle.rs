//! RAII handle for controlling executor lifecycle.
//!
//! [`ExecutorHandle`] wraps a `tokio::sync::mpsc::UnboundedSender<ExecutorSignal>`
//! and provides typed methods for event injection and lifecycle management.
//! Implements [`Drop`] to automatically send [`ExecutorSignal::Drain`] when the
//! handle goes out of scope without an explicit `drain()` or `close()` call.

use std::sync::Arc;

use libpetri_core::token::ErasedToken;
#[cfg(test)]
use libpetri_core::token::Token;

use crate::environment::{ExecutorSignal, ExternalEvent};
use crate::marking::Marking;

/// RAII handle for injecting events and controlling executor lifecycle.
///
/// Obtained by wrapping the sender half of an
/// `mpsc::unbounded_channel::<ExecutorSignal>()` before spawning the executor.
///
/// # RAII guarantee
///
/// When dropped without an explicit [`drain()`](Self::drain) or
/// [`close()`](Self::close), the handle automatically sends
/// [`ExecutorSignal::Drain`] — ensuring graceful shutdown even if the caller
/// forgets. This follows Rust's RAII convention (analogous to `MutexGuard`
/// releasing its lock on drop).
///
/// # Example
///
/// ```ignore (requires tokio runtime and executor setup)
/// let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
/// let mut handle = ExecutorHandle::new(tx);
/// let mut executor = BitmapNetExecutor::new(&net, marking, opts);
///
/// tokio::spawn(async move { executor.run_async(rx).await; });
///
/// handle.inject(Arc::from("sensor"), Token::new(42).erase());
/// handle.drain(); // graceful shutdown
/// ```
pub struct ExecutorHandle {
    tx: tokio::sync::mpsc::UnboundedSender<ExecutorSignal>,
    drained: bool,
}

impl ExecutorHandle {
    /// Creates a new handle from the sender half of an executor signal channel.
    pub fn new(tx: tokio::sync::mpsc::UnboundedSender<ExecutorSignal>) -> Self {
        Self { tx, drained: false }
    }

    /// Injects an external event into the running executor.
    ///
    /// Returns `false` if the handle has been drained/closed or the channel is
    /// disconnected. O(1) — single channel send.
    pub fn inject(&mut self, place_name: Arc<str>, token: ErasedToken) -> bool {
        if self.drained {
            return false;
        }
        self.tx
            .send(ExecutorSignal::Event(ExternalEvent { place_name, token }))
            .is_ok()
    }

    /// Initiates graceful drain per \[ENV-011\].
    ///
    /// After this call:
    /// - New [`inject()`](Self::inject) calls return `false`
    /// - Already-queued events are processed normally
    /// - In-flight actions complete
    /// - Executor terminates at quiescence
    ///
    /// Returns `false` if already drained/closed.
    pub fn drain(&mut self) -> bool {
        if self.drained {
            return false;
        }
        self.drained = true;
        self.tx.send(ExecutorSignal::Drain).is_ok()
    }

    /// Initiates immediate close per \[ENV-013\].
    ///
    /// After this call:
    /// - Queued events are discarded
    /// - In-flight actions complete
    /// - Executor terminates after in-flight completion
    ///
    /// Calling `close()` after `drain()` escalates from graceful to immediate.
    pub fn close(&mut self) -> bool {
        self.drained = true;
        self.tx.send(ExecutorSignal::Close).is_ok()
    }

    /// Returns `true` if `drain()` or `close()` has been called.
    pub fn is_drained(&self) -> bool {
        self.drained
    }

    /// Requests a mid-execution snapshot of the executor's current marking.
    ///
    /// Returns a oneshot receiver that resolves to an owned [`Marking`] once
    /// the executor processes the signal (typically within one orchestrator
    /// cycle). Returns `Err` if the handle is drained/closed or the channel
    /// is disconnected — in either case no snapshot will be delivered.
    ///
    /// Unlike `drain` / `close`, this does **not** affect lifecycle: the
    /// executor keeps running. Use this for checkpoint-saver patterns where
    /// the caller wants a consistent marking for persistence without
    /// interrupting execution.
    // `Result<_, ()>` is intentional: the only failure is "snapshot cannot be
    // requested" (drained/closed or channel gone), which carries no payload.
    // `Err(())` keeps the `?`/`is_err()` ergonomics the sibling lifecycle
    // tests rely on, so we opt out of `result_unit_err` here.
    #[allow(clippy::result_unit_err)]
    pub fn snapshot(&self) -> Result<tokio::sync::oneshot::Receiver<Marking>, ()> {
        if self.drained {
            return Err(());
        }
        let (tx, rx) = tokio::sync::oneshot::channel();
        self.tx
            .send(ExecutorSignal::Snapshot(tx))
            .map_err(|_| ())?;
        Ok(rx)
    }
}

impl Drop for ExecutorHandle {
    fn drop(&mut self) {
        if !self.drained {
            // RAII safety net: graceful drain on scope exit.
            let _ = self.tx.send(ExecutorSignal::Drain);
        }
        // Sender drops here → channel closes → executor detects None from recv()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn handle_drain_sets_drained_flag() {
        let (tx, _rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        assert!(!handle.is_drained());
        assert!(handle.drain());
        assert!(handle.is_drained());
        // Second drain returns false
        assert!(!handle.drain());
    }

    #[tokio::test]
    async fn handle_close_sets_drained_flag() {
        let (tx, _rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        assert!(handle.close());
        assert!(handle.is_drained());
    }

    #[tokio::test]
    async fn handle_inject_rejected_after_drain() {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        handle.drain();
        let result = handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::new(42i32)));
        assert!(!result);
        // Only the Drain signal should be in the channel
        match rx.recv().await {
            Some(ExecutorSignal::Drain) => {}
            other => panic!("expected Drain, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn handle_drop_sends_drain_automatically() {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        {
            let _handle = ExecutorHandle::new(tx);
            // handle dropped without explicit drain/close
        }
        match rx.recv().await {
            Some(ExecutorSignal::Drain) => {}
            other => panic!("expected Drain from RAII drop, got {:?}", other),
        }
        // Channel should be closed after sender dropped
        assert!(rx.recv().await.is_none());
    }

    #[tokio::test]
    async fn handle_drop_after_drain_does_not_double_send() {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        {
            let mut handle = ExecutorHandle::new(tx);
            handle.drain();
            // handle dropped — should NOT send another Drain
        }
        match rx.recv().await {
            Some(ExecutorSignal::Drain) => {}
            other => panic!("expected exactly one Drain, got {:?}", other),
        }
        // Channel closed, no more signals
        assert!(rx.recv().await.is_none());
    }

    #[tokio::test]
    async fn handle_snapshot_sends_signal_with_reply_channel() {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let handle = ExecutorHandle::new(tx);
        let receiver = handle.snapshot().expect("snapshot on live handle");
        match rx.recv().await {
            Some(ExecutorSignal::Snapshot(reply)) => {
                // Mimic the executor side: send back an empty marking.
                let _ = reply.send(Marking::default());
            }
            other => panic!("expected Snapshot signal, got {:?}", other),
        }
        receiver.await.expect("snapshot reply delivered");
    }

    #[tokio::test]
    async fn handle_snapshot_after_drain_returns_err() {
        let (tx, _rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        handle.drain();
        assert!(handle.snapshot().is_err());
    }

    #[tokio::test]
    async fn handle_close_after_drain_escalates() {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        handle.drain();
        handle.close(); // escalate
        match rx.recv().await {
            Some(ExecutorSignal::Drain) => {}
            other => panic!("expected Drain first, got {:?}", other),
        }
        match rx.recv().await {
            Some(ExecutorSignal::Close) => {}
            other => panic!("expected Close second, got {:?}", other),
        }
    }
}
