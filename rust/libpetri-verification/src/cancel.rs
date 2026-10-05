//! Cancelling a running verification from outside it ([VER-013]).
//!
//! A [`CancelToken`] is a shared flag: the caller keeps one clone, hands another
//! to `SmtVerifier::cancel_token` (under the `z3` feature), and calls
//! [`CancelToken::cancel`] from any thread. Cancellation is not a second stop
//! mechanism: it rides the total budget's deadline ([`crate::total_budget`]), so
//! every place that polls the deadline — the clamp before each z3 process, the
//! graph builds, the siphon/trap search, the semiflow enumeration, the colour-slot
//! simplex — sees it at the same points, and the watchdog loop of the z3 transport kills a running process
//! at once. The verdict is `Unknown` with the reason
//! `verification cancelled during <phase>`.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// A shared cancellation flag for a verification ([VER-013]).
///
/// `Clone` shares the flag, and it is `Send + Sync`, so the caller keeps one clone
/// and cancels from another thread while the verification runs on its own. Once
/// cancelled a token stays cancelled; a verification handed a token that is
/// already cancelled returns at once, before it starts any work or any process.
#[derive(Clone, Debug, Default)]
pub struct CancelToken {
    flag: Arc<AtomicBool>,
}

impl CancelToken {
    /// A token that has not been cancelled.
    pub fn new() -> Self {
        Self::default()
    }

    /// Cancels every verification this token (or a clone of it) was handed.
    /// Idempotent.
    pub fn cancel(&self) {
        self.flag.store(true, Ordering::SeqCst);
    }

    /// Whether [`cancel`](Self::cancel) has been called on this token or a clone.
    pub fn is_cancelled(&self) -> bool {
        self.flag.load(Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_share_the_flag_across_threads() {
        let token = CancelToken::new();
        assert!(!token.is_cancelled());
        let remote = token.clone();
        std::thread::spawn(move || remote.cancel()).join().unwrap();
        assert!(token.is_cancelled());
        token.cancel();
        assert!(token.is_cancelled());
    }
}
