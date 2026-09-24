//! Why a run ended (\[EXEC-041\] AC3).

use std::fmt;

/// Why the last run of an executor ended (\[EXEC-041\] AC3).
///
/// Read it with [`Executor::termination_reason`](crate::executor_core::executor::Executor::termination_reason)
/// after `run_sync` / `run_async` return, or from
/// [`RunOutcome`](crate::owned_precompiled::RunOutcome) on the owned entry
/// points. Two reasons are **complete** — the returned marking is the one the
/// net was designed to end in — and the rest are truncations; see
/// [`is_complete`](Self::is_complete).
///
/// `#[non_exhaustive]`: the spec also names `interrupted` (a cancellation the
/// orchestrator observes in its wait), which Rust has no ambient source for
/// today. Match with a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TerminationReason {
    /// No run has finished on this executor yet.
    Running,
    /// The net reached quiescence (\[EXEC-040\]): nothing enabled, nothing in
    /// flight. A complete reason.
    Quiescent,
    /// A terminal place was marked (\[EXEC-042\]). The run stopped at once —
    /// in-flight actions abandoned, queued events refused. A complete reason:
    /// the marking is a designed end.
    Terminal,
    /// A close (\[ENV-013\]) stopped the run before quiescence. A truncation.
    Closed,
    /// Some other caller-requested stop ended the run before quiescence. A
    /// truncation. No Rust path produces it today; it exists for parity with
    /// the other implementations' run budgets.
    Stopped,
}

impl TerminationReason {
    /// True for [`Quiescent`](Self::Quiescent) and
    /// [`Terminal`](Self::Terminal): the marking is the one the net was
    /// designed to end in, not a truncated one.
    pub fn is_complete(self) -> bool {
        matches!(self, Self::Quiescent | Self::Terminal)
    }

    /// The spec's lowercase name: `running`, `quiescent`, `terminal`,
    /// `closed`, `stopped` (\[EXEC-041\]).
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Running => "running",
            Self::Quiescent => "quiescent",
            Self::Terminal => "terminal",
            Self::Closed => "closed",
            Self::Stopped => "stopped",
        }
    }
}

impl fmt::Display for TerminationReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
