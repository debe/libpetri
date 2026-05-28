//! The internal seam between the shared 5-phase loop ([`Executor`]) and
//! each executor's choice of token storage / enablement representation /
//! dirty tracking.
//!
//! Implemented by `BitmapBackend` (reference) and `PrecompiledBackend`
//! (production hot path). The trait is `pub(crate)` because external
//! adapters aren't a goal yet — a public version waits for a second real
//! consumer outside the crate.
//!
//! [`Executor`]: crate::executor_core::executor::Executor

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use libpetri_core::token::ErasedToken;

use crate::compiled_net::CompiledNet;
use crate::marking::Marking;

/// The bundle of tokens a backend hands back when a transition fires.
///
/// All three buckets are keyed by place name (the loop emits
/// `TokenRemoved` events against these names, builds the
/// [`TransitionContext`] from them, and uses them to drive output
/// production).
///
/// [`TransitionContext`]: libpetri_core::context::TransitionContext
#[derive(Debug, Default)]
#[allow(dead_code)]
pub(crate) struct ConsumedInputs {
    /// Tokens consumed by input arcs (`In::One`, `In::Exactly`,
    /// `In::AtLeast`, `In::All`). Owned — the backend has removed them
    /// from its token store.
    pub inputs: HashMap<Arc<str>, Vec<ErasedToken>>,

    /// Tokens visible to read arcs (clones — not removed from the
    /// backend's store). Keyed by place name.
    pub reads: HashMap<Arc<str>, Vec<ErasedToken>>,

    /// Tokens drained by reset arcs. The backend has removed these and
    /// noted the reset for clock-restart detection.
    pub resets: HashMap<Arc<str>, Vec<ErasedToken>>,
}

/// Internal seam between the shared loop and per-executor storage.
///
/// **Stability:** every backend must yield the same observable behaviour
/// for the same net + initial marking. Performance characteristics differ
/// (the precompiled backend is ~3.86× faster on sync chains), but
/// semantics — firing order under priority + FIFO, deadline enforcement,
/// reset arc clock-restart, environment-place injection — are pinned by
/// the loop, not by the backend.
///
/// **Hot path:** monomorphised. The loop is generic over `S:
/// ExecutorBackend` so each backend's methods inline. No `dyn` dispatch
/// anywhere.
#[allow(dead_code)]
pub(crate) trait ExecutorBackend {
    // ============ Topology ============

    /// Borrow the precompiled net topology (place names, transition
    /// arcs, timing, priority — everything that doesn't change once the
    /// net is built).
    fn compiled(&self) -> &CompiledNet;

    // ============ Enablement (per cycle) ============

    /// Drain the dirty-transition set into `buf`. The buffer is cleared
    /// before filling. After this call, the backend's internal dirty
    /// state is empty until [`mark_dirty_after`] or
    /// [`take_dirty_into`]-callers re-mark transitions.
    ///
    /// Each dirty transition ID is yielded at most once per cycle.
    ///
    /// [`mark_dirty_after`]: ExecutorBackend::mark_dirty_after
    /// [`take_dirty_into`]: ExecutorBackend::take_dirty_into
    fn take_dirty_into(&mut self, buf: &mut Vec<usize>);

    /// True when the transition has all required input/read tokens
    /// available and no inhibitor blocks it. Does not consult timing —
    /// the loop layers deadline/window/exact checks on top.
    fn can_enable(&self, tid: usize) -> bool;

    /// Update the backend's per-transition enabled state. The loop calls
    /// this after every dirty re-evaluation. `now_ms` is the executor's
    /// monotonic clock (see `elapsed_ms_since`); it's recorded so the
    /// backend can answer [`earliest_enabled_at`].
    ///
    /// [`earliest_enabled_at`]: ExecutorBackend::earliest_enabled_at
    fn set_enabled(&mut self, tid: usize, enabled: bool, now_ms: f64);

    /// Pop the next ready transition for the immediate-priority firing
    /// pass (phase 4a). Returns `None` when there are no more
    /// immediately-fireable transitions this cycle.
    fn next_ready_immediate(&mut self) -> Option<usize>;

    /// Pop the next ready transition respecting priority and timing
    /// (phase 4b). Returns `None` when nothing is firable at `now_ms`.
    fn next_ready_general(&mut self, now_ms: f64) -> Option<usize>;

    /// Wall-clock (monotonic) milliseconds at which the transition first
    /// became enabled in the current enabled-streak. Used for FIFO
    /// tie-breaking inside a priority bucket and for deadline arithmetic.
    fn earliest_enabled_at(&self, tid: usize) -> f64;

    // ============ Token mutation ============

    /// Consume inputs (per arc spec), gather read-arc tokens, and drain
    /// reset arcs for transition `tid`. The backend mutates its token
    /// store; the loop emits `TokenRemoved` events from the returned
    /// bundle.
    fn consume_inputs(&mut self, tid: usize) -> ConsumedInputs;

    /// Produce a token at `place`. The backend handles bitmap/dirty
    /// updates so the next cycle's enablement scan sees the new token.
    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken);

    /// Mark every transition that reads from any place fired by `tid`
    /// (or its reset arcs) as dirty for the next enablement re-eval.
    fn mark_dirty_after(&mut self, tid: usize);

    // ============ Observation ============

    /// Snapshot the current marking. Bitmap backends return
    /// `Cow::Borrowed(&self.marking)` (zero copy). Precompiled backends
    /// materialise from ring buffers and return `Cow::Owned`.
    fn snapshot_marking(&self) -> Cow<'_, Marking>;

    /// True when no transition is enabled, no completion is pending,
    /// and (for async) no environment event is in flight. The loop
    /// uses this to decide between sleeping and terminating.
    fn is_quiescent(&self) -> bool;
}
