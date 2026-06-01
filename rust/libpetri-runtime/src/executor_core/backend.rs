//! The internal seam between the shared 6-phase execution loop
//! ([`Executor`]) and each executor's choice of token storage,
//! enablement representation, and dirty tracking.
//!
//! Implemented by [`BitmapBackend`] (reference) and
//! [`PrecompiledBackend`] (production hot path).
//!
//! ## Seam granularity
//!
//! The seam is at *phase* granularity, not per-primitive: methods like
//! [`update_enablement`](ExecutorBackend::update_enablement) and
//! [`consume_for_firing`](ExecutorBackend::consume_for_firing) wrap
//! whole cycle phases. The loop owns event emission, action execution,
//! and deadline arithmetic; each backend owns *how* its phase runs.
//!
//! ## Reusable buffers
//!
//! Input/read [`HashMap`]s are owned by [`Executor`] and passed as
//! `&mut` out-parameters to
//! [`consume_for_firing`](ExecutorBackend::consume_for_firing). The
//! loop reclaims them from [`TransitionContext`] after the action
//! runs, so no per-firing allocation happens for the hot path. This
//! mirrors the optimisation the legacy
//! [`PrecompiledNetExecutor`](crate::precompiled_executor::PrecompiledNetExecutor)
//! carried internally.
//!
//! [`Executor`]: crate::executor_core::executor::Executor
//! [`BitmapBackend`]: crate::bitmap_backend::BitmapBackend
//! [`PrecompiledBackend`]: crate::precompiled_backend::PrecompiledBackend
//! [`TransitionContext`]: libpetri_core::context::TransitionContext

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::token::ErasedToken;

use crate::compiled_net::CompiledNet;
use crate::marking::Marking;

/// Receives per-cycle enablement deltas from
/// [`ExecutorBackend::update_enablement`].
///
/// Two monomorphised impls:
/// - [`NoopChangeTracker`] — for `NoopEventStore` paths where events
///   are discarded anyway. All methods are empty so the backend's
///   push calls compile away to nothing, avoiding the per-cycle
///   `Vec::push` allocation on small benchmarks.
/// - [`RecordingChangeTracker`] — accumulates tids into Vecs the loop
///   then walks to emit `TransitionEnabled` and
///   `TransitionClockRestarted` events.
pub trait ChangeTracker {
    fn newly_enabled(&mut self, tid: usize);
    fn clock_restarted(&mut self, tid: usize);
}

/// Zero-cost tracker for `NoopEventStore` paths. Both methods are
/// `#[inline(always)]` no-ops so monomorphisation elides every
/// `tracker.newly_enabled(tid)` call inside the backend.
pub struct NoopChangeTracker;

impl ChangeTracker for NoopChangeTracker {
    #[inline(always)]
    fn newly_enabled(&mut self, _tid: usize) {}
    #[inline(always)]
    fn clock_restarted(&mut self, _tid: usize) {}
}

/// Recording tracker. Pushes tids into the supplied Vecs; the loop
/// drains them and emits events.
pub struct RecordingChangeTracker<'a> {
    pub newly_enabled: &'a mut Vec<usize>,
    pub clock_restarted: &'a mut Vec<usize>,
}

impl ChangeTracker for RecordingChangeTracker<'_> {
    #[inline]
    fn newly_enabled(&mut self, tid: usize) {
        self.newly_enabled.push(tid);
    }
    #[inline]
    fn clock_restarted(&mut self, tid: usize) {
        self.clock_restarted.push(tid);
    }
}

/// Internal seam between the shared loop and per-executor storage.
///
/// **Visibility:** `pub` because it appears in the bounds of
/// [`Executor`](crate::executor_core::executor::Executor) — but it
/// lives under the internal `executor_core` module path. External
/// implementations are not supported yet; if you implement it, expect
/// breaking changes on every release.
///
/// **Stability:** every backend must yield the same observable
/// behaviour for the same net + initial marking. Firing order under
/// priority + FIFO, deadline enforcement, reset-arc clock-restart
/// semantics, and environment-place injection are pinned by the loop,
/// not by the backend.
///
/// **Hot path:** monomorphised. The loop is generic over `S:
/// ExecutorBackend` so each backend's methods inline. No `dyn` dispatch
/// anywhere; the trait is intentionally object-unsafe via the generic
/// closure parameter on
/// [`consume_for_firing`](ExecutorBackend::consume_for_firing).
pub trait ExecutorBackend {
    // ============ Topology ============

    /// Borrow the precompiled net topology (place names, transition
    /// arcs, timing, priority — everything that doesn't change once the
    /// net is built).
    fn compiled(&self) -> &CompiledNet;

    /// Output place names for `tid`, used to build the
    /// [`TransitionContext`](libpetri_core::context::TransitionContext)'s
    /// allowed-output set. Both backends construct or clone a fresh
    /// `HashSet`; precompiled backends may use a precomputed cache,
    /// bitmap backends build from the transition's output places.
    fn output_place_names(&self, tid: usize) -> HashSet<Arc<str>>;

    // ============ Lifecycle ============

    /// Sync the presence bitmap from the initial marking and mark every
    /// transition dirty so the first `update_enablement` re-evaluates
    /// the entire net. Called once before the loop starts.
    fn initialize(&mut self);

    /// Snapshot the current marking. Bitmap backends return
    /// `Cow::Borrowed(&self.marking)` (zero copy). Precompiled backends
    /// materialise from ring buffers and return `Cow::Owned`.
    fn snapshot_marking(&self) -> Cow<'_, Marking>;

    /// True when nothing is enabled. The loop uses this alongside
    /// `has_environment_places` to decide between sleeping and
    /// terminating.
    fn is_quiescent(&self) -> bool;

    /// True when the dirty set is non-empty. Used by the sync loop to
    /// continue iterating if a re-evaluation is pending even with no
    /// currently-enabled transitions.
    fn has_dirty_bits(&self) -> bool;

    /// Count of currently-enabled transitions. The loop uses this for
    /// termination (no enabled + nothing in flight = done).
    fn enabled_count(&self) -> usize;

    // ============ Phase 3 — enablement ============

    /// Re-evaluate every dirty transition and update the enabled set.
    /// Reports newly-enabled transitions (for `TransitionEnabled`
    /// events) and transitions whose enabled-time clock just restarted
    /// because a reset arc drained one of their input places (for
    /// `TransitionClockRestarted` events).
    ///
    /// Generic over [`ChangeTracker`] so [`NoopChangeTracker`] elides
    /// the per-cycle push entirely on `NoopEventStore` paths.
    fn update_enablement<T: ChangeTracker>(&mut self, now_ms: f64, tracker: &mut T);

    // ============ Phase 4a — deadline enforcement ============

    /// Cheap "should I bother scanning?" check. False means the loop
    /// can skip the deadline-enforcement phase entirely.
    fn has_any_deadlines(&self) -> bool;

    /// Disable every enabled transition whose `enabled_at_ms +
    /// latest_ms + tolerance < now_ms`. Pushes timed-out transition IDs
    /// into `out` so the loop can emit `TransitionTimedOut` events.
    fn enforce_deadlines(&mut self, now_ms: f64, out: &mut Vec<usize>);

    // ============ Phase 4b — firing decision ============

    /// Cheap precomputed flag: every transition is `Immediate` with
    /// identical priority, so the loop can skip the priority +
    /// FIFO-sort general path and fire every enabled transition in
    /// transition-index order.
    fn fast_path_available(&self) -> bool;

    /// Fast-path collector: pushes every currently-enabled transition
    /// ID into `out` in transition-index order. Only valid when
    /// [`fast_path_available`](ExecutorBackend::fast_path_available)
    /// returned `true`.
    fn collect_ready_immediate(&mut self, out: &mut Vec<usize>);

    /// General-path collector: pushes every enabled transition whose
    /// earliest-time window has opened into `out`, sorted by priority
    /// (descending) then by enabled-at time (ascending FIFO).
    fn collect_ready_general(&mut self, now_ms: f64, out: &mut Vec<usize>);

    /// Re-check that a ready transition is still firable given that
    /// earlier transitions this cycle may have consumed shared inputs.
    /// Returns false when the transition can no longer fire; the loop
    /// then calls [`disable`](ExecutorBackend::disable).
    fn recheck_can_fire(&mut self, tid: usize) -> bool;

    // ============ Phase 4c — fire a single transition ============

    /// Consume inputs (per arc spec), gather read-arc tokens, drain
    /// reset arcs, update presence bitmaps and mark dirty for the
    /// affected places. The loop emits `TokenRemoved` events from the
    /// consumed tokens in spec-declaration order via `emit_removed`.
    ///
    /// Both `inputs` and `reads` are passed in already-cleared by the
    /// loop and filled in place by the backend — keeps the hot path
    /// allocation-free across firings.
    ///
    /// The closure is called for every consumed input/reset token at
    /// the moment it is removed, preserving the per-token event order
    /// the existing executor emits today.
    fn consume_for_firing<F>(
        &mut self,
        tid: usize,
        inputs: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        reads: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        emit_removed: F,
    ) where
        F: FnMut(&Arc<str>, &ErasedToken);

    /// Produce a token at `place`. The backend updates token storage,
    /// presence bitmap, and dirty bits so the next cycle's enablement
    /// scan sees the new token.
    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken);

    /// Post-firing housekeeping: disable the transition that just
    /// fired, clear its enabled-at timestamp, and mark it dirty for
    /// re-evaluation next cycle.
    fn post_fire(&mut self, tid: usize);

    /// Silently disable a transition (no events). Called when
    /// [`recheck_can_fire`](ExecutorBackend::recheck_can_fire) returns
    /// false: another transition this cycle stole the inputs.
    fn disable(&mut self, tid: usize);

    // ============ External event injection (async) ============

    /// Inject an environment-place token from the outside world.
    /// Updates token storage and dirty bits; the loop emits the
    /// `TokenAdded` event.
    fn inject_external_token(&mut self, place: &Arc<str>, token: ErasedToken);

    // ============ Async planning ============

    /// Milliseconds until the next deadline or earliest-firing window.
    /// Returns `f64::INFINITY` when no timed transition is waiting.
    /// Used by the async loop to bound its `tokio::time::sleep`.
    fn millis_until_next_timed_transition(&self, now_ms: f64) -> f64;
}
