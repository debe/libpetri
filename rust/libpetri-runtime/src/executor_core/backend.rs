//! The internal seam between the shared 5-phase execution loop
//! ([`Executor`]) and each executor's choice of token storage,
//! enablement representation, and dirty tracking.
//!
//! Implemented by `BitmapBackend` (reference) and `PrecompiledBackend`
//! (production hot path). The trait is `pub(crate)` because external
//! adapters aren't a goal yet — a public version waits for a second real
//! consumer outside the crate.
//!
//! ## Seam granularity
//!
//! The seam is at *phase* granularity, not per-primitive: methods like
//! [`update_enablement`](ExecutorBackend::update_enablement) and
//! [`consume_for_firing`](ExecutorBackend::consume_for_firing) wrap whole
//! cycle phases. The loop owns event emission, action execution, and
//! deadline arithmetic; each backend owns *how* its phase runs.
//!
//! [`Executor`]: crate::executor_core::executor::Executor

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use libpetri_core::token::ErasedToken;

use crate::compiled_net::CompiledNet;
use crate::marking::Marking;

/// Tokens consumed and tokens visible to read arcs when a single
/// transition fires.
///
/// The loop hands `inputs` and `reads` into the [`TransitionContext`].
/// Reset-arc tokens never reach the loop as a struct field — the
/// backend emits their `TokenRemoved` events via the
/// `emit_removed` closure passed to
/// [`consume_for_firing`](ExecutorBackend::consume_for_firing) and
/// drops the tokens.
///
/// [`TransitionContext`]: libpetri_core::context::TransitionContext
#[derive(Debug, Default)]
pub struct ConsumedInputs {
    pub inputs: HashMap<Arc<str>, Vec<ErasedToken>>,
    pub reads: HashMap<Arc<str>, Vec<ErasedToken>>,
}

/// Per-cycle enablement deltas reported by
/// [`ExecutorBackend::update_enablement`]. The loop walks each list to
/// emit `TransitionEnabled` and `TransitionClockRestarted` events.
#[derive(Debug, Default)]
pub struct EnablementChanges {
    pub newly_enabled: Vec<usize>,
    pub clock_restarted: Vec<usize>,
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
    fn update_enablement(&mut self, now_ms: f64, changes: &mut EnablementChanges);

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
    /// returned bundle in spec-declaration order via `emit_removed`.
    ///
    /// The closure is called for every consumed input/reset token at
    /// the moment it is removed, preserving the per-token event order
    /// the existing executor emits today.
    fn consume_for_firing<F>(&mut self, tid: usize, emit_removed: F) -> ConsumedInputs
    where
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
