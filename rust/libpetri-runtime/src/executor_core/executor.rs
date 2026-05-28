//! The shared 5-phase CTPN execution loop.
//!
//! [`Executor<S, E>`] owns the cross-cutting state — event store, monotonic
//! clock, pending-reset bookkeeping, async signal channel — and drives the
//! loop against an [`ExecutorBackend`] that supplies the storage primitives
//! (enablement, token mutation, dirty tracking).
//!
//! ## Status
//!
//! Step 2 of the executor-backend-seam refactor: struct skeleton + key
//! observation methods. The 5-phase loop bodies (`run_sync`, `run_async`)
//! land in step 3 alongside `BitmapBackend`. Nothing inside the crate
//! constructs an [`Executor`] yet, hence the `dead_code` allowance.

#![allow(dead_code)]

use std::borrow::Cow;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Instant;

use libpetri_event::event_store::EventStore;

use crate::executor_core::backend::ExecutorBackend;
use crate::marking::Marking;

/// The shared executor. Monomorphised per backend (`Executor<BitmapBackend,
/// E>` is the reference; `Executor<PrecompiledBackend, E>` is the
/// production hot path).
///
/// The struct is `pub(crate)` for the duration of the refactor; once steps
/// 3–4 land, `BitmapNetExecutor` and `PrecompiledNetExecutor` become
/// public type aliases over this.
pub(crate) struct Executor<S: ExecutorBackend, E: EventStore> {
    backend: S,
    event_store: E,
    start_time: Instant,

    /// Places drained by reset arcs this cycle — used to suppress
    /// clock-restart for transitions whose inputs were just reset.
    pending_reset_places: HashSet<Arc<str>>,

    /// Tracks whether the configured net has any environment places at
    /// all. The async loop short-circuits the event-injection phase
    /// when this is false.
    has_environment_places: bool,

    /// Skip XOR/AND output spec validation (bypass for trusted callers
    /// that have proven their outputs match the spec statically).
    skip_output_validation: bool,
}

impl<S: ExecutorBackend, E: EventStore> Executor<S, E> {
    /// Wraps a configured backend with cross-cutting executor state.
    ///
    /// The backend is expected to be constructed with the net's initial
    /// marking already loaded; this constructor only attaches the
    /// event store, clock, and the per-cycle bookkeeping.
    pub(crate) fn from_parts(
        backend: S,
        event_store: E,
        has_environment_places: bool,
        skip_output_validation: bool,
    ) -> Self {
        Self {
            backend,
            event_store,
            start_time: Instant::now(),
            pending_reset_places: HashSet::new(),
            has_environment_places,
            skip_output_validation,
        }
    }

    /// Borrow the event store. Used by FFI layers that want to extract
    /// captured events after a sync run.
    pub(crate) fn event_store(&self) -> &E {
        &self.event_store
    }

    /// Snapshot the current marking. Zero-copy on backends whose
    /// canonical state is a `Marking` (bitmap); materialises from the
    /// internal store on backends that don't (precompiled ring buffers).
    pub(crate) fn marking(&self) -> Cow<'_, Marking> {
        self.backend.snapshot_marking()
    }

    /// True when there are no enabled transitions, no async completions
    /// pending, and no environment events in flight.
    pub(crate) fn is_quiescent(&self) -> bool {
        self.backend.is_quiescent()
    }

    /// Borrow the backend. Reserved for step 3 — the loop bodies need
    /// `&mut self.backend` to drive enablement and token mutation.
    pub(crate) fn backend(&self) -> &S {
        &self.backend
    }

    /// Mutable borrow of the backend. Reserved for step 3.
    pub(crate) fn backend_mut(&mut self) -> &mut S {
        &mut self.backend
    }
}
