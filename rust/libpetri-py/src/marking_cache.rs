//! MarkingCache bindings — periodic state snapshots for fast seek/replay.
//!
//! Wraps `libpetri_debug::marking_cache::MarkingCache`. Per the
//! `feedback_pyo3_gil_cold` memory: the cache lives in Rust; Python only
//! crosses the GIL to issue queries. Snapshot computation and replay deltas
//! happen on the Rust side. Gated on the `archive` feature because
//! `MarkingCache` is part of `libpetri-debug`, which the umbrella crate
//! pulls in only when `debug` (and hence `archive`) is enabled.

use std::sync::Mutex;

use libpetri::debug::marking_cache::{ComputedState, MarkingCache};
use pyo3::prelude::*;
use pyo3::types::PyDict;

use crate::events::PyEventStoreHandle;

/// Snapshot of execution state at a given event index — marking, enabled
/// transitions, in-flight transitions. Output of `MarkingCache.compute_at`.
#[pyclass(module = "_libpetri", name = "ComputedState", frozen)]
pub struct PyComputedState {
    inner: ComputedState,
}

#[pymethods]
impl PyComputedState {
    /// Token-count marking per place: `{place_name: token_count}`.
    ///
    /// Note that — unlike `MarkingView.snapshot()` from a live executor —
    /// these tokens are *replayed* from the event stream and therefore lack
    /// their original value payloads (events only carry type + structured
    /// JSON metadata, not Python objects). The shape mirrors Java's
    /// `ComputedState.marking()` for debug-protocol parity.
    #[getter]
    fn marking<'py>(&self, py: Python<'py>) -> PyResult<Py<PyDict>> {
        let d = PyDict::new(py);
        for (place, tokens) in &self.inner.marking {
            d.set_item(place, tokens.len())?;
        }
        Ok(d.unbind())
    }

    #[getter]
    fn enabled_transitions(&self) -> Vec<String> {
        self.inner.enabled_transitions.clone()
    }

    #[getter]
    fn in_flight_transitions(&self) -> Vec<String> {
        self.inner.in_flight_transitions.clone()
    }

    fn __repr__(&self) -> String {
        format!(
            "ComputedState(places={}, enabled={}, in_flight={})",
            self.inner.marking.len(),
            self.inner.enabled_transitions.len(),
            self.inner.in_flight_transitions.len(),
        )
    }
}

/// Periodic-snapshot cache for replaying an event stream up to a target
/// index in roughly O(SNAPSHOT_INTERVAL) work (default interval = 256).
///
/// Use with an `InMemoryEventStore` to drive debug-protocol seeking and
/// step-forward/step-back from Python without re-walking the full stream
/// on every query.
#[pyclass(module = "_libpetri", name = "MarkingCache")]
pub struct PyMarkingCache {
    inner: Mutex<MarkingCache>,
}

#[pymethods]
impl PyMarkingCache {
    #[new]
    fn new() -> Self {
        Self {
            inner: Mutex::new(MarkingCache::new()),
        }
    }

    /// Compute the state at `event_index` by replaying from the nearest
    /// cached snapshot. Subsequent calls reuse the cache; computation cost
    /// is dominated by the delta from the nearest snapshot, not by the
    /// total event count.
    fn compute_at(
        &self,
        store: &PyEventStoreHandle,
        event_index: usize,
    ) -> PyResult<PyComputedState> {
        let events_arc = store.events_arc_vec();
        // The Rust API takes &[NetEvent], so we briefly materialize an owned
        // Vec<NetEvent> from the Arc<NetEvent> snapshot. NetEvent: Clone is
        // cheap (Arc bumps for the name fields), and the materialization is
        // proportional to event count — fine for debug-protocol querying.
        let events: Vec<libpetri::NetEvent> =
            events_arc.iter().map(|e| (**e).clone()).collect();
        let mut cache = self.inner.lock().unwrap();
        let state = cache.compute_at(&events, event_index);
        Ok(PyComputedState { inner: state })
    }

    /// Drops all cached snapshots. The next `compute_at` rebuilds them from
    /// scratch. Call this if the event stream is being replaced (e.g.
    /// switching debug sessions).
    fn invalidate(&self) {
        self.inner.lock().unwrap().invalidate();
    }

    fn __repr__(&self) -> &'static str {
        "MarkingCache(...)"
    }
}

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyMarkingCache>()?;
    m.add_class::<PyComputedState>()?;
    Ok(())
}
