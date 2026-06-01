//! Event store and live subscription bindings.
//!
//! Implements the **Rust-side, GIL-cold** event surface per the
//! `libpetri-py 2.7.0` plan and the `feedback_pyo3_gil_cold` memory:
//!
//! - The `InMemoryEventStore` is owned by Rust behind an `Arc<Mutex<...>>`.
//!   Python sees an opaque [`PyEventStoreHandle`], never the storage.
//! - The executor writes through [`PySharedEventStore`] (a thin
//!   `EventStore`-impl wrapper around the same `Arc`) — no GIL traffic on
//!   the hot path.
//! - Tier A: [`PyEventStoreHandle::events`] does *filtered* materialization
//!   into a `PyList` on demand. Filters evaluate in Rust; only matching
//!   events cross the boundary.
//! - Tier B: [`PyEventStoreHandle::subscribe`] returns an async iterator
//!   that yields **batches** of events through a bounded `tokio::mpsc`
//!   channel. One GIL acquisition per batch, not per event. Bridges to
//!   asyncio via the existing `pyo3_async_runtimes` + event-loop-locals
//!   pattern used by transition callbacks (`action.rs`).
//! - Tier C: counters / failures projections compute in Rust on demand.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
#[cfg(feature = "tokio")]
use std::time::Duration;

use libpetri::{EventStore, NetEvent};
#[cfg(feature = "tokio")]
use pyo3::exceptions::{PyStopAsyncIteration, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};

// ---------------------------------------------------------------------------
// NetEvent → Python: lazy, frozen wrapper
// ---------------------------------------------------------------------------

/// A single net event, frozen and held as `Arc<NetEvent>` on the Rust side.
///
/// Attribute getters materialize Python values on demand — there's no
/// upfront `Py<PyAny>` allocation, so dropping a `NetEvent` from Python
/// without inspecting its fields costs essentially nothing.
#[pyclass(module = "_libpetri", name = "NetEvent", frozen, skip_from_py_object)]
#[derive(Clone)]
pub struct PyNetEvent {
    inner: Arc<NetEvent>,
}

impl PyNetEvent {
    pub fn new(inner: Arc<NetEvent>) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl PyNetEvent {
    /// Discriminator matching the cross-language wire format
    /// (camelCase: `"TransitionStarted"`, `"TokenAdded"`, ...).
    #[getter]
    fn r#type(&self) -> &'static str {
        net_event_type(&self.inner)
    }

    /// Milliseconds since epoch (u64). Plain int for cheap construction —
    /// callers can `datetime.fromtimestamp(ev.timestamp / 1000)` when needed.
    #[getter]
    fn timestamp(&self) -> u64 {
        self.inner.timestamp()
    }

    /// Transition name for transition-related events; `None` otherwise.
    #[getter]
    fn transition_name(&self) -> Option<String> {
        self.inner.transition_name().map(str::to_owned)
    }

    /// Place name for `TokenAdded` / `TokenRemoved` events; `None` otherwise.
    #[getter]
    fn place_name(&self) -> Option<String> {
        self.inner.place_name().map(str::to_owned)
    }

    /// Full payload as a JSON-ish dict. Lazily constructed.
    fn payload<'py>(&self, py: Python<'py>) -> PyResult<Py<PyDict>> {
        let d = PyDict::new(py);
        match &*self.inner {
            NetEvent::ExecutionStarted { net_name, timestamp } => {
                d.set_item("net_name", net_name.as_ref())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::ExecutionCompleted { net_name, timestamp } => {
                d.set_item("net_name", net_name.as_ref())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::TransitionEnabled { transition_name, timestamp }
            | NetEvent::TransitionClockRestarted { transition_name, timestamp }
            | NetEvent::TransitionStarted { transition_name, timestamp }
            | NetEvent::TransitionCompleted { transition_name, timestamp }
            | NetEvent::TransitionTimedOut { transition_name, timestamp } => {
                d.set_item("transition_name", transition_name.as_ref())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::TransitionFailed { transition_name, error, timestamp } => {
                d.set_item("transition_name", transition_name.as_ref())?;
                d.set_item("error", error.as_str())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::ActionTimedOut { transition_name, timeout_ms, timestamp } => {
                d.set_item("transition_name", transition_name.as_ref())?;
                d.set_item("timeout_ms", *timeout_ms)?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::TokenAdded { place_name, timestamp, .. }
            | NetEvent::TokenRemoved { place_name, timestamp, .. } => {
                d.set_item("place_name", place_name.as_ref())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::LogMessage { transition_name, level, message, timestamp } => {
                d.set_item("transition_name", transition_name.as_ref())?;
                d.set_item("level", level.as_str())?;
                d.set_item("message", message.as_str())?;
                d.set_item("timestamp", *timestamp)?;
            }
            NetEvent::MarkingSnapshot { marking, timestamp } => {
                let inner = PyDict::new(py);
                for (place, count) in marking {
                    inner.set_item(place.as_ref(), *count)?;
                }
                d.set_item("marking", inner)?;
                d.set_item("timestamp", *timestamp)?;
            }
        }
        Ok(d.unbind())
    }

    fn __repr__(&self) -> String {
        format!(
            "NetEvent(type={}, timestamp={})",
            net_event_type(&self.inner),
            self.inner.timestamp()
        )
    }
}

/// Discriminator string for a `NetEvent` — matches the camelCase form used
/// by Java / TypeScript / Rust archive headers and the existing
/// `libpetri-debug` wire format.
fn net_event_type(event: &NetEvent) -> &'static str {
    match event {
        NetEvent::ExecutionStarted { .. } => "ExecutionStarted",
        NetEvent::ExecutionCompleted { .. } => "ExecutionCompleted",
        NetEvent::TransitionEnabled { .. } => "TransitionEnabled",
        NetEvent::TransitionClockRestarted { .. } => "TransitionClockRestarted",
        NetEvent::TransitionStarted { .. } => "TransitionStarted",
        NetEvent::TransitionCompleted { .. } => "TransitionCompleted",
        NetEvent::TransitionFailed { .. } => "TransitionFailed",
        NetEvent::TransitionTimedOut { .. } => "TransitionTimedOut",
        NetEvent::ActionTimedOut { .. } => "ActionTimedOut",
        NetEvent::TokenAdded { .. } => "TokenAdded",
        NetEvent::TokenRemoved { .. } => "TokenRemoved",
        NetEvent::LogMessage { .. } => "LogMessage",
        NetEvent::MarkingSnapshot { .. } => "MarkingSnapshot",
    }
}

// ---------------------------------------------------------------------------
// Filter predicates (Rust-evaluable, no Python callables)
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct FilterSpec {
    types: Option<HashSet<String>>,
    transitions: Option<HashSet<Arc<str>>>,
    places: Option<HashSet<Arc<str>>>,
}

impl FilterSpec {
    fn from_kwargs(
        types: Option<HashSet<String>>,
        transitions: Option<HashSet<String>>,
        places: Option<HashSet<String>>,
    ) -> Self {
        Self {
            types,
            transitions: transitions
                .map(|s| s.into_iter().map(Arc::<str>::from).collect()),
            places: places.map(|s| s.into_iter().map(Arc::<str>::from).collect()),
        }
    }

    fn matches(&self, event: &NetEvent) -> bool {
        if let Some(types) = &self.types
            && !types.contains(net_event_type(event))
        {
            return false;
        }
        if let Some(transitions) = &self.transitions {
            let Some(name) = event.transition_name() else {
                return false;
            };
            if !transitions.iter().any(|t| t.as_ref() == name) {
                return false;
            }
        }
        if let Some(places) = &self.places {
            let Some(name) = event.place_name() else {
                return false;
            };
            if !places.iter().any(|p| p.as_ref() == name) {
                return false;
            }
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Shared event-store storage
// ---------------------------------------------------------------------------

#[cfg(feature = "tokio")]
struct Subscriber {
    filter: FilterSpec,
    tx: tokio::sync::mpsc::Sender<Arc<NetEvent>>,
}

#[derive(Default)]
struct EventStoreInner {
    events: Vec<Arc<NetEvent>>,
    #[cfg(feature = "tokio")]
    subscribers: Vec<Subscriber>,
}

/// EventStore implementation handed to the executor. Cheaply cloneable
/// (`Arc` bump) and shares storage with the user-facing
/// [`PyEventStoreHandle`].
#[derive(Default, Clone)]
pub struct PySharedEventStore {
    inner: Arc<Mutex<EventStoreInner>>,
}

impl PySharedEventStore {
    fn from_handle(handle: &PyEventStoreHandle) -> Self {
        Self {
            inner: Arc::clone(&handle.inner),
        }
    }
}

impl EventStore for PySharedEventStore {
    const ENABLED: bool = true;

    fn append(&mut self, event: NetEvent) {
        let event = Arc::new(event);
        let mut inner = self.inner.lock().unwrap();
        inner.events.push(Arc::clone(&event));
        // Fan out to live subscribers. A subscriber is dropped if its
        // receiver disappeared (channel closed) — `try_send` returns Err on
        // both disconnect and full-channel. On full-channel we still drop:
        // a stalled consumer that can't keep up loses events rather than
        // back-pressuring the executor.
        #[cfg(feature = "tokio")]
        inner.subscribers.retain_mut(|sub| {
            if sub.filter.matches(&event) {
                sub.tx.try_send(Arc::clone(&event)).is_ok()
            } else {
                true
            }
        });
    }

    fn events(&self) -> &[NetEvent] {
        // The trait method is for in-process inspection through the
        // EventStore handle. The Python binding routes inspection through
        // PyEventStoreHandle::events instead (lifetime-safe, filtered) and
        // the executor never calls this method, so returning empty is
        // sound.
        &[]
    }

    fn size(&self) -> usize {
        self.inner.lock().unwrap().events.len()
    }

    fn is_empty(&self) -> bool {
        self.size() == 0
    }
}

// ---------------------------------------------------------------------------
// Python-facing handle (Tier A reads, Tier B subscriptions, Tier C projections)
// ---------------------------------------------------------------------------

/// Opaque handle to a Rust-side in-memory event store.
///
/// Pass to `run_sync` / `start_async` via the `event_store=` kwarg. The
/// executor writes events directly into the store on its own thread; this
/// handle is your read/subscribe surface from Python.
#[pyclass(module = "_libpetri", name = "InMemoryEventStore", skip_from_py_object)]
#[derive(Clone)]
pub struct PyEventStoreHandle {
    inner: Arc<Mutex<EventStoreInner>>,
}

#[pymethods]
impl PyEventStoreHandle {
    #[new]
    fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(EventStoreInner::default())),
        }
    }

    /// Total event count (cheap — single lock + len).
    fn __len__(&self) -> usize {
        self.inner.lock().unwrap().events.len()
    }

    /// Tier A: filtered, materialized event read.
    ///
    /// Filter predicates evaluate in Rust; only matching events cross the
    /// GIL boundary. `limit` and `offset` apply *after* filtering. Pass
    /// `types=None` (the default) to match all event types.
    #[pyo3(signature = (
        *,
        types = None,
        transitions = None,
        places = None,
        limit = None,
        offset = 0,
    ))]
    fn events<'py>(
        &self,
        py: Python<'py>,
        types: Option<HashSet<String>>,
        transitions: Option<HashSet<String>>,
        places: Option<HashSet<String>>,
        limit: Option<usize>,
        offset: usize,
    ) -> PyResult<Py<PyList>> {
        let filter = FilterSpec::from_kwargs(types, transitions, places);
        let inner = self.inner.lock().unwrap();
        let matches: Vec<Arc<NetEvent>> = inner
            .events
            .iter()
            .filter(|e| filter.matches(e))
            .skip(offset)
            .take(limit.unwrap_or(usize::MAX))
            .map(Arc::clone)
            .collect();
        drop(inner); // release lock before touching Python
        let list = PyList::empty(py);
        for ev in matches {
            list.append(Py::new(py, PyNetEvent::new(ev))?)?;
        }
        Ok(list.unbind())
    }

    /// Count events matching `types` (filtered in Rust). When `types` is
    /// `None`, returns the total — same as `len(store)`.
    #[pyo3(signature = (*, types = None))]
    fn count(&self, types: Option<HashSet<String>>) -> usize {
        let inner = self.inner.lock().unwrap();
        match types {
            None => inner.events.len(),
            Some(types) => inner
                .events
                .iter()
                .filter(|e| types.contains(net_event_type(e)))
                .count(),
        }
    }

    /// Tier C: histogram by event type, computed Rust-side.
    fn counters(&self, py: Python<'_>) -> PyResult<Py<PyDict>> {
        let inner = self.inner.lock().unwrap();
        let mut counts: HashMap<&'static str, usize> = HashMap::new();
        for ev in &inner.events {
            *counts.entry(net_event_type(ev)).or_insert(0) += 1;
        }
        drop(inner);
        let d = PyDict::new(py);
        for (k, v) in counts {
            d.set_item(k, v)?;
        }
        Ok(d.unbind())
    }

    /// Tier C: list of failure events as `PyNetEvent`s
    /// (`TransitionFailed`, `TransitionTimedOut`, `ActionTimedOut`).
    fn failures<'py>(&self, py: Python<'py>) -> PyResult<Py<PyList>> {
        let inner = self.inner.lock().unwrap();
        let matches: Vec<Arc<NetEvent>> = inner
            .events
            .iter()
            .filter(|e| e.is_failure())
            .map(Arc::clone)
            .collect();
        drop(inner);
        let list = PyList::empty(py);
        for ev in matches {
            list.append(Py::new(py, PyNetEvent::new(ev))?)?;
        }
        Ok(list.unbind())
    }

    /// Tier B: live filtered subscription.
    ///
    /// Returns an async iterator that yields batches of `NetEvent`. Filters
    /// are Rust-evaluable. Batching is Rust-driven: events buffer until
    /// `batch_size` is reached or `batch_timeout_ms` elapses, then the
    /// whole batch crosses the GIL in one acquisition.
    ///
    /// Pass `batch_size=1, batch_timeout_ms=0` for the unary low-latency
    /// mode (token-stream-style — yields each matching event immediately).
    ///
    /// `channel_capacity` bounds the in-Rust buffer; on overflow the
    /// executor drops events for this subscriber rather than back-pressuring
    /// the orchestrator loop. Match the capacity to your consumer's worst
    /// case to avoid loss.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (
        *,
        types = None,
        transitions = None,
        places = None,
        batch_size = 64,
        batch_timeout_ms = 10,
        channel_capacity = 4096,
    ))]
    fn subscribe(
        &self,
        types: Option<HashSet<String>>,
        transitions: Option<HashSet<String>>,
        places: Option<HashSet<String>>,
        batch_size: usize,
        batch_timeout_ms: u64,
        channel_capacity: usize,
    ) -> PyResult<PyEventSubscription> {
        if batch_size == 0 {
            return Err(PyValueError::new_err("batch_size must be >= 1"));
        }
        if channel_capacity == 0 {
            return Err(PyValueError::new_err("channel_capacity must be >= 1"));
        }
        let filter = FilterSpec::from_kwargs(types, transitions, places);
        let (tx, rx) = tokio::sync::mpsc::channel(channel_capacity);
        {
            let mut inner = self.inner.lock().unwrap();
            inner.subscribers.push(Subscriber { filter, tx });
        }
        Ok(PyEventSubscription {
            rx: Arc::new(tokio::sync::Mutex::new(Some(rx))),
            batch_size,
            batch_timeout: Duration::from_millis(batch_timeout_ms),
        })
    }
}

impl PyEventStoreHandle {
    pub fn shared(&self) -> PySharedEventStore {
        PySharedEventStore::from_handle(self)
    }

    /// Snapshot of all currently-stored events as a `Vec<Arc<NetEvent>>` —
    /// used by the archive writer (which copies them into a DebugEventStore
    /// to satisfy the `libpetri_debug` archive API).
    #[cfg(feature = "archive")]
    pub fn events_arc_vec(&self) -> Vec<Arc<NetEvent>> {
        self.inner.lock().unwrap().events.iter().map(Arc::clone).collect()
    }
}

// ---------------------------------------------------------------------------
// Tier B async subscription
// ---------------------------------------------------------------------------

/// Async iterator over batches of `NetEvent` (Tier B subscription handle).
///
/// The receiver lives behind `Mutex<Option<Receiver>>` so that
/// [`close`](PyEventSubscription::close) can take and drop it eagerly,
/// freeing the channel for the executor's `retain_mut`-driven unregister on
/// the next append. `__anext__` short-circuits to `StopAsyncIteration` once
/// the receiver has been taken.
#[cfg(feature = "tokio")]
#[pyclass(module = "_libpetri", name = "EventSubscription")]
pub struct PyEventSubscription {
    rx: Arc<tokio::sync::Mutex<Option<tokio::sync::mpsc::Receiver<Arc<NetEvent>>>>>,
    batch_size: usize,
    batch_timeout: Duration,
}

#[cfg(feature = "tokio")]
#[pymethods]
impl PyEventSubscription {
    fn __aiter__(slf: Py<Self>) -> Py<Self> {
        slf
    }

    fn __anext__<'py>(&self, py: Python<'py>) -> PyResult<Py<PyAny>> {
        let rx = Arc::clone(&self.rx);
        let batch_size = self.batch_size;
        let batch_timeout = self.batch_timeout;
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let mut guard = rx.lock().await;
            // `close()` may have taken the receiver — short-circuit cleanly.
            let rx = guard
                .as_mut()
                .ok_or_else(|| PyStopAsyncIteration::new_err(""))?;
            // Block until at least one matching event arrives — or the store
            // closes the channel, in which case stop iteration.
            let Some(first) = rx.recv().await else {
                return Err(PyStopAsyncIteration::new_err(""));
            };
            let mut batch: Vec<Arc<NetEvent>> = vec![first];

            if batch_size > 1 {
                if batch_timeout.is_zero() {
                    // No timeout — drain whatever's already buffered up to
                    // batch_size, but don't wait for more.
                    while batch.len() < batch_size {
                        match rx.try_recv() {
                            Ok(ev) => batch.push(ev),
                            Err(_) => break,
                        }
                    }
                } else {
                    let deadline = tokio::time::Instant::now() + batch_timeout;
                    while batch.len() < batch_size {
                        let remaining = deadline
                            .saturating_duration_since(tokio::time::Instant::now());
                        if remaining.is_zero() {
                            break;
                        }
                        match tokio::time::timeout(remaining, rx.recv()).await {
                            Ok(Some(ev)) => batch.push(ev),
                            Ok(None) | Err(_) => break,
                        }
                    }
                }
            }

            Python::attach(|py| {
                let list = PyList::empty(py);
                for ev in batch {
                    list.append(Py::new(py, PyNetEvent::new(ev))?)?;
                }
                Ok::<_, PyErr>(list.unbind().into_any())
            })
        })?;
        Ok(awaitable.unbind())
    }

    /// Stop the subscription. Drops the receiver eagerly when the lock is
    /// uncontended; otherwise (a batch is mid-await) the receiver drops when
    /// that batch returns or when the subscription object itself is GC'd.
    ///
    /// Either way the executor unregisters this subscriber the next time it
    /// tries to fan out an event (`retain_mut` sees the closed channel via
    /// `try_send`).
    fn close(&self) -> PyResult<()> {
        // try_lock so `close()` never blocks Python. The common path —
        // calling `close()` between batches or after the iterator was
        // already exhausted — always succeeds here.
        if let Ok(mut guard) = self.rx.try_lock() {
            let _ = guard.take();
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyNetEvent>()?;
    m.add_class::<PyEventStoreHandle>()?;
    #[cfg(feature = "tokio")]
    m.add_class::<PyEventSubscription>()?;
    Ok(())
}

