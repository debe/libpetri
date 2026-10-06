//! Event store and live subscription bindings.
//!
//! Implements the **Rust-side, GIL-cold** event surface per the
//! `libpetri-py 2.7.0` plan and the `feedback_pyo3_gil_cold` memory:
//!
//! - The `InMemoryEventStore` is owned by Rust behind an `Arc<Mutex<...>>`.
//!   Python sees an opaque [`PyEventStoreHandle`], never the storage.
//! - The executor writes through [`RunStore`] (a thin `EventStore`-impl
//!   wrapper around the same `Arc`), so there is no GIL traffic on the hot
//!   path.
//! - A store written in Python (any object with `append(event)`) receives
//!   events from one drainer thread per run, in batches: one GIL
//!   acquisition per batch, never on the executor's thread.
//! - Tier A: [`PyEventStoreHandle::events`] does *filtered* materialization
//!   into a `PyList` on demand. Filters evaluate in Rust; only matching
//!   events cross the boundary.
//! - Tier B: [`PyEventStoreHandle::subscribe`] returns an async iterator
//!   that yields **batches** of events through a bounded `tokio::mpsc`
//!   channel. One GIL acquisition per batch, not per event. Bridges to
//!   asyncio via the existing `pyo3_async_runtimes` + event-loop-locals
//!   pattern used by transition callbacks (`action.rs`).
//! - Tier C: counters / failures projections compute in Rust on demand.

use std::collections::{BTreeMap, HashSet};
use std::sync::{Arc, Mutex, mpsc};
#[cfg(feature = "tokio")]
use std::time::Duration;

use libpetri::{EventStore, NetEvent};
#[cfg(feature = "tokio")]
use pyo3::exceptions::{PyStopAsyncIteration, PyValueError};
use pyo3::exceptions::PyTypeError;
use pyo3::intern;
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyDict, PyList, PyString};

use crate::value::{PyTokenValue, place_name_from_object};

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

    /// The token value on a `TokenAdded` / `TokenRemoved` event, when the
    /// store asked for it (`capture_tokens` / `captures_tokens`). This is the
    /// token object itself, not a copy. `None` otherwise, and for events read
    /// back from an archive.
    #[getter]
    fn token(&self, py: Python<'_>) -> Option<Py<PyAny>> {
        token_value(py, &self.inner)
    }

    /// Full payload as a JSON-ish dict. Lazily constructed. Token events
    /// carry `"token"` when the value was captured.
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
                if let Some(token) = token_value(py, &self.inner) {
                    d.set_item("token", token)?;
                }
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

/// The Python token carried by a token event, if one was captured.
fn token_value(py: Python<'_>, event: &NetEvent) -> Option<Py<PyAny>> {
    let token = match event {
        NetEvent::TokenAdded { token, .. } | NetEvent::TokenRemoved { token, .. } => token.as_ref()?,
        _ => return None,
    };
    token
        .value_any()
        .downcast_ref::<PyTokenValue>()
        .map(|value| value.clone_ref(py))
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

impl EventStoreInner {
    /// Stores `event` and fans it out to live subscribers. A subscriber is
    /// dropped if its receiver disappeared (channel closed): `try_send`
    /// returns Err on both disconnect and full-channel. On full-channel we
    /// still drop: a stalled consumer that can't keep up loses events rather
    /// than back-pressuring the executor.
    fn push(&mut self, event: Arc<NetEvent>) {
        #[cfg(feature = "tokio")]
        self.subscribers.retain_mut(|sub| {
            if sub.filter.matches(&event) {
                sub.tx.try_send(Arc::clone(&event)).is_ok()
            } else {
                true
            }
        });
        self.events.push(event);
    }
}

/// Which token payloads a store asks for on `TokenAdded` / `TokenRemoved`.
#[derive(Clone, Default)]
pub enum CaptureSpec {
    /// No payloads (the default).
    #[default]
    Off,
    /// Payloads for every place.
    All,
    /// Payloads only for the listed places. The core captures every place
    /// and [`RunStore`] strips the rest.
    Places(Arc<HashSet<Arc<str>>>),
}

impl CaptureSpec {
    /// Reads `True`, `False`, `None` or an iterable of place names / `Place`s.
    /// A bare string is rejected: it is iterable, so it would otherwise be
    /// read as a list of one-character place names.
    fn from_py(value: Option<&Bound<'_, PyAny>>) -> PyResult<Self> {
        let Some(value) = value else {
            return Ok(Self::Off);
        };
        if value.is_none() {
            return Ok(Self::Off);
        }
        if let Ok(flag) = value.cast::<PyBool>() {
            return Ok(if flag.is_true() { Self::All } else { Self::Off });
        }
        if value.is_instance_of::<PyString>() {
            return Err(PyTypeError::new_err(
                "capture_tokens must be a bool or a list of place names, not a str",
            ));
        }
        let iter = value.try_iter().map_err(|_| {
            PyTypeError::new_err("capture_tokens must be a bool or a list of place names")
        })?;
        let mut places = HashSet::new();
        for item in iter {
            places.insert(place_name_from_object(&item?)?);
        }
        if places.is_empty() {
            return Ok(Self::Off);
        }
        Ok(Self::Places(Arc::new(places)))
    }
}

/// The store one run writes through. `CAPTURE` is the core's
/// [`EventStore::CAPTURES_TOKENS`] switch, so a run without capture pays
/// nothing for it.
///
/// - `memory` is the Rust-side [`PyEventStoreHandle`] storage; events land
///   there without touching the GIL and fan out to its subscribers.
/// - `forward` sends each event to the run's drainer thread, which hands it
///   to a store written in Python.
/// - `place_filter` keeps payloads only for the listed places.
///
/// Not `Clone`: the executor owns the only sender, so dropping the executor
/// at the end of the run closes the drainer's channel.
#[derive(Default)]
pub struct RunStore<const CAPTURE: bool> {
    memory: Option<Arc<Mutex<EventStoreInner>>>,
    forward: Option<mpsc::Sender<Arc<NetEvent>>>,
    place_filter: Option<Arc<HashSet<Arc<str>>>>,
    appended: usize,
}

impl<const CAPTURE: bool> RunStore<CAPTURE> {
    /// Drops the payload of a token event whose place is not in the filter.
    /// The variants are `#[non_exhaustive]`, so the stripped event is
    /// rebuilt through the public constructors.
    fn filter_payload(&self, event: NetEvent) -> NetEvent {
        let Some(filter) = &self.place_filter else {
            return event;
        };
        match &event {
            NetEvent::TokenAdded { place_name, timestamp, token: Some(_), .. }
                if !filter.contains(place_name.as_ref()) =>
            {
                NetEvent::token_added(Arc::clone(place_name), *timestamp)
            }
            NetEvent::TokenRemoved { place_name, timestamp, token: Some(_), .. }
                if !filter.contains(place_name.as_ref()) =>
            {
                NetEvent::token_removed(Arc::clone(place_name), *timestamp)
            }
            _ => event,
        }
    }
}

impl<const CAPTURE: bool> EventStore for RunStore<CAPTURE> {
    const ENABLED: bool = true;
    const CAPTURES_TOKENS: bool = CAPTURE;

    fn append(&mut self, event: NetEvent) {
        let event = if CAPTURE { self.filter_payload(event) } else { event };
        let event = Arc::new(event);
        self.appended += 1;
        if let Some(memory) = &self.memory {
            memory.lock().unwrap().push(Arc::clone(&event));
        }
        if let Some(forward) = &self.forward {
            // Unbounded, so the executor never waits on Python. A send only
            // fails once the drainer has gone, and then nobody is listening.
            let _ = forward.send(event);
        }
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
        self.appended
    }

    fn is_empty(&self) -> bool {
        self.appended == 0
    }
}

/// The store a run was given, resolved once at run start.
pub enum RunSink {
    /// No store, or a Python store whose `is_enabled()` returned False.
    Noop,
    Plain(RunStore<false>),
    Capture(RunStore<true>),
}

impl RunSink {
    fn new(
        memory: Option<Arc<Mutex<EventStoreInner>>>,
        forward: Option<mpsc::Sender<Arc<NetEvent>>>,
        capture: CaptureSpec,
    ) -> Self {
        match capture {
            CaptureSpec::Off => Self::Plain(RunStore { memory, forward, place_filter: None, appended: 0 }),
            CaptureSpec::All => Self::Capture(RunStore { memory, forward, place_filter: None, appended: 0 }),
            CaptureSpec::Places(places) => Self::Capture(RunStore {
                memory,
                forward,
                place_filter: Some(places),
                appended: 0,
            }),
        }
    }
}

/// The first exception a Python store's `append` raised during a run.
pub type StoreErrorSlot = Arc<Mutex<Option<Py<PyAny>>>>;

/// Everything a run needs for its `event_store=` argument.
pub struct RunPlan {
    pub sink: RunSink,
    /// Present when the store is written in Python.
    pub drainer: Option<Drainer>,
    pub error: StoreErrorSlot,
}

/// Events a drainer hands to Python per GIL acquisition, at most.
const DRAIN_BATCH: usize = 257;

/// The thread that delivers one run's events to a Python store.
///
/// It blocks on the channel, gathers whatever else is already queued (up to
/// [`DRAIN_BATCH`] events), attaches once and calls `append` for each event
/// in order. It ends when the channel closes, which happens when the
/// executor drops its [`RunStore`] at the end of the run.
pub struct Drainer {
    thread: std::thread::JoinHandle<()>,
    #[cfg(feature = "tokio")]
    done: tokio::sync::oneshot::Receiver<()>,
}

impl Drainer {
    fn spawn(
        target: Py<PyAny>,
        rx: mpsc::Receiver<Arc<NetEvent>>,
        error: StoreErrorSlot,
    ) -> PyResult<Self> {
        #[cfg(feature = "tokio")]
        let (done_tx, done) = tokio::sync::oneshot::channel::<()>();
        let thread = std::thread::Builder::new()
            .name("libpetri-event-drainer".into())
            .spawn(move || {
                let mut batch: Vec<Arc<NetEvent>> = Vec::new();
                while let Ok(first) = rx.recv() {
                    batch.push(first);
                    while batch.len() < DRAIN_BATCH {
                        match rx.try_recv() {
                            Ok(event) => batch.push(event),
                            Err(_) => break,
                        }
                    }
                    Python::attach(|py| deliver(py, &target, batch.drain(..), &error));
                }
                // Release the Python references while attached rather than
                // leaving them to the reference pool.
                Python::attach(|_py| {
                    drop(target);
                    drop(error);
                });
                #[cfg(feature = "tokio")]
                let _ = done_tx.send(());
            })
            .map_err(|e| {
                pyo3::exceptions::PyRuntimeError::new_err(format!(
                    "could not start the event-store drainer thread: {e}"
                ))
            })?;
        Ok(Self {
            thread,
            #[cfg(feature = "tokio")]
            done,
        })
    }

    /// Blocks until every event has been delivered. Call it detached: the
    /// drainer needs the GIL to deliver.
    pub fn join(self) {
        let _ = self.thread.join();
    }

    /// Resolves once every event has been delivered. Holds no GIL while it
    /// waits.
    #[cfg(feature = "tokio")]
    pub async fn finished(self) {
        // An Err means the thread died without signalling (a panic). It has
        // stopped delivering either way.
        let _ = self.done.await;
    }
}

/// Calls `target.append(event)` for each event. An exception is logged to
/// the `libpetri` logger, the first one is kept, and delivery goes on.
fn deliver(
    py: Python<'_>,
    target: &Py<PyAny>,
    events: impl Iterator<Item = Arc<NetEvent>>,
    error: &StoreErrorSlot,
) {
    let target = target.bind(py);
    for event in events {
        let result = Py::new(py, PyNetEvent::new(event))
            .and_then(|wrapped| target.call_method1(intern!(py, "append"), (wrapped,)));
        if let Err(err) = result {
            report_store_error(py, err, error);
        }
    }
}

fn report_store_error(py: Python<'_>, err: PyErr, slot: &StoreErrorSlot) {
    let value = err.value(py).clone();
    {
        let mut first = slot.lock().unwrap();
        if first.is_none() {
            *first = Some(value.clone().into_any().unbind());
        }
    }
    let logged = (|| -> PyResult<()> {
        let logger = py
            .import("logging")?
            .call_method1("getLogger", ("libpetri",))?;
        let kwargs = PyDict::new(py);
        kwargs.set_item("exc_info", &value)?;
        logger.call_method(
            "error",
            ("event store append raised; delivering the remaining events",),
            Some(&kwargs),
        )?;
        Ok(())
    })();
    if let Err(log_err) = logged {
        log_err.write_unraisable(py, None);
    }
}

/// Reads an optional protocol member: a zero-argument method is called, any
/// other value is used as is. `None` when the object has no such member.
fn optional_member<'py>(
    store: &Bound<'py, PyAny>,
    name: &Bound<'py, PyString>,
) -> PyResult<Option<Bound<'py, PyAny>>> {
    if !store.hasattr(name)? {
        return Ok(None);
    }
    let member = store.getattr(name)?;
    if member.is_callable() {
        Ok(Some(member.call0()?))
    } else {
        Ok(Some(member))
    }
}

/// Resolves `event_store=` for one run.
///
/// Accepts `None`, an [`PyEventStoreHandle`] (`InMemoryEventStore`), or any
/// object with a callable `append`. For a Python store, `is_enabled` and
/// `captures_tokens` are read here, once. Anything else is a `TypeError`.
pub fn prepare_run_store(
    py: Python<'_>,
    event_store: Option<&Bound<'_, PyAny>>,
) -> PyResult<RunPlan> {
    let error: StoreErrorSlot = Arc::new(Mutex::new(None));
    let Some(store) = event_store.filter(|s| !s.is_none()) else {
        return Ok(RunPlan { sink: RunSink::Noop, drainer: None, error });
    };
    if let Ok(handle) = store.cast::<PyEventStoreHandle>() {
        let handle = handle.borrow();
        let sink = RunSink::new(Some(Arc::clone(&handle.inner)), None, handle.capture.clone());
        return Ok(RunPlan { sink, drainer: None, error });
    }
    let has_append = store.hasattr(intern!(py, "append"))?
        && store.getattr(intern!(py, "append"))?.is_callable();
    if !has_append {
        return Err(PyTypeError::new_err(format!(
            "event_store must be an InMemoryEventStore or an object with a callable \
             append(event), got {}",
            store.get_type().name()?
        )));
    }
    if let Some(enabled) = optional_member(store, intern!(py, "is_enabled"))?
        && !enabled.is_truthy()?
    {
        return Ok(RunPlan { sink: RunSink::Noop, drainer: None, error });
    }
    let capture = CaptureSpec::from_py(
        optional_member(store, intern!(py, "captures_tokens"))?.as_ref(),
    )?;
    let (tx, rx) = mpsc::channel();
    let drainer = Drainer::spawn(store.clone().unbind(), rx, Arc::clone(&error))?;
    Ok(RunPlan {
        sink: RunSink::new(None, Some(tx), capture),
        drainer: Some(drainer),
        error,
    })
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
    capture: CaptureSpec,
}

#[pymethods]
impl PyEventStoreHandle {
    /// `capture_tokens` asks the executor to attach token values to
    /// `TokenAdded` / `TokenRemoved` events: `True` for every place, or a
    /// list of place names (or `Place`s) for just those. Read through
    /// `NetEvent.token`. Default `False`.
    #[new]
    #[pyo3(signature = (*, capture_tokens = None))]
    fn new(capture_tokens: Option<&Bound<'_, PyAny>>) -> PyResult<Self> {
        Ok(Self {
            inner: Arc::new(Mutex::new(EventStoreInner::default())),
            capture: CaptureSpec::from_py(capture_tokens)?,
        })
    }

    /// Appends `event` and fans it out to live subscribers, as the executor
    /// does. This lets a store written in Python pass events on to this one.
    /// The event is stored as given: when a Python store wraps this one, the
    /// outer store's `captures_tokens` decides which payloads exist.
    fn append(&self, event: PyRef<'_, PyNetEvent>) {
        self.inner.lock().unwrap().push(Arc::clone(&event.inner));
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

    /// Tier C: histogram by event type, computed Rust-side. Event types in
    /// ascending order — a Python dict is an ordered medium, so a hashed
    /// container here would reorder the histogram on every process run.
    fn counters(&self, py: Python<'_>) -> PyResult<Py<PyDict>> {
        let inner = self.inner.lock().unwrap();
        let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
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

    /// Streaming-mode subscription: yields one `NetEvent` per
    /// `__anext__`, no per-event list wrapper. Optimised for
    /// token-by-token consumers (LLM chunk delivery, byte streams) that
    /// want each event delivered immediately.
    ///
    /// Equivalent in semantics to `subscribe(batch_size=1,
    /// batch_timeout_ms=0)` but skips the `PyList[NetEvent]` allocation
    /// per yield. Use this for hot-path streaming; use `subscribe(...)`
    /// for batched / throughput-oriented consumers.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (
        *,
        types = None,
        transitions = None,
        places = None,
        channel_capacity = 4096,
    ))]
    fn subscribe_stream(
        &self,
        types: Option<HashSet<String>>,
        transitions: Option<HashSet<String>>,
        places: Option<HashSet<String>>,
        channel_capacity: usize,
    ) -> PyResult<PyEventStream> {
        if channel_capacity == 0 {
            return Err(PyValueError::new_err("channel_capacity must be >= 1"));
        }
        let filter = FilterSpec::from_kwargs(types, transitions, places);
        let (tx, rx) = tokio::sync::mpsc::channel(channel_capacity);
        {
            let mut inner = self.inner.lock().unwrap();
            inner.subscribers.push(Subscriber { filter, tx });
        }
        Ok(PyEventStream {
            rx: Arc::new(tokio::sync::Mutex::new(Some(rx))),
        })
    }
}

impl PyEventStoreHandle {
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

/// Streaming-mode subscription handle: `__anext__` returns a single
/// `PyNetEvent` (not a list-of-one). Trades batch throughput for the
/// tightest per-event latency on the unary path.
#[cfg(feature = "tokio")]
#[pyclass(module = "_libpetri", name = "EventStream")]
pub struct PyEventStream {
    rx: Arc<tokio::sync::Mutex<Option<tokio::sync::mpsc::Receiver<Arc<NetEvent>>>>>,
}

#[cfg(feature = "tokio")]
#[pymethods]
impl PyEventStream {
    fn __aiter__(slf: Py<Self>) -> Py<Self> {
        slf
    }

    fn __anext__<'py>(&self, py: Python<'py>) -> PyResult<Py<PyAny>> {
        let rx = Arc::clone(&self.rx);
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let mut guard = rx.lock().await;
            let rx = guard
                .as_mut()
                .ok_or_else(|| PyStopAsyncIteration::new_err(""))?;
            let Some(event) = rx.recv().await else {
                return Err(PyStopAsyncIteration::new_err(""));
            };
            Python::attach(|py| {
                let wrapper = Py::new(py, PyNetEvent::new(event))?;
                Ok::<_, PyErr>(wrapper.into_any())
            })
        })?;
        Ok(awaitable.unbind())
    }

    fn close(&self) -> PyResult<()> {
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
    {
        m.add_class::<PyEventSubscription>()?;
        m.add_class::<PyEventStream>()?;
    }
    Ok(())
}

