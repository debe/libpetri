//! Compiled-net and executor bindings.
//!
//! [`PyCompiledNet`] wraps [`OwnedPrecompiledNet`] (the FFI-safe entry to the
//! precompiled execution path). Sync runs return a marking dict; async runs
//! return an `(ExecutorHandle, awaitable)` pair so callers can inject
//! environment events.

use std::collections::HashSet;
use std::sync::Arc;

#[cfg(feature = "tokio")]
use std::sync::Mutex;

#[cfg(feature = "tokio")]
use libpetri::TerminationReason;
use libpetri::{
    EventStore, NoopEventStore, OwnedPrecompiledExecutorBuilder, OwnedPrecompiledNet, PetriNet,
    RunOutcome,
};
#[cfg(feature = "tokio")]
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict};

use crate::clock::HostClock;
use crate::error::panic_to_py;
#[cfg(feature = "tokio")]
use crate::events::StoreErrorSlot;
use crate::events::{RunSink, prepare_run_store};
use crate::model::PyPetriNet;
#[cfg(feature = "tokio")]
use crate::value::{erased_from_py_at, place_name_from_object};
use crate::value::{marking_from_python_at, marking_snapshot_to_python};

/// Run-time options for a single execution.
///
/// `environment_places` keeps the executor alive while external tokens may
/// still arrive. `skip_output_validation` disables AND/XOR output-spec checks
/// for trusted callers. `clock` installs a host clock (TIME-015).
#[pyclass(module = "_libpetri", name = "ExecutorOptions", from_py_object)]
#[derive(Clone, Default)]
pub struct PyExecutorOptions {
    environment_places: Vec<String>,
    skip_output_validation: bool,
    deadline_tolerance_ms: Option<f64>,
    execution_scope: Option<String>,
    clock: Option<HostClock>,
}

impl PyExecutorOptions {
    /// \[TIME-015\] The host clock, if any.
    pub fn clock(&self) -> Option<&HostClock> {
        self.clock.as_ref()
    }

    /// Epoch milliseconds for a token created now: from the host clock when
    /// one is installed, else wall time.
    pub fn epoch_now(&self) -> u64 {
        match &self.clock {
            Some(clock) => clock.as_executor_clock().epoch_ms(),
            None => libpetri::core::token::now_millis(),
        }
    }

    /// \[NU-011\] The host-pinned ν-name scope, if any.
    pub fn execution_scope(&self) -> Option<&str> {
        self.execution_scope.as_deref()
    }

    pub fn environment_place_set(&self) -> HashSet<Arc<str>> {
        self.environment_places
            .iter()
            .cloned()
            .map(Arc::<str>::from)
            .collect()
    }
}

#[pymethods]
impl PyExecutorOptions {
    /// Constructs options; pass `environment_places=[...]` to mark places that
    /// will receive external token injection during async runs.
    ///
    /// `deadline_tolerance_ms` is the grace band beyond a hard deadline
    /// (`deadline()` / `window()`) before a transition is force-disabled (TIME-013); `None` uses
    /// the library default (5ms). Real-time orchestrators whose runs can stall may widen it. Must
    /// be non-negative. Does not affect `exact()` transitions, which are enforced softly and never
    /// force-disabled (TIME-006).
    ///
    /// \[NU-011\] `execution_scope` is folded into every minted ν-name
    /// (`<transition>#<scope>:<n>`). `None` draws a fresh random scope per executor — 128 bits as
    /// exactly 32 lowercase hex characters, unique across processes and **not** reproducible; pin
    /// one to make a resumed segment's names reproducible (`<n>` is a per-executor counter from
    /// 0). Raises `ValueError` for an empty scope (whitespace is legal) or one containing `':'` or
    /// `'#'` — the same rule as every other implementation, under which a minted name parses
    /// uniquely: the last `':'` splits off the counter, then the last `'#'` before it the scope.
    ///
    /// \[TIME-015\] `clock` is a `ManualClock` or a `SteppedClock`; anything else raises
    /// `TypeError`. The run reads time from it, and tokens created without a timestamp (legacy
    /// `initial` values, `inject`) are stamped from its `epoch_ms()`.
    #[new]
    #[pyo3(signature = (*, environment_places = None, skip_output_validation = false, deadline_tolerance_ms = None, execution_scope = None, clock = None))]
    fn new(
        environment_places: Option<Vec<String>>,
        skip_output_validation: bool,
        deadline_tolerance_ms: Option<f64>,
        execution_scope: Option<String>,
        clock: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<Self> {
        let clock = match clock {
            Some(obj) if !obj.is_none() => Some(HostClock::from_python(obj)?),
            _ => None,
        };
        // Validated here with the core's own rule. The core *panics* on a bad
        // scope at executor construction, and a panic across the FFI at run
        // time is no way to report a typo — so it must never get that far.
        if let Some(scope) = &execution_scope {
            libpetri::validate_execution_scope(scope).map_err(|e| {
                pyo3::exceptions::PyValueError::new_err(format!("{e}: {scope:?}"))
            })?;
        }
        if let Some(ms) = deadline_tolerance_ms {
            if !(ms >= 0.0) {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "deadline_tolerance_ms must be non-negative: {ms}"
                )));
            }
        }
        Ok(Self {
            execution_scope,
            environment_places: environment_places.unwrap_or_default(),
            skip_output_validation,
            deadline_tolerance_ms,
            clock,
        })
    }

    /// Names of places that the executor must keep waiting on (env-driven inputs).
    #[getter]
    fn environment_places(&self) -> Vec<String> {
        self.environment_places.clone()
    }

    /// Whether per-transition output validation (AND/XOR) is bypassed.
    #[getter]
    fn skip_output_validation(&self) -> bool {
        self.skip_output_validation
    }

    /// \[NU-011\] The pinned ν-name scope, or `None` when the executor draws
    /// its own: a random 32-lowercase-hex token, fresh per executor and not
    /// observable here (it does not exist until the run mints a name).
    #[getter(execution_scope)]
    fn execution_scope_py(&self) -> Option<String> {
        self.execution_scope.clone()
    }

    /// Deadline-enforcement tolerance in milliseconds, or `None` for the library default (5ms).
    #[getter]
    fn deadline_tolerance_ms(&self) -> Option<f64> {
        self.deadline_tolerance_ms
    }

    /// \[TIME-015\] The host clock, or `None` for wall time. A new wrapper
    /// around the same clock, so it compares unequal to the object passed in
    /// but advancing it advances that clock.
    #[getter(clock)]
    fn clock_py(&self, py: Python<'_>) -> PyResult<Option<Py<PyAny>>> {
        self.clock.as_ref().map(|c| c.to_python(py)).transpose()
    }
}

/// A precompiled Petri net ready to be executed.
///
/// Construct from a `Net`, then call `run_sync` (returns a final marking dict)
/// or `run_async` (returns an `(ExecutorHandle, awaitable)` pair).
#[pyclass(module = "_libpetri", name = "CompiledNet", from_py_object)]
#[derive(Clone)]
pub struct PyCompiledNet {
    inner: OwnedPrecompiledNet,
}

impl PyCompiledNet {
    /// Compiles `net`, translating a structural rejection — CORE-043 among them — into
    /// `StructureError` rather than letting it unwind across the FFI boundary.
    pub fn from_petri_net(net: &PetriNet) -> PyResult<Self> {
        Ok(Self {
            inner: panic_to_py(|| OwnedPrecompiledNet::compile(net))?,
        })
    }
}

#[pymethods]
impl PyCompiledNet {
    /// Compiles `net` into the precompiled (flat-array) representation.
    #[new]
    fn new(net: &PyPetriNet) -> PyResult<Self> {
        Self::from_petri_net(net.net())
    }

    /// Name of the underlying net.
    #[getter]
    fn name(&self) -> String {
        self.inner.net().name().to_string()
    }

    /// Runs the net synchronously to completion.
    ///
    /// `initial` is a `{place_name_or_Place: iterable_of_token_values_or_snapshots}`
    /// dict. Two forms are accepted: legacy `[value, value, ...]` (timestamps
    /// reassigned to `now()`), or structured `[{"value": v, "created_at": ms},
    /// ...]` (timestamps preserved — used by `MarkingView.snapshot()` for
    /// timestamp-faithful restore).
    ///
    /// Returns `(marking, termination_reason)`: the final marking as a
    /// structured-snapshot dict `{place_name: [{"value": v, "created_at": ms},
    /// ...]}`, and why the run ended (EXEC-041 AC3) as one of `"quiescent"`,
    /// `"terminal"` (EXEC-042), `"closed"`, `"stopped"`. The Python
    /// `MarkingView` wrapper exposes the marking via `.snapshot()` and
    /// projects to the value-only form via `.to_dict()` / iteration, and
    /// carries the reason as `.termination_reason`. The GIL is released for
    /// the duration of the executor loop.
    #[pyo3(signature = (initial = None, options = None, event_store = None))]
    fn run_sync(
        &self,
        py: Python<'_>,
        initial: Option<&Bound<'_, PyAny>>,
        options: Option<&PyExecutorOptions>,
        event_store: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<(Py<PyDict>, String)> {
        let options = options.cloned().unwrap_or_default();
        let initial_marking = marking_from_python_at(py, initial, options.epoch_now())?;
        let clock_guard = claim_clock(&options)?;
        let plan = match prepare_run_store(py, event_store) {
            Ok(plan) => plan,
            Err(err) => {
                clock_guard.release();
                return Err(err);
            }
        };
        let owned = self.inner.clone();

        let outcome = py.detach(move || {
            // Marks a SteppedClock finished on every exit from this closure.
            let _clock_guard = clock_guard;
            let outcome = match plan.sink {
                RunSink::Noop => run_sync_with::<NoopEventStore>(&owned, initial_marking, &options, None),
                RunSink::Plain(store) => run_sync_with(&owned, initial_marking, &options, Some(store)),
                RunSink::Capture(store) => run_sync_with(&owned, initial_marking, &options, Some(store)),
            };
            // The executor dropped its store on return, which closed the
            // drainer's channel. Joined while detached: the drainer needs the
            // GIL to deliver what is still queued.
            if let Some(drainer) = plan.drainer {
                drainer.join();
            }
            outcome
        });

        Ok((
            marking_snapshot_to_python(py, &outcome.marking)?,
            outcome.termination_reason.as_str().to_string(),
        ))
    }

    /// Runs the net on tokio, returning an `(ExecutorHandle, awaitable)` pair.
    ///
    /// The handle lets you inject tokens into environment places mid-run; the
    /// awaitable resolves to `(marking, termination_reason)` when the run ends
    /// — the same pair `run_sync` returns — and the handle's
    /// `termination_reason` reports the reason from then on. When
    /// `event_store` is written in Python, every event has been passed to its
    /// `append` before the awaitable resolves.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (initial = None, options = None, event_store = None))]
    fn run_async<'py>(
        &self,
        py: Python<'py>,
        initial: Option<&Bound<'py, PyAny>>,
        options: Option<&PyExecutorOptions>,
        event_store: Option<&Bound<'py, PyAny>>,
    ) -> PyResult<(Py<PyExecutorHandle>, Py<PyAny>)> {
        let options = options.cloned().unwrap_or_default();
        let initial_marking = marking_from_python_at(py, initial, options.epoch_now())?;
        let owned = self.inner.clone();

        // Capture the running asyncio event loop so Python async callbacks
        // spawned onto tokio worker threads can drive themselves on it.
        // The guard is moved into the spawned future so the captured
        // locals are cleared at run-completion (allowing a subsequent
        // `run_async` on a different loop to install fresh). Installed
        // before the clock is claimed: a call with no running loop, or with
        // another run live on a different loop, starts no run and must not
        // use up a SteppedClock.
        let loop_guard = crate::action::install_event_loop_locals(py)?;
        let clock_guard = claim_clock(&options)?;
        let plan = match prepare_run_store(py, event_store) {
            Ok(plan) => plan,
            Err(err) => {
                clock_guard.release();
                return Err(err);
            }
        };
        let inject_clock = options.clock().map(HostClock::as_executor_clock);

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        let reason_cell: Arc<Mutex<Option<TerminationReason>>> = Arc::new(Mutex::new(None));
        let run_reason = Arc::clone(&reason_cell);
        let handle = match Py::new(
            py,
            PyExecutorHandle::new(
                libpetri::ExecutorHandle::new(tx),
                reason_cell,
                Arc::clone(&plan.error),
                inject_clock,
            ),
        ) {
            Ok(handle) => handle,
            Err(err) => {
                clock_guard.release();
                return Err(err);
            }
        };
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let _loop_guard = loop_guard;
            // Marks a SteppedClock finished when the run ends or this future
            // is dropped. Declared after the loop guard so it drops first.
            let clock_guard = clock_guard;
            let outcome = match plan.sink {
                RunSink::Noop => {
                    run_async_with::<NoopEventStore>(&owned, initial_marking, &options, None, rx).await
                }
                RunSink::Plain(store) => {
                    run_async_with(&owned, initial_marking, &options, Some(store), rx).await
                }
                RunSink::Capture(store) => {
                    run_async_with(&owned, initial_marking, &options, Some(store), rx).await
                }
            };
            // The executor and its store are gone, so the drainer's channel
            // is closed. Wait for it to hand the last events to Python, so a
            // caller that awaited the run sees them all in its store.
            if let Some(drainer) = plan.drainer {
                drainer.finished().await;
            }
            // [EXEC-041] AC3: published before the awaitable resolves, so a
            // caller that awaited it reads the final reason off the handle.
            *run_reason.lock().unwrap() = Some(outcome.termination_reason);
            // Released before the result is handed back, so a settle waiter
            // is free by the time the run's awaitable resolves.
            drop(clock_guard);
            Python::attach(|py| {
                Ok((
                    marking_snapshot_to_python(py, &outcome.marking)?,
                    outcome.termination_reason.as_str().to_string(),
                ))
            })
        })?;

        Ok((handle, awaitable.unbind()))
    }
}

/// Applies the run options to a builder. Shared by every store type and by
/// both run paths, so each option is wired once.
fn configure<E: EventStore>(
    mut builder: OwnedPrecompiledExecutorBuilder<E>,
    options: &PyExecutorOptions,
    store: Option<E>,
) -> OwnedPrecompiledExecutorBuilder<E> {
    builder = builder
        .environment_places(options.environment_place_set())
        .skip_output_validation(options.skip_output_validation);
    if let Some(ms) = options.deadline_tolerance_ms {
        builder = builder.deadline_tolerance_ms(ms);
    }
    if let Some(scope) = options.execution_scope() {
        builder = builder.execution_scope(Arc::<str>::from(scope));
    }
    // [TIME-015] The host clock. The executor reads time from it and stamps
    // the tokens it creates with its epoch.
    if let Some(clock) = options.clock() {
        builder = builder.clock(clock.as_executor_clock());
    }
    if let Some(store) = store {
        builder = builder.event_store(store);
    }
    builder
}

/// Claims the options' clock for this run (a `SteppedClock` is single-use).
fn claim_clock(options: &PyExecutorOptions) -> PyResult<crate::clock::RunClockGuard> {
    match options.clock() {
        Some(clock) => clock.claim(),
        None => Ok(crate::clock::RunClockGuard::none()),
    }
}

fn run_sync_with<E: EventStore>(
    owned: &OwnedPrecompiledNet,
    initial_marking: libpetri::Marking,
    options: &PyExecutorOptions,
    store: Option<E>,
) -> RunOutcome {
    configure(owned.builder::<E>(initial_marking), options, store).run_sync_outcome()
}

#[cfg(feature = "tokio")]
async fn run_async_with<E: EventStore>(
    owned: &OwnedPrecompiledNet,
    initial_marking: libpetri::Marking,
    options: &PyExecutorOptions,
    store: Option<E>,
    signal_rx: tokio::sync::mpsc::UnboundedReceiver<libpetri::ExecutorSignal>,
) -> RunOutcome {
    configure(owned.builder::<E>(initial_marking), options, store)
        .run_async_outcome(signal_rx)
        .await
}

/// Side-channel handle for an in-flight async executor.
///
/// Use `inject(place, value)` to push tokens into an environment place,
/// `drain()` to stop accepting new events, `close()` to abort, and the
/// `drained` getter to check whether the executor has stopped.
#[cfg(feature = "tokio")]
#[pyclass(module = "_libpetri", name = "ExecutorHandle")]
pub struct PyExecutorHandle {
    inner: Mutex<libpetri::ExecutorHandle>,
    /// Set by the run when it ends (EXEC-041 AC3); `None` while it runs.
    termination_reason: Arc<Mutex<Option<TerminationReason>>>,
    /// The first exception a Python event store's `append` raised.
    event_store_error: StoreErrorSlot,
    /// \[TIME-015\] The run's host clock; injected tokens are stamped from
    /// its epoch.
    clock: Option<Arc<dyn libpetri::ExecutorClock>>,
}

#[cfg(feature = "tokio")]
impl PyExecutorHandle {
    fn new(
        inner: libpetri::ExecutorHandle,
        termination_reason: Arc<Mutex<Option<TerminationReason>>>,
        event_store_error: StoreErrorSlot,
        clock: Option<Arc<dyn libpetri::ExecutorClock>>,
    ) -> Self {
        Self {
            inner: Mutex::new(inner),
            termination_reason,
            event_store_error,
            clock,
        }
    }

    /// Epoch milliseconds for an injected token: the run's clock if it has
    /// one, else wall time.
    fn epoch_now(&self) -> u64 {
        match &self.clock {
            Some(clock) => clock.epoch_ms(),
            None => libpetri::core::token::now_millis(),
        }
    }
}

#[cfg(feature = "tokio")]
#[pymethods]
impl PyExecutorHandle {
    /// Pushes `value` into an environment place. Returns `True` if accepted.
    fn inject(&self, place: &Bound<'_, PyAny>, value: Py<PyAny>) -> PyResult<bool> {
        let place_name = place_name_from_object(place)?;
        Ok(self
            .inner
            .lock()
            .unwrap()
            .inject(place_name, erased_from_py_at(value, self.epoch_now())))
    }

    /// Pushes each item of `values` into an environment place as one
    /// batched signal. Returns `True` if accepted. Crosses the FFI once
    /// for any number of tokens — drops the GIL crossing count from
    /// N to 1 vs. a Python-side loop of `inject()` calls.
    fn inject_many(
        &self,
        place: &Bound<'_, PyAny>,
        values: &Bound<'_, PyAny>,
    ) -> PyResult<bool> {
        let place_name = place_name_from_object(place)?;
        let created_at = self.epoch_now();
        let mut events: Vec<libpetri::runtime::environment::ExternalEvent> = Vec::new();
        if let Ok(size) = values.len() {
            events.reserve(size);
        }
        for item in values.try_iter()? {
            let value = item?.unbind();
            events.push(libpetri::runtime::environment::ExternalEvent {
                place_name: Arc::clone(&place_name),
                token: erased_from_py_at(value, created_at),
            });
        }
        Ok(self.inner.lock().unwrap().inject_many(events))
    }

    /// Signals the executor to stop waiting for new external events.
    fn drain(&self) -> bool {
        self.inner.lock().unwrap().drain()
    }

    /// Closes the side channel without draining (executor terminates).
    fn close(&self) -> bool {
        self.inner.lock().unwrap().close()
    }

    /// `True` once the executor has drained / closed.
    #[getter]
    fn drained(&self) -> bool {
        self.inner.lock().unwrap().is_drained()
    }

    /// Why the run ended (EXEC-041 AC3): `"running"` until it has, then
    /// `"quiescent"`, `"terminal"` (EXEC-042 — a terminal place was marked),
    /// `"closed"` or `"stopped"`.
    #[getter]
    fn termination_reason(&self) -> &'static str {
        self.termination_reason
            .lock()
            .unwrap()
            .unwrap_or(TerminationReason::Running)
            .as_str()
    }

    /// The first exception raised by the `append` of an event store written
    /// in Python, or `None`. Such an exception does not stop the run: it is
    /// logged to the `libpetri` logger and the remaining events are still
    /// delivered. Final once the run's awaitable has resolved.
    #[getter]
    fn event_store_error(&self, py: Python<'_>) -> Option<Py<PyAny>> {
        self.event_store_error
            .lock()
            .unwrap()
            .as_ref()
            .map(|err| err.clone_ref(py))
    }

    /// Requests a mid-execution marking snapshot. Returns an awaitable that
    /// resolves to `{"marking": {place: [{"value": v, "created_at": ms}, ...]},
    /// "action_in_flight": bool}` — the two read at one instant (\[ENV-014\]
    /// AC5/AC6). `"marking"` has the shape of `MarkingView.snapshot()`: places
    /// in ascending code-point order, empty places omitted.
    /// `"action_in_flight"` means work in flight: an action, or an accepted
    /// but un-injected external event — the latter cannot occur here, since
    /// injects and snapshot requests share one FIFO channel and an inject is
    /// applied on receipt. The `libpetri.ExecutorHandle` wrapper turns this
    /// into a `SnapshotResult`.
    ///
    /// Raises `RuntimeError` if the executor has already drained, closed, or
    /// disconnected.
    ///
    /// Legal from inside an action (\[ENV-014\] AC8). An `async def` action is
    /// driven from a Tokio worker with no running asyncio loop, so the
    /// awaitable is bound to the loop captured by `run_async` / `start_async`
    /// when the calling thread has none; the reply then reports the calling
    /// firing in flight. A **sync** action under `run_async` runs inline in the
    /// orchestrator loop: it may send the request, but blocking on the reply
    /// before returning waits on the orchestrator from the orchestrator.
    fn snapshot<'py>(&self, py: Python<'py>) -> PyResult<Py<PyAny>> {
        // Resolved before the request is sent, so a caller with no loop at
        // all fails without leaving an unanswerable request in the channel.
        let locals = match pyo3_async_runtimes::tokio::get_current_locals(py) {
            Ok(locals) => locals,
            Err(err) => crate::action::current_event_loop_locals().ok_or(err)?,
        };
        let rx = self
            .inner
            .lock()
            .unwrap()
            .snapshot()
            .map_err(|_| PyRuntimeError::new_err("executor handle is drained or closed"))?;
        let awaitable = pyo3_async_runtimes::tokio::future_into_py_with_locals(py, locals, async move {
            let result = rx.await.map_err(|_| {
                PyRuntimeError::new_err("executor dropped before snapshot was delivered")
            })?;
            // [ENV-014] AC5/AC6: the marking and whether anything was in
            // flight travel together, as one value read at one instant.
            // The Python wrapper builds a `SnapshotResult` from this.
            Python::attach(|py| {
                let out = pyo3::types::PyDict::new(py);
                out.set_item(
                    "marking",
                    crate::value::snapshot_form_to_python(py, &result.marking)?,
                )?;
                out.set_item("action_in_flight", result.action_in_flight)?;
                Ok::<_, pyo3::PyErr>(out.unbind())
            })
        })?;
        Ok(awaitable.unbind())
    }
}

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyExecutorOptions>()?;
    m.add_class::<PyCompiledNet>()?;
    #[cfg(feature = "tokio")]
    m.add_class::<PyExecutorHandle>()?;
    Ok(())
}
