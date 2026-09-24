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
use libpetri::{NoopEventStore, OwnedPrecompiledNet, PetriNet};
#[cfg(feature = "tokio")]
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict};

use crate::error::panic_to_py;
use crate::events::PyEventStoreHandle;
use crate::model::PyPetriNet;
#[cfg(feature = "tokio")]
use crate::value::{erased_from_py, place_name_from_object};
use crate::value::{marking_from_python, marking_snapshot_to_python};

/// Run-time options for a single execution.
///
/// `environment_places` keeps the executor alive while external tokens may
/// still arrive. `skip_output_validation` disables AND/XOR output-spec checks
/// for trusted callers.
#[pyclass(module = "_libpetri", name = "ExecutorOptions", from_py_object)]
#[derive(Clone, Default)]
pub struct PyExecutorOptions {
    environment_places: Vec<String>,
    skip_output_validation: bool,
    deadline_tolerance_ms: Option<f64>,
    execution_scope: Option<String>,
}

impl PyExecutorOptions {
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
    #[new]
    #[pyo3(signature = (*, environment_places = None, skip_output_validation = false, deadline_tolerance_ms = None, execution_scope = None))]
    fn new(
        environment_places: Option<Vec<String>>,
        skip_output_validation: bool,
        deadline_tolerance_ms: Option<f64>,
        execution_scope: Option<String>,
    ) -> PyResult<Self> {
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
        event_store: Option<&PyEventStoreHandle>,
    ) -> PyResult<(Py<PyDict>, String)> {
        let initial_marking = marking_from_python(py, initial)?;
        let options = options.cloned().unwrap_or_default();
        let environment_places = options.environment_place_set();
        let skip_output_validation = options.skip_output_validation;
        let deadline_tolerance_ms = options.deadline_tolerance_ms;
        let execution_scope = options.execution_scope().map(Arc::<str>::from);
        let owned = self.inner.clone();

        let outcome = py.detach(move || match event_store.map(|h| h.shared()) {
            None => {
                let mut builder = owned
                    .builder::<NoopEventStore>(initial_marking)
                    .environment_places(environment_places)
                    .skip_output_validation(skip_output_validation);
                if let Some(ms) = deadline_tolerance_ms {
                    builder = builder.deadline_tolerance_ms(ms);
                }
                if let Some(scope) = execution_scope.clone() {
                    builder = builder.execution_scope(scope);
                }
                builder.run_sync_outcome()
            }
            Some(shared) => {
                let mut builder = owned
                    .builder(initial_marking)
                    .event_store(shared)
                    .environment_places(environment_places)
                    .skip_output_validation(skip_output_validation);
                if let Some(ms) = deadline_tolerance_ms {
                    builder = builder.deadline_tolerance_ms(ms);
                }
                if let Some(scope) = execution_scope.clone() {
                    builder = builder.execution_scope(scope);
                }
                builder.run_sync_outcome()
            }
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
    /// `termination_reason` reports the reason from then on.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (initial = None, options = None, event_store = None))]
    fn run_async<'py>(
        &self,
        py: Python<'py>,
        initial: Option<&Bound<'py, PyAny>>,
        options: Option<&PyExecutorOptions>,
        event_store: Option<&PyEventStoreHandle>,
    ) -> PyResult<(Py<PyExecutorHandle>, Py<PyAny>)> {
        let initial_marking = marking_from_python(py, initial)?;
        let options = options.cloned().unwrap_or_default();
        let environment_places = options.environment_place_set();
        let skip_output_validation = options.skip_output_validation;
        let deadline_tolerance_ms = options.deadline_tolerance_ms;
        let execution_scope = options.execution_scope().map(Arc::<str>::from);
        let owned = self.inner.clone();
        let shared = event_store.map(|h| h.shared());

        // Capture the running asyncio event loop so Python async callbacks
        // spawned onto tokio worker threads can drive themselves on it.
        // The guard is moved into the spawned future so the captured
        // locals are cleared at run-completion (allowing a subsequent
        // `run_async` on a different loop to install fresh).
        let loop_guard = crate::action::install_event_loop_locals(py)?;

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        let reason_cell: Arc<Mutex<Option<TerminationReason>>> = Arc::new(Mutex::new(None));
        let run_reason = Arc::clone(&reason_cell);
        let handle = Py::new(
            py,
            PyExecutorHandle::new(libpetri::ExecutorHandle::new(tx), reason_cell),
        )?;
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let _loop_guard = loop_guard;
            let outcome = match shared {
                None => {
                    let mut builder = owned
                        .builder::<NoopEventStore>(initial_marking)
                        .environment_places(environment_places)
                        .skip_output_validation(skip_output_validation);
                    if let Some(ms) = deadline_tolerance_ms {
                        builder = builder.deadline_tolerance_ms(ms);
                    }
                    if let Some(scope) = execution_scope.clone() {
                        builder = builder.execution_scope(scope);
                    }
                    builder.run_async_outcome(rx).await
                }
                Some(shared) => {
                    let mut builder = owned
                        .builder(initial_marking)
                        .event_store(shared)
                        .environment_places(environment_places)
                        .skip_output_validation(skip_output_validation);
                    if let Some(ms) = deadline_tolerance_ms {
                        builder = builder.deadline_tolerance_ms(ms);
                    }
                    if let Some(scope) = execution_scope.clone() {
                        builder = builder.execution_scope(scope);
                    }
                    builder.run_async_outcome(rx).await
                }
            };
            // [EXEC-041] AC3: published before the awaitable resolves, so a
            // caller that awaited it reads the final reason off the handle.
            *run_reason.lock().unwrap() = Some(outcome.termination_reason);
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
}

#[cfg(feature = "tokio")]
impl PyExecutorHandle {
    fn new(
        inner: libpetri::ExecutorHandle,
        termination_reason: Arc<Mutex<Option<TerminationReason>>>,
    ) -> Self {
        Self {
            inner: Mutex::new(inner),
            termination_reason,
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
            .inject(place_name, erased_from_py(value)))
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
        let mut events: Vec<libpetri::runtime::environment::ExternalEvent> = Vec::new();
        if let Ok(size) = values.len() {
            events.reserve(size);
        }
        for item in values.try_iter()? {
            let value = item?.unbind();
            events.push(libpetri::runtime::environment::ExternalEvent {
                place_name: Arc::clone(&place_name),
                token: erased_from_py(value),
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
