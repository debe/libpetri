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

use libpetri::{NoopEventStore, OwnedPrecompiledNet, PetriNet};
#[cfg(feature = "tokio")]
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict};

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
}

impl PyExecutorOptions {
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
    #[new]
    #[pyo3(signature = (*, environment_places = None, skip_output_validation = false))]
    fn new(environment_places: Option<Vec<String>>, skip_output_validation: bool) -> Self {
        Self {
            environment_places: environment_places.unwrap_or_default(),
            skip_output_validation,
        }
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
    pub fn from_petri_net(net: &PetriNet) -> Self {
        Self {
            inner: OwnedPrecompiledNet::compile(net),
        }
    }
}

#[pymethods]
impl PyCompiledNet {
    /// Compiles `net` into the precompiled (flat-array) representation.
    #[new]
    fn new(net: &PyPetriNet) -> Self {
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
    /// Returns the final marking as a structured-snapshot dict
    /// `{place_name: [{"value": v, "created_at": ms}, ...]}`. The Python
    /// `MarkingView` wrapper exposes this via `.snapshot()` and projects to
    /// the value-only form via `.to_dict()` / iteration. The GIL is released
    /// for the duration of the executor loop.
    #[pyo3(signature = (initial = None, options = None, event_store = None))]
    fn run_sync(
        &self,
        py: Python<'_>,
        initial: Option<&Bound<'_, PyAny>>,
        options: Option<&PyExecutorOptions>,
        event_store: Option<&PyEventStoreHandle>,
    ) -> PyResult<Py<PyDict>> {
        let initial_marking = marking_from_python(py, initial)?;
        let options = options.cloned().unwrap_or_default();
        let environment_places = options.environment_place_set();
        let skip_output_validation = options.skip_output_validation;
        let owned = self.inner.clone();

        let marking = py.detach(move || match event_store.map(|h| h.shared()) {
            None => owned
                .builder::<NoopEventStore>(initial_marking)
                .environment_places(environment_places)
                .skip_output_validation(skip_output_validation)
                .run_sync(),
            Some(shared) => owned
                .builder(initial_marking)
                .event_store(shared)
                .environment_places(environment_places)
                .skip_output_validation(skip_output_validation)
                .run_sync(),
        });

        marking_snapshot_to_python(py, &marking)
    }

    /// Runs the net on tokio, returning an `(ExecutorHandle, awaitable)` pair.
    ///
    /// The handle lets you inject tokens into environment places mid-run; the
    /// awaitable resolves to the final marking when the executor drains.
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
        let owned = self.inner.clone();
        let shared = event_store.map(|h| h.shared());

        // Capture the running asyncio event loop so Python async callbacks
        // spawned onto tokio worker threads can drive themselves on it.
        crate::action::install_event_loop_locals(py)?;

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        let handle = Py::new(
            py,
            PyExecutorHandle::new(libpetri::ExecutorHandle::new(tx)),
        )?;
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let marking = match shared {
                None => {
                    owned
                        .builder::<NoopEventStore>(initial_marking)
                        .environment_places(environment_places)
                        .skip_output_validation(skip_output_validation)
                        .run_async(rx)
                        .await
                }
                Some(shared) => {
                    owned
                        .builder(initial_marking)
                        .event_store(shared)
                        .environment_places(environment_places)
                        .skip_output_validation(skip_output_validation)
                        .run_async(rx)
                        .await
                }
            };
            Python::attach(|py| marking_snapshot_to_python(py, &marking))
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
}

#[cfg(feature = "tokio")]
impl PyExecutorHandle {
    fn new(inner: libpetri::ExecutorHandle) -> Self {
        Self {
            inner: Mutex::new(inner),
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

    /// Requests a mid-execution marking snapshot. Returns an awaitable that
    /// resolves to a structured snapshot dict
    /// (`{place: [{"value": v, "created_at": ms}, ...]}`) — same shape as
    /// `MarkingView.snapshot()`. Wrap with `MarkingView.from_snapshot(...)`
    /// for a typed view.
    ///
    /// Raises `RuntimeError` if the executor has already drained, closed, or
    /// disconnected.
    fn snapshot<'py>(&self, py: Python<'py>) -> PyResult<Py<PyAny>> {
        let rx = self
            .inner
            .lock()
            .unwrap()
            .snapshot()
            .map_err(|_| PyRuntimeError::new_err("executor handle is drained or closed"))?;
        let awaitable = pyo3_async_runtimes::tokio::future_into_py(py, async move {
            let marking = rx.await.map_err(|_| {
                PyRuntimeError::new_err("executor dropped before snapshot was delivered")
            })?;
            Python::attach(|py| marking_snapshot_to_python(py, &marking))
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
