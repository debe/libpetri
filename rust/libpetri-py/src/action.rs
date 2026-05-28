//! Python sync / async callback adapters for libpetri transitions.
//!
//! [`PyCallbackAction`] implements [`TransitionAction`] over a stored
//! `Py<PyAny>` callable. The Python-facing [`PyActionContext`] surfaces the
//! consumed inputs, read tokens, and a buffered output collector that flushes
//! into the underlying Rust [`TransitionContext`] after the callback returns.

use std::collections::{HashMap, HashSet};
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
#[cfg(feature = "tokio")]
use std::sync::Mutex;

use libpetri::BoxedAction;
use libpetri::core::action::{ActionError, TransitionAction};
use libpetri::core::context::TransitionContext;
#[cfg(feature = "tokio")]
use pyo3::exceptions::PyStopIteration;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
#[cfg(feature = "tokio")]
use pyo3_async_runtimes::TaskLocals;
use pyo3::types::PyAny;

use crate::error::action_error;
use crate::value::PyTokenValue;

#[cfg(feature = "tokio")]
static EVENT_LOOP_LOCALS: Mutex<Option<TaskLocals>> = Mutex::new(None);

/// Captures the current asyncio event loop and stores it globally so Python
/// async callbacks invoked from tokio worker threads can drive themselves on
/// it. Called once at the top of each [`crate::executor::PyCompiledNet::run_async`].
#[cfg(feature = "tokio")]
pub fn install_event_loop_locals(py: Python<'_>) -> PyResult<()> {
    let locals = pyo3_async_runtimes::tokio::get_current_locals(py)?;
    *EVENT_LOOP_LOCALS.lock().unwrap() = Some(locals);
    Ok(())
}

#[cfg(feature = "tokio")]
fn current_event_loop_locals() -> Option<TaskLocals> {
    EVENT_LOOP_LOCALS.lock().unwrap().clone()
}

/// The context object passed to every Python transition callback.
///
/// Use `input(place)` / `inputs(place)` to read consumed tokens, `read(place)`
/// / `reads(place)` for read-arc tokens, and `output(place, value)` /
/// `output_many(place, values)` to emit tokens onto declared output places.
/// The transition's declared output places are the only ones writable.
#[pyclass(module = "_libpetri", name = "TransitionContext")]
pub struct PyActionContext {
    transition_name: Arc<str>,
    inputs: HashMap<Arc<str>, Vec<Py<PyAny>>>,
    reads: HashMap<Arc<str>, Vec<Py<PyAny>>>,
    allowed_outputs: HashSet<Arc<str>>,
    outputs: Vec<(Arc<str>, Py<PyAny>)>,
}

#[pymethods]
impl PyActionContext {
    /// Name of the firing transition.
    #[getter]
    fn transition_name(&self) -> String {
        self.transition_name.as_ref().to_owned()
    }

    /// Returns the single consumed token from `place_name`. Raises if the
    /// place had zero or more than one token (use `inputs` for the multi case).
    fn input(&self, py: Python<'_>, place_name: &str) -> PyResult<Py<PyAny>> {
        let values = self.inputs.get(place_name).ok_or_else(|| {
            PyValueError::new_err(format!("unknown input place: {place_name}"))
        })?;
        if values.len() != 1 {
            return Err(PyValueError::new_err(format!(
                "place '{place_name}' has {} consumed tokens; use inputs()",
                values.len()
            )));
        }
        Ok(values[0].clone_ref(py))
    }

    /// Returns all tokens consumed from `place_name`.
    fn inputs(&self, py: Python<'_>, place_name: &str) -> PyResult<Vec<Py<PyAny>>> {
        let values = self.inputs.get(place_name).ok_or_else(|| {
            PyValueError::new_err(format!("unknown input place: {place_name}"))
        })?;
        Ok(values.iter().map(|v| v.clone_ref(py)).collect())
    }

    /// Returns the first token tested by a read arc on `place_name`.
    fn read(&self, py: Python<'_>, place_name: &str) -> PyResult<Py<PyAny>> {
        let values = self
            .reads
            .get(place_name)
            .ok_or_else(|| PyValueError::new_err(format!("unknown read place: {place_name}")))?;
        if values.is_empty() {
            return Err(PyValueError::new_err(format!(
                "read place '{place_name}' is empty"
            )));
        }
        Ok(values[0].clone_ref(py))
    }

    /// Returns all tokens tested by a read arc on `place_name`.
    fn reads(&self, py: Python<'_>, place_name: &str) -> PyResult<Vec<Py<PyAny>>> {
        let values = self
            .reads
            .get(place_name)
            .ok_or_else(|| PyValueError::new_err(format!("unknown read place: {place_name}")))?;
        Ok(values.iter().map(|v| v.clone_ref(py)).collect())
    }

    /// Buffers a token to emit onto `place_name` once the callback returns.
    /// Raises if the transition does not declare `place_name` as an output.
    fn output(&mut self, place_name: &str, value: Py<PyAny>) -> PyResult<()> {
        let place_name = self.require_output(place_name)?;
        self.outputs.push((place_name, value));
        Ok(())
    }

    /// Buffers each item of `values` onto `place_name`.
    fn output_many(&mut self, place_name: &str, values: &Bound<'_, PyAny>) -> PyResult<()> {
        let place_name = self.require_output(place_name)?;
        for item in values.try_iter()? {
            self.outputs.push((Arc::clone(&place_name), item?.unbind()));
        }
        Ok(())
    }
}

impl PyActionContext {
    fn require_output(&self, place_name: &str) -> PyResult<Arc<str>> {
        self.allowed_outputs
            .get(place_name)
            .cloned()
            .ok_or_else(|| PyValueError::new_err(format!("unknown output place: {place_name}")))
    }

    fn from_transition_context(py: Python<'_>, ctx: &TransitionContext) -> PyResult<Self> {
        let input_names = ctx.input_place_names();
        let mut inputs = HashMap::with_capacity(input_names.len());
        for place_name in input_names {
            let values = ctx
                .input_tokens_raw(place_name.as_ref())
                .map_err(action_error)?;
            let values = values
                .into_iter()
                .map(|value| {
                    value
                        .downcast_ref::<PyTokenValue>()
                        .map(|wrapped| wrapped.clone_ref(py))
                        .ok_or_else(|| PyRuntimeError::new_err("input token is not python.object"))
                })
                .collect::<PyResult<Vec<_>>>()?;
            inputs.insert(place_name, values);
        }

        let read_names = ctx.read_place_names();
        let mut reads = HashMap::with_capacity(read_names.len());
        for place_name in read_names {
            let values = ctx
                .read_tokens_raw(place_name.as_ref())
                .map_err(action_error)?;
            let values = values
                .into_iter()
                .map(|value| {
                    value
                        .downcast_ref::<PyTokenValue>()
                        .map(|wrapped| wrapped.clone_ref(py))
                        .ok_or_else(|| PyRuntimeError::new_err("read token is not python.object"))
                })
                .collect::<PyResult<Vec<_>>>()?;
            reads.insert(place_name, values);
        }

        Ok(Self {
            transition_name: Arc::<str>::from(ctx.transition_name()),
            inputs,
            reads,
            allowed_outputs: ctx.output_place_names().into_iter().collect(),
            outputs: Vec::new(),
        })
    }

    fn take_outputs(&mut self) -> Vec<(Arc<str>, Py<PyAny>)> {
        std::mem::take(&mut self.outputs)
    }
}

enum PythonActionMode {
    Sync,
    Async,
}

struct PyCallbackAction {
    callback: Py<PyAny>,
    mode: PythonActionMode,
}

pub fn boxed_sync_action(callback: Py<PyAny>) -> BoxedAction {
    Arc::new(PyCallbackAction {
        callback,
        mode: PythonActionMode::Sync,
    })
}

pub fn boxed_async_action(callback: Py<PyAny>) -> BoxedAction {
    Arc::new(PyCallbackAction {
        callback,
        mode: PythonActionMode::Async,
    })
}

impl TransitionAction for PyCallbackAction {
    fn is_sync(&self) -> bool {
        matches!(self.mode, PythonActionMode::Sync)
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        Python::attach(|py| -> PyResult<()> {
            let py_ctx = Py::new(py, PyActionContext::from_transition_context(py, ctx)?)?;
            self.callback.bind(py).call1((py_ctx.clone_ref(py),))?;
            flush_outputs(py, &py_ctx, ctx)
        })
        .map_err(|err| ActionError::new(err.to_string()))
    }

    #[cfg(feature = "tokio")]
    fn run_async<'a>(
        &'a self,
        mut ctx: TransitionContext,
    ) -> Pin<Box<dyn Future<Output = Result<TransitionContext, ActionError>> + Send + 'a>> {
        Box::pin(async move {
            match self.mode {
                PythonActionMode::Sync => {
                    self.run_sync(&mut ctx)?;
                    Ok(ctx)
                }
                PythonActionMode::Async => {
                    let locals = current_event_loop_locals().ok_or_else(|| {
                        ActionError::new(
                            "no asyncio event loop captured; call libpetri.run_async \
                             from within an asyncio loop",
                        )
                    })?;

                    // Drive the coroutine manually. send(None) once: if the
                    // coroutine completes without yielding (the common case for
                    // `async def f(ctx): ctx.output(...)`), we skip asyncio
                    // entirely AND flush outputs in the same GIL acquisition.
                    // If it yields, we resolve each yielded awaitable through
                    // pyo3-async-runtimes and feed the result back via send —
                    // same semantics as asyncio Task, just without the Task
                    // wrapping overhead.
                    let (py_ctx, coroutine, mut current) = Python::attach(
                        |py| -> PyResult<(Py<PyActionContext>, Py<PyAny>, DriveStep)> {
                            let py_ctx = Py::new(
                                py,
                                PyActionContext::from_transition_context(py, &ctx)?,
                            )?;
                            let coroutine =
                                self.callback.bind(py).call1((py_ctx.clone_ref(py),))?;
                            let none = py.None();
                            let outcome = drive_coro_step(py, &coroutine, none.bind(py))?;
                            if matches!(outcome, DriveStep::Done) {
                                // Fast-path flush: never released the GIL, so
                                // do the whole transition in one attach block.
                                flush_outputs(py, &py_ctx, &mut ctx)?;
                            }
                            Ok((py_ctx, coroutine.unbind(), outcome))
                        },
                    )
                    .map_err(|err: PyErr| ActionError::new(err.to_string()))?;

                    if matches!(current, DriveStep::Done) {
                        return Ok(ctx);
                    }

                    while let DriveStep::Pending(yielded) = current {
                        let next_action =
                            Python::attach(|py| -> PyResult<NextAction> {
                                let yielded_bound = yielded.bind(py);
                                if yielded_bound.is_none() {
                                    // Coroutine yielded None — asyncio-style
                                    // scheduler tick. Just re-send None; no
                                    // real I/O to wait for.
                                    let step = drive_coro_step(
                                        py,
                                        coroutine.bind(py),
                                        py.None().bind(py),
                                    )?;
                                    Ok(NextAction::Continue(step))
                                } else {
                                    let fut = pyo3_async_runtimes::into_future_with_locals(
                                        &locals,
                                        yielded_bound.clone(),
                                    )?;
                                    Ok(NextAction::Await(Box::pin(fut)))
                                }
                            })
                            .map_err(|err: PyErr| ActionError::new(err.to_string()))?;

                        match next_action {
                            NextAction::Continue(step) => current = step,
                            NextAction::Await(fut) => {
                                let result = fut.await.map_err(|err: PyErr| {
                                    ActionError::new(err.to_string())
                                })?;
                                current = Python::attach(|py| -> PyResult<DriveStep> {
                                    drive_coro_step(
                                        py,
                                        coroutine.bind(py),
                                        result.bind(py),
                                    )
                                })
                                .map_err(|err: PyErr| {
                                    ActionError::new(err.to_string())
                                })?;
                            }
                        }
                    }

                    Python::attach(|py| flush_outputs(py, &py_ctx, &mut ctx))
                        .map_err(|err| ActionError::new(err.to_string()))?;
                    Ok(ctx)
                }
            }
        })
    }

    #[cfg(not(feature = "tokio"))]
    fn run_async<'a>(
        &'a self,
        mut ctx: TransitionContext,
    ) -> Pin<Box<dyn Future<Output = Result<TransitionContext, ActionError>> + Send + 'a>> {
        Box::pin(async move {
            self.run_sync(&mut ctx)?;
            Ok(ctx)
        })
    }
}

#[cfg(feature = "tokio")]
enum DriveStep {
    Done,
    Pending(Py<PyAny>),
}

#[cfg(feature = "tokio")]
enum NextAction {
    Continue(DriveStep),
    Await(Pin<Box<dyn Future<Output = PyResult<Py<PyAny>>> + Send>>),
}

#[cfg(feature = "tokio")]
fn drive_coro_step<'py>(
    py: Python<'py>,
    coroutine: &Bound<'py, PyAny>,
    send_value: &Bound<'py, PyAny>,
) -> PyResult<DriveStep> {
    match coroutine.call_method1("send", (send_value,)) {
        Err(err) if err.is_instance_of::<PyStopIteration>(py) => Ok(DriveStep::Done),
        Ok(yielded) => Ok(DriveStep::Pending(yielded.unbind())),
        Err(err) => Err(err),
    }
}

fn flush_outputs(
    py: Python<'_>,
    py_ctx: &Py<PyActionContext>,
    rust_ctx: &mut TransitionContext,
) -> PyResult<()> {
    let mut py_ctx_borrow = py_ctx.bind(py).borrow_mut();
    for (place_name, value) in py_ctx_borrow.take_outputs() {
        rust_ctx
            .output_raw(
                place_name.as_ref(),
                Arc::new(PyTokenValue::new(value)) as Arc<dyn std::any::Any + Send + Sync>,
            )
            .map_err(action_error)?;
    }
    Ok(())
}

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyActionContext>()?;
    Ok(())
}
