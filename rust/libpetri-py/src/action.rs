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
use libpetri::core::context::{FlushFn, FreshNameFn, OutputEntry, TransitionContext};
use libpetri::core::token::ErasedToken;
#[cfg(feature = "tokio")]
use pyo3::exceptions::PyStopIteration;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;
#[cfg(feature = "tokio")]
use pyo3_async_runtimes::TaskLocals;
use pyo3::types::PyAny;

use crate::error::action_error;
use crate::value::PyTokenValue;

/// Tracks the asyncio event loop captured by an in-flight `run_async`.
///
/// The `locals` are reused by every async transition action firing during
/// that run so Python coroutines can be driven on the correct loop from a
/// tokio worker thread. `loop_ptr` is the `PyObject*` of the loop, stored
/// as an opaque `usize` identity — never dereferenced — so a second
/// `run_async` on a **different** loop is detected and rejected instead of
/// silently clobbering the first run's locals.
///
/// A `usize`-typed pointer is used (rather than the live `*mut` pointer)
/// so the struct stays `Send` without an `unsafe impl`.
#[cfg(feature = "tokio")]
struct EventLoopState {
    locals: Option<TaskLocals>,
    loop_id: usize,
    in_flight: usize,
}

#[cfg(feature = "tokio")]
static EVENT_LOOP_LOCALS: Mutex<EventLoopState> = Mutex::new(EventLoopState {
    locals: None,
    loop_id: 0,
    in_flight: 0,
});

/// RAII guard returned by [`install_event_loop_locals`]; decrements the
/// in-flight counter on drop and clears the captured locals when the count
/// hits zero so a subsequent `run_async` on a different loop installs fresh
/// state instead of inheriting a stale one.
#[cfg(feature = "tokio")]
pub struct EventLoopGuard;

#[cfg(feature = "tokio")]
impl Drop for EventLoopGuard {
    fn drop(&mut self) {
        let mut state = EVENT_LOOP_LOCALS.lock().unwrap();
        state.in_flight = state.in_flight.saturating_sub(1);
        if state.in_flight == 0 {
            state.locals = None;
            state.loop_id = 0;
        }
    }
}

/// Captures the current asyncio event loop. Called once at the top of each
/// [`crate::executor::PyCompiledNet::run_async`]; the returned guard must
/// outlive the run (move it into the spawned future).
///
/// Two concurrent `run_async` calls on the **same** asyncio loop share the
/// captured locals — they're identical. A second call on a **different**
/// loop while the first is still in flight returns
/// `RuntimeError`: the global slot can only hold one loop at a time, and
/// silently overwriting it would route the first run's action helpers
/// (`action_gather`, `action_to_thread`, `captured_event_loop`) to the
/// wrong loop. Sequential calls on different loops are fine because the
/// guard drop clears the slot at quiescence.
#[cfg(feature = "tokio")]
pub fn install_event_loop_locals(py: Python<'_>) -> PyResult<EventLoopGuard> {
    let new_locals = pyo3_async_runtimes::tokio::get_current_locals(py)?;
    let new_loop_id = new_locals.event_loop(py).as_ptr() as usize;

    let mut state = EVENT_LOOP_LOCALS.lock().unwrap();
    if state.in_flight > 0 && state.loop_id != new_loop_id {
        return Err(PyRuntimeError::new_err(
            "another libpetri executor is already running on a different \
             asyncio event loop in this process; concurrent multi-loop \
             usage is not supported in libpetri-py 2.8.x. Call run_async / \
             start_async sequentially, share the loop across runs, or run \
             each executor in its own process",
        ));
    }
    state.locals = Some(new_locals);
    state.loop_id = new_loop_id;
    state.in_flight += 1;
    Ok(EventLoopGuard)
}

#[cfg(feature = "tokio")]
fn current_event_loop_locals() -> Option<TaskLocals> {
    EVENT_LOOP_LOCALS.lock().unwrap().locals.clone()
}

/// Returns the asyncio event loop captured by the most recent
/// `run_async` / `start_async` call. The `lp.action_gather` /
/// `lp.action_to_thread` helpers use this loop to schedule coroutines off
/// the tokio worker thread, where synchronous asyncio APIs would fail.
/// Raises `RuntimeError` if no `run_async`/`start_async` is in flight.
#[cfg(feature = "tokio")]
#[pyfunction]
fn captured_event_loop(py: Python<'_>) -> PyResult<Py<PyAny>> {
    let locals = current_event_loop_locals().ok_or_else(|| {
        PyRuntimeError::new_err(
            "no asyncio event loop captured; call libpetri.run_async or \
             libpetri.start_async from within an asyncio loop first",
        )
    })?;
    Ok(locals.event_loop(py).unbind())
}

#[cfg(not(feature = "tokio"))]
#[pyfunction]
fn captured_event_loop(_py: Python<'_>) -> PyResult<Py<PyAny>> {
    Err(PyRuntimeError::new_err(
        "libpetri was built without the tokio feature; no asyncio event loop \
         is captured",
    ))
}

/// The context object passed to every Python transition callback.
///
/// Use `input(place)` / `inputs(place)` to read consumed tokens, `read(place)`
/// / `reads(place)` for read-arc tokens, and `output(place, value)` /
/// `output_many(place, values)` to emit tokens onto declared output places.
/// The transition's declared output places are the only ones writable.
/// Process-global fallback counter for [`PyActionContext::fresh_name`] when no
/// executor-installed minter is present. Guarantees uniqueness; under the
/// executor the installed minter is always used (deterministic per run).
static GLOBAL_PY_FRESH_NAME_COUNTER: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
use std::sync::atomic::Ordering as AtomicOrdering;

#[pyclass(module = "_libpetri", name = "TransitionContext")]
pub struct PyActionContext {
    transition_name: Arc<str>,
    inputs: HashMap<Arc<str>, Vec<Py<PyAny>>>,
    reads: HashMap<Arc<str>, Vec<Py<PyAny>>>,
    allowed_outputs: HashSet<Arc<str>>,
    outputs: Vec<(Arc<str>, Py<PyAny>)>,
    /// Mid-action flush callback set by the async executor. `None` for
    /// sync execution paths; `ctx.flush()` raises in that case.
    flush_fn: Option<FlushFn>,
    /// ν-name minter installed by the executor (NU-010). Captured from the
    /// Rust context so `ctx.fresh_name()` mints through the same monotonic
    /// source.
    fresh_name_fn: Option<FreshNameFn>,
    /// Author-local → composed-name map inherited from the
    /// transition's `local_name_map`. Lookups try the literal name
    /// first, then fall back through this map. `None` when the
    /// transition was not composed.
    local_name_map: Option<Arc<HashMap<Arc<str>, Arc<str>>>>,
}

#[pymethods]
impl PyActionContext {
    /// Name of the firing transition.
    #[getter]
    fn transition_name(&self) -> String {
        self.transition_name.as_ref().to_owned()
    }

    /// Mints a fresh ν-name (the ν-binder primitive — spec NU-010), returned as
    /// a `str`. An action calls this on the fork side to create a correlation
    /// id, then writes it into the sibling output payloads; a later join
    /// correlates those siblings via a `match_spec`.
    fn fresh_name(&self) -> String {
        match &self.fresh_name_fn {
            Some(f) => f().as_str().to_owned(),
            None => {
                let n = GLOBAL_PY_FRESH_NAME_COUNTER.fetch_add(1, AtomicOrdering::Relaxed);
                format!("{}#{}", self.transition_name, n)
            }
        }
    }

    /// Returns the single consumed token from `place_name`. Raises if the
    /// place had zero or more than one token (use `inputs` for the multi case).
    fn input(&self, py: Python<'_>, place_name: &str) -> PyResult<Py<PyAny>> {
        let key = self.resolve_lookup_key(&self.inputs, place_name, "input")?;
        let values = &self.inputs[key.as_ref()];
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
        let key = self.resolve_lookup_key(&self.inputs, place_name, "input")?;
        let values = &self.inputs[key.as_ref()];
        Ok(values.iter().map(|v| v.clone_ref(py)).collect())
    }

    /// Returns the first token tested by a read arc on `place_name`.
    fn read(&self, py: Python<'_>, place_name: &str) -> PyResult<Py<PyAny>> {
        let key = self.resolve_lookup_key(&self.reads, place_name, "read")?;
        let values = &self.reads[key.as_ref()];
        if values.is_empty() {
            return Err(PyValueError::new_err(format!(
                "read place '{place_name}' is empty"
            )));
        }
        Ok(values[0].clone_ref(py))
    }

    /// Returns all tokens tested by a read arc on `place_name`.
    fn reads(&self, py: Python<'_>, place_name: &str) -> PyResult<Vec<Py<PyAny>>> {
        let key = self.resolve_lookup_key(&self.reads, place_name, "read")?;
        let values = &self.reads[key.as_ref()];
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

    /// Publishes the currently-buffered outputs immediately, before the
    /// action returns. Each call is its own published event boundary:
    /// already-flushed tokens remain in the marking even if the action
    /// later raises. Use to stream tokens (e.g. LLM chunks) from a
    /// long-running async action.
    ///
    /// Raises ``RuntimeError`` when called from a sync execution path
    /// (``run_sync``) — flush requires the async loop's signal channel.
    fn flush(&mut self) -> PyResult<()> {
        let cb = self.flush_fn.as_ref().ok_or_else(|| {
            PyRuntimeError::new_err(
                "ctx.flush() is only available under async execution \
                 (use libpetri.run_async or libpetri.start_async)",
            )
        })?;
        if self.outputs.is_empty() {
            return Ok(());
        }
        let outputs = std::mem::take(&mut self.outputs);
        let created_at = libpetri::core::token::now_millis();
        let entries: Vec<OutputEntry> = outputs
            .into_iter()
            .map(|(place_name, value)| OutputEntry {
                place_name,
                token: ErasedToken {
                    value: Arc::new(PyTokenValue::new(value))
                        as Arc<dyn std::any::Any + Send + Sync>,
                    created_at,
                    value_type_name: "py.object",
                },
            })
            .collect();
        cb(entries);
        Ok(())
    }
}

impl PyActionContext {
    fn require_output(&self, place_name: &str) -> PyResult<Arc<str>> {
        if let Some(name) = self.allowed_outputs.get(place_name) {
            return Ok(Arc::clone(name));
        }
        // Fall back through the local→composed name map: the user
        // wrote a SubnetDef-local name and after composition the actual
        // host place is what's in `allowed_outputs`.
        if let Some(map) = &self.local_name_map {
            if let Some(host) = map.get(place_name) {
                if let Some(name) = self.allowed_outputs.get(host.as_ref()) {
                    return Ok(Arc::clone(name));
                }
            }
        }
        Err(PyValueError::new_err(format!(
            "unknown output place: {place_name}"
        )))
    }

    /// Resolves a place name against an inputs / reads map, falling back
    /// through `local_name_map` for composed transitions. Returns the
    /// key to use against the underlying map.
    fn resolve_lookup_key(
        &self,
        map: &HashMap<Arc<str>, Vec<Py<PyAny>>>,
        place_name: &str,
        kind: &str,
    ) -> PyResult<Arc<str>> {
        if let Some((k, _)) = map.get_key_value(place_name) {
            return Ok(Arc::clone(k));
        }
        if let Some(local_map) = &self.local_name_map {
            if let Some(host) = local_map.get(place_name) {
                if let Some((k, _)) = map.get_key_value(host.as_ref()) {
                    return Ok(Arc::clone(k));
                }
            }
        }
        Err(PyValueError::new_err(format!(
            "unknown {kind} place: {place_name}"
        )))
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
            flush_fn: ctx.flush_fn(),
            fresh_name_fn: ctx.fresh_name_fn(),
            local_name_map: ctx.local_name_map(),
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
                                    // scheduler tick. Cooperatively yield to
                                    // tokio so the executor's main loop can
                                    // process flushes / signals before we
                                    // resume the action.
                                    Ok(NextAction::YieldToTokio)
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
                            NextAction::YieldToTokio => {
                                tokio::task::yield_now().await;
                                current = Python::attach(|py| -> PyResult<DriveStep> {
                                    drive_coro_step(
                                        py,
                                        coroutine.bind(py),
                                        py.None().bind(py),
                                    )
                                })
                                .map_err(|err: PyErr| {
                                    ActionError::new(err.to_string())
                                })?;
                            }
                            NextAction::Await(fut) => {
                                // If the awaited future errors, throw the
                                // exception into the coroutine so a Python
                                // try/except inside the action can catch it
                                // (asyncio.Task semantics). Only if the
                                // coroutine itself doesn't catch does this
                                // propagate as an ActionError.
                                let fut_result = fut.await;
                                current = Python::attach(|py| -> PyResult<DriveStep> {
                                    match fut_result {
                                        Ok(result) => drive_coro_step(
                                            py,
                                            coroutine.bind(py),
                                            result.bind(py),
                                        ),
                                        Err(err) => drive_coro_throw(
                                            py,
                                            coroutine.bind(py),
                                            err,
                                        ),
                                    }
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
    Await(Pin<Box<dyn Future<Output = PyResult<Py<PyAny>>> + Send>>),
    /// Coroutine yielded `None` — the asyncio "scheduler tick". We
    /// cooperatively yield to tokio so the executor's main loop can
    /// process flushes, completions, and signals from other tasks
    /// before resuming the action. Makes `await asyncio.sleep(0)` a
    /// real yield from the action's perspective.
    YieldToTokio,
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

/// Throws `err` into the running `coroutine` via `coro.throw(exc)`. If the
/// coroutine catches the exception with try/except, returns its next yielded
/// awaitable. If it re-raises (or doesn't catch), propagates that error so
/// the executor can record it as `TransitionFailed`.
#[cfg(feature = "tokio")]
fn drive_coro_throw<'py>(
    py: Python<'py>,
    coroutine: &Bound<'py, PyAny>,
    err: PyErr,
) -> PyResult<DriveStep> {
    let exc = err.value(py).clone();
    match coroutine.call_method1("throw", (exc,)) {
        Err(thrown) if thrown.is_instance_of::<PyStopIteration>(py) => Ok(DriveStep::Done),
        Ok(yielded) => Ok(DriveStep::Pending(yielded.unbind())),
        Err(thrown) => Err(thrown),
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
    m.add_function(wrap_pyfunction!(captured_event_loop, m)?)?;
    Ok(())
}
