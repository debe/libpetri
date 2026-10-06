//! \[TIME-015\] Host clocks for Python.
//!
//! Python hosts cannot implement a clock: the executor reads its clock every
//! cycle, and a Python clock would take the GIL each time. The two Rust
//! clocks are bound here instead, and passed to a run through
//! `ExecutorOptions(clock=...)`.
//!
//! - [`PyManualClock`] advances to each timing boundary by itself, so a
//!   timed net runs to quiescence in negligible real time.
//! - [`PySteppedClock`] moves only when the host calls `advance_ms`, and lets
//!   the host wait (`settle`) until the executor has caught up.
//!
//! Each wrapper holds the same `Arc` it hands the executor, so an advance
//! from Python is seen by the run that uses it.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use libpetri::{ExecutorClock, ManualClock, SteppedClock};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyAny;

/// Rejects a negative or NaN step. The Rust clocks ignore one silently,
/// which in Python would hide a sign error in a test.
fn checked_step(delta_ms: f64) -> PyResult<f64> {
    if delta_ms.is_nan() || delta_ms < 0.0 {
        return Err(PyValueError::new_err(format!(
            "advance_ms needs a non-negative number of milliseconds, got {delta_ms}"
        )));
    }
    Ok(delta_ms)
}

/// `timeout_s` (seconds, `None` for no limit) as a `Duration`.
fn timeout_from_secs(timeout_s: Option<f64>) -> PyResult<Option<Duration>> {
    match timeout_s {
        None => Ok(None),
        Some(secs) if secs.is_infinite() && secs > 0.0 => Ok(None),
        Some(secs) => Duration::try_from_secs_f64(secs).map(Some).map_err(|_| {
            PyValueError::new_err(format!(
                "timeout_s must be a non-negative number of seconds or None, got {secs}"
            ))
        }),
    }
}

/// A virtual clock that jumps to each timing boundary on its own
/// (\[TIME-015\]).
///
/// Firing time starts at 0 ms and epoch time at `epoch_origin_ms`; both
/// advance together. A `delayed(10_000)` transition fires at once in real
/// time, with the clock reading 10 000 ms afterwards. `advance_ms` moves the
/// clock forward by hand as well. A `ManualClock` may be reused across runs;
/// time carries on from where the previous run left it.
#[pyclass(module = "_libpetri", name = "ManualClock", frozen)]
pub struct PyManualClock {
    inner: Arc<ManualClock>,
}

#[pymethods]
impl PyManualClock {
    #[new]
    #[pyo3(signature = (epoch_origin_ms = 0))]
    fn new(epoch_origin_ms: u64) -> Self {
        Self {
            inner: Arc::new(ManualClock::starting_at_epoch(epoch_origin_ms)),
        }
    }

    /// Moves both time bases forward by `delta_ms`. Raises `ValueError` for
    /// a negative or NaN step; 0 is a no-op.
    fn advance_ms(&self, delta_ms: f64) -> PyResult<()> {
        self.inner.advance_ms(checked_step(delta_ms)?);
        Ok(())
    }

    /// Firing time in milliseconds since the clock was created.
    fn now_ms(&self) -> f64 {
        self.inner.elapsed_ms()
    }

    /// Same as `now_ms()`.
    fn elapsed_ms(&self) -> f64 {
        self.inner.elapsed_ms()
    }

    /// Epoch time in milliseconds: `epoch_origin_ms` plus the firing time.
    /// Tokens the run creates are stamped with this.
    fn epoch_ms(&self) -> u64 {
        self.inner.epoch_ms()
    }

    fn __repr__(&self) -> String {
        format!("ManualClock(now_ms={})", self.inner.elapsed_ms())
    }
}

/// A virtual clock that moves only when the host advances it (\[TIME-015\]).
///
/// The executor parks on the clock until `advance_ms` is called. `settle`
/// and its variants wait until the executor has parked again, so a test can
/// step time and then check what fired:
///
/// ```python
/// clock = SteppedClock()
/// handle, done = start_async(net, options=ExecutorOptions(clock=clock))
/// await clock.asettle()                                # first park
/// await clock.asettle_after(lambda: clock.advance_ms(1000))
/// ```
///
/// "Parked" describes the orchestrator only. An action still running is not
/// waited for.
///
/// A `SteppedClock` is single-use: one run per clock. Passing one that a run
/// has already used raises `ValueError` at run start. When the run ends, the
/// clock is marked finished and every settle waiter returns `True`.
#[pyclass(module = "_libpetri", name = "SteppedClock", frozen)]
pub struct PySteppedClock {
    pub(crate) inner: Arc<SteppedClock>,
    /// Set by the first run that uses this clock.
    pub(crate) claimed: Arc<AtomicBool>,
}

#[pymethods]
impl PySteppedClock {
    #[new]
    #[pyo3(signature = (epoch_origin_ms = 0))]
    fn new(epoch_origin_ms: u64) -> Self {
        Self {
            inner: Arc::new(SteppedClock::starting_at_epoch(epoch_origin_ms)),
            claimed: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Moves both time bases forward by `delta_ms` and wakes the executor.
    /// Raises `ValueError` for a negative or NaN step; 0 is a no-op.
    fn advance_ms(&self, delta_ms: f64) -> PyResult<()> {
        self.inner.advance_ms(checked_step(delta_ms)?);
        Ok(())
    }

    /// Firing time in milliseconds since the clock was created.
    fn now_ms(&self) -> f64 {
        self.inner.elapsed_ms()
    }

    /// Same as `now_ms()`.
    fn elapsed_ms(&self) -> f64 {
        self.inner.elapsed_ms()
    }

    /// Epoch time in milliseconds: `epoch_origin_ms` plus the firing time.
    /// Tokens the run creates are stamped with this.
    fn epoch_ms(&self) -> u64 {
        self.inner.epoch_ms()
    }

    /// True while the executor is parked on this clock.
    fn is_parked(&self) -> bool {
        self.inner.is_parked()
    }

    /// True once the run that used this clock has ended.
    fn is_finished(&self) -> bool {
        self.inner.is_finished()
    }

    /// How many times the executor has parked on this clock.
    fn park_count(&self) -> u64 {
        self.inner.park_count()
    }

    /// Blocks until the executor is parked or the run has ended. Returns
    /// `True` at once if either already holds, and `False` if `timeout_s`
    /// seconds pass first (`None` waits without limit).
    ///
    /// Use it to wait for a run's first park. After an advance or an inject,
    /// use `settle_after`: the parked flag can still describe the park the
    /// action just ended. The GIL is released while waiting. Do not call
    /// this on the thread that drives the run.
    #[pyo3(signature = (timeout_s = None))]
    fn settle(&self, py: Python<'_>, timeout_s: Option<f64>) -> PyResult<bool> {
        let timeout = timeout_from_secs(timeout_s)?;
        let clock = Arc::clone(&self.inner);
        Ok(py.detach(move || clock.settle(timeout)))
    }

    /// Calls `action()`, then blocks until the executor parks again or the
    /// run ends. Returns `False` if `timeout_s` seconds pass first.
    ///
    /// Only a park that starts after `action` began counts. `action` is
    /// typically `lambda: clock.advance_ms(...)` or an inject. An exception
    /// from `action` propagates and nothing is waited for. If `action` does
    /// not wake the executor, no new park comes and this times out.
    #[pyo3(signature = (action, timeout_s = None))]
    fn settle_after(
        &self,
        py: Python<'_>,
        action: &Bound<'_, PyAny>,
        timeout_s: Option<f64>,
    ) -> PyResult<bool> {
        let timeout = timeout_from_secs(timeout_s)?;
        let before = self.inner.park_count();
        action.call0()?;
        let clock = Arc::clone(&self.inner);
        Ok(py.detach(move || clock.settle_since(before, timeout)))
    }

    /// The awaitable form of `settle`. It suspends the caller's asyncio task
    /// rather than blocking the thread, so it may be awaited on the loop
    /// that started the run.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (timeout_s = None))]
    fn asettle<'py>(
        &self,
        py: Python<'py>,
        timeout_s: Option<f64>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let timeout = timeout_from_secs(timeout_s)?;
        let clock = Arc::clone(&self.inner);
        pyo3_async_runtimes::tokio::future_into_py(py, async move {
            Ok(clock.settled(timeout).await)
        })
    }

    /// The awaitable form of `settle_after`. `action()` runs now, before the
    /// awaitable is returned; awaiting it waits for the next park.
    #[cfg(feature = "tokio")]
    #[pyo3(signature = (action, timeout_s = None))]
    fn asettle_after<'py>(
        &self,
        py: Python<'py>,
        action: &Bound<'py, PyAny>,
        timeout_s: Option<f64>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let timeout = timeout_from_secs(timeout_s)?;
        let before = self.inner.park_count();
        action.call0()?;
        let clock = Arc::clone(&self.inner);
        pyo3_async_runtimes::tokio::future_into_py(py, async move {
            Ok(clock.settled_since(before, timeout).await)
        })
    }

    fn __repr__(&self) -> String {
        let py_bool = |b: bool| if b { "True" } else { "False" };
        format!(
            "SteppedClock(now_ms={}, parked={}, finished={})",
            self.inner.elapsed_ms(),
            py_bool(self.inner.is_parked()),
            py_bool(self.inner.is_finished())
        )
    }
}

/// The clock an `ExecutorOptions` carries.
#[derive(Clone)]
pub enum HostClock {
    Manual(Arc<ManualClock>),
    Stepped {
        clock: Arc<SteppedClock>,
        claimed: Arc<AtomicBool>,
    },
}

impl HostClock {
    /// Accepts a `ManualClock` or a `SteppedClock`; anything else is a
    /// `TypeError`.
    pub fn from_python(obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(manual) = obj.cast::<PyManualClock>() {
            return Ok(Self::Manual(Arc::clone(&manual.get().inner)));
        }
        if let Ok(stepped) = obj.cast::<PySteppedClock>() {
            let stepped = stepped.get();
            return Ok(Self::Stepped {
                clock: Arc::clone(&stepped.inner),
                claimed: Arc::clone(&stepped.claimed),
            });
        }
        Err(PyTypeError::new_err(format!(
            "clock must be a libpetri.ManualClock or libpetri.SteppedClock, got {}",
            obj.get_type()
                .name()
                .map(|n| n.to_string())
                .unwrap_or_else(|_| "?".into())
        )))
    }

    /// A Python object wrapping the same clock.
    pub fn to_python(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(match self {
            Self::Manual(clock) => Py::new(
                py,
                PyManualClock {
                    inner: Arc::clone(clock),
                },
            )?
            .into_any(),
            Self::Stepped { clock, claimed } => Py::new(
                py,
                PySteppedClock {
                    inner: Arc::clone(clock),
                    claimed: Arc::clone(claimed),
                },
            )?
            .into_any(),
        })
    }

    pub fn as_executor_clock(&self) -> Arc<dyn ExecutorClock> {
        match self {
            Self::Manual(clock) => Arc::clone(clock) as Arc<dyn ExecutorClock>,
            Self::Stepped { clock, .. } => Arc::clone(clock) as Arc<dyn ExecutorClock>,
        }
    }

    /// Claims a `SteppedClock` for one run. Raises `ValueError` if another
    /// run has already used it. A `ManualClock` needs no claim.
    pub fn claim(&self) -> PyResult<RunClockGuard> {
        match self {
            Self::Manual(_) => Ok(RunClockGuard(None)),
            Self::Stepped { clock, claimed } => {
                if claimed.swap(true, Ordering::AcqRel) || clock.is_finished() {
                    return Err(PyValueError::new_err(
                        "this SteppedClock was already used by a run; a SteppedClock is \
                         single-use, so create a new one for each run",
                    ));
                }
                Ok(RunClockGuard(Some((Arc::clone(clock), Arc::clone(claimed)))))
            }
        }
    }
}

/// Marks a claimed `SteppedClock` finished when the run ends, however it
/// ends (return, error, panic, or a dropped async run), so settle waiters
/// are released instead of timing out.
pub struct RunClockGuard(Option<(Arc<SteppedClock>, Arc<AtomicBool>)>);

impl RunClockGuard {
    /// A guard with no clock to finish.
    pub fn none() -> Self {
        Self(None)
    }

    /// Gives the claim back without finishing the clock, for a run that
    /// failed before it started.
    pub fn release(mut self) {
        if let Some((_, claimed)) = self.0.take() {
            claimed.store(false, Ordering::Release);
        }
    }
}

impl Drop for RunClockGuard {
    fn drop(&mut self) {
        if let Some((clock, _)) = self.0.take() {
            clock.mark_finished();
        }
    }
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyManualClock>()?;
    m.add_class::<PySteppedClock>()?;
    Ok(())
}
