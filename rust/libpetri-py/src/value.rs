//! Python value bridging.
//!
//! Tokens crossing the FFI boundary are wrapped in [`PyTokenValue`], which
//! holds a `Py<PyAny>` and is registered as a `python.object`-typed value in
//! the libpetri marking. Markings convert from/to Python dicts of place name
//! to a list of token values.

use std::any::Any;
use std::sync::Arc;

use libpetri::Marking;
use libpetri::core::token::{ErasedToken, now_millis};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::intern;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyBool, PyDict, PyFloat, PyList};

use crate::error::LibpetriError;
use crate::model::PyPlace;

#[derive(Debug)]
pub struct PyTokenValue {
    value: Py<PyAny>,
}

// Python objects are only touched while holding the GIL. The wrapper is
// otherwise opaque to the executor and only cloned / moved across threads.
//
// The executor owns tokens once it has consumed them (no rollback, EXEC-031) and
// drops them wherever it happens to be running — inside `Python::detach` for
// `run_sync`, or on a tokio worker for `run_async`. That is deliberately left to
// pyo3's reference pool, which queues a detached decref and drains it on the next
// attach. Do NOT add a `Drop` that calls `Python::attach`: this runs per token, so
// it would turn every drop into a GIL acquisition on a detached thread — far more
// expensive than the pool, and on the multi-threaded async path it serialises the
// executor against every other worker. See the note on
// `--cfg=pyo3_disable_reference_pool` in CLAUDE.md.
unsafe impl Send for PyTokenValue {}
unsafe impl Sync for PyTokenValue {}

impl PyTokenValue {
    pub fn new(value: Py<PyAny>) -> Self {
        Self { value }
    }

    pub fn clone_ref(&self, py: Python<'_>) -> Py<PyAny> {
        self.value.clone_ref(py)
    }
}

pub fn erased_from_py_at(value: Py<PyAny>, created_at: u64) -> ErasedToken {
    ErasedToken {
        value: Arc::new(PyTokenValue::new(value)) as Arc<dyn Any + Send + Sync>,
        created_at,
        value_type_name: "python.object",
    }
}

pub fn erased_from_py(value: Py<PyAny>) -> ErasedToken {
    erased_from_py_at(value, now_millis())
}

pub fn py_from_erased(py: Python<'_>, token: &ErasedToken) -> PyResult<Py<PyAny>> {
    let wrapped = token
        .value
        .downcast_ref::<PyTokenValue>()
        .ok_or_else(|| {
            LibpetriError::new_err(format!(
                "Expected python.object token, found {}",
                token.value_type_name
            ))
        })?;
    Ok(wrapped.clone_ref(py))
}

pub fn place_name_from_object(place_obj: &Bound<'_, PyAny>) -> PyResult<Arc<str>> {
    if let Ok(name) = place_obj.extract::<String>() {
        return Ok(Arc::<str>::from(name));
    }
    if let Ok(place) = place_obj.extract::<PyRef<'_, PyPlace>>() {
        return Ok(Arc::clone(place.place().name_arc()));
    }
    Err(PyTypeError::new_err(
        "expected a str place name or Place instance",
    ))
}

/// Validates a snapshot token's `created_at` — never alters it (\[CORE-073\] AC#9).
///
/// The same rule as `MarkingView` on the Python side (`runtime.py`
/// `_coerce_created_at`), so a dict means the same thing whether or not it
/// went through a view first: an integer (anything with `__index__`) or an
/// integral float — JSON pipelines produce `1700000000000.0` — that fits a
/// `u64`. `TypeError` for a value that is not a number of milliseconds at
/// all, `ValueError` for one that is but cannot be a timestamp. Called with
/// the GIL held, on the caller's thread, once per restored token.
fn created_at_from_python(obj: &Bound<'_, PyAny>) -> PyResult<u64> {
    let not_an_int = || {
        PyTypeError::new_err(format!(
            "snapshot token 'created_at' must be an int (ms since epoch), got {}",
            obj.repr().map(|r| r.to_string()).unwrap_or_default()
        ))
    };
    // `True` has an `__index__` of 1; a bool timestamp is a bug, not a value.
    if obj.is_instance_of::<PyBool>() {
        return Err(not_an_int());
    }
    if let Ok(float) = obj.cast::<PyFloat>() {
        let ms = float.value();
        // 2^64 exactly; `u64::MAX as f64` rounds up to it, hence `<`.
        return if ms.fract() == 0.0 && ms >= 0.0 && ms < 18_446_744_073_709_551_616.0 {
            Ok(ms as u64)
        } else if ms.is_finite() && ms.fract() == 0.0 {
            Err(created_at_out_of_range(obj))
        } else {
            Err(PyValueError::new_err(format!(
                "snapshot token 'created_at' must be a whole number of milliseconds, got {ms}"
            )))
        };
    }
    match obj.extract::<u64>() {
        Ok(ms) => Ok(ms),
        // An int that does not fit is a different mistake from a non-int.
        Err(_) if obj.hasattr(intern!(obj.py(), "__index__")).unwrap_or(false) => {
            Err(created_at_out_of_range(obj))
        }
        Err(_) => Err(not_an_int()),
    }
}

fn created_at_out_of_range(obj: &Bound<'_, PyAny>) -> PyErr {
    PyValueError::new_err(format!(
        "snapshot token 'created_at' must be a non-negative int that fits in 64 bits \
         (ms since epoch), got {}",
        obj.repr().map(|r| r.to_string()).unwrap_or_default()
    ))
}

/// Builds a [`Marking`] from a Python dict.
///
/// Accepts both the **legacy value-only form** (`{place: [v1, v2, ...]}`,
/// timestamps reassigned to `now()`) and the **structured snapshot form**
/// (`{place: [{"value": v, "created_at": ms}, ...]}`, timestamps preserved
/// per token). Auto-detected by element type: a `dict` with both `value` and
/// `created_at` keys is treated as a structured token; anything else is a
/// raw value. A structured token's `created_at` is validated, never coerced
/// — see [`created_at_from_python`].
pub fn marking_from_python(
    py: Python<'_>,
    initial: Option<&Bound<'_, PyAny>>,
) -> PyResult<Marking> {
    let mut marking = Marking::new();
    let Some(initial) = initial else {
        return Ok(marking);
    };

    let dict = initial
        .cast::<PyDict>()
        .map_err(|_| PyTypeError::new_err("initial must be a dict[str | Place, iterable]"))?;

    let fallback_created_at = now_millis();
    let value_key = intern!(py, "value");
    let created_at_key = intern!(py, "created_at");
    for (place_obj, tokens_obj) in dict.iter() {
        let place = place_name_from_object(&place_obj)?;
        for item in tokens_obj.try_iter()? {
            let item = item?;
            if let Ok(item_dict) = item.cast::<PyDict>()
                && let (Some(value_obj), Some(created_at_obj)) = (
                    item_dict.get_item(value_key)?,
                    item_dict.get_item(created_at_key)?,
                )
            {
                let created_at = created_at_from_python(&created_at_obj)?;
                marking.add_erased(
                    &place,
                    erased_from_py_at(value_obj.unbind(), created_at),
                );
                continue;
            }
            marking.add_erased(
                &place,
                erased_from_py_at(item.unbind(), fallback_created_at),
            );
        }
    }

    Ok(marking)
}

/// Emits a [`Marking`] as the **value-only legacy dict**
/// (`{place: [v1, v2, ...]}`). Timestamps are dropped at this boundary.
///
/// Kept for paths that intentionally project to the legacy form (e.g. the
/// `MarkingView.to_dict()` accessor on the Python side).
pub fn marking_to_python(py: Python<'_>, marking: &Marking) -> PyResult<Py<PyDict>> {
    let dict = PyDict::new(py);
    // Sorted for the same reason as the structured form: a Python dict is an
    // ordered medium, so hash order would leak into anything a host does
    // with it ([CORE-073] AC#12).
    let mut places = marking.non_empty_places();
    places.sort_unstable();
    for place in places {
        let list = PyList::empty(py);
        if let Some(queue) = marking.queue(place.as_ref()) {
            for token in queue {
                list.append(py_from_erased(py, token)?)?;
            }
        }
        dict.set_item(place.as_ref(), list)?;
    }
    Ok(dict.unbind())
}

/// Emits a \[CORE-073\] [`MarkingSnapshot`](libpetri::runtime::marking::MarkingSnapshot)
/// as the structured snapshot dict.
///
/// Same shape as [`marking_snapshot_to_python`], but from the snapshot form
/// rather than a live `Marking` — which is what
/// [`ExecutorHandle::snapshot`](libpetri::runtime::ExecutorHandle::snapshot)
/// replies with. Place order follows the `BTreeMap`: ascending code-point
/// order (Rust `str` order is byte order, which for UTF-8 is code-point
/// order), identical on every run (CORE-073 AC#12).
pub fn snapshot_form_to_python(
    py: Python<'_>,
    snapshot: &libpetri::runtime::marking::MarkingSnapshot,
) -> PyResult<Py<PyDict>> {
    let dict = PyDict::new(py);
    let value_key = intern!(py, "value");
    let created_at_key = intern!(py, "created_at");
    for (place, entries) in snapshot {
        let list = PyList::empty(py);
        for token in entries {
            let entry = PyDict::new(py);
            entry.set_item(value_key, py_from_erased(py, token)?)?;
            entry.set_item(created_at_key, token.created_at)?;
            list.append(entry)?;
        }
        dict.set_item(place.as_ref(), list)?;
    }
    Ok(dict.unbind())
}

/// Emits a [`Marking`] as the **structured snapshot dict**
/// (`{place: [{"value": v, "created_at": ms}, ...]}`), preserving each
/// token's `created_at` timestamp so a later `marking_from_python` round-trip
/// reproduces the original marking exactly. This is the default form
/// returned from executor runs in 2.7.0+; the Python `MarkingView` wrapper
/// projects to either form on demand.
pub fn marking_snapshot_to_python(py: Python<'_>, marking: &Marking) -> PyResult<Py<PyDict>> {
    // Routed through the [CORE-073] snapshot form rather than walking the
    // marking's `HashMap` directly. That walk emitted places in hash order,
    // so the run-result dict — which a Python host sees on *every* run and
    // may persist, diff or content-address — had a nondeterministic key
    // order, violating AC#12. The handle path and the run-result path now
    // produce the same, sorted, form.
    snapshot_form_to_python(py, &marking.snapshot())
}
