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
use pyo3::exceptions::PyTypeError;
use pyo3::intern;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyList};

use crate::error::LibpetriError;
use crate::model::PyPlace;

#[derive(Debug)]
pub struct PyTokenValue {
    value: Py<PyAny>,
}

// Python objects are only touched while holding the GIL. The wrapper is
// otherwise opaque to the executor and only cloned / moved across threads.
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

/// Builds a [`Marking`] from a Python dict.
///
/// Accepts both the **legacy value-only form** (`{place: [v1, v2, ...]}`,
/// timestamps reassigned to `now()`) and the **structured snapshot form**
/// (`{place: [{"value": v, "created_at": ms}, ...]}`, timestamps preserved
/// per token). Auto-detected by element type: a `dict` with both `value` and
/// `created_at` keys is treated as a structured token; anything else is a
/// raw value.
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
                let created_at: u64 = created_at_obj.extract().map_err(|_| {
                    PyTypeError::new_err(
                        "snapshot token 'created_at' must be an int (ms since epoch)",
                    )
                })?;
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
    for place in marking.non_empty_places() {
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

/// Emits a [`Marking`] as the **structured snapshot dict**
/// (`{place: [{"value": v, "created_at": ms}, ...]}`), preserving each
/// token's `created_at` timestamp so a later `marking_from_python` round-trip
/// reproduces the original marking exactly. This is the default form
/// returned from executor runs in 2.7.0+; the Python `MarkingView` wrapper
/// projects to either form on demand.
pub fn marking_snapshot_to_python(py: Python<'_>, marking: &Marking) -> PyResult<Py<PyDict>> {
    let dict = PyDict::new(py);
    let value_key = intern!(py, "value");
    let created_at_key = intern!(py, "created_at");
    for place in marking.non_empty_places() {
        let list = PyList::empty(py);
        if let Some(queue) = marking.queue(place.as_ref()) {
            for token in queue {
                let entry = PyDict::new(py);
                entry.set_item(value_key, py_from_erased(py, token)?)?;
                entry.set_item(created_at_key, token.created_at)?;
                list.append(entry)?;
            }
        }
        dict.set_item(place.as_ref(), list)?;
    }
    Ok(dict.unbind())
}
