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

pub fn marking_from_python(
    _py: Python<'_>,
    initial: Option<&Bound<'_, PyAny>>,
) -> PyResult<Marking> {
    let mut marking = Marking::new();
    let Some(initial) = initial else {
        return Ok(marking);
    };

    let dict = initial
        .cast::<PyDict>()
        .map_err(|_| PyTypeError::new_err("initial must be a dict[str | Place, iterable]"))?;

    let created_at = now_millis();
    for (place_obj, tokens_obj) in dict.iter() {
        let place = place_name_from_object(&place_obj)?;
        for item in tokens_obj.try_iter()? {
            let item = item?;
            marking.add_erased(&place, erased_from_py_at(item.unbind(), created_at));
        }
    }

    Ok(marking)
}

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
