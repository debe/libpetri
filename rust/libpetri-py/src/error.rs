//! Rust ↔ Python error translation.
//!
//! Provides three Python exception classes that mirror the libpetri error
//! taxonomy, plus helpers that turn Rust [`ActionError`] values and panics
//! into clean Python errors.

use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind};

use libpetri::core::action::ActionError;
use pyo3::create_exception;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;

create_exception!(_libpetri, LibpetriError, PyRuntimeError);
create_exception!(_libpetri, CallbackError, LibpetriError);
create_exception!(_libpetri, StructureError, PyValueError);

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    m.add("LibpetriError", py.get_type::<LibpetriError>())?;
    m.add("CallbackError", py.get_type::<CallbackError>())?;
    m.add("StructureError", py.get_type::<StructureError>())?;
    Ok(())
}

/// Wraps a Rust [`ActionError`] into a Python `CallbackError`.
pub fn action_error(err: ActionError) -> PyErr {
    CallbackError::new_err(err.message)
}

/// Converts a panic payload into a Python `StructureError`.
pub fn panic_payload(payload: Box<dyn Any + Send>) -> PyErr {
    if let Some(message) = payload.downcast_ref::<String>() {
        return StructureError::new_err(message.clone());
    }
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        return StructureError::new_err((*message).to_string());
    }
    StructureError::new_err("libpetri panicked without a string payload")
}

/// Runs `f` and translates any panic into a Python `StructureError`.
pub fn panic_to_py<T>(f: impl FnOnce() -> T) -> PyResult<T> {
    catch_unwind(AssertUnwindSafe(f)).map_err(panic_payload)
}
