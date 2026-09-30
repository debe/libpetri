//! Rust ↔ Python error translation.
//!
//! Provides three Python exception classes that mirror the libpetri error
//! taxonomy, plus helpers that turn Rust [`ActionError`] values and panics
//! into clean Python errors.

use std::any::Any;
use std::cell::Cell;
use std::panic::{self, AssertUnwindSafe, catch_unwind};
use std::sync::Once;

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
    install_panic_hook();
    Ok(())
}

thread_local! {
    /// True while [`panic_to_py`] is on the stack on this thread.
    static TRANSLATING: Cell<bool> = const { Cell::new(false) };
}

/// Silences the default panic dump for panics [`panic_to_py`] is about to turn into a
/// Python exception — a structural rejection (CORE-043, name collisions, …) is an
/// ordinary validation error and must not print a backtrace hint before the raised
/// `StructureError`. Every other panic, on this or any other thread, still reaches the
/// default hook.
fn install_panic_hook() {
    static INSTALLED: Once = Once::new();
    INSTALLED.call_once(|| {
        let default = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            // `try_with`: a panic during TLS teardown must not panic the hook itself.
            if !TRANSLATING.try_with(Cell::get).unwrap_or(false) {
                default(info);
            }
        }));
    });
}

/// Restores the previous flag value even if `f` unwinds.
struct TranslatingGuard(bool);

impl Drop for TranslatingGuard {
    fn drop(&mut self) {
        TRANSLATING.with(|f| f.set(self.0));
    }
}

/// Wraps a Rust [`ActionError`] into a Python `CallbackError`.
pub fn action_error(err: ActionError) -> PyErr {
    CallbackError::new_err(err.message)
}

/// The message a panic carried, or a fixed text when it carried no string.
fn panic_message(payload: Box<dyn Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        return message.clone();
    }
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        return (*message).to_string();
    }
    "libpetri panicked without a string payload".to_string()
}

/// Converts a panic payload into a Python `StructureError`.
pub fn panic_payload(payload: Box<dyn Any + Send>) -> PyErr {
    StructureError::new_err(panic_message(payload))
}

/// Runs `f` and translates any panic into a Python `StructureError`, without the
/// default hook's stderr dump (see [`install_panic_hook`]).
pub fn panic_to_py<T>(f: impl FnOnce() -> T) -> PyResult<T> {
    let _guard = TranslatingGuard(TRANSLATING.replace(true));
    catch_unwind(AssertUnwindSafe(f)).map_err(panic_payload)
}

/// Runs `f` and translates a panic into a Python `ValueError` carrying the panic's
/// message, without the stderr dump. For the arc and timing factories, whose Rust
/// counterparts assert their arguments (`delayed` past `MAX_DURATION_MS`, `window` with
/// `latest < earliest`, `exactly(0, p)`, ...): a bad argument is a `ValueError` in Python.
pub fn panic_to_value_error<T>(f: impl FnOnce() -> T) -> PyResult<T> {
    let _guard = TranslatingGuard(TRANSLATING.replace(true));
    catch_unwind(AssertUnwindSafe(f)).map_err(|payload| PyValueError::new_err(panic_message(payload)))
}
