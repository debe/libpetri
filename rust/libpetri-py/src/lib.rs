//! PyO3 bindings for libpetri.

use pyo3::prelude::*;

pub mod action;
#[cfg(feature = "debug")]
pub mod debug;
pub mod error;
pub mod executor;
pub mod export;
pub mod model;
pub mod value;
pub mod verification;

#[pymodule]
fn _libpetri(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    error::register(m)?;
    action::register(py, m)?;
    model::register(m)?;
    executor::register(py, m)?;
    export::register(m)?;
    verification::register(m)?;
    #[cfg(feature = "debug")]
    debug::register(py, m)?;

    m.add("HAS_TOKIO", cfg!(feature = "tokio"))?;
    m.add("HAS_Z3", cfg!(feature = "z3"))?;
    m.add("HAS_DEBUG", cfg!(feature = "debug"))?;
    Ok(())
}
