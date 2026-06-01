//! PyO3 bindings for libpetri.

use pyo3::prelude::*;

pub mod action;
#[cfg(feature = "archive")]
pub mod archive;
#[cfg(feature = "debug")]
pub mod debug;
pub mod error;
pub mod events;
pub mod executor;
pub mod export;
#[cfg(feature = "archive")]
pub mod marking_cache;
pub mod model;
pub mod value;
pub mod verification;

#[pymodule]
fn _libpetri(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    error::register(m)?;
    action::register(py, m)?;
    model::register(m)?;
    events::register(py, m)?;
    executor::register(py, m)?;
    export::register(m)?;
    verification::register(m)?;
    #[cfg(feature = "debug")]
    debug::register(py, m)?;
    #[cfg(feature = "archive")]
    archive::register(py, m)?;
    #[cfg(feature = "archive")]
    marking_cache::register(py, m)?;

    m.add("HAS_TOKIO", cfg!(feature = "tokio"))?;
    m.add("HAS_Z3", cfg!(feature = "z3"))?;
    m.add("HAS_DEBUG", cfg!(feature = "debug"))?;
    m.add("HAS_ARCHIVE", cfg!(feature = "archive"))?;
    Ok(())
}
