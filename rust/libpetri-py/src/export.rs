//! DOT export bindings.

use std::collections::HashSet;

use libpetri::export::graph::RankDir;
use libpetri::export::mapper::DotConfig;
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

use crate::model::PyPetriNet;

/// Graph layout direction for DOT rendering.
#[pyclass(module = "_libpetri", name = "RankDir", eq, eq_int)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PyRankDir {
    TopToBottom,
    LeftToRight,
    BottomToTop,
    RightToLeft,
}

impl PyRankDir {
    fn to_rust(self) -> RankDir {
        match self {
            Self::TopToBottom => RankDir::TopToBottom,
            Self::LeftToRight => RankDir::LeftToRight,
            Self::BottomToTop => RankDir::BottomToTop,
            Self::RightToLeft => RankDir::RightToLeft,
        }
    }
}

/// DOT rendering options: layout direction, what to label on each node, and which places are environment-typed.
#[pyclass(module = "_libpetri", name = "DotConfig")]
#[derive(Clone)]
pub struct PyDotConfig {
    #[pyo3(get, set)]
    direction: PyRankDir,
    #[pyo3(get, set)]
    show_types: bool,
    #[pyo3(get, set)]
    show_intervals: bool,
    #[pyo3(get, set)]
    show_priority: bool,
    #[pyo3(get, set)]
    environment_places: Vec<String>,
}

impl Default for PyDotConfig {
    fn default() -> Self {
        Self {
            direction: PyRankDir::TopToBottom,
            show_types: true,
            show_intervals: true,
            show_priority: true,
            environment_places: Vec::new(),
        }
    }
}

impl PyDotConfig {
    pub fn to_rust(&self) -> DotConfig {
        // Use struct-update syntax so any non-Python-exposed DotConfig field
        // (e.g. cluster_source) inherits its Default. This keeps the binding
        // forward-compatible with new layout-control fields added in Rust.
        DotConfig {
            direction: self.direction.to_rust(),
            show_types: self.show_types,
            show_intervals: self.show_intervals,
            show_priority: self.show_priority,
            environment_places: self
                .environment_places
                .iter()
                .cloned()
                .collect::<HashSet<_>>(),
            ..DotConfig::default()
        }
    }
}

#[pymethods]
impl PyDotConfig {
    /// Builds a config; all parameters are keyword-only and have sensible defaults.
    #[new]
    #[pyo3(signature = (
        direction = PyRankDir::TopToBottom,
        show_types = true,
        show_intervals = true,
        show_priority = true,
        environment_places = Vec::new()
    ))]
    fn new(
        direction: PyRankDir,
        show_types: bool,
        show_intervals: bool,
        show_priority: bool,
        environment_places: Vec<String>,
    ) -> Self {
        Self {
            direction,
            show_types,
            show_intervals,
            show_priority,
            environment_places,
        }
    }
}

/// Renders `net` as Graphviz DOT source. `config` controls layout and labels.
#[pyfunction(name = "dot_export")]
#[pyo3(signature = (net, config = None))]
fn py_dot_export(net: &PyPetriNet, config: Option<&PyDotConfig>) -> String {
    let config = config.cloned().unwrap_or_default().to_rust();
    libpetri::dot_export(net.net(), Some(&config))
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyRankDir>()?;
    m.add_class::<PyDotConfig>()?;
    m.add_function(wrap_pyfunction!(py_dot_export, m)?)?;
    Ok(())
}
