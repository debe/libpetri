//! Debug protocol bindings.

use std::collections::HashMap;
use std::sync::Mutex;

use libpetri::debug::{DebugCommand, DebugProtocolHandler, DebugSession, DebugSessionRegistry};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;

use crate::model::PyPetriNet;

/// Read-only summary of a debug session — id, net name, active flag, event count, tags, end time, duration.
#[pyclass(module = "_libpetri", name = "SessionSummary", from_py_object)]
#[derive(Clone)]
pub struct PySessionSummary {
    #[pyo3(get)]
    session_id: String,
    #[pyo3(get)]
    net_name: String,
    #[pyo3(get)]
    active: bool,
    #[pyo3(get)]
    event_count: usize,
    #[pyo3(get)]
    tags: HashMap<String, String>,
    #[pyo3(get)]
    end_time: Option<String>,
    #[pyo3(get)]
    duration_ms: Option<u64>,
}

impl PySessionSummary {
    fn from_session(session: &DebugSession) -> Self {
        Self {
            session_id: session.session_id.clone(),
            net_name: session.net_name.clone(),
            active: session.active,
            event_count: session.event_store.event_count(),
            tags: session.tags.clone(),
            end_time: session.end_time.map(|ts| ts.to_string()),
            duration_ms: session.duration_ms(),
        }
    }
}

/// Server-side handler for the libpetri debug protocol — drives a `DebugSessionRegistry`
/// and routes JSON commands from connected clients.
#[pyclass(module = "_libpetri", name = "DebugProtocolHandler")]
pub struct PyDebugProtocolHandler {
    inner: Mutex<DebugProtocolHandler>,
}

#[pymethods]
impl PyDebugProtocolHandler {
    /// Builds a handler over a fresh session registry.
    #[new]
    fn new() -> Self {
        Self {
            inner: Mutex::new(DebugProtocolHandler::new(DebugSessionRegistry::new())),
        }
    }

    /// Registers a session for live inspection. Optional `tags` are searchable in `list_sessions`.
    #[pyo3(signature = (session_id, net, tags = None))]
    fn register_session(
        &self,
        session_id: String,
        net: &PyPetriNet,
        tags: Option<HashMap<String, String>>,
    ) {
        let mut handler = self.inner.lock().unwrap();
        if let Some(tags) = tags {
            handler
                .session_registry_mut()
                .register_with_tags(session_id, net.net(), tags);
        } else {
            handler
                .session_registry_mut()
                .register(session_id, net.net());
        }
    }

    /// Marks a session as completed (still inspectable for replay).
    fn complete_session(&self, session_id: &str) {
        self.inner
            .lock()
            .unwrap()
            .session_registry_mut()
            .complete(session_id);
    }

    /// Removes a session from the registry.
    fn remove_session(&self, session_id: &str) {
        self.inner
            .lock()
            .unwrap()
            .session_registry_mut()
            .remove(session_id);
    }

    /// Lists sessions, optionally filtered to active-only and by tag equality.
    #[pyo3(signature = (limit = 50, active_only = None, tag_filter = None))]
    fn list_sessions(
        &self,
        limit: usize,
        active_only: Option<bool>,
        tag_filter: Option<HashMap<String, String>>,
    ) -> Vec<PySessionSummary> {
        let handler = self.inner.lock().unwrap();
        let registry = handler.session_registry();
        let tag_filter = tag_filter.unwrap_or_default();
        let sessions = if active_only.unwrap_or(false) {
            registry.list_active_sessions_tagged(limit, &tag_filter)
        } else {
            registry.list_sessions_tagged(limit, &tag_filter)
        };
        sessions
            .into_iter()
            .map(PySessionSummary::from_session)
            .collect()
    }

    /// Connects a client. `callback(json_str)` is invoked for every outbound response.
    fn client_connected(
        &self,
        py: Python<'_>,
        client_id: String,
        callback: Py<PyAny>,
    ) -> PyResult<()> {
        if !callback.bind(py).is_callable() {
            return Err(PyTypeError::new_err("debug callback must be callable"));
        }
        let sink = move |response: libpetri::debug::DebugResponse| {
            if let Ok(json) = serde_json::to_string(&response) {
                Python::attach(|py| {
                    let _ = callback.bind(py).call1((json,));
                });
            }
        };
        self.inner
            .lock()
            .unwrap()
            .client_connected(client_id, Box::new(sink));
        Ok(())
    }

    /// Disconnects a client (no further responses delivered).
    fn client_disconnected(&self, client_id: &str) {
        self.inner.lock().unwrap().client_disconnected(client_id);
    }

    /// Routes a JSON command from `client_id` to the handler.
    fn handle_command(&self, client_id: &str, command_json: &str) -> PyResult<()> {
        let command: DebugCommand = serde_json::from_str(command_json)
            .map_err(|err| PyValueError::new_err(err.to_string()))?;
        self.inner.lock().unwrap().handle_command(client_id, command);
        Ok(())
    }
}

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySessionSummary>()?;
    m.add_class::<PyDebugProtocolHandler>()?;
    Ok(())
}
