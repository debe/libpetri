//! Session-archive (v3) read/write bindings — gated on the `archive` feature.
//!
//! Wraps `libpetri_debug::archive::{SessionArchiveWriter, SessionArchiveReader}`
//! (gzip-compressed, length-prefixed binary, header versions v1/v2/v3 with v3
//! as the default writer). Per the libpetri-py 2.7.0 plan and the
//! `feedback_pyo3_gil_cold` memory: the writer takes a Rust-side
//! `PyEventStoreHandle` directly — events are never round-tripped through
//! Python. Serialization runs with the GIL released via `py.detach()`.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use libpetri::NetEvent;
use libpetri::debug::archive::{
    SessionArchive, SessionArchiveReader, SessionArchiveWriter,
};
use libpetri::debug::debug_event_store::DebugEventStore;
use libpetri::debug::debug_session_registry::DebugSession;
use libpetri::export::dot_exporter::dot_export;
use pyo3::exceptions::{PyIOError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyType};

use crate::events::{PyEventStoreHandle, PyNetEvent};
use crate::model::PyPetriNet;

// ---------------------------------------------------------------------------
// Writer
// ---------------------------------------------------------------------------

/// Writes session archives (v3 by default, gzip-compressed) to disk.
///
/// Wire-compatible with the TypeScript and Rust archive readers; structured
/// token payloads round-trip as JSON.
#[pyclass(module = "_libpetri", name = "SessionArchiveWriter")]
pub struct PySessionArchiveWriter;

#[pymethods]
impl PySessionArchiveWriter {
    /// Class method: `SessionArchiveWriter.write_from_store(path, ...)`.
    ///
    /// Serializes all events in `store` into a v3 archive file. The writer
    /// runs on a Rust thread with the GIL released — events never cross
    /// into Python.
    #[classmethod]
    #[pyo3(signature = (
        path,
        *,
        session_id,
        net,
        store,
        tags = None,
    ))]
    fn write_from_store(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        path: PathBuf,
        session_id: String,
        net: &PyPetriNet,
        store: &PyEventStoreHandle,
        tags: Option<HashMap<String, String>>,
    ) -> PyResult<()> {
        let events = store.events_arc_vec();
        let dot = dot_export(net.net(), None);
        let transition_names: Vec<String> = net
            .net()
            .transitions()
            .iter()
            .map(|t| t.name().to_string())
            .collect();
        let now_ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);
        let start_time = events
            .first()
            .map(|e| e.timestamp())
            .unwrap_or(now_ms);
        let end_time = events.last().map(|e| e.timestamp()).unwrap_or(now_ms);
        let net_name = net.net().name().to_string();
        let tags = tags.unwrap_or_default();

        let bytes = py
            .detach(move || {
                let debug_store = Arc::new(DebugEventStore::new(session_id.clone()));
                for event in events {
                    debug_store.append((*event).clone());
                }
                let session = DebugSession {
                    session_id,
                    net_name,
                    dot_diagram: dot,
                    places: None,
                    transition_names,
                    event_store: debug_store,
                    start_time,
                    active: false,
                    imported_structure: None,
                    end_time: Some(end_time),
                    tags,
                };
                SessionArchiveWriter::write(&session)
            })
            .map_err(PyValueError::new_err)?;

        std::fs::write(&path, bytes).map_err(|e| PyIOError::new_err(e.to_string()))?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Reader
// ---------------------------------------------------------------------------

/// In-memory representation of a deserialized session archive.
///
/// Use `.events()` to materialize the event stream as a list of `NetEvent`,
/// or `.event_count`, `.tags`, etc. for the header fields.
#[pyclass(module = "_libpetri", name = "SessionArchive")]
pub struct PySessionArchive {
    metadata: SessionArchive,
    events: Vec<Arc<NetEvent>>,
}

#[pymethods]
impl PySessionArchive {
    /// Archive format version (1, 2, or 3).
    #[getter]
    fn version(&self) -> u32 {
        self.metadata.version()
    }

    #[getter]
    fn session_id(&self) -> String {
        self.metadata.session_id().to_string()
    }

    #[getter]
    fn net_name(&self) -> String {
        self.metadata.net_name().to_string()
    }

    #[getter]
    fn event_count(&self) -> usize {
        self.metadata.event_count()
    }

    #[getter]
    fn dot_diagram(&self) -> String {
        self.metadata.dot_diagram().to_string()
    }

    #[getter]
    fn start_time(&self) -> String {
        self.metadata.start_time().to_string()
    }

    #[getter]
    fn end_time(&self) -> Option<String> {
        self.metadata.end_time().map(str::to_owned)
    }

    /// Tags map (v2+); empty dict for v1 archives.
    #[getter]
    fn tags<'py>(&self, py: Python<'py>) -> PyResult<Py<PyDict>> {
        let d = PyDict::new(py);
        for (k, v) in self.metadata.tags() {
            d.set_item(k, v)?;
        }
        Ok(d.unbind())
    }

    /// All events in the archive as a list of `NetEvent`. Materializes
    /// lazily — fine for archives up to ~100k events; for very large
    /// archives stream from the underlying file with the Rust API.
    fn events<'py>(&self, py: Python<'py>) -> PyResult<Py<PyList>> {
        let list = PyList::empty(py);
        for ev in &self.events {
            list.append(Py::new(py, PyNetEvent::new(Arc::clone(ev)))?)?;
        }
        Ok(list.unbind())
    }

    fn __repr__(&self) -> String {
        format!(
            "SessionArchive(version={}, session_id={:?}, event_count={})",
            self.metadata.version(),
            self.metadata.session_id(),
            self.metadata.event_count(),
        )
    }
}

/// Reads session archives from disk.
#[pyclass(module = "_libpetri", name = "SessionArchiveReader")]
pub struct PySessionArchiveReader;

#[pymethods]
impl PySessionArchiveReader {
    /// Reads a v1/v2/v3 archive from `path`. Raises `IOError` on missing
    /// file, `ValueError` on corrupt or unsupported-version archives.
    #[classmethod]
    fn read(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        path: PathBuf,
    ) -> PyResult<PySessionArchive> {
        let compressed =
            std::fs::read(&path).map_err(|e| PyIOError::new_err(e.to_string()))?;
        let imported = py
            .detach(move || SessionArchiveReader::read_full(&compressed))
            .map_err(PyValueError::new_err)?;
        let events: Vec<Arc<NetEvent>> = imported
            .event_store
            .events()
            .into_iter()
            .map(Arc::new)
            .collect();
        Ok(PySessionArchive {
            metadata: imported.metadata,
            events,
        })
    }
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

pub fn register(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySessionArchiveWriter>()?;
    m.add_class::<PySessionArchive>()?;
    m.add_class::<PySessionArchiveReader>()?;
    Ok(())
}
