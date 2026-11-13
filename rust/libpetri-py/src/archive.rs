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

use libpetri::NetEvent;
use libpetri::debug::archive::{
    SessionArchive, SessionArchiveReader, SessionArchiveWriter,
};
use libpetri::debug::debug_event_store::DebugEventStore;
use libpetri::debug::debug_session_registry::DebugSession;
use libpetri::debug::place_analysis::PlaceAnalysis;
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
/// token payloads round-trip as JSON. `write_v1` / `write_v2` write the
/// earlier header versions, as Rust's `SessionArchiveWriter::write_v1` /
/// `write_v2` do (EVT-025).
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
        write_archive(py, path, session_id, net, store, tags, SessionArchiveWriter::write)
    }

    /// Class method: `SessionArchiveWriter.write_v1(path, ...)`.
    ///
    /// Writes the legacy v1 header, which has no `end_time`, `tags` or
    /// metadata, so it takes no `tags`.
    #[classmethod]
    #[pyo3(signature = (path, *, session_id, net, store))]
    fn write_v1(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        path: PathBuf,
        session_id: String,
        net: &PyPetriNet,
        store: &PyEventStoreHandle,
    ) -> PyResult<()> {
        write_archive(py, path, session_id, net, store, None, SessionArchiveWriter::write_v1)
    }

    /// Class method: `SessionArchiveWriter.write_v2(path, ...)`.
    ///
    /// Writes the v2 header: v3's header shape, without the `structured`
    /// token payloads v3 adds to the event body.
    #[classmethod]
    #[pyo3(signature = (
        path,
        *,
        session_id,
        net,
        store,
        tags = None,
    ))]
    fn write_v2(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        path: PathBuf,
        session_id: String,
        net: &PyPetriNet,
        store: &PyEventStoreHandle,
        tags: Option<HashMap<String, String>>,
    ) -> PyResult<()> {
        write_archive(py, path, session_id, net, store, tags, SessionArchiveWriter::write_v2)
    }
}

/// Builds the archived session from `net` and the snapshot of `store`, and
/// writes it with `write`, with the GIL released.
///
/// The session is run data only (EVT-025): every event of the snapshot (the
/// debug store holds exactly as many as the snapshot has, so none is evicted),
/// the net's places and transitions as the header `structure`, and times taken
/// from the first and last event. An empty store has no time, so it reads
/// `start_time` 0 and no `end_time` rather than the wall clock.
fn write_archive(
    py: Python<'_>,
    path: PathBuf,
    session_id: String,
    net: &PyPetriNet,
    store: &PyEventStoreHandle,
    tags: Option<HashMap<String, String>>,
    write: fn(&DebugSession) -> Result<Vec<u8>, String>,
) -> PyResult<()> {
    let events = store.events_arc_vec();
    let dot = dot_export(net.net(), None);
    let places = PlaceAnalysis::from_net(net.net());
    let transition_names: Vec<String> = net
        .net()
        .transitions()
        .iter()
        .map(|t| t.name().to_string())
        .collect();
    let start_time = events.first().map(|e| e.timestamp()).unwrap_or(0);
    let end_time = events.last().map(|e| e.timestamp());
    let net_name = net.net().name().to_string();
    let tags = tags.unwrap_or_default();

    let bytes = py
        .detach(move || {
            let debug_store = Arc::new(DebugEventStore::with_capacity(
                session_id.clone(),
                events.len().max(1),
            ));
            for event in events {
                debug_store.append((*event).clone());
            }
            let session = DebugSession {
                session_id,
                net_name,
                dot_diagram: dot,
                places: Some(places),
                transition_names,
                event_store: debug_store,
                start_time,
                active: false,
                imported_structure: None,
                end_time,
                tags,
            };
            write(&session)
        })
        .map_err(PyValueError::new_err)?;

    std::fs::write(&path, bytes).map_err(|e| PyIOError::new_err(e.to_string()))?;
    Ok(())
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

    /// Tags map (v2+); empty dict for v1 archives. Keys in ascending order:
    /// a Python dict is an ordered medium, and the header holds them in a
    /// per-process seeded `HashMap`.
    #[getter]
    fn tags<'py>(&self, py: Python<'py>) -> PyResult<Py<PyDict>> {
        let d = PyDict::new(py);
        let mut tags: Vec<_> = self.metadata.tags().iter().collect();
        tags.sort_unstable();
        for (k, v) in tags {
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
