//! Writes a debug session to a length-prefixed binary archive format.
//!
//! Format (inside gzip):
//! `[4 bytes: metadata JSON length][N bytes: metadata JSON]`
//! `[4 bytes: event JSON length][N bytes: event JSON]`
//! ...
//! (EOF terminates the stream)
//!
//! ## Format selection
//!
//! [`write`](SessionArchiveWriter::write) defaults to
//! [`CURRENT_VERSION`](super::session_archive::CURRENT_VERSION) (v2 as of
//! libpetri 1.7.0). Callers that need to emit legacy archives — compatibility
//! tests or readers pinned to libpetri ≤ 1.6.1 — can call
//! [`write_v1`](SessionArchiveWriter::write_v1). v2 archives cost one extra
//! pass over the event store to pre-compute
//! [`SessionMetadata`](super::session_archive::SessionMetadata); the savings
//! at read time (no event scan needed for `has_errors` / histogram queries)
//! pay it back the first time a caller lists or samples a bucket of sessions.

use std::io::Write;

use flate2::Compression;
use flate2::write::GzEncoder;
use libpetri_event::net_event::NetEvent;

use crate::debug_session_registry::{DebugSession, build_net_structure};
use crate::net_event_converter::to_event_info;

use super::session_archive::{
    SessionArchiveV1, SessionArchiveV2,
};
use super::session_metadata::compute_metadata;

/// Writes debug sessions to the archive format.
pub struct SessionArchiveWriter;

impl SessionArchiveWriter {
    /// Writes a complete session archive in the current format (v2 as of 1.7.0)
    /// and returns the compressed bytes.
    pub fn write(session: &DebugSession) -> Result<Vec<u8>, String> {
        Self::write_v2(session)
    }

    /// Writes a session in the legacy v1 format. Use only for compatibility
    /// testing or when producing archives for consumers pinned to libpetri ≤ 1.6.1.
    pub fn write_v1(session: &DebugSession) -> Result<Vec<u8>, String> {
        let header = SessionArchiveV1 {
            version: 1,
            session_id: session.session_id.clone(),
            net_name: session.net_name.clone(),
            dot_diagram: session.dot_diagram.clone(),
            start_time: session.start_time.to_string(),
            event_count: session.event_store.event_count(),
            structure: build_net_structure(session),
        };
        let header_bytes = serde_json::to_vec(&header).map_err(|e| e.to_string())?;
        let events = session.event_store.events();
        Self::write_framed(&header_bytes, &events)
    }

    /// Writes a session in the v2 format — richer header with `end_time`,
    /// `tags`, and pre-computed
    /// [`SessionMetadata`](super::session_archive::SessionMetadata).
    ///
    /// Requires two passes over the event slice. The existing event store
    /// `events()` method returns an owned `Vec<NetEvent>`, so we fetch the
    /// slice once and walk it twice (metadata scan, then serialization) —
    /// no extra allocation.
    pub fn write_v2(session: &DebugSession) -> Result<Vec<u8>, String> {
        // One eager fetch; iterate the owned slice twice.
        let events = session.event_store.events();
        let metadata = compute_metadata(&events);

        let header = SessionArchiveV2 {
            version: 2,
            session_id: session.session_id.clone(),
            net_name: session.net_name.clone(),
            dot_diagram: session.dot_diagram.clone(),
            start_time: session.start_time.to_string(),
            end_time: session.end_time.map(|t| t.to_string()),
            event_count: events.len(),
            // Snapshot of tags at archive-write time — record the state that
            // was current when the session was archived, not whatever happens
            // on the live session afterwards.
            tags: session.tags.clone(),
            metadata,
            structure: build_net_structure(session),
        };

        let header_bytes = serde_json::to_vec(&header).map_err(|e| e.to_string())?;
        Self::write_framed(&header_bytes, &events)
    }

    /// Shared framing logic: length-prefixed header, length-prefixed events,
    /// then gzip. Both v1 and v2 archives use the identical event wire format,
    /// so the body loop is version-agnostic.
    fn write_framed(header_bytes: &[u8], events: &[NetEvent]) -> Result<Vec<u8>, String> {
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());

        // Header
        encoder
            .write_all(&(header_bytes.len() as u32).to_be_bytes())
            .map_err(|e| e.to_string())?;
        encoder.write_all(header_bytes).map_err(|e| e.to_string())?;

        // Events — same serialization for both versions.
        for event in events {
            let event_info = to_event_info(event);
            let event_bytes = serde_json::to_vec(&event_info).map_err(|e| e.to_string())?;
            encoder
                .write_all(&(event_bytes.len() as u32).to_be_bytes())
                .map_err(|e| e.to_string())?;
            encoder.write_all(&event_bytes).map_err(|e| e.to_string())?;
        }

        encoder.finish().map_err(|e| e.to_string())
    }
}
