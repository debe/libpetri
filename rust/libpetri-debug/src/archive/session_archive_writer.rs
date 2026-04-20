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
//! [`CURRENT_VERSION`](super::session_archive::CURRENT_VERSION) (v3 as of
//! libpetri 1.8.0). Callers that need to emit legacy headers — compatibility
//! tests or readers pinned to older libpetri versions — can call
//! [`write_v1`](SessionArchiveWriter::write_v1) or
//! [`write_v2`](SessionArchiveWriter::write_v2).
//!
//! Note that the event-body token format is controlled by
//! [`to_event_info_with_registry`](crate::net_event_converter::to_event_info_with_registry)
//! and always emits the current (v3) structured shape regardless of which
//! header version is written; a 1.8.0+ writer cannot produce byte-for-byte
//! 1.7.x event bodies. `write_v1` / `write_v2` therefore primarily exist to
//! exercise the header-version dispatch code in the reader.

use std::io::Write;

use flate2::Compression;
use flate2::write::GzEncoder;
use libpetri_event::net_event::NetEvent;

use crate::debug_session_registry::{DebugSession, build_net_structure};
use crate::net_event_converter::to_event_info_with_registry;
use crate::token_projector_registry::TokenProjectorRegistry;

use super::session_archive::{SessionArchiveV1, SessionArchiveV2, SessionArchiveV3};
use super::session_metadata::compute_metadata;

/// Writes debug sessions to the archive format.
pub struct SessionArchiveWriter;

impl SessionArchiveWriter {
    /// Writes a complete session archive in the current format (v3 as of 1.8.0)
    /// and returns the compressed bytes. Uses a default (empty)
    /// [`TokenProjectorRegistry`] — unregistered token types fall back to the
    /// `{"type", "text"}` projection. For typed projection of user-defined token
    /// types, use [`write_with_registry`](Self::write_with_registry).
    pub fn write(session: &DebugSession) -> Result<Vec<u8>, String> {
        Self::write_v3(session, None)
    }

    /// Variant of [`write`](Self::write) that lets the caller supply a
    /// [`TokenProjectorRegistry`] so typed token values surface as JSON fields
    /// inside each `TokenAdded` / `TokenRemoved` event's `structured` entry.
    pub fn write_with_registry(
        session: &DebugSession,
        registry: &TokenProjectorRegistry,
    ) -> Result<Vec<u8>, String> {
        Self::write_v3(session, Some(registry))
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
        Self::write_framed(&header_bytes, &events, None)
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
        Self::write_framed(&header_bytes, &events, None)
    }

    /// Writes a session in the v3 format — same header shape as v2, with a
    /// version tag of `3` signalling that token payloads in the event body
    /// carry a `structured` JSON field alongside the legacy `value` string.
    ///
    /// When `registry` is `Some(_)`, typed token values are projected into the
    /// `structured` field via the registry. When `None`, payloads fall back to
    /// the type-name + Debug-repr projection (matching Java's `{"valueType",
    /// "text"}` fallback shape).
    pub fn write_v3(
        session: &DebugSession,
        registry: Option<&TokenProjectorRegistry>,
    ) -> Result<Vec<u8>, String> {
        let events = session.event_store.events();
        let metadata = compute_metadata(&events);

        let header = SessionArchiveV3 {
            version: 3,
            session_id: session.session_id.clone(),
            net_name: session.net_name.clone(),
            dot_diagram: session.dot_diagram.clone(),
            start_time: session.start_time.to_string(),
            end_time: session.end_time.map(|t| t.to_string()),
            event_count: events.len(),
            tags: session.tags.clone(),
            metadata,
            structure: build_net_structure(session),
        };

        let header_bytes = serde_json::to_vec(&header).map_err(|e| e.to_string())?;
        Self::write_framed(&header_bytes, &events, registry)
    }

    /// Shared framing logic: length-prefixed header, length-prefixed events,
    /// then gzip. All versions share the event wire format (the token
    /// `structured` field is serde-optional — v1/v2 readers tolerate its
    /// presence, v3 readers consume it).
    fn write_framed(
        header_bytes: &[u8],
        events: &[NetEvent],
        registry: Option<&TokenProjectorRegistry>,
    ) -> Result<Vec<u8>, String> {
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());

        // Header
        encoder
            .write_all(&(header_bytes.len() as u32).to_be_bytes())
            .map_err(|e| e.to_string())?;
        encoder.write_all(header_bytes).map_err(|e| e.to_string())?;

        for event in events {
            let event_info = to_event_info_with_registry(event, registry);
            let event_bytes = serde_json::to_vec(&event_info).map_err(|e| e.to_string())?;
            encoder
                .write_all(&(event_bytes.len() as u32).to_be_bytes())
                .map_err(|e| e.to_string())?;
            encoder.write_all(&event_bytes).map_err(|e| e.to_string())?;
        }

        encoder.finish().map_err(|e| e.to_string())
    }
}
