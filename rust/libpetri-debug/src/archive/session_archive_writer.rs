//! Writes a debug session to a length-prefixed binary archive format.
//!
//! Format (inside gzip):
//! `[4 bytes: metadata JSON length][N bytes: metadata JSON]`
//! `[4 bytes: event JSON length][N bytes: event JSON]`
//! ...
//! (EOF terminates the stream)

use std::io::Write;

use flate2::Compression;
use flate2::write::GzEncoder;

use crate::debug_session_registry::{DebugSession, build_net_structure};
use crate::net_event_converter::to_event_info;

use super::session_archive::{CURRENT_VERSION, SessionArchive};

/// Writes debug sessions to the archive format.
pub struct SessionArchiveWriter;

impl SessionArchiveWriter {
    /// Writes a complete session archive and returns the compressed bytes.
    pub fn write(session: &DebugSession) -> Result<Vec<u8>, String> {
        let structure = build_net_structure(session);

        let metadata = SessionArchive {
            version: CURRENT_VERSION,
            session_id: session.session_id.clone(),
            net_name: session.net_name.clone(),
            dot_diagram: session.dot_diagram.clone(),
            start_time: session.start_time.to_string(),
            event_count: session.event_store.event_count(),
            structure,
        };

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());

        // Write metadata
        let meta_bytes = serde_json::to_vec(&metadata).map_err(|e| e.to_string())?;
        encoder
            .write_all(&(meta_bytes.len() as u32).to_be_bytes())
            .map_err(|e| e.to_string())?;
        encoder.write_all(&meta_bytes).map_err(|e| e.to_string())?;

        // Write events
        let events = session.event_store.events();
        for event in &events {
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
