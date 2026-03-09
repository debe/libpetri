//! Metadata header for a session archive file.

use serde::{Deserialize, Serialize};

use crate::debug_response::NetStructure;

/// Current archive format version.
pub const CURRENT_VERSION: u32 = 1;

/// Metadata header for a session archive.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SessionArchive {
    pub version: u32,
    pub session_id: String,
    pub net_name: String,
    pub dot_diagram: String,
    pub start_time: String,
    pub event_count: usize,
    pub structure: NetStructure,
}
