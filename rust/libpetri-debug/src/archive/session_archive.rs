//! Metadata header for a session archive file.
//!
//! Sealed across format versions so callers can pattern-match on [`SessionArchive::V1`]
//! / [`SessionArchive::V2`] to access v2-only fields with exhaustive coverage:
//!
//! ```ignore
//! match archive {
//!     SessionArchive::V1(v1) => println!("legacy: {}", v1.session_id),
//!     SessionArchive::V2(v2) => println!("v2: {} tags={:?}", v2.session_id, v2.tags),
//! }
//! ```
//!
//! ## Version contract
//!
//! - **v1** (libpetri 1.5.x–1.6.x): original format. Header carries `sessionId`,
//!   `netName`, `dotDiagram`, `startTime`, `eventCount`, and net `structure`.
//! - **v2** (libpetri 1.7.x): adds `endTime`, user-defined `tags`, and pre-computed
//!   [`SessionMetadata`] (event-type histogram, first/last event timestamps,
//!   `hasErrors`). Token payloads in v2 event bodies are toString-based — types erased.
//! - **v3** (libpetri 1.8.0+): same header shape as v2, but token payloads in the
//!   event body carry a `structured` JSON projection alongside the legacy `value`
//!   string. Writer-side projection is driven by
//!   [`TokenProjectorRegistry`](crate::token_projector_registry::TokenProjectorRegistry);
//!   reader-side hydration surfaces the payload on `NetEvent::TokenAdded` /
//!   `TokenRemoved` via a
//!   [`ReplayedTokenPayload`](super::session_archive_reader::ReplayedTokenPayload)
//!   so live and replayed tokens expose the same [`TokenPayload`] contract.
//!
//! The reader peeks the header `version` field via a lenient probe struct and
//! dispatches to the correct concrete type. All three versions coexist in the same
//! storage bucket. The Rust writer emits v3 by default — matching the Java and
//! TypeScript writers.

use std::collections::{BTreeMap, HashMap};
use std::sync::OnceLock;

use serde::{Deserialize, Serialize};

use crate::debug_response::NetStructure;

/// Version written by default by [`SessionArchiveWriter::write`](super::session_archive_writer::SessionArchiveWriter::write).
/// v3 carries typed token payloads in the event body — matching the Java and TypeScript writers.
pub const CURRENT_VERSION: u32 = 3;

/// Lowest version [`SessionArchiveReader`](super::session_archive_reader::SessionArchiveReader) can decode.
pub const MIN_SUPPORTED_VERSION: u32 = 1;

/// Legacy v1 archive header (libpetri 1.5.x–1.6.x).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SessionArchiveV1 {
    pub version: u32,
    pub session_id: String,
    pub net_name: String,
    pub dot_diagram: String,
    pub start_time: String,
    pub event_count: usize,
    pub structure: NetStructure,
}

/// v2 archive header (libpetri 1.7.x). Adds end time, tags, and pre-computed
/// metadata so listing tools and samplers can filter/aggregate without scanning
/// the event body.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SessionArchiveV2 {
    pub version: u32,
    pub session_id: String,
    pub net_name: String,
    pub dot_diagram: String,
    pub start_time: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_time: Option<String>,
    pub event_count: usize,
    #[serde(default)]
    pub tags: HashMap<String, String>,
    pub metadata: SessionMetadata,
    pub structure: NetStructure,
}

/// v3 archive header (libpetri 1.8.0+). Structurally identical to v2; the version
/// bump signals that token payloads in the event body carry a `structured` JSON
/// field alongside the legacy `value` string.
///
/// Rust's writer emits v3 by default so Rust, Java, and TypeScript archives all
/// round-trip with typed token payloads (see
/// [`EVT-025`](https://github.com/libpetri/libpetri/blob/main/spec/08-events-observability.md)).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SessionArchiveV3 {
    pub version: u32,
    pub session_id: String,
    pub net_name: String,
    pub dot_diagram: String,
    pub start_time: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_time: Option<String>,
    pub event_count: usize,
    #[serde(default)]
    pub tags: HashMap<String, String>,
    pub metadata: SessionMetadata,
    pub structure: NetStructure,
}

/// Sealed archive header across all supported format versions.
///
/// Callers pattern-match to access v2/v3-only fields (`tags`, `end_time`, `metadata`).
/// Shared accessors on the enum return sensible defaults for v1 so uniform callers
/// don't need to branch.
#[derive(Debug, Clone)]
pub enum SessionArchive {
    V1(SessionArchiveV1),
    V2(SessionArchiveV2),
    V3(SessionArchiveV3),
}

impl SessionArchive {
    pub fn version(&self) -> u32 {
        match self {
            Self::V1(a) => a.version,
            Self::V2(a) => a.version,
            Self::V3(a) => a.version,
        }
    }

    pub fn session_id(&self) -> &str {
        match self {
            Self::V1(a) => &a.session_id,
            Self::V2(a) => &a.session_id,
            Self::V3(a) => &a.session_id,
        }
    }

    pub fn net_name(&self) -> &str {
        match self {
            Self::V1(a) => &a.net_name,
            Self::V2(a) => &a.net_name,
            Self::V3(a) => &a.net_name,
        }
    }

    pub fn dot_diagram(&self) -> &str {
        match self {
            Self::V1(a) => &a.dot_diagram,
            Self::V2(a) => &a.dot_diagram,
            Self::V3(a) => &a.dot_diagram,
        }
    }

    pub fn start_time(&self) -> &str {
        match self {
            Self::V1(a) => &a.start_time,
            Self::V2(a) => &a.start_time,
            Self::V3(a) => &a.start_time,
        }
    }

    pub fn event_count(&self) -> usize {
        match self {
            Self::V1(a) => a.event_count,
            Self::V2(a) => a.event_count,
            Self::V3(a) => a.event_count,
        }
    }

    pub fn structure(&self) -> &NetStructure {
        match self {
            Self::V1(a) => &a.structure,
            Self::V2(a) => &a.structure,
            Self::V3(a) => &a.structure,
        }
    }

    /// v2/v3-only. Returns `None` for v1 archives.
    pub fn end_time(&self) -> Option<&str> {
        match self {
            Self::V1(_) => None,
            Self::V2(a) => a.end_time.as_deref(),
            Self::V3(a) => a.end_time.as_deref(),
        }
    }

    /// Returns the session tags. v1 archives produce an empty static map.
    pub fn tags(&self) -> &HashMap<String, String> {
        static EMPTY: OnceLock<HashMap<String, String>> = OnceLock::new();
        match self {
            Self::V1(_) => EMPTY.get_or_init(HashMap::new),
            Self::V2(a) => &a.tags,
            Self::V3(a) => &a.tags,
        }
    }

    /// Pre-computed aggregate stats. `None` for v1 archives — callers that need
    /// them for a v1 session should call
    /// [`compute_metadata`](super::session_metadata::compute_metadata) on the
    /// event store after [`SessionArchiveReader::read_full`](super::session_archive_reader::SessionArchiveReader::read_full).
    pub fn metadata(&self) -> Option<&SessionMetadata> {
        match self {
            Self::V1(_) => None,
            Self::V2(a) => Some(&a.metadata),
            Self::V3(a) => Some(&a.metadata),
        }
    }
}

/// Pre-computed aggregate statistics attached to a v2 session archive header.
///
/// Computed once during archive write by a single-pass scan of the event store.
/// Readers can answer `has_errors`, histogram, and first/last timestamp queries
/// without iterating the event stream — enabling cheap triage, sampling, and
/// listing of many archives.
///
/// `BTreeMap` for the histogram guarantees deterministic JSON key order (matches
/// Java's `TreeMap` and TypeScript's alphabetical sort).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SessionMetadata {
    #[serde(default)]
    pub event_type_histogram: BTreeMap<String, u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_event_time: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_event_time: Option<String>,
    #[serde(default)]
    pub has_errors: bool,
}

impl SessionMetadata {
    /// Returns a `SessionMetadata` with no data. Used as a default for empty
    /// sessions and as the fallback for v1 archive imports.
    pub fn empty() -> Self {
        Self::default()
    }
}
