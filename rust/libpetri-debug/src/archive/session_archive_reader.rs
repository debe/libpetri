//! Reads session archives from length-prefixed binary format.
//!
//! Handles v1 (libpetri 1.5.x–1.6.x), v2 (libpetri 1.7.x), and v3 (libpetri
//! 1.8.0+) archives via a lenient version probe: deserialize the header bytes
//! into a minimal [`VersionProbe`] struct, switch on the integer tag, and
//! re-parse the full header into the correct concrete type. Events inside the
//! body share the same wire format across versions (the `structured` token
//! field is serde-optional) so the event read path is shared.

use std::any::Any;
use std::io::Read;
use std::sync::Arc;

use flate2::read::GzDecoder;
use libpetri_event::token_payload::TokenPayload;
use serde::Deserialize;

use crate::debug_event_store::DebugEventStore;
use crate::debug_response::NetEventInfo;

use super::session_archive::{
    CURRENT_VERSION, MIN_SUPPORTED_VERSION, SessionArchive, SessionArchiveV1, SessionArchiveV2,
    SessionArchiveV3,
};

/// Result of importing a session archive.
pub struct ImportedSession {
    pub metadata: SessionArchive,
    pub event_store: Arc<DebugEventStore>,
}

/// Maximum size for a single event in the archive.
const MAX_EVENT_SIZE: u32 = 10 * 1024 * 1024; // 10 MB

/// Minimal DTO used to peek the archive `version` field before the full
/// header parse. Kept separate so we never partially-parse a v2 archive as v1.
#[derive(Deserialize)]
struct VersionProbe {
    version: u32,
}

/// Reads session archives.
pub struct SessionArchiveReader;

impl SessionArchiveReader {
    /// Reads only the metadata header from an archive.
    pub fn read_metadata(compressed: &[u8]) -> Result<SessionArchive, String> {
        let mut decoder = GzDecoder::new(compressed);
        let mut data = Vec::new();
        decoder.read_to_end(&mut data).map_err(|e| e.to_string())?;

        if data.len() < 4 {
            return Err("Archive too small".into());
        }

        let meta_len = u32::from_be_bytes([data[0], data[1], data[2], data[3]]) as usize;
        if 4 + meta_len > data.len() {
            return Err("Metadata length exceeds data".into());
        }

        parse_header(&data[4..4 + meta_len])
    }

    /// Reads the full archive: metadata + all events into a `DebugEventStore`.
    pub fn read_full(compressed: &[u8]) -> Result<ImportedSession, String> {
        let mut decoder = GzDecoder::new(compressed);
        let mut data = Vec::new();
        decoder.read_to_end(&mut data).map_err(|e| e.to_string())?;

        let mut offset = 0;

        // Read metadata
        if offset + 4 > data.len() {
            return Err("Archive too small".into());
        }
        let meta_len = u32::from_be_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]) as usize;
        offset += 4;

        if offset + meta_len > data.len() {
            return Err("Metadata length exceeds data".into());
        }
        let metadata = parse_header(&data[offset..offset + meta_len])?;
        offset += meta_len;

        // Read events — same wire format across versions.
        let event_store = Arc::new(DebugEventStore::with_capacity(
            metadata.session_id().to_string(),
            usize::MAX,
        ));

        while offset < data.len() {
            if offset + 4 > data.len() {
                return Err(format!(
                    "Truncated archive: expected event length prefix at offset {offset}, have only {} bytes remaining",
                    data.len() - offset
                ));
            }
            let event_len = u32::from_be_bytes([
                data[offset],
                data[offset + 1],
                data[offset + 2],
                data[offset + 3],
            ]);
            offset += 4;

            if event_len == 0 || event_len > MAX_EVENT_SIZE {
                return Err(format!("Invalid event size: {event_len}"));
            }

            let event_len = event_len as usize;
            if offset + event_len > data.len() {
                return Err(format!(
                    "Truncated archive: expected {event_len} bytes for event body at offset {offset}, have only {} bytes remaining",
                    data.len() - offset
                ));
            }

            let event_info: NetEventInfo =
                serde_json::from_slice(&data[offset..offset + event_len])
                    .map_err(|e| e.to_string())?;
            offset += event_len;

            let net_event = event_info_to_net_event(&event_info)?;
            event_store.append(net_event);
        }

        Ok(ImportedSession {
            metadata,
            event_store,
        })
    }
}

/// Peeks the archive `version` field then re-parses the full header into the
/// matching concrete type. The two-step parse avoids fragile `#[serde(untagged)]`
/// fallbacks that could silently misclassify a partial v2 as a v1 on field
/// shape alone.
fn parse_header(meta_bytes: &[u8]) -> Result<SessionArchive, String> {
    let probe: VersionProbe = serde_json::from_slice(meta_bytes).map_err(|e| e.to_string())?;
    match probe.version {
        1 => {
            let v1: SessionArchiveV1 =
                serde_json::from_slice(meta_bytes).map_err(|e| e.to_string())?;
            Ok(SessionArchive::V1(v1))
        }
        2 => {
            let v2: SessionArchiveV2 =
                serde_json::from_slice(meta_bytes).map_err(|e| e.to_string())?;
            Ok(SessionArchive::V2(v2))
        }
        3 => {
            let v3: SessionArchiveV3 =
                serde_json::from_slice(meta_bytes).map_err(|e| e.to_string())?;
            Ok(SessionArchive::V3(v3))
        }
        v => Err(format!(
            "Unsupported archive version: {v} (reader supports {MIN_SUPPORTED_VERSION}..{CURRENT_VERSION})"
        )),
    }
}

/// Converts a serialized `NetEventInfo` back to a `NetEvent`.
///
/// Returns `Err` if `info.timestamp` is not a valid `u64`. A silently defaulted
/// timestamp would corrupt the replay timeline without surfacing anything to the
/// caller, so we treat parse failures the same way we treat structural archive
/// corruption (truncated events, invalid lengths).
fn event_info_to_net_event(
    info: &NetEventInfo,
) -> Result<libpetri_event::net_event::NetEvent, String> {
    use libpetri_event::net_event::NetEvent;

    let timestamp: u64 = info.timestamp.parse().map_err(|e| {
        format!(
            "Corrupt archive: event timestamp {:?} is not a valid u64 ({e})",
            info.timestamp
        )
    })?;

    let event = match info.event_type.as_str() {
        "ExecutionStarted" => {
            let net_name = info
                .details
                .get("netName")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            NetEvent::ExecutionStarted {
                net_name: Arc::from(net_name),
                timestamp,
            }
        }
        "ExecutionCompleted" => {
            let net_name = info
                .details
                .get("netName")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            NetEvent::ExecutionCompleted {
                net_name: Arc::from(net_name),
                timestamp,
            }
        }
        "TransitionEnabled" => NetEvent::TransitionEnabled {
            transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "TransitionClockRestarted" => NetEvent::TransitionClockRestarted {
            transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "TransitionStarted" => NetEvent::TransitionStarted {
            transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "TransitionCompleted" => NetEvent::TransitionCompleted {
            transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "TransitionFailed" => {
            let error = info
                .details
                .get("errorMessage")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            NetEvent::TransitionFailed {
                transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
                error: error.to_string(),
                timestamp,
            }
        }
        "TransitionTimedOut" => NetEvent::TransitionTimedOut {
            transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "ActionTimedOut" => {
            let timeout_ms = info
                .details
                .get("timeoutMs")
                .and_then(|v| v.as_u64())
                .unwrap_or(0);
            NetEvent::ActionTimedOut {
                transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
                timeout_ms,
                timestamp,
            }
        }
        "TokenAdded" => {
            let place = Arc::from(info.place_name.as_deref().unwrap_or("unknown"));
            match hydrate_token_payload(&info) {
                Some(payload) => NetEvent::token_added_with(place, timestamp, payload),
                None => NetEvent::token_added(place, timestamp),
            }
        }
        "TokenRemoved" => {
            let place = Arc::from(info.place_name.as_deref().unwrap_or("unknown"));
            match hydrate_token_payload(&info) {
                Some(payload) => NetEvent::token_removed_with(place, timestamp, payload),
                None => NetEvent::token_removed(place, timestamp),
            }
        }
        "LogMessage" => {
            let level = info
                .details
                .get("level")
                .and_then(|v| v.as_str())
                .unwrap_or("INFO");
            let message = info
                .details
                .get("message")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            NetEvent::LogMessage {
                transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
                level: level.to_string(),
                message: message.to_string(),
                timestamp,
            }
        }
        _ => {
            // Fallback for unknown types
            NetEvent::TransitionEnabled {
                transition_name: Arc::from(info.transition_name.as_deref().unwrap_or("unknown")),
                timestamp,
            }
        }
    };
    Ok(event)
}

/// Token payload produced on the read side of a v3 archive replay.
///
/// Rust's replay reconstructs tokens as untyped JSON — we do not attempt to
/// revive the original `T` (Rust has no name → type registry equivalent to
/// Java's `Class.forName`). Consumers who need the original concrete type
/// should look up the `type_name` string and deserialize `value_json` via
/// their own `serde` registry.
#[derive(Debug, Clone)]
pub struct ReplayedTokenPayload {
    /// Fully-qualified name captured by the original writer (via
    /// [`ErasedToken::value_type_name`](libpetri_core::token::ErasedToken::value_type_name)).
    pub type_name_str: String,
    /// Structured JSON projection produced by the original writer's
    /// [`TokenProjectorRegistry`](crate::TokenProjectorRegistry). May be
    /// [`serde_json::Value::Null`] when the original archive lacked a
    /// structured field (e.g. legacy v1/v2 bodies that only carried
    /// `value`/`toString`).
    pub value_json: serde_json::Value,
}

impl TokenPayload for ReplayedTokenPayload {
    fn type_name(&self) -> &str {
        &self.type_name_str
    }

    fn value_any(&self) -> &(dyn Any + Send + Sync) {
        &self.value_json
    }
}

/// Reads the `details.token` field produced by [`to_event_info_with_registry`]
/// and returns a replay payload wrapping the structured JSON and carrier type
/// name. Returns `None` for pre-v3 archives that omit the `token` entry.
fn hydrate_token_payload(info: &NetEventInfo) -> Option<Arc<dyn TokenPayload>> {
    let token_json = info.details.get("token")?;
    let type_name_str = token_json
        .get("type")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    let value_json = token_json
        .get("structured")
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    Some(Arc::new(ReplayedTokenPayload {
        type_name_str,
        value_json,
    }))
}

#[cfg(test)]
mod tests {
    // Archive tests require the `archive` feature, which is enabled when this module is compiled.

    use super::*;
    use crate::debug_event_store::DebugEventStore;
    use crate::debug_response::NetStructure;
    use crate::debug_session_registry::DebugSession;
    use crate::place_analysis::PlaceAnalysis;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;
    use libpetri_event::net_event::NetEvent;
    use std::collections::HashMap;

    fn test_session_with_events() -> DebugSession {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let event_store = Arc::new(DebugEventStore::new("s1".into()));
        event_store.append(NetEvent::ExecutionStarted {
            net_name: Arc::from("test"),
            timestamp: 1000,
        });
        event_store.append(NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 2000,
        });
        event_store.append(NetEvent::TransitionCompleted {
            transition_name: Arc::from("t1"),
            timestamp: 3000,
        });

        let analysis = PlaceAnalysis::from_net(&net);

        DebugSession {
            session_id: "s1".into(),
            net_name: "test".into(),
            dot_diagram: "digraph test {}".into(),
            places: Some(analysis),
            transition_names: vec!["t1".into()],
            event_store,
            start_time: 1000,
            active: false,
            imported_structure: None,
            end_time: None,
            tags: HashMap::new(),
        }
    }

    // ========== existing round-trip tests, updated for accessor methods ==========

    #[test]
    fn write_and_read_metadata() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        let metadata = SessionArchiveReader::read_metadata(&compressed).unwrap();
        assert_eq!(metadata.session_id(), "s1");
        assert_eq!(metadata.net_name(), "test");
        assert_eq!(metadata.event_count(), 3);
        assert_eq!(metadata.version(), CURRENT_VERSION);
    }

    #[test]
    fn write_and_read_full() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        let imported = SessionArchiveReader::read_full(&compressed).unwrap();
        assert_eq!(imported.metadata.session_id(), "s1");
        assert_eq!(imported.event_store.event_count(), 3);

        let events = imported.event_store.events();
        assert!(matches!(events[0], NetEvent::ExecutionStarted { .. }));
        assert!(matches!(events[1], NetEvent::TransitionStarted { .. }));
        assert!(matches!(events[2], NetEvent::TransitionCompleted { .. }));
    }

    #[test]
    fn read_full_rejects_corrupt_timestamp() {
        use flate2::Compression;
        use flate2::write::GzEncoder;
        use std::io::Write;

        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        // Decompress so we can hand-edit the on-wire bytes.
        let mut decoder = GzDecoder::new(&compressed[..]);
        let mut raw = Vec::new();
        decoder.read_to_end(&mut raw).unwrap();

        // Find the first occurrence of `"timestamp":"1000"` (from test_session_with_events)
        // and replace it with a non-numeric string of the same length so every length prefix
        // in the archive stays valid — we are testing parse failure, not structural corruption.
        let needle = br#""timestamp":"1000""#;
        let replacement = br#""timestamp":"abcd""#;
        assert_eq!(needle.len(), replacement.len());
        let pos = raw
            .windows(needle.len())
            .position(|w| w == needle)
            .expect("test fixture must contain a 1000 timestamp");
        raw[pos..pos + needle.len()].copy_from_slice(replacement);

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&raw).unwrap();
        let corrupted = encoder.finish().unwrap();

        let err = match SessionArchiveReader::read_full(&corrupted) {
            Ok(_) => panic!("corrupt timestamp must surface as an error, not a zero default"),
            Err(e) => e,
        };
        assert!(
            err.contains("Corrupt archive") && err.contains("timestamp"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn read_full_rejects_truncated_event() {
        use flate2::Compression;
        use flate2::write::GzEncoder;
        use std::io::Write;

        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        let mut decoder = GzDecoder::new(&compressed[..]);
        let mut raw = Vec::new();
        decoder.read_to_end(&mut raw).unwrap();

        // Truncate the last 5 bytes — leaves the final event body incomplete.
        let truncate_to = raw.len() - 5;
        raw.truncate(truncate_to);

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&raw).unwrap();
        let truncated_compressed = encoder.finish().unwrap();

        let err = match SessionArchiveReader::read_full(&truncated_compressed) {
            Ok(_) => panic!("expected error reading truncated archive"),
            Err(e) => e,
        };
        assert!(
            err.to_lowercase().contains("truncated"),
            "expected truncation error, got: {err}"
        );
    }

    #[test]
    fn round_trip_all_event_types() {
        let event_store = Arc::new(DebugEventStore::new("s2".into()));
        event_store.append(NetEvent::ExecutionStarted {
            net_name: Arc::from("n"),
            timestamp: 0,
        });
        event_store.append(NetEvent::TransitionEnabled {
            transition_name: Arc::from("t"),
            timestamp: 1,
        });
        event_store.append(NetEvent::TransitionStarted {
            transition_name: Arc::from("t"),
            timestamp: 2,
        });
        event_store.append(NetEvent::TransitionCompleted {
            transition_name: Arc::from("t"),
            timestamp: 3,
        });
        event_store.append(NetEvent::TransitionFailed {
            transition_name: Arc::from("t"),
            error: "err".into(),
            timestamp: 4,
        });
        event_store.append(NetEvent::token_added(Arc::from("p"), 5));
        event_store.append(NetEvent::token_removed(Arc::from("p"), 6));
        event_store.append(NetEvent::ActionTimedOut {
            transition_name: Arc::from("t"),
            timeout_ms: 100,
            timestamp: 7,
        });
        event_store.append(NetEvent::LogMessage {
            transition_name: Arc::from("t"),
            level: "INFO".into(),
            message: "msg".into(),
            timestamp: 8,
        });
        event_store.append(NetEvent::ExecutionCompleted {
            net_name: Arc::from("n"),
            timestamp: 9,
        });

        let session = DebugSession {
            session_id: "s2".into(),
            net_name: "test".into(),
            dot_diagram: "digraph {}".into(),
            places: None,
            transition_names: vec!["t".into()],
            event_store,
            start_time: 0,
            active: false,
            imported_structure: Some(NetStructure {
                places: vec![],
                transitions: vec![],
            }),
            end_time: None,
            tags: HashMap::new(),
        };

        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();
        assert_eq!(imported.event_store.event_count(), 10);
    }

    // ========== v2-specific tests (libpetri 1.7.0) ==========

    fn session_with_tags(tags: HashMap<String, String>) -> DebugSession {
        let mut session = test_session_with_events();
        session.tags = tags;
        session.end_time = Some(5000);
        session
    }

    #[test]
    fn default_write_is_v3() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let metadata = SessionArchiveReader::read_metadata(&compressed).unwrap();
        assert_eq!(metadata.version(), 3);
        assert!(matches!(metadata, SessionArchive::V3(_)));
    }

    #[test]
    fn default_write_round_trip_preserves_tags_and_end_time() {
        let mut tags = HashMap::new();
        tags.insert("channel".to_string(), "voice".to_string());
        tags.insert("env".to_string(), "staging".to_string());

        let session = session_with_tags(tags.clone());
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected v3");
        };
        assert_eq!(v3.tags, tags);
        assert_eq!(v3.end_time, Some("5000".to_string()));
    }

    #[test]
    fn default_write_metadata_histogram_matches_events() {
        let session = test_session_with_events();
        // test_session_with_events appends: ExecutionStarted, TransitionStarted, TransitionCompleted.
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected v3");
        };
        assert_eq!(
            v3.metadata.event_type_histogram.get("ExecutionStarted"),
            Some(&1)
        );
        assert_eq!(
            v3.metadata.event_type_histogram.get("TransitionStarted"),
            Some(&1)
        );
        assert_eq!(
            v3.metadata.event_type_histogram.get("TransitionCompleted"),
            Some(&1)
        );
        assert_eq!(v3.metadata.first_event_time, Some("1000".to_string()));
        assert_eq!(v3.metadata.last_event_time, Some("3000".to_string()));
        assert!(!v3.metadata.has_errors);
    }

    #[test]
    fn default_write_has_errors_for_transition_failed() {
        let session = test_session_with_events();
        session.event_store.append(NetEvent::TransitionFailed {
            transition_name: Arc::from("t1"),
            error: "boom".into(),
            timestamp: 4000,
        });

        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected v3");
        };
        assert!(v3.metadata.has_errors);
    }

    #[test]
    fn default_write_has_errors_for_log_at_error_level() {
        let session = test_session_with_events();
        session.event_store.append(NetEvent::LogMessage {
            transition_name: Arc::from("t1"),
            level: "ERROR".to_string(),
            message: "boom".to_string(),
            timestamp: 4000,
        });

        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected v3");
        };
        assert!(v3.metadata.has_errors);
    }

    #[test]
    fn default_write_has_errors_for_log_at_lowercase_error_level() {
        let session = test_session_with_events();
        session.event_store.append(NetEvent::LogMessage {
            transition_name: Arc::from("t1"),
            level: "error".to_string(),
            message: "boom".to_string(),
            timestamp: 4000,
        });

        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected v3");
        };
        assert!(v3.metadata.has_errors);
    }

    #[test]
    fn write_v1_produces_v1_archive() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write_v1(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        assert!(matches!(imported.metadata, SessionArchive::V1(_)));
        assert_eq!(imported.metadata.version(), 1);
        assert_eq!(imported.metadata.session_id(), "s1");
        assert_eq!(imported.event_store.event_count(), 3);
        // v1 accessors return defaults
        assert!(imported.metadata.end_time().is_none());
        assert!(imported.metadata.tags().is_empty());
        assert!(imported.metadata.metadata().is_none());
    }

    #[test]
    fn reader_handles_mixed_v1_v2_v3_archives() {
        let session = test_session_with_events();
        let v1_bytes = super::super::SessionArchiveWriter::write_v1(&session).unwrap();
        let v2_bytes = super::super::SessionArchiveWriter::write_v2(&session).unwrap();
        let v3_bytes = super::super::SessionArchiveWriter::write(&session).unwrap();

        let v1 = SessionArchiveReader::read_full(&v1_bytes).unwrap();
        let v2 = SessionArchiveReader::read_full(&v2_bytes).unwrap();
        let v3 = SessionArchiveReader::read_full(&v3_bytes).unwrap();

        assert!(matches!(v1.metadata, SessionArchive::V1(_)));
        assert!(matches!(v2.metadata, SessionArchive::V2(_)));
        assert!(matches!(v3.metadata, SessionArchive::V3(_)));
        assert_eq!(v1.event_store.event_count(), 3);
        assert_eq!(v2.event_store.event_count(), 3);
        assert_eq!(v3.event_store.event_count(), 3);
    }

    #[test]
    fn reader_accepts_v3_archives() {
        use flate2::Compression;
        use flate2::write::GzEncoder;
        use std::io::Write;

        // Hand-crafted v3 archive so the test is not coupled to the Rust writer —
        // asserts that a third-party v3 archive round-trips with the payload hydrated.
        let v3_header = br#"{"version":3,"sessionId":"v3-rust","netName":"n","dotDiagram":"digraph{}","startTime":"0","endTime":"5000","eventCount":1,"tags":{"channel":"voice"},"metadata":{"eventTypeHistogram":{"TokenAdded":1},"firstEventTime":"1000","lastEventTime":"1000","hasErrors":false},"structure":{"places":[],"transitions":[]}}"#;
        let event = br#"{"type":"TokenAdded","timestamp":"1000","transitionName":null,"placeName":"P","details":{"token":{"id":null,"type":"TestMessage","value":"TestMessage{...}","structured":{"kind":"USER","text":"hi"},"timestamp":"1000"}}}"#;

        let mut raw = Vec::new();
        raw.extend_from_slice(&(v3_header.len() as u32).to_be_bytes());
        raw.extend_from_slice(v3_header);
        raw.extend_from_slice(&(event.len() as u32).to_be_bytes());
        raw.extend_from_slice(event);

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&raw).unwrap();
        let compressed = encoder.finish().unwrap();

        let imported = SessionArchiveReader::read_full(&compressed)
            .expect("v3 archive must be readable on the Rust reader");

        let SessionArchive::V3(v3) = &imported.metadata else {
            panic!("expected V3 subtype, got {:?}", imported.metadata);
        };
        assert_eq!(v3.session_id, "v3-rust");
        assert_eq!(v3.tags.get("channel"), Some(&"voice".to_string()));
        assert_eq!(v3.end_time.as_deref(), Some("5000"));
        assert_eq!(v3.metadata.event_type_histogram.get("TokenAdded"), Some(&1));
        assert_eq!(imported.event_store.event_count(), 1);

        // The hydrated event should carry a TokenPayload whose type_name and
        // structured JSON survived the round-trip.
        let events = imported.event_store.events();
        let NetEvent::TokenAdded { token, .. } = &events[0] else {
            panic!("expected TokenAdded, got {:?}", events[0]);
        };
        let payload = token.as_ref().expect("token payload must be hydrated on v3");
        assert_eq!(payload.type_name(), "TestMessage");
        let value_json = payload
            .value_any()
            .downcast_ref::<serde_json::Value>()
            .expect("replay payload must carry serde_json::Value");
        assert_eq!(value_json["kind"], "USER");
        assert_eq!(value_json["text"], "hi");
    }

    #[test]
    fn v3_roundtrip_preserves_structured_token() {
        use crate::TokenProjectorRegistry;
        use libpetri_core::token::{ErasedToken, Token};

        #[derive(serde::Serialize, serde::Deserialize, Debug)]
        struct Message {
            kind: String,
            text: String,
        }

        // 1. Build a session with a real typed-token event.
        let event_store = Arc::new(DebugEventStore::new("v3-rt".into()));
        let erased = ErasedToken::from_typed(&Token::new(Message {
            kind: "USER".into(),
            text: "hi".into(),
        }));
        let payload: Arc<dyn TokenPayload> = Arc::new(erased);
        event_store.append(NetEvent::token_added_with(
            Arc::from("P"),
            1000,
            Arc::clone(&payload),
        ));

        let session = DebugSession {
            session_id: "v3-rt".into(),
            net_name: "n".into(),
            dot_diagram: "digraph {}".into(),
            places: None,
            transition_names: vec![],
            event_store,
            start_time: 0,
            active: false,
            imported_structure: Some(NetStructure {
                places: vec![],
                transitions: vec![],
            }),
            end_time: Some(5000),
            tags: HashMap::new(),
        };

        // 2. Register the token type so `structured` contains typed JSON.
        let registry = TokenProjectorRegistry::new();
        registry.register::<Message>();

        // 3. Write via the registry-aware writer, read back, assert structured JSON survives.
        let compressed =
            super::super::SessionArchiveWriter::write_with_registry(&session, &registry).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();

        assert!(matches!(imported.metadata, SessionArchive::V3(_)));
        let events = imported.event_store.events();
        let NetEvent::TokenAdded { token, .. } = &events[0] else {
            panic!("expected TokenAdded, got {:?}", events[0]);
        };
        let hydrated = token.as_ref().expect("payload must hydrate");
        let value_json = hydrated
            .value_any()
            .downcast_ref::<serde_json::Value>()
            .expect("replay payload carries serde_json::Value");
        assert_eq!(value_json["kind"], "USER");
        assert_eq!(value_json["text"], "hi");
    }

    #[test]
    fn v2_writer_still_produces_v2_header() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write_v2(&session).unwrap();
        let metadata = SessionArchiveReader::read_metadata(&compressed).unwrap();
        assert_eq!(metadata.version(), 2);
        assert!(matches!(metadata, SessionArchive::V2(_)));
    }

    #[test]
    fn read_rejects_unsupported_version() {
        use flate2::Compression;
        use flate2::write::GzEncoder;
        use std::io::Write;

        // Hand-build a header with version=99.
        let header_json =
            br#"{"version":99,"sessionId":"x","netName":"n","dotDiagram":"digraph{}","startTime":"0","eventCount":0,"structure":{"places":[],"transitions":[]}}"#;
        let mut raw = Vec::new();
        raw.extend_from_slice(&(header_json.len() as u32).to_be_bytes());
        raw.extend_from_slice(header_json);

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&raw).unwrap();
        let compressed = encoder.finish().unwrap();

        let err = SessionArchiveReader::read_metadata(&compressed).unwrap_err();
        assert!(
            err.contains("Unsupported archive version: 99"),
            "unexpected error: {err}"
        );
        assert!(
            err.contains(&format!(
                "{}..{}",
                MIN_SUPPORTED_VERSION, CURRENT_VERSION
            )),
            "expected supported-version range in error: {err}"
        );
    }
}
