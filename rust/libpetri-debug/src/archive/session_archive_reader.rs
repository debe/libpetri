//! Reads session archives from length-prefixed binary format.

use std::io::Read;
use std::sync::Arc;

use flate2::read::GzDecoder;

use crate::debug_event_store::DebugEventStore;
use crate::debug_response::NetEventInfo;

use super::session_archive::{CURRENT_VERSION, SessionArchive};

/// Result of importing a session archive.
pub struct ImportedSession {
    pub metadata: SessionArchive,
    pub event_store: Arc<DebugEventStore>,
}

/// Maximum size for a single event in the archive.
const MAX_EVENT_SIZE: u32 = 10 * 1024 * 1024; // 10 MB

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

        let metadata: SessionArchive =
            serde_json::from_slice(&data[4..4 + meta_len]).map_err(|e| e.to_string())?;
        if metadata.version != CURRENT_VERSION {
            return Err(format!(
                "Unsupported archive version: {} (expected {CURRENT_VERSION})",
                metadata.version
            ));
        }

        Ok(metadata)
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
        let metadata: SessionArchive =
            serde_json::from_slice(&data[offset..offset + meta_len]).map_err(|e| e.to_string())?;
        offset += meta_len;

        if metadata.version != CURRENT_VERSION {
            return Err(format!(
                "Unsupported archive version: {} (expected {CURRENT_VERSION})",
                metadata.version
            ));
        }

        // Read events
        let event_store = Arc::new(DebugEventStore::with_capacity(
            metadata.session_id.clone(),
            usize::MAX,
        ));

        while offset < data.len() {
            if offset + 4 > data.len() {
                break;
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
                break;
            }

            let event_info: NetEventInfo =
                serde_json::from_slice(&data[offset..offset + event_len])
                    .map_err(|e| e.to_string())?;
            offset += event_len;

            let net_event = event_info_to_net_event(&event_info);
            event_store.append(net_event);
        }

        Ok(ImportedSession {
            metadata,
            event_store,
        })
    }
}

/// Converts a serialized `NetEventInfo` back to a `NetEvent`.
fn event_info_to_net_event(info: &NetEventInfo) -> libpetri_event::net_event::NetEvent {
    use libpetri_event::net_event::NetEvent;

    let timestamp: u64 = info.timestamp.parse().unwrap_or(0);

    match info.event_type.as_str() {
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
        "TokenAdded" => NetEvent::TokenAdded {
            place_name: Arc::from(info.place_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
        "TokenRemoved" => NetEvent::TokenRemoved {
            place_name: Arc::from(info.place_name.as_deref().unwrap_or("unknown")),
            timestamp,
        },
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
    }
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
        }
    }

    #[test]
    fn write_and_read_metadata() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        let metadata = SessionArchiveReader::read_metadata(&compressed).unwrap();
        assert_eq!(metadata.session_id, "s1");
        assert_eq!(metadata.net_name, "test");
        assert_eq!(metadata.event_count, 3);
        assert_eq!(metadata.version, CURRENT_VERSION);
    }

    #[test]
    fn write_and_read_full() {
        let session = test_session_with_events();
        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();

        let imported = SessionArchiveReader::read_full(&compressed).unwrap();
        assert_eq!(imported.metadata.session_id, "s1");
        assert_eq!(imported.event_store.event_count(), 3);

        let events = imported.event_store.events();
        assert!(matches!(events[0], NetEvent::ExecutionStarted { .. }));
        assert!(matches!(events[1], NetEvent::TransitionStarted { .. }));
        assert!(matches!(events[2], NetEvent::TransitionCompleted { .. }));
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
        event_store.append(NetEvent::TokenAdded {
            place_name: Arc::from("p"),
            timestamp: 5,
        });
        event_store.append(NetEvent::TokenRemoved {
            place_name: Arc::from("p"),
            timestamp: 6,
        });
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
        };

        let compressed = super::super::SessionArchiveWriter::write(&session).unwrap();
        let imported = SessionArchiveReader::read_full(&compressed).unwrap();
        assert_eq!(imported.event_store.event_count(), 10);
    }
}
