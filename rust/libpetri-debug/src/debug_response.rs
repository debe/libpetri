//! Responses sent from server to debug UI client via WebSocket.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::debug_command::{BreakpointConfig, EventFilter};

/// Summary of a debug session.
///
/// `tags`, `end_time`, and `duration_ms` were added in libpetri 1.6.0. Older clients that
/// do not know these fields ignore them (serde tolerance).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct SessionSummary {
    pub session_id: String,
    pub net_name: String,
    pub start_time: String,
    pub active: bool,
    pub event_count: usize,
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub tags: HashMap<String, String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_time: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

/// Serializable token information.
///
/// `structured` (libpetri 1.8.0+) carries a typed JSON projection of the token
/// value produced by [`TokenProjectorRegistry`](crate::TokenProjectorRegistry).
/// Populated alongside `value` (not instead of) so the bundled debug UI keeps
/// rendering unchanged while LLM-facing consumers get typed fields. Omitted
/// from the wire when absent.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TokenInfo {
    pub id: Option<String>,
    #[serde(rename = "type")]
    pub token_type: String,
    pub value: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub structured: Option<serde_json::Value>,
    pub timestamp: Option<String>,
}

/// Serializable event information.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetEventInfo {
    #[serde(rename = "type")]
    pub event_type: String,
    pub timestamp: String,
    pub transition_name: Option<String>,
    pub place_name: Option<String>,
    pub details: HashMap<String, serde_json::Value>,
}

/// Information about a place in the net structure.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PlaceInfo {
    pub name: String,
    pub graph_id: String,
    pub token_type: String,
    pub is_start: bool,
    pub is_end: bool,
    pub is_environment: bool,
}

/// Information about a transition in the net structure.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransitionInfo {
    pub name: String,
    pub graph_id: String,
}

/// Structure of a Petri net for the debug UI.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetStructure {
    pub places: Vec<PlaceInfo>,
    pub transitions: Vec<TransitionInfo>,
}

/// Summary of an archived session.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchiveSummary {
    pub session_id: String,
    pub key: String,
    pub size_bytes: u64,
    pub last_modified: String,
}

/// Responses from server to debug UI client.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase", rename_all_fields = "camelCase")]
pub enum DebugResponse {
    SessionList {
        sessions: Vec<SessionSummary>,
    },
    Subscribed {
        session_id: String,
        net_name: String,
        dot_diagram: String,
        structure: NetStructure,
        current_marking: HashMap<String, Vec<TokenInfo>>,
        enabled_transitions: Vec<String>,
        in_flight_transitions: Vec<String>,
        event_count: usize,
        mode: String,
    },
    Unsubscribed {
        session_id: String,
    },
    Event {
        session_id: String,
        index: usize,
        event: NetEventInfo,
    },
    EventBatch {
        session_id: String,
        start_index: usize,
        events: Vec<NetEventInfo>,
        has_more: bool,
    },
    MarkingSnapshot {
        session_id: String,
        marking: HashMap<String, Vec<TokenInfo>>,
        enabled_transitions: Vec<String>,
        in_flight_transitions: Vec<String>,
    },
    PlaybackStateChanged {
        session_id: String,
        paused: bool,
        speed: f64,
        current_index: usize,
    },
    FilterApplied {
        session_id: String,
        filter: EventFilter,
    },
    BreakpointHit {
        session_id: String,
        breakpoint_id: String,
        event: NetEventInfo,
        event_index: usize,
    },
    BreakpointList {
        session_id: String,
        breakpoints: Vec<BreakpointConfig>,
    },
    BreakpointSet {
        session_id: String,
        breakpoint: BreakpointConfig,
    },
    BreakpointCleared {
        session_id: String,
        breakpoint_id: String,
    },
    Error {
        code: String,
        message: String,
        session_id: Option<String>,
    },
    ArchiveList {
        archives: Vec<ArchiveSummary>,
        storage_available: bool,
    },
    ArchiveImported {
        session_id: String,
        net_name: String,
        event_count: usize,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde_round_trip_session_list() {
        let resp = DebugResponse::SessionList {
            sessions: vec![SessionSummary {
                session_id: "s1".into(),
                net_name: "test".into(),
                start_time: "2025-01-01T00:00:00Z".into(),
                active: true,
                event_count: 42,
                ..Default::default()
            }],
        };
        let json = serde_json::to_string(&resp).unwrap();
        assert!(json.contains("\"type\":\"sessionList\""));
        // New 1.6.0 fields are omitted when unset (skip_serializing_if)
        assert!(!json.contains("\"tags\""));
        assert!(!json.contains("\"endTime\""));
        assert!(!json.contains("\"durationMs\""));
        let back: DebugResponse = serde_json::from_str(&json).unwrap();
        match back {
            DebugResponse::SessionList { sessions } => {
                assert_eq!(sessions.len(), 1);
                assert_eq!(sessions[0].session_id, "s1");
                assert!(sessions[0].tags.is_empty());
                assert!(sessions[0].end_time.is_none());
                assert!(sessions[0].duration_ms.is_none());
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn serde_round_trip_session_summary_with_1_6_0_fields() {
        let mut tags = HashMap::new();
        tags.insert("channel".to_string(), "voice".to_string());
        tags.insert("env".to_string(), "staging".to_string());

        let summary = SessionSummary {
            session_id: "s1".into(),
            net_name: "test".into(),
            start_time: "1000".into(),
            active: false,
            event_count: 42,
            tags,
            end_time: Some("2500".into()),
            duration_ms: Some(1500),
        };
        let json = serde_json::to_string(&summary).unwrap();

        assert!(json.contains("\"tags\""));
        assert!(json.contains("\"channel\":\"voice\""));
        assert!(json.contains("\"endTime\":\"2500\""));
        assert!(json.contains("\"durationMs\":1500"));

        let back: SessionSummary = serde_json::from_str(&json).unwrap();
        assert_eq!(back.session_id, "s1");
        assert_eq!(back.end_time, Some("2500".into()));
        assert_eq!(back.duration_ms, Some(1500));
        assert_eq!(back.tags.get("channel"), Some(&"voice".to_string()));
        assert_eq!(back.tags.get("env"), Some(&"staging".to_string()));
    }

    #[test]
    fn serde_deserialize_session_summary_tolerates_missing_1_6_0_fields() {
        // An old-format payload (pre-1.6.0) must deserialize cleanly.
        let json = r#"{
            "sessionId": "s1",
            "netName": "test",
            "startTime": "1000",
            "active": true,
            "eventCount": 0
        }"#;
        let summary: SessionSummary = serde_json::from_str(json).unwrap();
        assert_eq!(summary.session_id, "s1");
        assert!(summary.tags.is_empty());
        assert!(summary.end_time.is_none());
        assert!(summary.duration_ms.is_none());
    }

    #[test]
    fn serde_round_trip_subscribed() {
        let resp = DebugResponse::Subscribed {
            session_id: "s1".into(),
            net_name: "test".into(),
            dot_diagram: "digraph {}".into(),
            structure: NetStructure {
                places: vec![PlaceInfo {
                    name: "p1".into(),
                    graph_id: "p_p1".into(),
                    token_type: "i32".into(),
                    is_start: true,
                    is_end: false,
                    is_environment: false,
                }],
                transitions: vec![TransitionInfo {
                    name: "t1".into(),
                    graph_id: "t_t1".into(),
                }],
            },
            current_marking: HashMap::new(),
            enabled_transitions: vec!["t1".into()],
            in_flight_transitions: vec![],
            event_count: 5,
            mode: "live".into(),
        };
        let json = serde_json::to_string(&resp).unwrap();
        assert!(json.contains("\"type\":\"subscribed\""));
        let _back: DebugResponse = serde_json::from_str(&json).unwrap();
    }

    #[test]
    fn serde_round_trip_error() {
        let resp = DebugResponse::Error {
            code: "NOT_FOUND".into(),
            message: "Session not found".into(),
            session_id: Some("s1".into()),
        };
        let json = serde_json::to_string(&resp).unwrap();
        let back: DebugResponse = serde_json::from_str(&json).unwrap();
        match back {
            DebugResponse::Error {
                code,
                message,
                session_id,
            } => {
                assert_eq!(code, "NOT_FOUND");
                assert_eq!(message, "Session not found");
                assert_eq!(session_id, Some("s1".into()));
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn serde_response_inline_fields_use_camelcase() {
        // Cross-language interop: inline enum-variant fields must serialize as camelCase
        // so the TypeScript debug-ui (and Java client) can parse them.
        let resp = DebugResponse::Subscribed {
            session_id: "s1".into(),
            net_name: "test".into(),
            dot_diagram: "digraph {}".into(),
            structure: NetStructure {
                places: vec![],
                transitions: vec![],
            },
            current_marking: HashMap::new(),
            enabled_transitions: vec!["t1".into()],
            in_flight_transitions: vec![],
            event_count: 5,
            mode: "live".into(),
        };
        let json = serde_json::to_string(&resp).unwrap();
        assert!(json.contains("\"sessionId\":\"s1\""));
        assert!(json.contains("\"netName\":\"test\""));
        assert!(json.contains("\"dotDiagram\""));
        assert!(json.contains("\"currentMarking\""));
        assert!(json.contains("\"enabledTransitions\""));
        assert!(json.contains("\"inFlightTransitions\""));
        assert!(json.contains("\"eventCount\":5"));
        assert!(!json.contains("\"session_id\""));
        assert!(!json.contains("\"net_name\""));
        assert!(!json.contains("\"event_count\""));
    }

    #[test]
    fn serde_event_batch_camelcase_interop() {
        // Cross-language interop: a Java/TS-shaped EventBatch payload must deserialize.
        let json = r#"{"type":"eventBatch","sessionId":"s1","startIndex":0,"events":[],"hasMore":true}"#;
        let resp: DebugResponse = serde_json::from_str(json).unwrap();
        match resp {
            DebugResponse::EventBatch {
                session_id,
                start_index,
                has_more,
                ..
            } => {
                assert_eq!(session_id, "s1");
                assert_eq!(start_index, 0);
                assert!(has_more);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn serde_all_response_variants() {
        let responses: Vec<DebugResponse> = vec![
            DebugResponse::SessionList { sessions: vec![] },
            DebugResponse::Unsubscribed {
                session_id: "s1".into(),
            },
            DebugResponse::Event {
                session_id: "s1".into(),
                index: 0,
                event: NetEventInfo {
                    event_type: "TransitionStarted".into(),
                    timestamp: "2025-01-01T00:00:00Z".into(),
                    transition_name: Some("t1".into()),
                    place_name: None,
                    details: HashMap::new(),
                },
            },
            DebugResponse::EventBatch {
                session_id: "s1".into(),
                start_index: 0,
                events: vec![],
                has_more: false,
            },
            DebugResponse::MarkingSnapshot {
                session_id: "s1".into(),
                marking: HashMap::new(),
                enabled_transitions: vec![],
                in_flight_transitions: vec![],
            },
            DebugResponse::PlaybackStateChanged {
                session_id: "s1".into(),
                paused: true,
                speed: 1.0,
                current_index: 0,
            },
            DebugResponse::FilterApplied {
                session_id: "s1".into(),
                filter: EventFilter::all(),
            },
            DebugResponse::BreakpointList {
                session_id: "s1".into(),
                breakpoints: vec![],
            },
            DebugResponse::BreakpointCleared {
                session_id: "s1".into(),
                breakpoint_id: "bp1".into(),
            },
            DebugResponse::Error {
                code: "ERR".into(),
                message: "msg".into(),
                session_id: None,
            },
            DebugResponse::ArchiveList {
                archives: vec![],
                storage_available: false,
            },
            DebugResponse::ArchiveImported {
                session_id: "s1".into(),
                net_name: "test".into(),
                event_count: 10,
            },
        ];
        for resp in responses {
            let json = serde_json::to_string(&resp).unwrap();
            let _back: DebugResponse = serde_json::from_str(&json).unwrap();
        }
    }
}
