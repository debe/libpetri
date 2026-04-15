//! Commands sent from debug UI client to server via WebSocket.

use serde::{Deserialize, Serialize};

/// Subscription mode for a debug session.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SubscriptionMode {
    Live,
    Replay,
}

/// Breakpoint trigger types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum BreakpointType {
    TransitionEnabled,
    TransitionStart,
    TransitionComplete,
    TransitionFail,
    TokenAdded,
    TokenRemoved,
}

/// Configuration for a single breakpoint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BreakpointConfig {
    pub id: String,
    #[serde(rename = "type")]
    pub bp_type: BreakpointType,
    pub target: Option<String>,
    pub enabled: bool,
}

/// Event filter for restricting which events are delivered.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EventFilter {
    pub event_types: Option<Vec<String>>,
    pub transition_names: Option<Vec<String>>,
    pub place_names: Option<Vec<String>>,
    #[serde(default)]
    pub exclude_event_types: Option<Vec<String>>,
    #[serde(default)]
    pub exclude_transition_names: Option<Vec<String>>,
    #[serde(default)]
    pub exclude_place_names: Option<Vec<String>>,
}

impl EventFilter {
    /// Creates a filter that matches all events.
    pub fn all() -> Self {
        Self::default()
    }
}

/// Commands from debug UI client to server.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase", rename_all_fields = "camelCase")]
pub enum DebugCommand {
    ListSessions {
        limit: Option<usize>,
        active_only: Option<bool>,
        /// Optional tag filter (AND semantics). Empty or missing matches all. (libpetri 1.6.0+)
        #[serde(default, skip_serializing_if = "Option::is_none")]
        tag_filter: Option<std::collections::HashMap<String, String>>,
    },
    Subscribe {
        session_id: String,
        mode: SubscriptionMode,
        from_index: Option<usize>,
    },
    Unsubscribe {
        session_id: String,
    },
    Seek {
        session_id: String,
        timestamp: String,
    },
    PlaybackSpeed {
        session_id: String,
        speed: f64,
    },
    Filter {
        session_id: String,
        filter: EventFilter,
    },
    Pause {
        session_id: String,
    },
    Resume {
        session_id: String,
    },
    StepForward {
        session_id: String,
    },
    StepBackward {
        session_id: String,
    },
    SetBreakpoint {
        session_id: String,
        breakpoint: BreakpointConfig,
    },
    ClearBreakpoint {
        session_id: String,
        breakpoint_id: String,
    },
    ListBreakpoints {
        session_id: String,
    },
    ListArchives {
        limit: Option<usize>,
        prefix: Option<String>,
    },
    ImportArchive {
        session_id: String,
    },
    UploadArchive {
        file_name: String,
        data: String,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde_round_trip_subscribe() {
        let cmd = DebugCommand::Subscribe {
            session_id: "s1".into(),
            mode: SubscriptionMode::Live,
            from_index: Some(10),
        };
        let json = serde_json::to_string(&cmd).unwrap();
        assert!(json.contains("\"type\":\"subscribe\""));
        let back: DebugCommand = serde_json::from_str(&json).unwrap();
        match back {
            DebugCommand::Subscribe {
                session_id,
                mode,
                from_index,
            } => {
                assert_eq!(session_id, "s1");
                assert_eq!(mode, SubscriptionMode::Live);
                assert_eq!(from_index, Some(10));
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn serde_round_trip_list_sessions() {
        let cmd = DebugCommand::ListSessions {
            limit: None,
            active_only: Some(true),
            tag_filter: None,
        };
        let json = serde_json::to_string(&cmd).unwrap();
        assert!(json.contains("\"type\":\"listSessions\""));
        // `tag_filter: None` must be omitted from the wire so older clients parse it.
        assert!(!json.contains("\"tagFilter\""));
        let back: DebugCommand = serde_json::from_str(&json).unwrap();
        match back {
            DebugCommand::ListSessions {
                limit,
                active_only,
                tag_filter,
            } => {
                assert!(limit.is_none());
                assert_eq!(active_only, Some(true));
                assert!(tag_filter.is_none());
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn serde_list_sessions_with_tag_filter() {
        let mut filter = std::collections::HashMap::new();
        filter.insert("channel".to_string(), "voice".to_string());
        let cmd = DebugCommand::ListSessions {
            limit: Some(10),
            active_only: Some(false),
            tag_filter: Some(filter),
        };
        let json = serde_json::to_string(&cmd).unwrap();
        assert!(json.contains("\"tagFilter\""));
        assert!(json.contains("\"activeOnly\""));
        assert!(json.contains("\"channel\":\"voice\""));
        let back: DebugCommand = serde_json::from_str(&json).unwrap();
        if let DebugCommand::ListSessions { tag_filter, .. } = back {
            let f = tag_filter.expect("tag_filter should be Some");
            assert_eq!(f.get("channel"), Some(&"voice".to_string()));
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn serde_list_sessions_without_tag_filter() {
        // Payloads without the 1.6.0 tag_filter field must still deserialize cleanly.
        let json = r#"{"type":"listSessions","limit":10,"activeOnly":false}"#;
        let cmd: DebugCommand = serde_json::from_str(json).unwrap();
        if let DebugCommand::ListSessions {
            limit,
            active_only,
            tag_filter,
        } = cmd
        {
            assert_eq!(limit, Some(10));
            assert_eq!(active_only, Some(false));
            assert!(tag_filter.is_none());
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn serde_list_sessions_camelcase_interop() {
        // Cross-language interop: a literal Java/TS-shaped payload must deserialize.
        let json = r#"{"type":"listSessions","limit":10,"activeOnly":true,"tagFilter":{"channel":"voice","env":"staging"}}"#;
        let cmd: DebugCommand = serde_json::from_str(json).unwrap();
        if let DebugCommand::ListSessions {
            limit,
            active_only,
            tag_filter,
        } = cmd
        {
            assert_eq!(limit, Some(10));
            assert_eq!(active_only, Some(true));
            let f = tag_filter.expect("tag_filter should be Some");
            assert_eq!(f.get("channel"), Some(&"voice".to_string()));
            assert_eq!(f.get("env"), Some(&"staging".to_string()));
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn serde_subscribe_camelcase_interop() {
        // Cross-language interop: Subscribe payload from Java/TS uses camelCase fields.
        let json = r#"{"type":"subscribe","sessionId":"s1","mode":"live","fromIndex":10}"#;
        let cmd: DebugCommand = serde_json::from_str(json).unwrap();
        if let DebugCommand::Subscribe {
            session_id,
            mode,
            from_index,
        } = cmd
        {
            assert_eq!(session_id, "s1");
            assert_eq!(mode, SubscriptionMode::Live);
            assert_eq!(from_index, Some(10));
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn serde_breakpoint_config() {
        let bp = BreakpointConfig {
            id: "bp1".into(),
            bp_type: BreakpointType::TransitionStart,
            target: Some("t1".into()),
            enabled: true,
        };
        let json = serde_json::to_string(&bp).unwrap();
        assert!(json.contains("\"type\":\"TRANSITION_START\""));
        let back: BreakpointConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(back.bp_type, BreakpointType::TransitionStart);
    }

    #[test]
    fn serde_event_filter_all() {
        let filter = EventFilter::all();
        let json = serde_json::to_string(&filter).unwrap();
        let back: EventFilter = serde_json::from_str(&json).unwrap();
        assert!(back.event_types.is_none());
        assert!(back.transition_names.is_none());
        assert!(back.place_names.is_none());
        assert!(back.exclude_event_types.is_none());
        assert!(back.exclude_transition_names.is_none());
        assert!(back.exclude_place_names.is_none());
    }

    #[test]
    fn serde_event_filter_backward_compat() {
        let json = r#"{"eventTypes":["TransitionStarted"],"transitionNames":null,"placeNames":null}"#;
        let filter: EventFilter = serde_json::from_str(json).unwrap();
        assert!(filter.exclude_event_types.is_none());
        assert!(filter.exclude_transition_names.is_none());
        assert!(filter.exclude_place_names.is_none());
    }

    #[test]
    fn serde_event_filter_with_exclusions() {
        let filter = EventFilter {
            event_types: None,
            transition_names: None,
            place_names: None,
            exclude_event_types: Some(vec!["LogMessage".into()]),
            exclude_transition_names: Some(vec!["t1".into()]),
            exclude_place_names: None,
        };
        let json = serde_json::to_string(&filter).unwrap();
        let back: EventFilter = serde_json::from_str(&json).unwrap();
        assert_eq!(back.exclude_event_types, Some(vec!["LogMessage".into()]));
        assert_eq!(back.exclude_transition_names, Some(vec!["t1".into()]));
        assert!(back.exclude_place_names.is_none());
    }

    #[test]
    fn serde_all_command_variants() {
        let cmds = vec![
            DebugCommand::ListSessions {
                limit: Some(10),
                active_only: None,
                tag_filter: None,
            },
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: SubscriptionMode::Replay,
                from_index: None,
            },
            DebugCommand::Unsubscribe {
                session_id: "s1".into(),
            },
            DebugCommand::Seek {
                session_id: "s1".into(),
                timestamp: "2025-01-01T00:00:00Z".into(),
            },
            DebugCommand::PlaybackSpeed {
                session_id: "s1".into(),
                speed: 2.0,
            },
            DebugCommand::Filter {
                session_id: "s1".into(),
                filter: EventFilter::all(),
            },
            DebugCommand::Pause {
                session_id: "s1".into(),
            },
            DebugCommand::Resume {
                session_id: "s1".into(),
            },
            DebugCommand::StepForward {
                session_id: "s1".into(),
            },
            DebugCommand::StepBackward {
                session_id: "s1".into(),
            },
            DebugCommand::SetBreakpoint {
                session_id: "s1".into(),
                breakpoint: BreakpointConfig {
                    id: "bp1".into(),
                    bp_type: BreakpointType::TokenAdded,
                    target: None,
                    enabled: true,
                },
            },
            DebugCommand::ClearBreakpoint {
                session_id: "s1".into(),
                breakpoint_id: "bp1".into(),
            },
            DebugCommand::ListBreakpoints {
                session_id: "s1".into(),
            },
            DebugCommand::ListArchives {
                limit: None,
                prefix: None,
            },
            DebugCommand::ImportArchive {
                session_id: "s1".into(),
            },
            DebugCommand::UploadArchive {
                file_name: "test.gz".into(),
                data: "base64data".into(),
            },
        ];
        for cmd in cmds {
            let json = serde_json::to_string(&cmd).unwrap();
            let _back: DebugCommand = serde_json::from_str(&json).unwrap();
        }
    }
}
