//! Converts Rust `NetEvent` instances to serializable `NetEventInfo`.

use std::collections::HashMap;
use std::sync::Arc;

use libpetri_event::net_event::NetEvent;
use libpetri_event::token_payload::TokenPayload;

use crate::debug_response::{NetEventInfo, TokenInfo};
use crate::token_projector_registry::TokenProjectorRegistry;

/// Converts a `NetEvent` to a serializable `NetEventInfo`.
///
/// Equivalent to calling [`to_event_info_with_registry`] with a default
/// (empty) registry: unknown token types fall back to the type-name + Debug
/// projection, which is fine for the default debug experience. Callers that
/// want typed JSON projection for their domain token types should use
/// [`to_event_info_with_registry`] with a registry where those types are
/// registered.
pub fn to_event_info(event: &NetEvent) -> NetEventInfo {
    to_event_info_with_registry(event, None)
}

/// Like [`to_event_info`] but lets the caller supply a
/// [`TokenProjectorRegistry`] for typed JSON projection of token values
/// on `TokenAdded` / `TokenRemoved` events.
pub fn to_event_info_with_registry(
    event: &NetEvent,
    registry: Option<&TokenProjectorRegistry>,
) -> NetEventInfo {
    match event {
        NetEvent::ExecutionStarted {
            net_name,
            timestamp,
        } => NetEventInfo {
            event_type: "ExecutionStarted".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: None,
            place_name: None,
            details: HashMap::from([(
                "netName".into(),
                serde_json::Value::String(net_name.to_string()),
            )]),
        },
        NetEvent::ExecutionCompleted {
            net_name,
            timestamp,
        } => NetEventInfo {
            event_type: "ExecutionCompleted".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: None,
            place_name: None,
            details: HashMap::from([(
                "netName".into(),
                serde_json::Value::String(net_name.to_string()),
            )]),
        },
        NetEvent::TransitionEnabled {
            transition_name,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionEnabled".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::new(),
        },
        NetEvent::TransitionClockRestarted {
            transition_name,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionClockRestarted".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::new(),
        },
        NetEvent::TransitionStarted {
            transition_name,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionStarted".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::new(),
        },
        NetEvent::TransitionCompleted {
            transition_name,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionCompleted".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::new(),
        },
        NetEvent::TransitionFailed {
            transition_name,
            error,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionFailed".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::from([(
                "errorMessage".into(),
                serde_json::Value::String(error.clone()),
            )]),
        },
        NetEvent::TransitionTimedOut {
            transition_name,
            timestamp,
        } => NetEventInfo {
            event_type: "TransitionTimedOut".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::new(),
        },
        NetEvent::ActionTimedOut {
            transition_name,
            timeout_ms,
            timestamp,
        } => NetEventInfo {
            event_type: "ActionTimedOut".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::from([("timeoutMs".into(), serde_json::json!(*timeout_ms))]),
        },
        NetEvent::TokenAdded {
            place_name,
            timestamp,
            token,
            ..
        } => NetEventInfo {
            event_type: "TokenAdded".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: None,
            place_name: Some(place_name.to_string()),
            details: token_details(token.as_ref(), registry, *timestamp),
        },
        NetEvent::TokenRemoved {
            place_name,
            timestamp,
            token,
            ..
        } => NetEventInfo {
            event_type: "TokenRemoved".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: None,
            place_name: Some(place_name.to_string()),
            details: token_details(token.as_ref(), registry, *timestamp),
        },
        NetEvent::LogMessage {
            transition_name,
            level,
            message,
            timestamp,
        } => NetEventInfo {
            event_type: "LogMessage".into(),
            timestamp: format_timestamp(*timestamp),
            transition_name: Some(transition_name.to_string()),
            place_name: None,
            details: HashMap::from([
                ("level".into(), serde_json::Value::String(level.clone())),
                ("message".into(), serde_json::Value::String(message.clone())),
            ]),
        },
        NetEvent::MarkingSnapshot { marking, timestamp } => {
            let marking_map: HashMap<String, usize> =
                marking.iter().map(|(k, v)| (k.to_string(), *v)).collect();
            NetEventInfo {
                event_type: "MarkingSnapshot".into(),
                timestamp: format_timestamp(*timestamp),
                transition_name: None,
                place_name: None,
                details: HashMap::from([("marking".into(), serde_json::json!(marking_map))]),
            }
        }
    }
}

/// Formats a timestamp (milliseconds since epoch) as a string.
/// Uses simple numeric format since Rust's std doesn't have ISO-8601 formatting.
fn format_timestamp(ms: u64) -> String {
    ms.to_string()
}

/// Projects an optional token payload into the `details` map for a
/// `TokenAdded` / `TokenRemoved` `NetEventInfo`. Absent payloads yield an
/// empty map; present payloads surface as
/// `{"token": <TokenInfo>}` so the archive body format matches the
/// TypeScript and Java protocols.
fn token_details(
    token: Option<&Arc<dyn TokenPayload>>,
    registry: Option<&TokenProjectorRegistry>,
    timestamp: u64,
) -> HashMap<String, serde_json::Value> {
    let Some(payload) = token else {
        return HashMap::new();
    };
    let structured = registry.map(|r| r.project(payload.as_ref()));
    let info = TokenInfo {
        id: None,
        token_type: payload.type_name().to_string(),
        value: Some(format!("{:?}", payload)),
        structured,
        timestamp: Some(format_timestamp(timestamp)),
    };
    HashMap::from([(
        "token".into(),
        serde_json::to_value(info).unwrap_or(serde_json::Value::Null),
    )])
}

/// Extracts a transition name from an event, if applicable.
pub fn extract_transition_name(event: &NetEvent) -> Option<&str> {
    event.transition_name()
}

/// Extracts a place name from an event, if applicable.
pub fn extract_place_name(event: &NetEvent) -> Option<&str> {
    match event {
        NetEvent::TokenAdded { place_name, .. } | NetEvent::TokenRemoved { place_name, .. } => {
            Some(place_name)
        }
        _ => None,
    }
}

/// Maps a Rust `NetEvent` variant to a PascalCase type name string.
pub fn event_type_name(event: &NetEvent) -> &'static str {
    match event {
        NetEvent::ExecutionStarted { .. } => "ExecutionStarted",
        NetEvent::ExecutionCompleted { .. } => "ExecutionCompleted",
        NetEvent::TransitionEnabled { .. } => "TransitionEnabled",
        NetEvent::TransitionClockRestarted { .. } => "TransitionClockRestarted",
        NetEvent::TransitionStarted { .. } => "TransitionStarted",
        NetEvent::TransitionCompleted { .. } => "TransitionCompleted",
        NetEvent::TransitionFailed { .. } => "TransitionFailed",
        NetEvent::TransitionTimedOut { .. } => "TransitionTimedOut",
        NetEvent::ActionTimedOut { .. } => "ActionTimedOut",
        NetEvent::TokenAdded { .. } => "TokenAdded",
        NetEvent::TokenRemoved { .. } => "TokenRemoved",
        NetEvent::LogMessage { .. } => "LogMessage",
        NetEvent::MarkingSnapshot { .. } => "MarkingSnapshot",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn convert_execution_started() {
        let event = NetEvent::ExecutionStarted {
            net_name: Arc::from("test"),
            timestamp: 1000,
        };
        let info = to_event_info(&event);
        assert_eq!(info.event_type, "ExecutionStarted");
        assert_eq!(info.timestamp, "1000");
        assert!(info.transition_name.is_none());
        assert_eq!(info.details["netName"], "test");
    }

    #[test]
    fn convert_transition_started() {
        let event = NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 2000,
        };
        let info = to_event_info(&event);
        assert_eq!(info.event_type, "TransitionStarted");
        assert_eq!(info.transition_name.as_deref(), Some("t1"));
    }

    #[test]
    fn convert_token_added() {
        let event = NetEvent::token_added(Arc::from("p1"), 3000);
        let info = to_event_info(&event);
        assert_eq!(info.event_type, "TokenAdded");
        assert_eq!(info.place_name.as_deref(), Some("p1"));
    }

    #[test]
    fn convert_all_variants() {
        let events = vec![
            NetEvent::ExecutionStarted {
                net_name: Arc::from("n"),
                timestamp: 0,
            },
            NetEvent::ExecutionCompleted {
                net_name: Arc::from("n"),
                timestamp: 1,
            },
            NetEvent::TransitionEnabled {
                transition_name: Arc::from("t"),
                timestamp: 2,
            },
            NetEvent::TransitionClockRestarted {
                transition_name: Arc::from("t"),
                timestamp: 3,
            },
            NetEvent::TransitionStarted {
                transition_name: Arc::from("t"),
                timestamp: 4,
            },
            NetEvent::TransitionCompleted {
                transition_name: Arc::from("t"),
                timestamp: 5,
            },
            NetEvent::TransitionFailed {
                transition_name: Arc::from("t"),
                error: "err".into(),
                timestamp: 6,
            },
            NetEvent::TransitionTimedOut {
                transition_name: Arc::from("t"),
                timestamp: 7,
            },
            NetEvent::ActionTimedOut {
                transition_name: Arc::from("t"),
                timeout_ms: 100,
                timestamp: 8,
            },
            NetEvent::token_added(Arc::from("p"), 9),
            NetEvent::token_removed(Arc::from("p"), 10),
            NetEvent::LogMessage {
                transition_name: Arc::from("t"),
                level: "INFO".into(),
                message: "msg".into(),
                timestamp: 11,
            },
            NetEvent::MarkingSnapshot {
                marking: HashMap::from([(Arc::from("p"), 1)]),
                timestamp: 12,
            },
        ];
        for event in &events {
            let info = to_event_info(event);
            // Verify serializable
            let _json = serde_json::to_string(&info).unwrap();
        }
    }

    #[test]
    fn event_type_names() {
        let event = NetEvent::TransitionStarted {
            transition_name: Arc::from("t"),
            timestamp: 0,
        };
        assert_eq!(event_type_name(&event), "TransitionStarted");
    }
}
