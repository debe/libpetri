//! Shared metadata computation for session archives.
//!
//! Mirrors the Java `SessionMetadata.computeFrom` helper and the TypeScript
//! `computeMetadata` function: a single-pass scan producing the histogram /
//! first-last timestamps / hasErrors triple. Reused by the v2 archive writer
//! (at archive time) and by read-path fallbacks that need aggregate stats for
//! a v1 archive.

use std::collections::BTreeMap;

use libpetri_event::net_event::NetEvent;

use super::session_archive::SessionMetadata;

/// Walks the given event slice once and produces a [`SessionMetadata`] summary.
///
/// `BTreeMap<String, u64>` for the histogram gives deterministic iteration
/// order — matches Java's `TreeMap` and TypeScript's alphabetical key sort.
///
/// Histogram keys match the wire format used by Java (`event.getClass().getSimpleName()`)
/// and TypeScript (`toEventInfo(event).type`), both PascalCase like
/// `TransitionStarted` / `LogMessage`.
pub fn compute_metadata(events: &[NetEvent]) -> SessionMetadata {
    let mut histogram: BTreeMap<String, u64> = BTreeMap::new();
    let mut first: Option<u64> = None;
    let mut last: Option<u64> = None;
    let mut has_errors = false;

    for event in events {
        let type_name = event_type_name(event);
        *histogram.entry(type_name.to_string()).or_insert(0) += 1;

        let ts = event.timestamp();
        if first.is_none() {
            first = Some(ts);
        }
        last = Some(ts);

        if event_has_error_signal(event) {
            has_errors = true;
        }
    }

    SessionMetadata {
        event_type_histogram: histogram,
        first_event_time: first.map(|t| t.to_string()),
        last_event_time: last.map(|t| t.to_string()),
        has_errors,
    }
}

/// Returns the PascalCase variant name of a `NetEvent`. Kept in sync with the
/// Java/TS conventions so the histogram keys are identical across languages.
fn event_type_name(event: &NetEvent) -> &'static str {
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

/// Superset of [`NetEvent::is_failure`](libpetri_event::net_event::NetEvent::is_failure)
/// that additionally treats `LogMessage` at level `ERROR` (case-insensitive)
/// as an error signal.
///
/// `NetEvent::is_failure` has a narrower meaning (transition-lifecycle failures
/// only) and other callers rely on that, so the superset lives here rather
/// than replacing the existing method.
fn event_has_error_signal(event: &NetEvent) -> bool {
    match event {
        NetEvent::TransitionFailed { .. }
        | NetEvent::TransitionTimedOut { .. }
        | NetEvent::ActionTimedOut { .. } => true,
        NetEvent::LogMessage { level, .. } => level.eq_ignore_ascii_case("ERROR"),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn mk_enabled(ts: u64) -> NetEvent {
        NetEvent::TransitionEnabled {
            transition_name: Arc::from("Process"),
            timestamp: ts,
        }
    }

    fn mk_started(ts: u64) -> NetEvent {
        NetEvent::TransitionStarted {
            transition_name: Arc::from("Process"),
            timestamp: ts,
        }
    }

    fn mk_completed(ts: u64) -> NetEvent {
        NetEvent::TransitionCompleted {
            transition_name: Arc::from("Process"),
            timestamp: ts,
        }
    }

    fn mk_failed(ts: u64) -> NetEvent {
        NetEvent::TransitionFailed {
            transition_name: Arc::from("Process"),
            error: "boom".into(),
            timestamp: ts,
        }
    }

    fn mk_timed_out(ts: u64) -> NetEvent {
        NetEvent::TransitionTimedOut {
            transition_name: Arc::from("Process"),
            timestamp: ts,
        }
    }

    fn mk_action_timed_out(ts: u64) -> NetEvent {
        NetEvent::ActionTimedOut {
            transition_name: Arc::from("Process"),
            timeout_ms: 100,
            timestamp: ts,
        }
    }

    fn mk_log(level: &str, ts: u64) -> NetEvent {
        NetEvent::LogMessage {
            transition_name: Arc::from("Process"),
            level: level.to_string(),
            message: "msg".into(),
            timestamp: ts,
        }
    }

    #[test]
    fn histogram_counts_events_by_type() {
        let events = vec![
            mk_enabled(1000),
            mk_started(1010),
            mk_started(1020),
            mk_completed(1050),
        ];
        let metadata = compute_metadata(&events);

        assert_eq!(metadata.event_type_histogram.get("TransitionEnabled"), Some(&1));
        assert_eq!(metadata.event_type_histogram.get("TransitionStarted"), Some(&2));
        assert_eq!(metadata.event_type_histogram.get("TransitionCompleted"), Some(&1));
        assert!(!metadata.event_type_histogram.contains_key("TokenAdded"));
    }

    #[test]
    fn histogram_key_order_is_deterministic() {
        let events = vec![mk_completed(1000), mk_enabled(1010), mk_started(1020)];
        let metadata = compute_metadata(&events);

        // BTreeMap guarantees sorted iteration.
        let keys: Vec<&String> = metadata.event_type_histogram.keys().collect();
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted);
    }

    #[test]
    fn tracks_first_and_last_timestamps() {
        let events = vec![mk_enabled(1000), mk_started(1100), mk_completed(1200)];
        let metadata = compute_metadata(&events);

        assert_eq!(metadata.first_event_time, Some("1000".to_string()));
        assert_eq!(metadata.last_event_time, Some("1200".to_string()));
    }

    #[test]
    fn empty_events_produces_empty_metadata() {
        let metadata = compute_metadata(&[]);
        assert!(metadata.event_type_histogram.is_empty());
        assert!(metadata.first_event_time.is_none());
        assert!(metadata.last_event_time.is_none());
        assert!(!metadata.has_errors);
    }

    #[test]
    fn has_errors_for_transition_failed() {
        assert!(compute_metadata(&[mk_failed(1000)]).has_errors);
    }

    #[test]
    fn has_errors_for_transition_timed_out() {
        assert!(compute_metadata(&[mk_timed_out(1000)]).has_errors);
    }

    #[test]
    fn has_errors_for_action_timed_out() {
        assert!(compute_metadata(&[mk_action_timed_out(1000)]).has_errors);
    }

    #[test]
    fn has_errors_for_log_message_error_level() {
        assert!(compute_metadata(&[mk_log("ERROR", 1000)]).has_errors);
    }

    #[test]
    fn has_errors_for_log_message_lowercase_error() {
        assert!(compute_metadata(&[mk_log("error", 1000)]).has_errors);
    }

    #[test]
    fn clean_session_leaves_has_errors_false() {
        let events = vec![
            mk_enabled(1000),
            mk_log("INFO", 1010),
            mk_started(1020),
            mk_completed(1050),
        ];
        assert!(!compute_metadata(&events).has_errors);
    }
}
