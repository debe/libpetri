use std::collections::HashMap;
use std::sync::Arc;

/// All observable events during Petri net execution.
///
/// 13 event types as a discriminated union matching the TypeScript/Java implementations.
#[derive(Debug, Clone)]
pub enum NetEvent {
    /// Net execution started.
    ExecutionStarted { net_name: Arc<str>, timestamp: u64 },
    /// Net execution completed (no more enabled transitions, no in-flight actions).
    ExecutionCompleted { net_name: Arc<str>, timestamp: u64 },
    /// Transition became enabled (all input/inhibitor/read conditions satisfied).
    TransitionEnabled {
        transition_name: Arc<str>,
        timestamp: u64,
    },
    /// Transition's enabling clock restarted (input place tokens changed while enabled).
    TransitionClockRestarted {
        transition_name: Arc<str>,
        timestamp: u64,
    },
    /// Transition started firing (tokens consumed, action dispatched).
    TransitionStarted {
        transition_name: Arc<str>,
        timestamp: u64,
    },
    /// Transition completed successfully (outputs produced).
    TransitionCompleted {
        transition_name: Arc<str>,
        timestamp: u64,
    },
    /// Transition action failed with error.
    TransitionFailed {
        transition_name: Arc<str>,
        error: String,
        timestamp: u64,
    },
    /// Transition exceeded its timing deadline and was force-disabled.
    TransitionTimedOut {
        transition_name: Arc<str>,
        timestamp: u64,
    },
    /// Transition action exceeded its action timeout.
    ActionTimedOut {
        transition_name: Arc<str>,
        timeout_ms: u64,
        timestamp: u64,
    },
    /// Token added to a place.
    TokenAdded {
        place_name: Arc<str>,
        timestamp: u64,
    },
    /// Token removed from a place.
    TokenRemoved {
        place_name: Arc<str>,
        timestamp: u64,
    },
    /// Log message emitted by a transition action.
    LogMessage {
        transition_name: Arc<str>,
        level: String,
        message: String,
        timestamp: u64,
    },
    /// Snapshot of the current marking (token counts per place).
    MarkingSnapshot {
        marking: HashMap<Arc<str>, usize>,
        timestamp: u64,
    },
}

impl NetEvent {
    /// Returns the timestamp of this event.
    pub fn timestamp(&self) -> u64 {
        match self {
            NetEvent::ExecutionStarted { timestamp, .. }
            | NetEvent::ExecutionCompleted { timestamp, .. }
            | NetEvent::TransitionEnabled { timestamp, .. }
            | NetEvent::TransitionClockRestarted { timestamp, .. }
            | NetEvent::TransitionStarted { timestamp, .. }
            | NetEvent::TransitionCompleted { timestamp, .. }
            | NetEvent::TransitionFailed { timestamp, .. }
            | NetEvent::TransitionTimedOut { timestamp, .. }
            | NetEvent::ActionTimedOut { timestamp, .. }
            | NetEvent::TokenAdded { timestamp, .. }
            | NetEvent::TokenRemoved { timestamp, .. }
            | NetEvent::LogMessage { timestamp, .. }
            | NetEvent::MarkingSnapshot { timestamp, .. } => *timestamp,
        }
    }

    /// Returns the transition name if this event is transition-related.
    pub fn transition_name(&self) -> Option<&str> {
        match self {
            NetEvent::TransitionEnabled {
                transition_name, ..
            }
            | NetEvent::TransitionClockRestarted {
                transition_name, ..
            }
            | NetEvent::TransitionStarted {
                transition_name, ..
            }
            | NetEvent::TransitionCompleted {
                transition_name, ..
            }
            | NetEvent::TransitionFailed {
                transition_name, ..
            }
            | NetEvent::TransitionTimedOut {
                transition_name, ..
            }
            | NetEvent::ActionTimedOut {
                transition_name, ..
            }
            | NetEvent::LogMessage {
                transition_name, ..
            } => Some(transition_name),
            _ => None,
        }
    }

    /// Returns true if this is a failure event.
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            NetEvent::TransitionFailed { .. }
                | NetEvent::TransitionTimedOut { .. }
                | NetEvent::ActionTimedOut { .. }
        )
    }

    /// Returns true if this event carries any error signal — superset of
    /// [`is_failure`](Self::is_failure) that additionally treats a
    /// [`LogMessage`](NetEvent::LogMessage) at level `ERROR` (case-insensitive)
    /// as an error. Used by the v2 archive writer to pre-compute the
    /// `hasErrors` flag so listing/sampling tools can filter archives without
    /// scanning their event bodies. (libpetri 1.7.0+)
    pub fn has_error_signal(&self) -> bool {
        match self {
            NetEvent::TransitionFailed { .. }
            | NetEvent::TransitionTimedOut { .. }
            | NetEvent::ActionTimedOut { .. } => true,
            NetEvent::LogMessage { level, .. } => level.eq_ignore_ascii_case("ERROR"),
            _ => false,
        }
    }
}
