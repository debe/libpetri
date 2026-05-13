use std::collections::HashMap;
use std::sync::Arc;

use crate::token_payload::TokenPayload;

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
    ///
    /// The optional `token` payload is populated only by event stores that opt in
    /// via [`EventStore::CAPTURES_TOKENS`](crate::event_store::EventStore::CAPTURES_TOKENS).
    /// Production stores (`NoopEventStore`, `InMemoryEventStore`) leave it `None`
    /// so the capture path is monomorphized out — preserving the zero-cost event
    /// recording invariant.
    ///
    /// Marked `#[non_exhaustive]` so future fields (e.g. token identity,
    /// source-transition attribution) can be added without a breaking change;
    /// downstream matches must use `{ .., .. }`.
    #[non_exhaustive]
    TokenAdded {
        place_name: Arc<str>,
        timestamp: u64,
        token: Option<Arc<dyn TokenPayload>>,
    },
    /// Token removed from a place.
    ///
    /// See [`TokenAdded`](Self::TokenAdded) for payload semantics and for the
    /// `#[non_exhaustive]` contract.
    #[non_exhaustive]
    TokenRemoved {
        place_name: Arc<str>,
        timestamp: u64,
        token: Option<Arc<dyn TokenPayload>>,
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

/// Returns the instance prefix carried by a node name, or [`None`] when the
/// name has no `/` (i.e. is not part of any composed subnet instance) per
/// `spec/11-modular-composition.md` **MOD-041**.
///
/// The prefix is the substring up to (but not including) the **last** `/`
/// — so `producer1/internal` returns `Some("producer1")` and
/// `outer/inner/leaf` returns `Some("outer/inner")`.
///
/// Duplicated locally inside the event package (rather than delegated to
/// `libpetri_export::subnet_prefixes`) to keep the event subsystem
/// dependency-free of the export layer per the package-isolation contract.
/// Mirrors `org.libpetri.event.NetEvent#instancePrefixOf`.
pub fn instance_prefix_of(name: &str) -> Option<&str> {
    let idx = name.rfind('/')?;
    if idx == 0 {
        return None;
    }
    Some(&name[..idx])
}

impl NetEvent {
    /// Constructs a [`TokenAdded`](Self::TokenAdded) event without a payload —
    /// the default for production event stores.
    pub fn token_added(place_name: Arc<str>, timestamp: u64) -> Self {
        Self::TokenAdded { place_name, timestamp, token: None }
    }

    /// Constructs a [`TokenAdded`](Self::TokenAdded) event carrying a token
    /// payload — used by debug-aware event stores that set
    /// [`EventStore::CAPTURES_TOKENS = true`](crate::event_store::EventStore::CAPTURES_TOKENS).
    pub fn token_added_with(
        place_name: Arc<str>,
        timestamp: u64,
        token: Arc<dyn TokenPayload>,
    ) -> Self {
        Self::TokenAdded { place_name, timestamp, token: Some(token) }
    }

    /// Constructs a [`TokenRemoved`](Self::TokenRemoved) event without a payload.
    pub fn token_removed(place_name: Arc<str>, timestamp: u64) -> Self {
        Self::TokenRemoved { place_name, timestamp, token: None }
    }

    /// Constructs a [`TokenRemoved`](Self::TokenRemoved) event carrying a token
    /// payload. See [`token_added_with`](Self::token_added_with).
    pub fn token_removed_with(
        place_name: Arc<str>,
        timestamp: u64,
        token: Arc<dyn TokenPayload>,
    ) -> Self {
        Self::TokenRemoved { place_name, timestamp, token: Some(token) }
    }

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

    /// Returns the place name if this event is place-related.
    pub fn place_name(&self) -> Option<&str> {
        match self {
            NetEvent::TokenAdded { place_name, .. }
            | NetEvent::TokenRemoved { place_name, .. } => Some(place_name),
            _ => None,
        }
    }

    /// Returns the derived instance prefix per **MOD-041** for this event,
    /// computed from whichever of [`Self::transition_name`] or
    /// [`Self::place_name`] is populated. Returns [`None`] for events that
    /// don't carry a node name (e.g. [`Self::ExecutionStarted`],
    /// [`Self::MarkingSnapshot`]) or when the carried name is flat (no `/`).
    pub fn instance_prefix(&self) -> Option<&str> {
        let name = self.transition_name().or_else(|| self.place_name())?;
        instance_prefix_of(name)
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
