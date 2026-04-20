//! Caches computed state snapshots at periodic intervals for efficient seek/step.

use std::collections::{HashMap, HashSet};

use libpetri_event::net_event::NetEvent;

use crate::debug_response::TokenInfo;

/// Number of events between cached snapshots.
pub const SNAPSHOT_INTERVAL: usize = 256;

/// Computed state from replaying events.
#[derive(Debug, Clone)]
pub struct ComputedState {
    pub marking: HashMap<String, Vec<TokenInfo>>,
    pub enabled_transitions: Vec<String>,
    pub in_flight_transitions: Vec<String>,
}

/// Cache of computed state snapshots for efficient seek/step operations.
pub struct MarkingCache {
    snapshots: Vec<ComputedState>,
}

impl MarkingCache {
    /// Creates a new empty cache.
    pub fn new() -> Self {
        Self {
            snapshots: Vec::new(),
        }
    }

    /// Computes the state at the given event index, using cached snapshots
    /// to minimize the number of events that need to be replayed.
    pub fn compute_at(&mut self, events: &[NetEvent], target_index: usize) -> ComputedState {
        if target_index == 0 {
            return compute_state(&[]);
        }

        self.ensure_cached_up_to(events, target_index);

        if self.snapshots.is_empty() {
            return compute_state(&events[..target_index.min(events.len())]);
        }

        // Find highest snapshot <= target_index
        let snapshot_slot = (target_index / SNAPSHOT_INTERVAL)
            .min(self.snapshots.len())
            .saturating_sub(1);
        let snapshot_event_index = (snapshot_slot + 1) * SNAPSHOT_INTERVAL;

        if snapshot_event_index == target_index {
            return self.snapshots[snapshot_slot].clone();
        }

        let end = target_index.min(events.len());
        if snapshot_event_index >= end {
            return compute_state(&events[..end]);
        }

        replay_delta(
            &self.snapshots[snapshot_slot],
            &events[snapshot_event_index..end],
        )
    }

    /// Invalidates the cache.
    pub fn invalidate(&mut self) {
        self.snapshots.clear();
    }

    fn ensure_cached_up_to(&mut self, events: &[NetEvent], target_index: usize) {
        let needed_snapshots = target_index / SNAPSHOT_INTERVAL;

        while self.snapshots.len() < needed_snapshots {
            let next_snapshot_index = (self.snapshots.len() + 1) * SNAPSHOT_INTERVAL;
            if next_snapshot_index > events.len() {
                break;
            }

            if self.snapshots.is_empty() {
                self.snapshots
                    .push(compute_state(&events[..next_snapshot_index]));
            } else {
                let prev_snapshot_index = self.snapshots.len() * SNAPSHOT_INTERVAL;
                let delta = &events[prev_snapshot_index..next_snapshot_index];
                let state = replay_delta(self.snapshots.last().unwrap(), delta);
                self.snapshots.push(state);
            }
        }
    }
}

impl Default for MarkingCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Computes marking, enabled transitions, and in-flight transitions from events.
pub fn compute_state(events: &[NetEvent]) -> ComputedState {
    let mut marking = HashMap::new();
    let mut enabled = HashSet::new();
    let mut in_flight = HashSet::new();
    apply_events(&mut marking, &mut enabled, &mut in_flight, events);
    to_computed_state(marking, enabled, in_flight)
}

/// Applies events to mutable accumulator collections.
pub fn apply_events(
    marking: &mut HashMap<String, Vec<TokenInfo>>,
    enabled: &mut HashSet<String>,
    in_flight: &mut HashSet<String>,
    events: &[NetEvent],
) {
    for event in events {
        match event {
            NetEvent::TokenAdded {
                place_name,
                timestamp,
                token: _,
                ..
            } => {
                marking
                    .entry(place_name.to_string())
                    .or_default()
                    .push(TokenInfo {
                        id: None,
                        token_type: "unknown".into(),
                        value: None,
                        structured: None,
                        timestamp: Some(timestamp.to_string()),
                    });
            }
            NetEvent::TokenRemoved { place_name, .. } => {
                if let Some(tokens) = marking.get_mut(place_name.as_ref()) {
                    if !tokens.is_empty() {
                        tokens.remove(0);
                    }
                }
            }
            NetEvent::MarkingSnapshot { marking: m, .. } => {
                marking.clear();
                for (name, count) in m {
                    let tokens = (0..*count)
                        .map(|_| TokenInfo {
                            id: None,
                            token_type: "unknown".into(),
                            value: None,
                            structured: None,
                            timestamp: None,
                        })
                        .collect();
                    marking.insert(name.to_string(), tokens);
                }
            }
            NetEvent::TransitionEnabled {
                transition_name, ..
            } => {
                enabled.insert(transition_name.to_string());
            }
            NetEvent::TransitionStarted {
                transition_name, ..
            } => {
                enabled.remove(transition_name.as_ref());
                in_flight.insert(transition_name.to_string());
            }
            NetEvent::TransitionCompleted {
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
            } => {
                in_flight.remove(transition_name.as_ref());
            }
            _ => {}
        }
    }
}

fn to_computed_state(
    marking: HashMap<String, Vec<TokenInfo>>,
    enabled: HashSet<String>,
    in_flight: HashSet<String>,
) -> ComputedState {
    ComputedState {
        marking,
        enabled_transitions: enabled.into_iter().collect(),
        in_flight_transitions: in_flight.into_iter().collect(),
    }
}

fn replay_delta(base: &ComputedState, delta: &[NetEvent]) -> ComputedState {
    let mut marking: HashMap<String, Vec<TokenInfo>> = base
        .marking
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let mut enabled: HashSet<String> = base.enabled_transitions.iter().cloned().collect();
    let mut in_flight: HashSet<String> = base.in_flight_transitions.iter().cloned().collect();
    apply_events(&mut marking, &mut enabled, &mut in_flight, delta);
    to_computed_state(marking, enabled, in_flight)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn token_added(place: &str, ts: u64) -> NetEvent {
        NetEvent::token_added(Arc::from(place), ts)
    }

    fn token_removed(place: &str, ts: u64) -> NetEvent {
        NetEvent::token_removed(Arc::from(place), ts)
    }

    fn transition_enabled(name: &str, ts: u64) -> NetEvent {
        NetEvent::TransitionEnabled {
            transition_name: Arc::from(name),
            timestamp: ts,
        }
    }

    fn transition_started(name: &str, ts: u64) -> NetEvent {
        NetEvent::TransitionStarted {
            transition_name: Arc::from(name),
            timestamp: ts,
        }
    }

    fn transition_completed(name: &str, ts: u64) -> NetEvent {
        NetEvent::TransitionCompleted {
            transition_name: Arc::from(name),
            timestamp: ts,
        }
    }

    #[test]
    fn compute_empty_state() {
        let state = compute_state(&[]);
        assert!(state.marking.is_empty());
        assert!(state.enabled_transitions.is_empty());
        assert!(state.in_flight_transitions.is_empty());
    }

    #[test]
    fn compute_state_with_tokens() {
        let events = [
            token_added("p1", 0),
            token_added("p1", 1),
            token_added("p2", 2),
            token_removed("p1", 3),
        ];
        let state = compute_state(&events);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(1));
        assert_eq!(state.marking.get("p2").map(|t| t.len()), Some(1));
    }

    #[test]
    fn compute_state_with_transitions() {
        let events = [
            transition_enabled("t1", 0),
            transition_started("t1", 1),
            transition_completed("t1", 2),
        ];
        let state = compute_state(&events);
        assert!(state.enabled_transitions.is_empty());
        assert!(state.in_flight_transitions.is_empty());
    }

    #[test]
    fn compute_state_in_flight() {
        let events = [transition_enabled("t1", 0), transition_started("t1", 1)];
        let state = compute_state(&events);
        assert!(state.enabled_transitions.is_empty());
        assert!(state.in_flight_transitions.contains(&"t1".to_string()));
    }

    #[test]
    fn marking_cache_basic() {
        let mut cache = MarkingCache::new();
        let events: Vec<NetEvent> = (0..10).map(|i| token_added("p1", i)).collect();

        let state = cache.compute_at(&events, 5);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(5));

        let state = cache.compute_at(&events, 10);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(10));
    }

    #[test]
    fn marking_cache_with_snapshots() {
        let mut cache = MarkingCache::new();
        // Create enough events to trigger snapshot creation
        let events: Vec<NetEvent> = (0..512).map(|i| token_added("p1", i)).collect();

        let state = cache.compute_at(&events, 300);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(300));

        // Second query should use cached snapshot
        let state = cache.compute_at(&events, 260);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(260));
    }

    #[test]
    fn marking_cache_invalidate() {
        let mut cache = MarkingCache::new();
        let events: Vec<NetEvent> = (0..512).map(|i| token_added("p1", i)).collect();

        let _ = cache.compute_at(&events, 300);
        cache.invalidate();

        // After invalidation, still produces correct results
        let state = cache.compute_at(&events, 300);
        assert_eq!(state.marking.get("p1").map(|t| t.len()), Some(300));
    }
}
