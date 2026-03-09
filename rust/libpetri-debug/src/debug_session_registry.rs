//! Registry for managing Petri net debug sessions.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use libpetri_core::petri_net::PetriNet;
use libpetri_export::dot_exporter::dot_export;
use libpetri_export::mapper::sanitize;

use crate::debug_event_store::DebugEventStore;
use crate::debug_response::{NetStructure, PlaceInfo, TransitionInfo};
use crate::place_analysis::PlaceAnalysis;

/// A registered debug session.
pub struct DebugSession {
    pub session_id: String,
    pub net_name: String,
    pub dot_diagram: String,
    pub places: Option<PlaceAnalysis>,
    pub transition_names: Vec<String>,
    pub event_store: Arc<DebugEventStore>,
    pub start_time: u64,
    pub active: bool,
    pub imported_structure: Option<NetStructure>,
}

/// Callback invoked when a session completes.
pub type SessionCompletionListener = Box<dyn Fn(&DebugSession) + Send + Sync>;

/// Builds the `NetStructure` from a session's stored place and transition info.
pub fn build_net_structure(session: &DebugSession) -> NetStructure {
    if let Some(ref imported) = session.imported_structure {
        return imported.clone();
    }

    let Some(ref places) = session.places else {
        return NetStructure {
            places: Vec::new(),
            transitions: Vec::new(),
        };
    };

    let place_infos: Vec<PlaceInfo> = places
        .data()
        .iter()
        .map(|(name, info)| PlaceInfo {
            name: name.clone(),
            graph_id: format!("p_{}", sanitize(name)),
            token_type: info.token_type.clone(),
            is_start: !info.has_incoming,
            is_end: !info.has_outgoing,
            is_environment: false,
        })
        .collect();

    let transition_infos: Vec<TransitionInfo> = session
        .transition_names
        .iter()
        .map(|name| TransitionInfo {
            name: name.clone(),
            graph_id: format!("t_{}", sanitize(name)),
        })
        .collect();

    NetStructure {
        places: place_infos,
        transitions: transition_infos,
    }
}

/// Factory function for creating `DebugEventStore` instances.
pub type EventStoreFactory = Box<dyn Fn(&str) -> DebugEventStore + Send + Sync>;

/// Registry for managing debug sessions.
pub struct DebugSessionRegistry {
    sessions: HashMap<String, DebugSession>,
    max_sessions: usize,
    event_store_factory: EventStoreFactory,
    completion_listeners: Vec<SessionCompletionListener>,
}

impl DebugSessionRegistry {
    /// Creates a new registry with default settings.
    pub fn new() -> Self {
        Self::with_options(50, None, Vec::new())
    }

    /// Creates a registry with custom options.
    pub fn with_options(
        max_sessions: usize,
        event_store_factory: Option<EventStoreFactory>,
        completion_listeners: Vec<SessionCompletionListener>,
    ) -> Self {
        Self {
            sessions: HashMap::new(),
            max_sessions,
            event_store_factory: event_store_factory
                .unwrap_or_else(|| Box::new(|id: &str| DebugEventStore::new(id.to_string()))),
            completion_listeners,
        }
    }

    /// Registers a new debug session for the given Petri net.
    pub fn register(&mut self, session_id: String, net: &PetriNet) -> Arc<DebugEventStore> {
        let dot_diagram = dot_export(net, None);
        let places = PlaceAnalysis::from_net(net);
        let event_store = Arc::new((self.event_store_factory)(&session_id));

        let transition_names: Vec<String> = net
            .transitions()
            .iter()
            .map(|t| t.name().to_string())
            .collect();

        let session = DebugSession {
            session_id: session_id.clone(),
            net_name: net.name().to_string(),
            dot_diagram,
            places: Some(places),
            transition_names,
            event_store: Arc::clone(&event_store),
            start_time: now_ms(),
            active: true,
            imported_structure: None,
        };

        self.evict_if_necessary();
        self.sessions.insert(session_id, session);
        event_store
    }

    /// Marks a session as completed.
    pub fn complete(&mut self, session_id: &str) {
        if let Some(session) = self.sessions.get_mut(session_id) {
            session.active = false;
            for listener in &self.completion_listeners {
                listener(session);
            }
        }
    }

    /// Removes a session from the registry.
    pub fn remove(&mut self, session_id: &str) -> Option<DebugSession> {
        let removed = self.sessions.remove(session_id);
        if let Some(ref session) = removed {
            session.event_store.close();
        }
        removed
    }

    /// Returns a reference to a session by ID.
    pub fn get_session(&self, session_id: &str) -> Option<&DebugSession> {
        self.sessions.get(session_id)
    }

    /// Lists sessions, ordered by start time (most recent first).
    pub fn list_sessions(&self, limit: usize) -> Vec<&DebugSession> {
        let mut sessions: Vec<&DebugSession> = self.sessions.values().collect();
        sessions.sort_by(|a, b| b.start_time.cmp(&a.start_time));
        sessions.truncate(limit);
        sessions
    }

    /// Lists only active sessions.
    pub fn list_active_sessions(&self, limit: usize) -> Vec<&DebugSession> {
        let mut sessions: Vec<&DebugSession> =
            self.sessions.values().filter(|s| s.active).collect();
        sessions.sort_by(|a, b| b.start_time.cmp(&a.start_time));
        sessions.truncate(limit);
        sessions
    }

    /// Total number of sessions.
    pub fn size(&self) -> usize {
        self.sessions.len()
    }

    /// Registers an imported (archived) session as inactive.
    pub fn register_imported(
        &mut self,
        session_id: String,
        net_name: String,
        dot_diagram: String,
        structure: NetStructure,
        event_store: Arc<DebugEventStore>,
        start_time: u64,
    ) {
        self.evict_if_necessary();

        let session = DebugSession {
            session_id: session_id.clone(),
            net_name,
            dot_diagram,
            places: None,
            transition_names: Vec::new(),
            event_store,
            start_time,
            active: false,
            imported_structure: Some(structure),
        };

        self.sessions.insert(session_id, session);
    }

    fn evict_if_necessary(&mut self) {
        if self.sessions.len() < self.max_sessions {
            return;
        }

        // Sort: inactive first, then oldest
        let mut candidates: Vec<(&String, bool, u64)> = self
            .sessions
            .iter()
            .map(|(id, s)| (id, s.active, s.start_time))
            .collect();
        candidates.sort_by(|a, b| {
            if a.1 != b.1 {
                return if a.1 {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Less
                };
            }
            a.2.cmp(&b.2)
        });

        let to_remove: Vec<String> = candidates
            .iter()
            .take_while(|_| self.sessions.len() >= self.max_sessions)
            .map(|(id, _, _)| (*id).clone())
            .collect();

        for id in to_remove {
            if self.sessions.len() < self.max_sessions {
                break;
            }
            if let Some(session) = self.sessions.remove(&id) {
                session.event_store.close();
            }
        }
    }
}

impl Default for DebugSessionRegistry {
    fn default() -> Self {
        Self::new()
    }
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn test_net() -> PetriNet {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        PetriNet::builder("test").transition(t).build()
    }

    #[test]
    fn register_and_get_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        let session = registry.get_session("s1").unwrap();
        assert_eq!(session.net_name, "test");
        assert!(session.active);
        assert!(!session.dot_diagram.is_empty());
    }

    #[test]
    fn complete_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        registry.complete("s1");
        let session = registry.get_session("s1").unwrap();
        assert!(!session.active);
    }

    #[test]
    fn list_sessions() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _s1 = registry.register("s1".into(), &net);
        let _s2 = registry.register("s2".into(), &net);

        assert_eq!(registry.list_sessions(10).len(), 2);
        assert_eq!(registry.size(), 2);
    }

    #[test]
    fn list_active_sessions() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _s1 = registry.register("s1".into(), &net);
        let _s2 = registry.register("s2".into(), &net);
        registry.complete("s1");

        assert_eq!(registry.list_active_sessions(10).len(), 1);
    }

    #[test]
    fn remove_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        let removed = registry.remove("s1");
        assert!(removed.is_some());
        assert!(registry.get_session("s1").is_none());
        assert_eq!(registry.size(), 0);
    }

    #[test]
    fn build_net_structure_from_live_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        let session = registry.get_session("s1").unwrap();
        let structure = build_net_structure(session);

        assert_eq!(structure.places.len(), 2);
        assert_eq!(structure.transitions.len(), 1);

        let p1 = structure.places.iter().find(|p| p.name == "p1").unwrap();
        assert_eq!(p1.graph_id, "p_p1");
        assert!(p1.is_start);
        assert!(!p1.is_end);

        let p2 = structure.places.iter().find(|p| p.name == "p2").unwrap();
        assert!(p2.is_end);
        assert!(!p2.is_start);

        assert_eq!(structure.transitions[0].name, "t1");
        assert_eq!(structure.transitions[0].graph_id, "t_t1");
    }

    #[test]
    fn eviction_at_capacity() {
        let mut registry = DebugSessionRegistry::with_options(2, None, Vec::new());
        let net = test_net();

        let _s1 = registry.register("s1".into(), &net);
        let _s2 = registry.register("s2".into(), &net);
        registry.complete("s1");
        // s3 should evict s1 (inactive, oldest)
        let _s3 = registry.register("s3".into(), &net);

        assert_eq!(registry.size(), 2);
        assert!(registry.get_session("s1").is_none());
        assert!(registry.get_session("s2").is_some());
        assert!(registry.get_session("s3").is_some());
    }
}
