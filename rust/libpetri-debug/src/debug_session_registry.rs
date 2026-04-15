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
    /// Stamped on first [`DebugSessionRegistry::complete`]. `None` while active. (libpetri 1.6.0+)
    pub end_time: Option<u64>,
    /// Per-session tag storage. Prefer [`DebugSessionRegistry::tag`] /
    /// [`DebugSessionRegistry::tags_for`] over direct access. (libpetri 1.6.0+)
    pub tags: HashMap<String, String>,
}

impl DebugSession {
    /// Returns the session duration in milliseconds if the session has completed.
    /// (libpetri 1.6.0+)
    pub fn duration_ms(&self) -> Option<u64> {
        self.end_time.map(|end| end.saturating_sub(self.start_time))
    }
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
///
/// # Thread Safety
///
/// `DebugSessionRegistry` is **not** internally synchronized. All mutating methods
/// (`register`, `register_with_tags`, `complete`, `tag`, `remove`, `register_imported*`)
/// take `&mut self`, so concurrent callers must wrap the registry in an external
/// `Arc<Mutex<_>>` or `Arc<RwLock<_>>`. The read-only methods (`get_session`,
/// `list_sessions*`, `tags_for`, `size`) take `&self` and may run concurrently
/// under an `RwLock` read guard.
///
/// ## Re-entrancy contract
///
/// `SessionCompletionListener`s are invoked from within `complete()` while the
/// caller still holds any external lock guarding the registry. Listeners **must
/// not** call back into the same registry — doing so would deadlock under a
/// `Mutex` and panic under a `RwLock` write guard. If a listener needs to
/// observe the registry, it should copy what it needs from the borrowed
/// `&DebugSession` and defer any registry calls until after its caller has
/// released the lock.
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
        self.register_with_tags(session_id, net, HashMap::new())
    }

    /// Registers a new debug session with user-defined tags. (libpetri 1.6.0+)
    ///
    /// Tags are arbitrary `HashMap<String,String>` attributes attached to the session
    /// (e.g., `channel=voice`, `env=staging`). They can be used to filter via
    /// [`list_sessions_tagged`](Self::list_sessions_tagged).
    pub fn register_with_tags(
        &mut self,
        session_id: String,
        net: &PetriNet,
        tags: HashMap<String, String>,
    ) -> Arc<DebugEventStore> {
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
            end_time: None,
            tags,
        };

        self.evict_if_necessary();
        self.sessions.insert(session_id, session);
        event_store
    }

    /// Marks a session as completed and stamps `end_time` on first completion.
    ///
    /// Idempotent: subsequent calls preserve the existing `end_time`. (libpetri 1.6.0+)
    pub fn complete(&mut self, session_id: &str) {
        if let Some(session) = self.sessions.get_mut(session_id) {
            session.active = false;
            if session.end_time.is_none() {
                session.end_time = Some(now_ms());
            }
            for listener in &self.completion_listeners {
                listener(session);
            }
        }
    }

    /// Removes a session from the registry. Tags die with the session.
    pub fn remove(&mut self, session_id: &str) -> Option<DebugSession> {
        let removed = self.sessions.remove(session_id);
        if let Some(ref session) = removed {
            session.event_store.close();
        }
        removed
    }

    /// Sets or overwrites a single tag on a session. (libpetri 1.6.0+)
    ///
    /// If `session_id` does not correspond to a currently-registered session the
    /// call is a no-op.
    pub fn tag(&mut self, session_id: &str, key: String, value: String) {
        if let Some(session) = self.sessions.get_mut(session_id) {
            session.tags.insert(key, value);
        }
    }

    /// Returns a clone of the tags attached to a session.
    ///
    /// Returns an empty map if the session has no tags or does not exist. (libpetri 1.6.0+)
    pub fn tags_for(&self, session_id: &str) -> HashMap<String, String> {
        self.sessions
            .get(session_id)
            .map(|s| s.tags.clone())
            .unwrap_or_default()
    }

    /// Returns a reference to a session by ID.
    pub fn get_session(&self, session_id: &str) -> Option<&DebugSession> {
        self.sessions.get(session_id)
    }

    /// Lists sessions, ordered by start time (most recent first).
    pub fn list_sessions(&self, limit: usize) -> Vec<&DebugSession> {
        self.list_sessions_tagged(limit, &HashMap::new())
    }

    /// Lists sessions matching the given tag filter (AND semantics).
    ///
    /// An empty filter matches all sessions. (libpetri 1.6.0+)
    pub fn list_sessions_tagged(
        &self,
        limit: usize,
        tag_filter: &HashMap<String, String>,
    ) -> Vec<&DebugSession> {
        let mut sessions: Vec<&DebugSession> = self
            .sessions
            .values()
            .filter(|s| Self::matches_tag_filter(s, tag_filter))
            .collect();
        sessions.sort_by(|a, b| b.start_time.cmp(&a.start_time));
        sessions.truncate(limit);
        sessions
    }

    /// Lists only active sessions.
    pub fn list_active_sessions(&self, limit: usize) -> Vec<&DebugSession> {
        self.list_active_sessions_tagged(limit, &HashMap::new())
    }

    /// Lists active sessions matching the given tag filter. (libpetri 1.6.0+)
    pub fn list_active_sessions_tagged(
        &self,
        limit: usize,
        tag_filter: &HashMap<String, String>,
    ) -> Vec<&DebugSession> {
        let mut sessions: Vec<&DebugSession> = self
            .sessions
            .values()
            .filter(|s| s.active)
            .filter(|s| Self::matches_tag_filter(s, tag_filter))
            .collect();
        sessions.sort_by(|a, b| b.start_time.cmp(&a.start_time));
        sessions.truncate(limit);
        sessions
    }

    /// AND-match: every entry in `filter` must exactly match one of the session's tags.
    fn matches_tag_filter(session: &DebugSession, filter: &HashMap<String, String>) -> bool {
        if filter.is_empty() {
            return true;
        }
        filter.iter().all(|(k, v)| session.tags.get(k) == Some(v))
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
        self.register_imported_with_metadata(
            session_id,
            net_name,
            dot_diagram,
            structure,
            event_store,
            start_time,
            None,
            HashMap::new(),
        );
    }

    /// Registers an imported (archived) session with `end_time` and tags. (libpetri 1.6.0+)
    #[allow(clippy::too_many_arguments)]
    pub fn register_imported_with_metadata(
        &mut self,
        session_id: String,
        net_name: String,
        dot_diagram: String,
        structure: NetStructure,
        event_store: Arc<DebugEventStore>,
        start_time: u64,
        end_time: Option<u64>,
        tags: HashMap<String, String>,
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
            end_time,
            tags,
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

    // ======================== Tags + end_time (libpetri 1.6.0) ========================

    fn tags_map<const N: usize>(pairs: [(&str, &str); N]) -> HashMap<String, String> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    #[test]
    fn register_with_tags() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags(
            "s1".into(),
            &net,
            tags_map([("channel", "voice"), ("env", "staging")]),
        );

        let tags = registry.tags_for("s1");
        assert_eq!(tags.get("channel"), Some(&"voice".to_string()));
        assert_eq!(tags.get("env"), Some(&"staging".to_string()));
    }

    #[test]
    fn default_register_has_empty_tags() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register("s1".into(), &net);

        assert!(registry.tags_for("s1").is_empty());
    }

    #[test]
    fn tags_for_unknown_session_returns_empty() {
        let registry = DebugSessionRegistry::new();
        assert!(registry.tags_for("never-registered").is_empty());
    }

    #[test]
    fn set_tag_after_registration() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register("s1".into(), &net);

        registry.tag("s1", "channel".into(), "text".into());
        registry.tag("s1", "experiment".into(), "abc".into());

        let tags = registry.tags_for("s1");
        assert_eq!(tags.len(), 2);
        assert_eq!(tags.get("channel"), Some(&"text".to_string()));
        assert_eq!(tags.get("experiment"), Some(&"abc".to_string()));
    }

    #[test]
    fn replace_existing_tag_value() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags("s1".into(), &net, tags_map([("channel", "voice")]));

        registry.tag("s1", "channel".into(), "text".into());

        assert_eq!(
            registry.tags_for("s1").get("channel"),
            Some(&"text".to_string())
        );
    }

    #[test]
    fn tag_unknown_session_is_no_op() {
        let mut registry = DebugSessionRegistry::new();

        registry.tag("never-registered", "channel".into(), "voice".into());

        assert!(registry.tags_for("never-registered").is_empty());
        assert!(
            registry
                .list_sessions_tagged(10, &tags_map([("channel", "voice")]))
                .is_empty()
        );
    }

    #[test]
    fn tag_removed_session_is_no_op() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register("s1".into(), &net);
        registry.remove("s1");

        registry.tag("s1", "channel".into(), "voice".into());

        assert!(registry.tags_for("s1").is_empty());
    }

    #[test]
    fn filter_sessions_by_tag() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags("text-1".into(), &net, tags_map([("channel", "text")]));
        registry.register_with_tags("voice-1".into(), &net, tags_map([("channel", "voice")]));
        registry.register_with_tags("voice-2".into(), &net, tags_map([("channel", "voice")]));

        let voices = registry.list_sessions_tagged(10, &tags_map([("channel", "voice")]));

        assert_eq!(voices.len(), 2);
        assert!(voices.iter().all(|s| s.session_id.starts_with("voice")));
    }

    #[test]
    fn and_match_multiple_tag_keys() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags(
            "s1".into(),
            &net,
            tags_map([("channel", "voice"), ("env", "staging")]),
        );
        registry.register_with_tags(
            "s2".into(),
            &net,
            tags_map([("channel", "voice"), ("env", "prod")]),
        );
        registry.register_with_tags(
            "s3".into(),
            &net,
            tags_map([("channel", "text"), ("env", "staging")]),
        );

        let filtered = registry.list_sessions_tagged(
            10,
            &tags_map([("channel", "voice"), ("env", "staging")]),
        );

        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].session_id, "s1");
    }

    #[test]
    fn filter_active_sessions_by_tag() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags(
            "active-voice".into(),
            &net,
            tags_map([("channel", "voice")]),
        );
        registry.register_with_tags(
            "completed-voice".into(),
            &net,
            tags_map([("channel", "voice")]),
        );
        registry.register_with_tags(
            "active-text".into(),
            &net,
            tags_map([("channel", "text")]),
        );
        registry.complete("completed-voice");

        let active_voices =
            registry.list_active_sessions_tagged(10, &tags_map([("channel", "voice")]));

        assert_eq!(active_voices.len(), 1);
        assert_eq!(active_voices[0].session_id, "active-voice");
    }

    #[test]
    fn stamp_end_time_on_complete() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);
        assert!(registry.get_session("s1").unwrap().end_time.is_none());

        registry.complete("s1");

        let s = registry.get_session("s1").unwrap();
        assert!(s.end_time.is_some());
        assert!(!s.active);
    }

    #[test]
    fn preserve_end_time_on_second_complete() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        registry.complete("s1");
        let first_end = registry.get_session("s1").unwrap().end_time;

        std::thread::sleep(std::time::Duration::from_millis(5));
        registry.complete("s1");
        let second_end = registry.get_session("s1").unwrap().end_time;

        assert_eq!(first_end, second_end);
    }

    #[test]
    fn duration_ms_for_completed_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        std::thread::sleep(std::time::Duration::from_millis(2));
        registry.complete("s1");

        let s = registry.get_session("s1").unwrap();
        let duration = s.duration_ms().expect("duration should be Some");
        // We slept at least 2ms between register and complete.
        assert!(duration >= 1, "expected duration >= 1ms, got {}", duration);
    }

    #[test]
    fn duration_ms_is_none_for_active_session() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        let _store = registry.register("s1".into(), &net);

        assert!(registry.get_session("s1").unwrap().duration_ms().is_none());
    }

    #[test]
    fn clear_tags_on_remove() {
        let mut registry = DebugSessionRegistry::new();
        let net = test_net();
        registry.register_with_tags("s1".into(), &net, tags_map([("channel", "voice")]));

        registry.remove("s1");

        assert!(registry.tags_for("s1").is_empty());
    }

    #[test]
    fn register_imported_with_metadata() {
        let mut registry = DebugSessionRegistry::new();
        let structure = NetStructure {
            places: vec![],
            transitions: vec![],
        };
        let start_time = 1000;
        let end_time = 1500;

        registry.register_imported_with_metadata(
            "imported-1".into(),
            "TestNet".into(),
            "digraph{}".into(),
            structure,
            Arc::new(DebugEventStore::new("imported-1".into())),
            start_time,
            Some(end_time),
            tags_map([("channel", "voice"), ("source", "archive")]),
        );

        let s = registry.get_session("imported-1").unwrap();
        assert!(!s.active);
        assert_eq!(s.end_time, Some(end_time));
        assert_eq!(s.duration_ms(), Some(500));

        let tags = registry.tags_for("imported-1");
        assert_eq!(tags.get("channel"), Some(&"voice".to_string()));
        assert_eq!(tags.get("source"), Some(&"archive".to_string()));
    }

    #[test]
    fn backward_compat_register_imported_no_metadata() {
        let mut registry = DebugSessionRegistry::new();
        let structure = NetStructure {
            places: vec![],
            transitions: vec![],
        };

        registry.register_imported(
            "imported-1".into(),
            "TestNet".into(),
            "digraph{}".into(),
            structure,
            Arc::new(DebugEventStore::new("imported-1".into())),
            1000,
        );

        let s = registry.get_session("imported-1").unwrap();
        assert!(s.end_time.is_none());
        assert!(registry.tags_for("imported-1").is_empty());
    }

    #[test]
    fn cleanup_tags_on_eviction() {
        let mut registry = DebugSessionRegistry::with_options(2, None, Vec::new());
        let net = test_net();

        registry.register_with_tags("s1".into(), &net, tags_map([("channel", "voice")]));
        registry.register_with_tags("s2".into(), &net, tags_map([("channel", "text")]));
        registry.complete("s1");

        // Forces eviction of s1 (inactive, oldest)
        registry.register_with_tags("s3".into(), &net, tags_map([("channel", "voice")]));

        assert!(registry.get_session("s1").is_none());
        assert!(registry.tags_for("s1").is_empty());
        assert_eq!(
            registry.tags_for("s2").get("channel"),
            Some(&"text".to_string())
        );
        assert_eq!(
            registry.tags_for("s3").get("channel"),
            Some(&"voice".to_string())
        );
    }

    #[test]
    fn concurrent_tag_and_complete_smoke() {
        use std::sync::{Barrier, Mutex};
        use std::thread;

        let registry = Arc::new(Mutex::new(DebugSessionRegistry::new()));
        let net = test_net();
        registry.lock().unwrap().register("s1".into(), &net);

        let barrier = Arc::new(Barrier::new(8));
        let mut handles = Vec::new();

        for i in 0..8 {
            let registry = Arc::clone(&registry);
            let barrier = Arc::clone(&barrier);
            handles.push(thread::spawn(move || {
                barrier.wait();
                let mut reg = registry.lock().unwrap();
                if i % 2 == 0 {
                    reg.tag("s1", format!("k{i}"), "v".into());
                } else {
                    reg.complete("s1");
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        let reg = registry.lock().unwrap();
        let session = reg.get_session("s1").expect("session must exist");
        assert!(!session.active, "session should be marked complete");
        assert!(
            session.end_time.is_some(),
            "end time should be stamped after complete()"
        );
        let tags = reg.tags_for("s1");
        assert_eq!(tags.len(), 4, "four even-indexed threads tagged the session");
        for k in ["k0", "k2", "k4", "k6"] {
            assert_eq!(tags.get(k), Some(&"v".to_string()), "missing tag {k}");
        }
    }
}
