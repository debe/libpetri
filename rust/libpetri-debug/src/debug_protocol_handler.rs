//! Framework-agnostic handler for the Petri net debug protocol.
//!
//! Manages debug subscriptions, event filtering, breakpoints, and replay
//! for connected clients. Decoupled from any specific WebSocket framework
//! via the [`ResponseSink`] trait.

use std::collections::HashMap;

use libpetri_event::net_event::NetEvent;

use crate::debug_command::{BreakpointConfig, BreakpointType, DebugCommand, EventFilter};
use crate::debug_response::{DebugResponse, NetEventInfo, SessionSummary};
use crate::debug_session_registry::{DebugSession, DebugSessionRegistry, build_net_structure};
use crate::marking_cache::{MarkingCache, compute_state};
use crate::net_event_converter::{
    event_type_name, extract_place_name, extract_transition_name, to_event_info,
};

/// Callback for sending responses to a connected client.
pub trait ResponseSink: Send + Sync {
    fn send(&self, response: DebugResponse);
}

/// Blanket impl for closures.
impl<F: Fn(DebugResponse) + Send + Sync> ResponseSink for F {
    fn send(&self, response: DebugResponse) {
        self(response);
    }
}

/// Maximum events per batch when sending historical events.
const BATCH_SIZE: usize = 500;

/// Debug protocol handler managing client connections and command dispatch.
pub struct DebugProtocolHandler {
    session_registry: DebugSessionRegistry,
    clients: HashMap<String, ClientState>,
}

struct ClientState {
    sink: Box<dyn ResponseSink>,
    subscriptions: SubscriptionState,
}

impl DebugProtocolHandler {
    /// Creates a new protocol handler.
    pub fn new(session_registry: DebugSessionRegistry) -> Self {
        Self {
            session_registry,
            clients: HashMap::new(),
        }
    }

    /// Returns a reference to the session registry.
    pub fn session_registry(&self) -> &DebugSessionRegistry {
        &self.session_registry
    }

    /// Returns a mutable reference to the session registry.
    pub fn session_registry_mut(&mut self) -> &mut DebugSessionRegistry {
        &mut self.session_registry
    }

    /// Registers a new client connection.
    pub fn client_connected(&mut self, client_id: String, sink: Box<dyn ResponseSink>) {
        self.clients.insert(
            client_id,
            ClientState {
                sink,
                subscriptions: SubscriptionState::new(),
            },
        );
    }

    /// Cleans up when a client disconnects.
    pub fn client_disconnected(&mut self, client_id: &str) {
        self.clients.remove(client_id);
    }

    /// Handles a command from a connected client.
    pub fn handle_command(&mut self, client_id: &str, command: DebugCommand) {
        if !self.clients.contains_key(client_id) {
            return;
        }

        let result = match command {
            DebugCommand::ListSessions { limit, active_only } => {
                self.handle_list_sessions(client_id, limit, active_only)
            }
            DebugCommand::Subscribe {
                session_id,
                mode,
                from_index,
            } => self.handle_subscribe(client_id, session_id, mode, from_index),
            DebugCommand::Unsubscribe { session_id } => {
                self.handle_unsubscribe(client_id, session_id)
            }
            DebugCommand::Seek {
                session_id,
                timestamp,
            } => self.handle_seek(client_id, session_id, timestamp),
            DebugCommand::PlaybackSpeed { session_id, speed } => {
                self.handle_playback_speed(client_id, session_id, speed)
            }
            DebugCommand::Filter { session_id, filter } => {
                self.handle_set_filter(client_id, session_id, filter)
            }
            DebugCommand::Pause { session_id } => self.handle_pause(client_id, session_id),
            DebugCommand::Resume { session_id } => self.handle_resume(client_id, session_id),
            DebugCommand::StepForward { session_id } => {
                self.handle_step_forward(client_id, session_id)
            }
            DebugCommand::StepBackward { session_id } => {
                self.handle_step_backward(client_id, session_id)
            }
            DebugCommand::SetBreakpoint {
                session_id,
                breakpoint,
            } => self.handle_set_breakpoint(client_id, session_id, breakpoint),
            DebugCommand::ClearBreakpoint {
                session_id,
                breakpoint_id,
            } => self.handle_clear_breakpoint(client_id, session_id, breakpoint_id),
            DebugCommand::ListBreakpoints { session_id } => {
                self.handle_list_breakpoints(client_id, session_id)
            }
            DebugCommand::ListArchives { .. }
            | DebugCommand::ImportArchive { .. }
            | DebugCommand::UploadArchive { .. } => {
                // Archive commands not yet implemented
                Ok(())
            }
        };

        if let Err(e) = result {
            if let Some(client) = self.clients.get(client_id) {
                send(
                    &*client.sink,
                    DebugResponse::Error {
                        code: "COMMAND_ERROR".into(),
                        message: e,
                        session_id: None,
                    },
                );
            }
        }
    }

    /// Delivers a live event to all subscribed clients for the given session.
    pub fn broadcast_event(&mut self, session_id: &str, event: &NetEvent) {
        let event_info = to_event_info(event);

        // Collect client IDs to avoid borrow issues
        let client_ids: Vec<String> = self.clients.keys().cloned().collect();

        for client_id in client_ids {
            let client = self.clients.get_mut(&client_id).unwrap();
            let Some(sub) = client.subscriptions.sessions.get_mut(session_id) else {
                continue;
            };

            if sub.paused {
                continue;
            }

            if !matches_filter(&sub.filter, event) {
                sub.event_index += 1;
                continue;
            }

            // Check breakpoints
            let hit_bp = check_breakpoints(&sub.breakpoints, event);
            let idx = sub.event_index;
            sub.event_index += 1;

            if let Some(bp) = hit_bp {
                sub.paused = true;
                send(
                    &*client.sink,
                    DebugResponse::BreakpointHit {
                        session_id: session_id.to_string(),
                        breakpoint_id: bp.id.clone(),
                        event: event_info.clone(),
                        event_index: idx,
                    },
                );
            }

            send(
                &*client.sink,
                DebugResponse::Event {
                    session_id: session_id.to_string(),
                    index: idx,
                    event: event_info.clone(),
                },
            );
        }
    }

    // ======================== Command Handlers ========================

    fn handle_list_sessions(
        &self,
        client_id: &str,
        limit: Option<usize>,
        active_only: Option<bool>,
    ) -> Result<(), String> {
        let limit = limit.unwrap_or(50);
        let sessions = if active_only.unwrap_or(false) {
            self.session_registry.list_active_sessions(limit)
        } else {
            self.session_registry.list_sessions(limit)
        };

        let summaries: Vec<SessionSummary> = sessions.iter().map(|s| session_summary(s)).collect();

        send_to(
            &self.clients,
            client_id,
            DebugResponse::SessionList {
                sessions: summaries,
            },
        );
        Ok(())
    }

    fn handle_subscribe(
        &mut self,
        client_id: &str,
        session_id: String,
        mode: crate::debug_command::SubscriptionMode,
        from_index: Option<usize>,
    ) -> Result<(), String> {
        let session = self
            .session_registry
            .get_session(&session_id)
            .ok_or_else(|| format!("Session not found: {session_id}"))?;

        let events = session.event_store.events();
        let computed = compute_state(&events);
        let structure = build_net_structure(session);
        let from_index = from_index.unwrap_or(0);

        let mode_str = match mode {
            crate::debug_command::SubscriptionMode::Live => "live",
            crate::debug_command::SubscriptionMode::Replay => "replay",
        };

        let current_marking = computed
            .marking
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        let client = self.clients.get(client_id).unwrap();
        send(
            &*client.sink,
            DebugResponse::Subscribed {
                session_id: session_id.clone(),
                net_name: session.net_name.clone(),
                dot_diagram: session.dot_diagram.clone(),
                structure,
                current_marking,
                enabled_transitions: computed.enabled_transitions.clone(),
                in_flight_transitions: computed.in_flight_transitions.clone(),
                event_count: session.event_store.event_count(),
                mode: mode_str.into(),
            },
        );

        // Send historical events
        let historical = session.event_store.events_from(from_index);
        let converted: Vec<NetEventInfo> = historical.iter().map(|e| to_event_info(e)).collect();
        send_in_batches(
            &self.clients,
            client_id,
            &session_id,
            from_index,
            &converted,
        );

        let event_index = from_index + historical.len();
        let paused = matches!(mode, crate::debug_command::SubscriptionMode::Replay);

        let client = self.clients.get_mut(client_id).unwrap();
        client
            .subscriptions
            .add_subscription(session_id, event_index, paused);

        Ok(())
    }

    fn handle_unsubscribe(&mut self, client_id: &str, session_id: String) -> Result<(), String> {
        if let Some(client) = self.clients.get_mut(client_id) {
            client.subscriptions.cancel(&session_id);
        }
        send_to(
            &self.clients,
            client_id,
            DebugResponse::Unsubscribed { session_id },
        );
        Ok(())
    }

    fn handle_seek(
        &mut self,
        client_id: &str,
        session_id: String,
        timestamp: String,
    ) -> Result<(), String> {
        let session = self
            .session_registry
            .get_session(&session_id)
            .ok_or("Session not found")?;

        let events = session.event_store.events();
        let target_ts: u64 = timestamp.parse().unwrap_or(0);

        let mut target_index = events.len();
        for (i, e) in events.iter().enumerate() {
            if e.timestamp() >= target_ts {
                target_index = i;
                break;
            }
        }

        let client = self.clients.get_mut(client_id).unwrap();
        client
            .subscriptions
            .set_event_index(&session_id, target_index);
        let computed = client
            .subscriptions
            .compute_state_at(&events, &session_id, target_index);

        send(
            &*client.sink,
            DebugResponse::MarkingSnapshot {
                session_id,
                marking: computed.marking,
                enabled_transitions: computed.enabled_transitions,
                in_flight_transitions: computed.in_flight_transitions,
            },
        );
        Ok(())
    }

    fn handle_playback_speed(
        &mut self,
        client_id: &str,
        session_id: String,
        speed: f64,
    ) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client.subscriptions.set_speed(&session_id, speed);
        let paused = client.subscriptions.is_paused(&session_id);
        let current_index = client.subscriptions.get_event_index(&session_id);
        send(
            &*client.sink,
            DebugResponse::PlaybackStateChanged {
                session_id,
                paused,
                speed,
                current_index,
            },
        );
        Ok(())
    }

    fn handle_set_filter(
        &mut self,
        client_id: &str,
        session_id: String,
        filter: EventFilter,
    ) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client.subscriptions.set_filter(&session_id, filter.clone());
        send(
            &*client.sink,
            DebugResponse::FilterApplied { session_id, filter },
        );
        Ok(())
    }

    fn handle_pause(&mut self, client_id: &str, session_id: String) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client.subscriptions.set_paused(&session_id, true);
        let speed = client.subscriptions.get_speed(&session_id);
        let current_index = client.subscriptions.get_event_index(&session_id);
        send(
            &*client.sink,
            DebugResponse::PlaybackStateChanged {
                session_id,
                paused: true,
                speed,
                current_index,
            },
        );
        Ok(())
    }

    fn handle_resume(&mut self, client_id: &str, session_id: String) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client.subscriptions.set_paused(&session_id, false);
        let speed = client.subscriptions.get_speed(&session_id);
        let current_index = client.subscriptions.get_event_index(&session_id);
        send(
            &*client.sink,
            DebugResponse::PlaybackStateChanged {
                session_id,
                paused: false,
                speed,
                current_index,
            },
        );
        Ok(())
    }

    fn handle_step_forward(&mut self, client_id: &str, session_id: String) -> Result<(), String> {
        let session = self
            .session_registry
            .get_session(&session_id)
            .ok_or("Session not found")?;

        let events = session.event_store.events();
        let client = self.clients.get_mut(client_id).unwrap();
        let current_index = client.subscriptions.get_event_index(&session_id);

        if current_index < events.len() {
            let event_info = to_event_info(&events[current_index]);
            send(
                &*client.sink,
                DebugResponse::Event {
                    session_id: session_id.clone(),
                    index: current_index,
                    event: event_info,
                },
            );
            client
                .subscriptions
                .set_event_index(&session_id, current_index + 1);
        }
        Ok(())
    }

    fn handle_step_backward(&mut self, client_id: &str, session_id: String) -> Result<(), String> {
        let session = self
            .session_registry
            .get_session(&session_id)
            .ok_or("Session not found")?;

        let events = session.event_store.events();
        let client = self.clients.get_mut(client_id).unwrap();
        let current_index = client.subscriptions.get_event_index(&session_id);

        if current_index > 0 {
            let new_index = current_index - 1;
            client.subscriptions.set_event_index(&session_id, new_index);
            let computed = client
                .subscriptions
                .compute_state_at(&events, &session_id, new_index);

            send(
                &*client.sink,
                DebugResponse::MarkingSnapshot {
                    session_id,
                    marking: computed.marking,
                    enabled_transitions: computed.enabled_transitions,
                    in_flight_transitions: computed.in_flight_transitions,
                },
            );
        }
        Ok(())
    }

    fn handle_set_breakpoint(
        &mut self,
        client_id: &str,
        session_id: String,
        breakpoint: BreakpointConfig,
    ) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client
            .subscriptions
            .add_breakpoint(&session_id, breakpoint.clone());
        send(
            &*client.sink,
            DebugResponse::BreakpointSet {
                session_id,
                breakpoint,
            },
        );
        Ok(())
    }

    fn handle_clear_breakpoint(
        &mut self,
        client_id: &str,
        session_id: String,
        breakpoint_id: String,
    ) -> Result<(), String> {
        let client = self.clients.get_mut(client_id).unwrap();
        client
            .subscriptions
            .remove_breakpoint(&session_id, &breakpoint_id);
        send(
            &*client.sink,
            DebugResponse::BreakpointCleared {
                session_id,
                breakpoint_id,
            },
        );
        Ok(())
    }

    fn handle_list_breakpoints(&self, client_id: &str, session_id: String) -> Result<(), String> {
        let client = self.clients.get(client_id).unwrap();
        let breakpoints = client.subscriptions.get_breakpoints(&session_id);
        send(
            &*client.sink,
            DebugResponse::BreakpointList {
                session_id,
                breakpoints,
            },
        );
        Ok(())
    }
}

// ======================== Helper Functions ========================

fn send(sink: &dyn ResponseSink, response: DebugResponse) {
    sink.send(response);
}

fn send_to(clients: &HashMap<String, ClientState>, client_id: &str, response: DebugResponse) {
    if let Some(client) = clients.get(client_id) {
        send(&*client.sink, response);
    }
}

fn send_in_batches(
    clients: &HashMap<String, ClientState>,
    client_id: &str,
    session_id: &str,
    start_index: usize,
    events: &[NetEventInfo],
) {
    let Some(client) = clients.get(client_id) else {
        return;
    };

    if events.is_empty() {
        send(
            &*client.sink,
            DebugResponse::EventBatch {
                session_id: session_id.to_string(),
                start_index,
                events: vec![],
                has_more: false,
            },
        );
        return;
    }

    for (i, chunk) in events.chunks(BATCH_SIZE).enumerate() {
        let chunk_start = start_index + i * BATCH_SIZE;
        let has_more = chunk_start + chunk.len() < start_index + events.len();
        send(
            &*client.sink,
            DebugResponse::EventBatch {
                session_id: session_id.to_string(),
                start_index: chunk_start,
                events: chunk.to_vec(),
                has_more,
            },
        );
    }
}

fn session_summary(session: &DebugSession) -> SessionSummary {
    SessionSummary {
        session_id: session.session_id.clone(),
        net_name: session.net_name.clone(),
        start_time: session.start_time.to_string(),
        active: session.active,
        event_count: session.event_store.event_count(),
    }
}

fn matches_filter(filter: &Option<EventFilter>, event: &NetEvent) -> bool {
    let Some(filter) = filter else { return true };

    if let Some(ref types) = filter.event_types {
        if !types.is_empty() {
            let name = event_type_name(event);
            if !types.iter().any(|t| t == name) {
                return false;
            }
        }
    }

    if let Some(ref names) = filter.transition_names {
        if !names.is_empty() {
            let t_name = extract_transition_name(event);
            match t_name {
                Some(n) => {
                    if !names.iter().any(|t| t == n) {
                        return false;
                    }
                }
                None => return false,
            }
        }
    }

    if let Some(ref names) = filter.place_names {
        if !names.is_empty() {
            let p_name = extract_place_name(event);
            match p_name {
                Some(n) => {
                    if !names.iter().any(|t| t == n) {
                        return false;
                    }
                }
                None => return false,
            }
        }
    }

    true
}

fn matches_breakpoint(bp: &BreakpointConfig, event: &NetEvent) -> bool {
    if !bp.enabled {
        return false;
    }
    match bp.bp_type {
        BreakpointType::TransitionEnabled => {
            matches!(event, NetEvent::TransitionEnabled { transition_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == transition_name.as_ref()))
        }
        BreakpointType::TransitionStart => {
            matches!(event, NetEvent::TransitionStarted { transition_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == transition_name.as_ref()))
        }
        BreakpointType::TransitionComplete => {
            matches!(event, NetEvent::TransitionCompleted { transition_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == transition_name.as_ref()))
        }
        BreakpointType::TransitionFail => {
            matches!(event, NetEvent::TransitionFailed { transition_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == transition_name.as_ref()))
        }
        BreakpointType::TokenAdded => {
            matches!(event, NetEvent::TokenAdded { place_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == place_name.as_ref()))
        }
        BreakpointType::TokenRemoved => {
            matches!(event, NetEvent::TokenRemoved { place_name, .. }
                if bp.target.as_ref().is_none_or(|t| t == place_name.as_ref()))
        }
    }
}

fn check_breakpoints(
    breakpoints: &HashMap<String, BreakpointConfig>,
    event: &NetEvent,
) -> Option<BreakpointConfig> {
    for bp in breakpoints.values() {
        if matches_breakpoint(bp, event) {
            return Some(bp.clone());
        }
    }
    None
}

// ======================== Subscription State ========================

struct SessionSubscription {
    event_index: usize,
    marking_cache: MarkingCache,
    breakpoints: HashMap<String, BreakpointConfig>,
    paused: bool,
    speed: f64,
    filter: Option<EventFilter>,
}

struct SubscriptionState {
    sessions: HashMap<String, SessionSubscription>,
}

impl SubscriptionState {
    fn new() -> Self {
        Self {
            sessions: HashMap::new(),
        }
    }

    fn add_subscription(&mut self, session_id: String, event_index: usize, paused: bool) {
        self.sessions.insert(
            session_id,
            SessionSubscription {
                event_index,
                marking_cache: MarkingCache::new(),
                breakpoints: HashMap::new(),
                paused,
                speed: 1.0,
                filter: None,
            },
        );
    }

    fn cancel(&mut self, session_id: &str) {
        self.sessions.remove(session_id);
    }

    fn is_paused(&self, session_id: &str) -> bool {
        self.sessions.get(session_id).is_some_and(|s| s.paused)
    }

    fn set_paused(&mut self, session_id: &str, paused: bool) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.paused = paused;
        }
    }

    fn get_speed(&self, session_id: &str) -> f64 {
        self.sessions.get(session_id).map_or(1.0, |s| s.speed)
    }

    fn set_speed(&mut self, session_id: &str, speed: f64) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.speed = speed;
        }
    }

    fn get_event_index(&self, session_id: &str) -> usize {
        self.sessions.get(session_id).map_or(0, |s| s.event_index)
    }

    fn set_event_index(&mut self, session_id: &str, index: usize) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.event_index = index;
        }
    }

    fn compute_state_at(
        &mut self,
        events: &[NetEvent],
        session_id: &str,
        target_index: usize,
    ) -> crate::marking_cache::ComputedState {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.marking_cache.compute_at(events, target_index)
        } else {
            compute_state(&events[..target_index.min(events.len())])
        }
    }

    fn set_filter(&mut self, session_id: &str, filter: EventFilter) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.filter = Some(filter);
        }
    }

    fn add_breakpoint(&mut self, session_id: &str, breakpoint: BreakpointConfig) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.breakpoints.insert(breakpoint.id.clone(), breakpoint);
        }
    }

    fn remove_breakpoint(&mut self, session_id: &str, breakpoint_id: &str) {
        if let Some(sub) = self.sessions.get_mut(session_id) {
            sub.breakpoints.remove(breakpoint_id);
        }
    }

    fn get_breakpoints(&self, session_id: &str) -> Vec<BreakpointConfig> {
        self.sessions
            .get(session_id)
            .map_or_else(Vec::new, |s| s.breakpoints.values().cloned().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug_event_store::DebugEventStore;
    use std::sync::{Arc, Mutex};

    fn make_handler_with_net() -> (DebugProtocolHandler, Arc<DebugEventStore>) {
        use libpetri_core::input::one;
        use libpetri_core::output::out_place;
        use libpetri_core::place::Place;
        use libpetri_core::transition::Transition;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = libpetri_core::petri_net::PetriNet::builder("test")
            .transition(t)
            .build();

        let mut registry = DebugSessionRegistry::new();
        let store = registry.register("s1".into(), &net);
        let handler = DebugProtocolHandler::new(registry);
        (handler, store)
    }

    fn collector_sink() -> (Box<dyn ResponseSink>, Arc<Mutex<Vec<DebugResponse>>>) {
        let collected = Arc::new(Mutex::new(Vec::new()));
        let collected_clone = Arc::clone(&collected);
        let sink: Box<dyn ResponseSink> = Box::new(move |resp: DebugResponse| {
            collected_clone.lock().unwrap().push(resp);
        });
        (sink, collected)
    }

    #[test]
    fn list_sessions() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::ListSessions {
                limit: None,
                active_only: None,
            },
        );

        let responses = collected.lock().unwrap();
        assert_eq!(responses.len(), 1);
        match &responses[0] {
            DebugResponse::SessionList { sessions } => {
                assert_eq!(sessions.len(), 1);
                assert_eq!(sessions[0].net_name, "test");
            }
            _ => panic!("expected SessionList"),
        }
    }

    #[test]
    fn subscribe_and_unsubscribe() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: crate::debug_command::SubscriptionMode::Live,
                from_index: None,
            },
        );

        {
            let responses = collected.lock().unwrap();
            assert!(responses.len() >= 1);
            match &responses[0] {
                DebugResponse::Subscribed {
                    session_id,
                    net_name,
                    ..
                } => {
                    assert_eq!(session_id, "s1");
                    assert_eq!(net_name, "test");
                }
                _ => panic!("expected Subscribed"),
            }
        }

        handler.handle_command(
            "c1",
            DebugCommand::Unsubscribe {
                session_id: "s1".into(),
            },
        );

        let responses = collected.lock().unwrap();
        let last = responses.last().unwrap();
        match last {
            DebugResponse::Unsubscribed { session_id } => {
                assert_eq!(session_id, "s1");
            }
            _ => panic!("expected Unsubscribed"),
        }
    }

    #[test]
    fn subscribe_to_nonexistent_session() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "nonexistent".into(),
                mode: crate::debug_command::SubscriptionMode::Live,
                from_index: None,
            },
        );

        let responses = collected.lock().unwrap();
        match &responses[0] {
            DebugResponse::Error { code, .. } => assert_eq!(code, "COMMAND_ERROR"),
            _ => panic!("expected Error"),
        }
    }

    #[test]
    fn pause_and_resume() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: crate::debug_command::SubscriptionMode::Live,
                from_index: None,
            },
        );

        handler.handle_command(
            "c1",
            DebugCommand::Pause {
                session_id: "s1".into(),
            },
        );

        let responses = collected.lock().unwrap();
        let pause_resp = responses
            .iter()
            .find(|r| matches!(r, DebugResponse::PlaybackStateChanged { paused: true, .. }));
        assert!(pause_resp.is_some());
    }

    #[test]
    fn set_and_list_breakpoints() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: crate::debug_command::SubscriptionMode::Live,
                from_index: None,
            },
        );

        handler.handle_command(
            "c1",
            DebugCommand::SetBreakpoint {
                session_id: "s1".into(),
                breakpoint: BreakpointConfig {
                    id: "bp1".into(),
                    bp_type: BreakpointType::TransitionStart,
                    target: Some("t1".into()),
                    enabled: true,
                },
            },
        );

        handler.handle_command(
            "c1",
            DebugCommand::ListBreakpoints {
                session_id: "s1".into(),
            },
        );

        let responses = collected.lock().unwrap();
        let bp_list = responses
            .iter()
            .find(|r| matches!(r, DebugResponse::BreakpointList { .. }));
        match bp_list.unwrap() {
            DebugResponse::BreakpointList { breakpoints, .. } => {
                assert_eq!(breakpoints.len(), 1);
                assert_eq!(breakpoints[0].id, "bp1");
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn broadcast_event_to_subscribers() {
        let (mut handler, store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: crate::debug_command::SubscriptionMode::Live,
                from_index: None,
            },
        );

        let event = NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 1000,
        };
        store.append(event.clone());
        handler.broadcast_event("s1", &event);

        let responses = collected.lock().unwrap();
        let event_resp = responses
            .iter()
            .find(|r| matches!(r, DebugResponse::Event { .. }));
        assert!(event_resp.is_some());
    }

    #[test]
    fn filter_matching() {
        let event = NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 0,
        };

        // No filter — matches all
        assert!(matches_filter(&None, &event));

        // Type filter matching
        let filter = EventFilter {
            event_types: Some(vec!["TransitionStarted".into()]),
            transition_names: None,
            place_names: None,
        };
        assert!(matches_filter(&Some(filter), &event));

        // Type filter not matching
        let filter = EventFilter {
            event_types: Some(vec!["TokenAdded".into()]),
            transition_names: None,
            place_names: None,
        };
        assert!(!matches_filter(&Some(filter), &event));

        // Transition name filter
        let filter = EventFilter {
            event_types: None,
            transition_names: Some(vec!["t1".into()]),
            place_names: None,
        };
        assert!(matches_filter(&Some(filter), &event));

        let filter = EventFilter {
            event_types: None,
            transition_names: Some(vec!["t2".into()]),
            place_names: None,
        };
        assert!(!matches_filter(&Some(filter), &event));
    }

    #[test]
    fn breakpoint_matching() {
        let event = NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 0,
        };

        let bp = BreakpointConfig {
            id: "bp1".into(),
            bp_type: BreakpointType::TransitionStart,
            target: Some("t1".into()),
            enabled: true,
        };
        assert!(matches_breakpoint(&bp, &event));

        // Disabled breakpoint
        let bp_disabled = BreakpointConfig {
            id: "bp2".into(),
            bp_type: BreakpointType::TransitionStart,
            target: Some("t1".into()),
            enabled: false,
        };
        assert!(!matches_breakpoint(&bp_disabled, &event));

        // Wrong target
        let bp_wrong = BreakpointConfig {
            id: "bp3".into(),
            bp_type: BreakpointType::TransitionStart,
            target: Some("t2".into()),
            enabled: true,
        };
        assert!(!matches_breakpoint(&bp_wrong, &event));

        // Wildcard (no target)
        let bp_wild = BreakpointConfig {
            id: "bp4".into(),
            bp_type: BreakpointType::TransitionStart,
            target: None,
            enabled: true,
        };
        assert!(matches_breakpoint(&bp_wild, &event));
    }

    #[test]
    fn client_disconnect_cleanup() {
        let (mut handler, _store) = make_handler_with_net();
        let (sink, _collected) = collector_sink();
        handler.client_connected("c1".into(), sink);
        handler.client_disconnected("c1");
        assert!(handler.clients.is_empty());
    }

    #[test]
    fn step_forward_and_backward() {
        let (mut handler, store) = make_handler_with_net();
        let (sink, collected) = collector_sink();
        handler.client_connected("c1".into(), sink);

        // Add some events
        for i in 0..5 {
            store.append(NetEvent::TokenAdded {
                place_name: Arc::from("p1"),
                timestamp: i,
            });
        }

        handler.handle_command(
            "c1",
            DebugCommand::Subscribe {
                session_id: "s1".into(),
                mode: crate::debug_command::SubscriptionMode::Replay,
                from_index: Some(0),
            },
        );

        // Step forward
        handler.handle_command(
            "c1",
            DebugCommand::StepForward {
                session_id: "s1".into(),
            },
        );

        // Step backward
        handler.handle_command(
            "c1",
            DebugCommand::StepBackward {
                session_id: "s1".into(),
            },
        );

        let responses = collected.lock().unwrap();
        assert!(responses.len() >= 3); // subscribed + batch + step responses
    }
}
