//! The shared 5-phase CTPN execution loop.
//!
//! [`Executor<S, E>`] owns the cross-cutting state — event store,
//! monotonic clock, environment-place flag, async signal channel — and
//! drives the loop against an [`ExecutorBackend`] that supplies the
//! storage primitives (enablement, token mutation, dirty tracking).
//!
//! Public type aliases live with each backend:
//! - [`BitmapNetExecutor<E>`](crate::executor::BitmapNetExecutor)
//!   `= Executor<BitmapBackend, E>` — reference / verification path.
//! - `PrecompiledNetExecutor<'a, E>` (added in step 4) — production hot
//!   path.

use std::borrow::Cow;
use std::sync::Arc;
use std::time::Instant;

use libpetri_core::context::TransitionContext;
use libpetri_event::event_store::EventStore;
use libpetri_event::net_event::NetEvent;

use crate::executor_core::backend::{ConsumedInputs, EnablementChanges, ExecutorBackend};
use crate::executor_core::deadline::{elapsed_ms_since, now_millis};
use crate::executor_core::event_payload::{token_added_event, token_removed_event};
use crate::marking::Marking;

/// Shared executor over an [`ExecutorBackend`] and an `EventStore`.
///
/// Monomorphised per backend (`Executor<BitmapBackend, E>` is the
/// reference; `Executor<PrecompiledBackend<'_>, E>` is the production
/// hot path). The struct + 5-phase loop are written once; each backend
/// supplies storage semantics.
///
/// Public so type aliases like
/// [`BitmapNetExecutor<E>`](crate::executor::BitmapNetExecutor) can
/// expose it.
pub struct Executor<S: ExecutorBackend, E: EventStore> {
    backend: S,
    event_store: E,
    start_time: Instant,

    /// True when the configured net references any environment places.
    /// The async loop short-circuits the event-injection phase when this
    /// is false. The sync loop uses it to decide whether to terminate
    /// at quiescence (no env places) or wait (env places exist).
    has_environment_places: bool,
}

impl<S: ExecutorBackend, E: EventStore> Executor<S, E> {
    /// Wraps a configured backend with cross-cutting executor state.
    /// The backend is expected to be constructed with the net's initial
    /// marking already loaded.
    pub fn from_parts(backend: S, event_store: E, has_environment_places: bool) -> Self {
        Self {
            backend,
            event_store,
            start_time: Instant::now(),
            has_environment_places,
        }
    }

    /// Borrow the event store.
    pub fn event_store(&self) -> &E {
        &self.event_store
    }

    /// Snapshot the current marking. Zero-copy on `BitmapBackend`;
    /// materialises from ring buffers on `PrecompiledBackend`.
    pub fn marking(&self) -> Cow<'_, Marking> {
        self.backend.snapshot_marking()
    }

    /// True when no transition is enabled.
    pub fn is_quiescent(&self) -> bool {
        self.backend.is_quiescent()
    }

    #[inline]
    fn elapsed_ms(&self) -> f64 {
        elapsed_ms_since(self.start_time)
    }

    /// Runs the executor synchronously until completion. All transition
    /// actions must be sync (`Action::is_sync()` returns `true`).
    pub fn run_sync(&mut self) -> Cow<'_, Marking> {
        self.backend.initialize();

        if E::ENABLED {
            let net_name: Arc<str> = self.backend.compiled().net().name().into();
            self.event_store.append(NetEvent::ExecutionStarted {
                net_name,
                timestamp: now_millis(),
            });
        }

        let mut changes = EnablementChanges::default();
        let mut timed_out: Vec<usize> = Vec::new();
        let mut ready: Vec<usize> = Vec::new();

        loop {
            let cycle_now = self.elapsed_ms();
            self.update_enablement_and_emit(cycle_now, &mut changes);

            if self.backend.has_any_deadlines() {
                timed_out.clear();
                self.backend.enforce_deadlines(cycle_now, &mut timed_out);
                if E::ENABLED {
                    let ts = now_millis();
                    for &tid in &timed_out {
                        let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                        self.event_store.append(NetEvent::TransitionTimedOut {
                            transition_name: name,
                            timestamp: ts,
                        });
                    }
                }
            }

            if !self.has_environment_places && self.backend.enabled_count() == 0 {
                break;
            }

            ready.clear();
            if self.backend.fast_path_available() {
                self.backend.collect_ready_immediate(&mut ready);
            } else {
                self.backend.collect_ready_general(cycle_now, &mut ready);
            }

            for i in 0..ready.len() {
                let tid = ready[i];
                if self.backend.recheck_can_fire(tid) {
                    self.fire_transition_sync(tid);
                } else {
                    self.backend.disable(tid);
                }
            }

            if !self.backend.has_dirty_bits() && self.backend.enabled_count() == 0 {
                break;
            }
        }

        if E::ENABLED {
            let net_name: Arc<str> = self.backend.compiled().net().name().into();
            self.event_store.append(NetEvent::ExecutionCompleted {
                net_name,
                timestamp: now_millis(),
            });
        }

        self.backend.snapshot_marking()
    }

    /// Drives backend enablement and emits the resulting events.
    #[inline]
    fn update_enablement_and_emit(&mut self, now_ms: f64, changes: &mut EnablementChanges) {
        changes.newly_enabled.clear();
        changes.clock_restarted.clear();
        self.backend.update_enablement(now_ms, changes);

        if E::ENABLED {
            let ts = now_millis();
            for &tid in &changes.newly_enabled {
                let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                self.event_store.append(NetEvent::TransitionEnabled {
                    transition_name: name,
                    timestamp: ts,
                });
            }
            for &tid in &changes.clock_restarted {
                let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                self.event_store.append(NetEvent::TransitionClockRestarted {
                    transition_name: name,
                    timestamp: ts,
                });
            }
        }
    }

    /// Fire a single transition synchronously: consume inputs, run the
    /// action inline, process outputs, post-fire housekeeping.
    fn fire_transition_sync(&mut self, tid: usize) {
        let (transition_name, action, output_place_names) = {
            let t = self.backend.compiled().transition(tid);
            let name = Arc::clone(t.name_arc());
            let action = Arc::clone(t.action());
            let outputs = t
                .output_places()
                .iter()
                .map(|p| Arc::clone(p.name_arc()))
                .collect();
            (name, action, outputs)
        };

        let consumed = self.consume_and_emit(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        let mut ctx = TransitionContext::new(
            Arc::clone(&transition_name),
            consumed.inputs,
            consumed.reads,
            output_place_names,
            None,
        );

        let result = action.run_sync(&mut ctx);
        match result {
            Ok(()) => {
                self.process_outputs(&mut ctx);
                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionCompleted {
                        transition_name: Arc::clone(&transition_name),
                        timestamp: now_millis(),
                    });
                }
            }
            Err(err) => {
                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionFailed {
                        transition_name: Arc::clone(&transition_name),
                        error: err.message,
                        timestamp: now_millis(),
                    });
                }
            }
        }

        self.backend.post_fire(tid);
    }

    /// Drive the backend's consume phase, emitting `TokenRemoved`
    /// events in spec-declaration order via the closure.
    #[inline]
    fn consume_and_emit(&mut self, tid: usize) -> ConsumedInputs {
        // Borrow split: capture &mut event_store via a re-borrow that
        // lives separately from the &mut backend call below.
        let Self {
            backend,
            event_store,
            ..
        } = self;
        backend.consume_for_firing(tid, |place, token| {
            if E::ENABLED {
                event_store.append(token_removed_event::<E>(
                    Arc::clone(place),
                    now_millis(),
                    token,
                ));
            }
        })
    }

    /// Move outputs from `ctx` into the backend's storage, emitting
    /// `TokenAdded` events in produce-order.
    #[inline]
    fn process_outputs(&mut self, ctx: &mut TransitionContext) {
        let outputs = ctx.take_outputs();
        for entry in outputs {
            let event = if E::ENABLED {
                Some(token_added_event::<E>(
                    Arc::clone(&entry.place_name),
                    now_millis(),
                    &entry.token,
                ))
            } else {
                None
            };
            self.backend.produce_token(&entry.place_name, entry.token);
            if let Some(ev) = event {
                self.event_store.append(ev);
            }
        }
    }
}

// ============================ Async loop ============================

#[cfg(feature = "tokio")]
use crate::environment::ExecutorSignal;

#[cfg(feature = "tokio")]
use libpetri_core::context::OutputEntry;

/// Completion message sent by spawned async transition tasks back to
/// the executor.
#[cfg(feature = "tokio")]
struct ActionCompletion {
    transition_name: Arc<str>,
    result: Result<Vec<OutputEntry>, String>,
}

#[cfg(feature = "tokio")]
impl<S: ExecutorBackend, E: EventStore> Executor<S, E> {
    /// Run the executor asynchronously with tokio. Supports sync and
    /// async transition actions; sync actions run inline, async actions
    /// are spawned as tokio tasks whose completions feed back through
    /// an mpsc channel.
    pub async fn run_async(
        &mut self,
        mut signal_rx: tokio::sync::mpsc::UnboundedReceiver<ExecutorSignal>,
    ) -> Cow<'_, Marking> {
        let (completion_tx, mut completion_rx) =
            tokio::sync::mpsc::unbounded_channel::<ActionCompletion>();

        self.backend.initialize();

        let mut in_flight_count: usize = 0;
        let mut signal_channel_open = true;
        let mut draining = false;
        let mut closed = false;

        if E::ENABLED {
            let net_name: Arc<str> = self.backend.compiled().net().name().into();
            self.event_store.append(NetEvent::ExecutionStarted {
                net_name,
                timestamp: now_millis(),
            });
        }

        let mut changes = EnablementChanges::default();
        let mut timed_out: Vec<usize> = Vec::new();
        let mut ready: Vec<usize> = Vec::new();

        loop {
            // Phase 1: process completed async actions.
            while let Ok(completion) = completion_rx.try_recv() {
                in_flight_count -= 1;
                self.handle_completion(completion);
            }

            // Phase 2: drain queued signals (events + lifecycle).
            while let Ok(signal) = signal_rx.try_recv() {
                self.handle_signal(signal, &mut draining, &mut closed, &mut signal_rx);
            }

            // Phase 3: update enablement and emit events.
            let cycle_now = self.elapsed_ms();
            self.update_enablement_and_emit(cycle_now, &mut changes);

            // Phase 4: enforce deadlines.
            if self.backend.has_any_deadlines() {
                timed_out.clear();
                self.backend.enforce_deadlines(cycle_now, &mut timed_out);
                if E::ENABLED {
                    let ts = now_millis();
                    for &tid in &timed_out {
                        let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                        self.event_store.append(NetEvent::TransitionTimedOut {
                            transition_name: name,
                            timestamp: ts,
                        });
                    }
                }
            }

            // Termination checks (O(1)).
            if closed && in_flight_count == 0 {
                break;
            }
            if draining && self.backend.enabled_count() == 0 && in_flight_count == 0 {
                break;
            }
            if self.backend.enabled_count() == 0
                && in_flight_count == 0
                && (!self.has_environment_places || !signal_channel_open)
            {
                break;
            }

            // Phase 5: fire ready transitions (async-aware).
            ready.clear();
            if self.backend.fast_path_available() {
                self.backend.collect_ready_immediate(&mut ready);
            } else {
                self.backend.collect_ready_general(cycle_now, &mut ready);
            }

            let mut fired_any = false;
            for i in 0..ready.len() {
                let tid = ready[i];
                if self.backend.recheck_can_fire(tid) {
                    self.fire_transition_async(tid, &completion_tx, &mut in_flight_count);
                    fired_any = true;
                } else {
                    self.backend.disable(tid);
                }
            }

            if fired_any || self.backend.has_dirty_bits() {
                tokio::task::yield_now().await;
                continue;
            }

            // Phase 6: await work — completion, signal, or timer.
            if in_flight_count == 0
                && !self.has_environment_places
                && self.backend.enabled_count() == 0
            {
                break;
            }
            if in_flight_count == 0
                && self.backend.enabled_count() == 0
                && (draining || !signal_channel_open)
            {
                break;
            }

            let timer_ms = self.backend.millis_until_next_timed_transition(cycle_now);

            tokio::select! {
                Some(completion) = completion_rx.recv() => {
                    in_flight_count -= 1;
                    self.handle_completion(completion);
                }
                result = signal_rx.recv(), if signal_channel_open && !closed => {
                    match result {
                        Some(signal) => {
                            self.handle_signal(signal, &mut draining, &mut closed, &mut signal_rx);
                        }
                        None => {
                            signal_channel_open = false;
                        }
                    }
                }
                _ = tokio::time::sleep(std::time::Duration::from_millis(
                    if timer_ms < f64::INFINITY { timer_ms as u64 } else { 60_000 }
                )) => {}
            }
        }

        if E::ENABLED {
            let net_name: Arc<str> = self.backend.compiled().net().name().into();
            self.event_store.append(NetEvent::ExecutionCompleted {
                net_name,
                timestamp: now_millis(),
            });
        }

        self.backend.snapshot_marking()
    }

    /// Handle an action-completion message: emit
    /// `TransitionCompleted` (with outputs) or `TransitionFailed`.
    #[inline]
    fn handle_completion(&mut self, completion: ActionCompletion) {
        match completion.result {
            Ok(outputs) => {
                for entry in outputs {
                    let event = if E::ENABLED {
                        Some(token_added_event::<E>(
                            Arc::clone(&entry.place_name),
                            now_millis(),
                            &entry.token,
                        ))
                    } else {
                        None
                    };
                    self.backend.produce_token(&entry.place_name, entry.token);
                    if let Some(ev) = event {
                        self.event_store.append(ev);
                    }
                }
                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionCompleted {
                        transition_name: Arc::clone(&completion.transition_name),
                        timestamp: now_millis(),
                    });
                }
            }
            Err(err) => {
                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionFailed {
                        transition_name: Arc::clone(&completion.transition_name),
                        error: err,
                        timestamp: now_millis(),
                    });
                }
            }
        }
    }

    /// Handle a single executor signal (event injection or lifecycle).
    #[inline]
    fn handle_signal(
        &mut self,
        signal: ExecutorSignal,
        draining: &mut bool,
        closed: &mut bool,
        signal_rx: &mut tokio::sync::mpsc::UnboundedReceiver<ExecutorSignal>,
    ) {
        match signal {
            ExecutorSignal::Event(event) if !*draining => {
                let captured = if E::ENABLED {
                    Some(token_added_event::<E>(
                        Arc::clone(&event.place_name),
                        now_millis(),
                        &event.token,
                    ))
                } else {
                    None
                };
                self.backend
                    .inject_external_token(&event.place_name, event.token);
                if let Some(ev) = captured {
                    self.event_store.append(ev);
                }
            }
            ExecutorSignal::Event(_) => {
                // Draining: discard events arriving after drain signal.
            }
            ExecutorSignal::Drain => {
                *draining = true;
            }
            ExecutorSignal::Close => {
                *closed = true;
                *draining = true;
                // ENV-013: discard remaining queued signals.
                while signal_rx.try_recv().is_ok() {}
            }
        }
    }

    /// Fire one transition: consume inputs, then either run sync action
    /// inline (same as `fire_transition_sync`) or spawn the async
    /// action as a tokio task whose completion feeds the completion
    /// channel.
    fn fire_transition_async(
        &mut self,
        tid: usize,
        completion_tx: &tokio::sync::mpsc::UnboundedSender<ActionCompletion>,
        in_flight_count: &mut usize,
    ) {
        let (transition_name, action, output_place_names) = {
            let t = self.backend.compiled().transition(tid);
            let name = Arc::clone(t.name_arc());
            let action = Arc::clone(t.action());
            let outputs = t
                .output_places()
                .iter()
                .map(|p| Arc::clone(p.name_arc()))
                .collect();
            (name, action, outputs)
        };
        let is_sync = action.is_sync();

        let consumed = self.consume_and_emit(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        // Disable + mark dirty before running the action (sync inline
        // or async spawn) so that re-evaluation next cycle sees the
        // transition as a candidate again.
        self.backend.post_fire(tid);

        if is_sync {
            let mut ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                consumed.inputs,
                consumed.reads,
                output_place_names,
                None,
            );
            let result = action.run_sync(&mut ctx);
            match result {
                Ok(()) => {
                    self.process_outputs(&mut ctx);
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionCompleted {
                            transition_name: Arc::clone(&transition_name),
                            timestamp: now_millis(),
                        });
                    }
                }
                Err(err) => {
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionFailed {
                            transition_name: Arc::clone(&transition_name),
                            error: err.message,
                            timestamp: now_millis(),
                        });
                    }
                }
            }
        } else {
            *in_flight_count += 1;
            let tx = completion_tx.clone();
            let name = Arc::clone(&transition_name);
            let ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                consumed.inputs,
                consumed.reads,
                output_place_names,
                None,
            );
            tokio::spawn(async move {
                let result = action.run_async(ctx).await;
                let completion = match result {
                    Ok(mut completed_ctx) => ActionCompletion {
                        transition_name: Arc::clone(&name),
                        result: Ok(completed_ctx.take_outputs()),
                    },
                    Err(err) => ActionCompletion {
                        transition_name: Arc::clone(&name),
                        result: Err(err.message),
                    },
                };
                let _ = tx.send(completion);
            });
        }
    }
}
