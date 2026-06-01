//! The shared 6-phase CTPN execution loop.
//!
//! [`Executor<S, E>`] owns the cross-cutting state — event store,
//! monotonic clock, environment-place flag, reusable HashMap buffers,
//! async signal channel — and drives the loop against an
//! [`ExecutorBackend`] that supplies the storage primitives
//! (enablement, token mutation, dirty tracking).
//!
//! Public type aliases live with each backend:
//! - [`BitmapNetExecutor<E>`](crate::executor::BitmapNetExecutor)
//!   `= Executor<BitmapBackend, E>` — reference / verification path.
//! - [`PrecompiledNetExecutor<'a, E>`](crate::precompiled_executor::PrecompiledNetExecutor)
//!   `= Executor<PrecompiledBackend<'a>, E>` — production hot path.

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Instant;

use libpetri_core::context::TransitionContext;
use libpetri_core::token::ErasedToken;
use libpetri_event::event_store::EventStore;
use libpetri_event::net_event::NetEvent;

use crate::executor_core::backend::{
    ExecutorBackend, NoopChangeTracker, RecordingChangeTracker,
};
use crate::executor_core::deadline::{elapsed_ms_since, now_millis};
use crate::executor_core::event_payload::{token_added_event, token_removed_event};
use crate::marking::Marking;

/// Shared executor over an [`ExecutorBackend`] and an `EventStore`.
///
/// Monomorphised per backend (`Executor<BitmapBackend, E>` is the
/// reference; `Executor<PrecompiledBackend<'_>, E>` is the production
/// hot path). The struct + 6-phase loop are written once; each backend
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

    /// Reusable HashMap for `TransitionContext` inputs, kept across
    /// firings to avoid per-firing allocation. Cleared by the loop
    /// before each `consume_for_firing` call, then moved into the
    /// context and reclaimed via `take_inputs()` after the action.
    reusable_inputs: HashMap<Arc<str>, Vec<ErasedToken>>,

    /// Companion to [`reusable_inputs`](Self::reusable_inputs) for
    /// read-arc tokens.
    reusable_reads: HashMap<Arc<str>, Vec<ErasedToken>>,
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
            reusable_inputs: HashMap::new(),
            reusable_reads: HashMap::new(),
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

        let mut newly_enabled: Vec<usize> = Vec::new();
        let mut clock_restarted: Vec<usize> = Vec::new();
        let mut timed_out: Vec<usize> = Vec::new();
        let mut ready: Vec<usize> = Vec::new();

        loop {
            let cycle_now = self.elapsed_ms();
            self.update_enablement_and_emit(cycle_now, &mut newly_enabled, &mut clock_restarted);

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

            for &tid in &ready {
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
    /// When `E::ENABLED` is false, passes
    /// [`NoopChangeTracker`](crate::executor_core::backend::NoopChangeTracker)
    /// so the backend's tracking calls compile to no-ops and the
    /// per-cycle Vec stays unallocated — measurable on the small
    /// single-passthrough / fan-out micro-benchmarks.
    #[inline]
    fn update_enablement_and_emit(
        &mut self,
        now_ms: f64,
        newly_enabled: &mut Vec<usize>,
        clock_restarted: &mut Vec<usize>,
    ) {
        if E::ENABLED {
            newly_enabled.clear();
            clock_restarted.clear();
            let mut tracker = RecordingChangeTracker {
                newly_enabled,
                clock_restarted,
            };
            self.backend.update_enablement(now_ms, &mut tracker);

            let ts = now_millis();
            for &tid in newly_enabled.iter() {
                let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                self.event_store.append(NetEvent::TransitionEnabled {
                    transition_name: name,
                    timestamp: ts,
                });
            }
            for &tid in clock_restarted.iter() {
                let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
                self.event_store.append(NetEvent::TransitionClockRestarted {
                    transition_name: name,
                    timestamp: ts,
                });
            }
        } else {
            let mut tracker = NoopChangeTracker;
            self.backend.update_enablement(now_ms, &mut tracker);
        }
    }

    /// Drive the backend's consume phase, emitting `TokenRemoved`
    /// events in spec-declaration order via a closure. Fills the
    /// reusable input/read buffers in place.
    #[inline]
    fn consume_and_emit(&mut self, tid: usize) {
        self.reusable_inputs.clear();
        self.reusable_reads.clear();
        let Self {
            backend,
            event_store,
            reusable_inputs,
            reusable_reads,
            ..
        } = self;
        backend.consume_for_firing(tid, reusable_inputs, reusable_reads, |place, token| {
            if E::ENABLED {
                event_store.append(token_removed_event::<E>(
                    Arc::clone(place),
                    now_millis(),
                    token,
                ));
            }
        });
    }

    /// Fire a single transition synchronously: consume inputs, run the
    /// action inline, process outputs, post-fire housekeeping.
    fn fire_transition_sync(&mut self, tid: usize) {
        let (transition_name, action, output_place_names) = {
            let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
            let action = Arc::clone(self.backend.compiled().transition(tid).action());
            let outputs = self.backend.output_place_names(tid);
            (name, action, outputs)
        };

        self.consume_and_emit(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        let inputs = std::mem::take(&mut self.reusable_inputs);
        let reads = std::mem::take(&mut self.reusable_reads);
        let mut ctx = TransitionContext::new(
            Arc::clone(&transition_name),
            inputs,
            reads,
            output_place_names,
            None,
        );

        let result = action.run_sync(&mut ctx);

        // Reclaim buffers before processing outputs so the next firing
        // reuses the HashMap allocations.
        self.reusable_inputs = ctx.take_inputs();
        self.reusable_reads = ctx.take_reads();

        match result {
            Ok(()) => {
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
    /// `Some(timeout_ms)` when this completion came from an
    /// `Out::Timeout` budget expiring rather than the action finishing
    /// normally. Drives the `ActionTimedOut` event in
    /// [`handle_completion`](Executor::handle_completion).
    timed_out: Option<u64>,
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

        let mut newly_enabled: Vec<usize> = Vec::new();
        let mut clock_restarted: Vec<usize> = Vec::new();
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
            self.update_enablement_and_emit(cycle_now, &mut newly_enabled, &mut clock_restarted);

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
            for &tid in &ready {
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
                // [IO-013]/[EXEC-022]: a timed-out async action emits
                // ActionTimedOut (not TransitionCompleted) before its
                // timeout-branch tokens are deposited.
                if E::ENABLED && let Some(timeout_ms) = completion.timed_out {
                    self.event_store.append(NetEvent::ActionTimedOut {
                        transition_name: Arc::clone(&completion.transition_name),
                        timeout_ms,
                        timestamp: now_millis(),
                    });
                }
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
                if E::ENABLED && completion.timed_out.is_none() {
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
            ExecutorSignal::Snapshot(reply) => {
                // Mid-execution marking snapshot per ExecutorHandle::snapshot.
                // One arm covers both backends: bitmap clones its Marking,
                // precompiled materialises from its ring buffers — both via
                // snapshot_marking(). Receiver gone = silently drop.
                let _ = reply.send(self.backend.snapshot_marking().into_owned());
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
            let name = Arc::clone(self.backend.compiled().transition(tid).name_arc());
            let action = Arc::clone(self.backend.compiled().transition(tid).action());
            let outputs = self.backend.output_place_names(tid);
            (name, action, outputs)
        };
        let is_sync = action.is_sync();

        self.consume_and_emit(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        // Disable + mark dirty before running the action (sync inline
        // or async spawn) so re-evaluation next cycle sees the
        // transition as a candidate again.
        self.backend.post_fire(tid);

        let inputs = std::mem::take(&mut self.reusable_inputs);
        let reads = std::mem::take(&mut self.reusable_reads);

        if is_sync {
            let mut ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                inputs,
                reads,
                output_place_names,
                None,
            );
            let result = action.run_sync(&mut ctx);
            self.reusable_inputs = ctx.take_inputs();
            self.reusable_reads = ctx.take_reads();
            match result {
                Ok(()) => {
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
            // Async spawn: the spawned task owns its own HashMaps; we
            // don't reclaim the reusable buffers in this path because
            // the context moves into the task. Fresh allocations next
            // firing — async hot paths are dominated by tokio overhead,
            // not HashMap construction.
            *in_flight_count += 1;
            let tx = completion_tx.clone();
            let name = Arc::clone(&transition_name);

            // Capture the Out::Timeout budget (if any) before moving
            // ctx into the spawned task. The `child` Out is cloned out
            // of the transition's static spec so the spawned task can
            // build its timeout outputs without borrowing back into
            // self.backend.
            let timeout_info = libpetri_core::output::find_timeout(
                self.backend.compiled().transition(tid).output_spec().unwrap_or(&NO_OUTPUT_SPEC),
            )
            .map(|(after_ms, child)| (after_ms, child.clone()));

            // [EXEC-022] c3: if the timeout branch forwards inputs, snapshot
            // the consumed token(s) now — `inputs` is about to move into the
            // context, and that context is dropped when the action future is
            // cancelled on timeout. Gated on the presence of a ForwardInput
            // so the common path allocates nothing extra.
            let forwarded_inputs: HashMap<Arc<str>, Vec<ErasedToken>> =
                match timeout_info.as_ref() {
                    Some((_, child)) => libpetri_core::output::find_forward_inputs(child)
                        .into_iter()
                        .filter_map(|(from, _to)| {
                            inputs
                                .get(from.name())
                                .map(|tokens| (Arc::clone(from.name_arc()), tokens.clone()))
                        })
                        .collect(),
                    None => HashMap::new(),
                };

            let ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                inputs,
                reads,
                output_place_names,
                None,
            );

            tokio::spawn(async move {
                let completion = if let Some((after_ms, timeout_child)) = timeout_info {
                    tokio::select! {
                        biased;
                        result = action.run_async(ctx) => action_completion(&name, result),
                        _ = tokio::time::sleep(std::time::Duration::from_millis(after_ms)) => {
                            ActionCompletion {
                                transition_name: Arc::clone(&name),
                                result: Ok(crate::executor_core::output::timeout_outputs(
                                    &timeout_child,
                                    &forwarded_inputs,
                                )),
                                timed_out: Some(after_ms),
                            }
                        }
                    }
                } else {
                    action_completion(&name, action.run_async(ctx).await)
                };
                let _ = tx.send(completion);
            });
        }
    }
}

/// A neutral output spec used only as a placeholder when `output_spec()`
/// is `None`: `find_timeout` walks the tree and returns `None` for
/// `Out::Place`, which is what we want for "no timeout".
#[cfg(feature = "tokio")]
static NO_OUTPUT_SPEC: std::sync::LazyLock<libpetri_core::output::Out> =
    std::sync::LazyLock::new(|| {
        libpetri_core::output::Out::Place(libpetri_core::place::PlaceRef::new(Arc::from(
            "__no_output__",
        )))
    });

#[cfg(feature = "tokio")]
#[inline]
fn action_completion(
    name: &Arc<str>,
    result: Result<TransitionContext, libpetri_core::action::ActionError>,
) -> ActionCompletion {
    match result {
        Ok(mut completed_ctx) => ActionCompletion {
            transition_name: Arc::clone(name),
            result: Ok(completed_ctx.take_outputs()),
            timed_out: None,
        },
        Err(err) => ActionCompletion {
            transition_name: Arc::clone(name),
            result: Err(err.message),
            timed_out: None,
        },
    }
}
