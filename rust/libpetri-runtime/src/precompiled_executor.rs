//! `PrecompiledNetExecutor` — the public type alias surface for the
//! precompiled (production hot path) executor.
//!
//! The 6-phase loop lives in
//! [`Executor`](crate::executor_core::executor::Executor); the
//! precompiled state lives in
//! [`PrecompiledBackend`](crate::precompiled_backend::PrecompiledBackend).
//! This module only wires them together via a type alias + a builder +
//! a few convenience constructors.

use std::collections::HashSet;
use std::sync::Arc;

use libpetri_event::event_store::EventStore;

use crate::executor_core::executor::Executor;
use crate::marking::Marking;
use crate::precompiled_backend::PrecompiledBackend;
use crate::precompiled_net::PrecompiledNet;

/// High-performance executor over a borrowed [`PrecompiledNet`].
///
/// Type alias over the shared
/// [`Executor`](crate::executor_core::executor::Executor) parameterised
/// by [`PrecompiledBackend`]. The 6-phase loop, event emission, and
/// action execution live in `Executor`; the ring buffer token pool,
/// presence / enablement / dirty bitmaps, priority-partitioned ready
/// queues, opcode-based consume dispatch, and reset-clock detection
/// live in the backend.
pub type PrecompiledNetExecutor<'a, E> = Executor<PrecompiledBackend<'a>, E>;

/// Builder for [`PrecompiledNetExecutor`].
///
/// `skip_output_validation` disables the \[IO-015\] output-spec check for
/// every firing, matching Java's `Builder.skipOutputValidation` and
/// TypeScript's `skipOutputValidation` option.
pub struct PrecompiledExecutorBuilder<'a, E: EventStore> {
    program: &'a PrecompiledNet,
    initial_marking: Marking,
    event_store: Option<E>,
    environment_places: HashSet<Arc<str>>,
    skip_output_validation: bool,
    deadline_tolerance_ms: Option<f64>,
}

impl<'a, E: EventStore> PrecompiledExecutorBuilder<'a, E> {
    /// Sets the event store.
    pub fn event_store(mut self, store: E) -> Self {
        self.event_store = Some(store);
        self
    }

    /// Sets the environment places.
    pub fn environment_places(mut self, places: HashSet<Arc<str>>) -> Self {
        self.environment_places = places;
        self
    }

    /// Skips the \[IO-015\] output-spec check for trusted transition
    /// actions: every firing's output is accepted without consulting the
    /// declared `Out` spec.
    pub fn skip_output_validation(mut self, skip: bool) -> Self {
        self.skip_output_validation = skip;
        self
    }

    /// Sets the deadline-enforcement tolerance (ms) — the grace band beyond a hard deadline
    /// (`deadline()` / `window()`) before a transition is force-disabled with a
    /// `TransitionTimedOut` event (TIME-013). Defaults to
    /// [`DEADLINE_TOLERANCE_MS`](crate::executor_core::deadline) (5ms); `0.0` gives strict
    /// enforcement. Real-time orchestrators whose cycles can stall may widen it. Should be
    /// non-negative. Does not affect `exact()` transitions, which are enforced softly (TIME-006).
    pub fn deadline_tolerance_ms(mut self, ms: f64) -> Self {
        debug_assert!(ms >= 0.0, "deadline tolerance must be non-negative: {ms}");
        self.deadline_tolerance_ms = Some(ms);
        self
    }

    /// Builds the executor.
    pub fn build(self) -> PrecompiledNetExecutor<'a, E> {
        let mut backend = PrecompiledBackend::new(self.program, self.initial_marking);
        if let Some(ms) = self.deadline_tolerance_ms {
            backend.set_deadline_tolerance_ms(ms);
        }
        let has_environment_places = !self.environment_places.is_empty();
        let mut executor = Executor::from_parts(
            backend,
            self.event_store.unwrap_or_default(),
            has_environment_places,
        );
        executor.set_skip_output_validation(self.skip_output_validation);
        executor
    }
}

impl<'a, E: EventStore> Executor<PrecompiledBackend<'a>, E> {
    /// Creates a builder for a `PrecompiledNetExecutor`.
    pub fn builder(
        program: &'a PrecompiledNet,
        initial_marking: Marking,
    ) -> PrecompiledExecutorBuilder<'a, E> {
        PrecompiledExecutorBuilder {
            program,
            initial_marking,
            event_store: None,
            environment_places: HashSet::new(),
            skip_output_validation: false,
            deadline_tolerance_ms: None,
        }
    }

    /// Creates a new executor with default options.
    pub fn new(program: &'a PrecompiledNet, initial_marking: Marking) -> Self {
        let backend = PrecompiledBackend::new(program, initial_marking);
        Executor::from_parts(backend, E::default(), false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiled_net::CompiledNet;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::token::Token;
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::NoopEventStore;

    #[cfg(feature = "tokio")]
    mod async_tests {
        use super::*;
        use crate::environment::{ExecutorSignal, ExternalEvent};
        use libpetri_core::action::async_action;
        use libpetri_core::petri_net::PetriNet;
        use libpetri_core::token::ErasedToken;

        #[tokio::test]
        async fn async_linear_chain() {
            let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
            let transitions: Vec<Transition> = (0..5)
                .map(|i| {
                    Transition::builder(format!("t{i}"))
                        .input(one(&places[i]))
                        .output(out_place(&places[i + 1]))
                        .action(fork())
                        .build()
                })
                .collect();

            let net = PetriNet::builder("chain5").transitions(transitions).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&places[0], Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p0"), 0);
            assert_eq!(result.count("p5"), 1);
        }

        #[tokio::test]
        async fn async_action_execution() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(async_action(|ctx| async { Ok(ctx) }))
                .build();

            let net = PetriNet::builder("async_test").transition(t).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p1"), 0);
        }

        // ==================== Drain/Close lifecycle tests ====================

        #[tokio::test]
        async fn async_drain_terminates_at_quiescence() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(42, 0)),
                }))
                .unwrap();
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }

        #[tokio::test]
        async fn async_drain_rejects_post_drain_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(99, 0)),
                }))
                .unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 0);
        }

        #[tokio::test]
        async fn async_close_discards_queued_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(1, 0)),
            }))
            .unwrap();
            tx.send(ExecutorSignal::Close).unwrap();
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(2, 0)),
            }))
            .unwrap();
            drop(tx);

            let result = executor.run_async(rx).await;
            assert!(result.count("p2") <= 1);
        }

        #[tokio::test]
        async fn async_close_after_drain_escalates() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Close).unwrap();
            });

            let _result = executor.run_async(rx).await;
            // Test passes if run_async returns — close escalated from drain
        }

        #[tokio::test]
        async fn async_handle_raii_drain_on_drop() {
            use crate::executor_handle::ExecutorHandle;

            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                let mut handle = ExecutorHandle::new(tx);
                handle.inject(
                    Arc::from("p1"),
                    ErasedToken::from_typed(&Token::at(7, 0)),
                );
                // handle dropped here — RAII sends Drain automatically
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }

        // ==================== Out::Timeout tests ====================
        // The async timeout fix is exercised against the production
        // (precompiled) backend here; the bitmap equivalents live in
        // `executor.rs`. Both must produce the timeout branch's outputs.

        #[tokio::test]
        async fn async_timeout_produces_timeout_token() {
            use libpetri_core::output::{timeout_place, xor};

            let p1 = Place::<i32>::new("p1");
            let success = Place::<i32>::new("success");
            let timeout_out = Place::<i32>::new("timeout_out");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(xor(vec![
                    out_place(&success),
                    timeout_place(50, &timeout_out),
                ]))
                .action(async_action(|mut ctx| async move {
                    let v: i32 = *ctx.input::<i32>("p1")?;
                    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                    ctx.output("success", v)?;
                    Ok(ctx)
                }))
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("timeout_out"), 1);
            assert_eq!(result.count("success"), 0);
        }

        // Regression for the Marvin exact(45s) "sometimes never fires" bug, on the production
        // (precompiled) backend. A higher-priority sync action busy-waits 200ms, blocking the
        // executor thread past the exact(50) target; with soft enforcement the exact transition
        // must STILL fire and must NOT be force-disabled.
        #[tokio::test]
        async fn async_exact_survives_busy_executor() {
            use libpetri_core::action::sync_action;
            use libpetri_core::timing::exact;
            use libpetri_event::event_store::InMemoryEventStore;
            use libpetri_event::net_event::NetEvent;

            let p_slow = Place::<i32>::new("p_slow");
            let p_exact = Place::<i32>::new("p_exact");
            let slow_out = Place::<i32>::new("slow_out");
            let exact_out = Place::<i32>::new("exact_out");

            let t_slow = Transition::builder("slow")
                .input(one(&p_slow))
                .output(out_place(&slow_out))
                .priority(10)
                .action(sync_action(|ctx| {
                    let v = ctx.input::<i32>("p_slow")?;
                    let start = std::time::Instant::now();
                    while start.elapsed().as_millis() < 200 {
                        std::hint::spin_loop();
                    }
                    ctx.output("slow_out", *v)?;
                    Ok(())
                }))
                .build();

            let t_exact = Transition::builder("exact")
                .input(one(&p_exact))
                .output(out_place(&exact_out))
                .timing(exact(50))
                .action(fork())
                .build();

            let net = PetriNet::builder("test")
                .transitions([t_slow, t_exact])
                .build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p_slow, Token::at(1, 0));
            marking.add(&p_exact, Token::at(2, 0));

            let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
                .event_store(InMemoryEventStore::new())
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(500)).await;
                drop(tx);
            });
            let result = executor.run_async(rx).await;

            assert_eq!(
                result.count("exact_out"),
                1,
                "exact transition must still fire under soft enforcement"
            );
            assert!(
                !executor
                    .event_store()
                    .events()
                    .iter()
                    .any(|e| matches!(e, NetEvent::TransitionTimedOut { .. })),
                "exact() must never be force-disabled"
            );
        }

        // A wide `deadline_tolerance_ms` on the builder lets a slightly-late HARD deadline still
        // fire (TIME-013). The window([50,100]) transition is reaped under the default 5ms band
        // when the executor stalls 200ms, but survives with a 400ms tolerance.
        #[tokio::test]
        async fn async_deadline_tolerance_allows_late_fire() {
            use libpetri_core::action::sync_action;
            use libpetri_core::timing::window;
            use libpetri_event::event_store::InMemoryEventStore;
            use libpetri_event::net_event::NetEvent;

            let p_slow = Place::<i32>::new("p_slow");
            let p_windowed = Place::<i32>::new("p_windowed");
            let slow_out = Place::<i32>::new("slow_out");
            let windowed_out = Place::<i32>::new("windowed_out");

            let t_slow = Transition::builder("slow")
                .input(one(&p_slow))
                .output(out_place(&slow_out))
                .priority(10)
                .action(sync_action(|ctx| {
                    let v = ctx.input::<i32>("p_slow")?;
                    let start = std::time::Instant::now();
                    while start.elapsed().as_millis() < 200 {
                        std::hint::spin_loop();
                    }
                    ctx.output("slow_out", *v)?;
                    Ok(())
                }))
                .build();

            let t_windowed = Transition::builder("windowed")
                .input(one(&p_windowed))
                .output(out_place(&windowed_out))
                .timing(window(50, 100))
                .action(fork())
                .build();

            let net = PetriNet::builder("test")
                .transitions([t_slow, t_windowed])
                .build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p_slow, Token::at(1, 0));
            marking.add(&p_windowed, Token::at(2, 0));

            let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
                .event_store(InMemoryEventStore::new())
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .deadline_tolerance_ms(400.0)
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(500)).await;
                drop(tx);
            });
            let result = executor.run_async(rx).await;

            assert_eq!(
                result.count("windowed_out"),
                1,
                "wide tolerance lets the slightly-late window transition fire"
            );
            assert!(
                !executor
                    .event_store()
                    .events()
                    .iter()
                    .any(|e| matches!(e, NetEvent::TransitionTimedOut { .. })),
                "no timeout within the configured tolerance band"
            );
        }

        #[tokio::test]
        async fn async_timeout_normal_when_fast() {
            use libpetri_core::output::{timeout_place, xor};

            let p1 = Place::<i32>::new("p1");
            let success = Place::<i32>::new("success");
            let timeout_out = Place::<i32>::new("timeout_out");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(xor(vec![
                    out_place(&success),
                    timeout_place(500, &timeout_out),
                ]))
                .action(async_action(|mut ctx| async move {
                    let v: i32 = *ctx.input::<i32>("p1")?;
                    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                    ctx.output("success", v)?;
                    Ok(ctx)
                }))
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("success"), 1);
            assert_eq!(result.count("timeout_out"), 0);
        }

        // ==================== Mid-execution snapshot ====================

        #[tokio::test]
        async fn async_snapshot_returns_live_marking() {
            use crate::executor_handle::ExecutorHandle;

            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            // Environment place keeps the executor alive at quiescence so the
            // snapshot request is serviced while it is still running.
            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            let driver = tokio::spawn(async move {
                let mut handle = ExecutorHandle::new(tx);
                // Inject a token and let it fire p1 -> p2.
                handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(42, 0)));
                tokio::time::sleep(std::time::Duration::from_millis(20)).await;
                // Snapshot forces the precompiled backend to materialise its
                // ring-buffer marking on demand without stopping execution.
                let snap = handle
                    .snapshot()
                    .expect("snapshot on live handle")
                    .await
                    .expect("snapshot reply delivered");
                handle.drain();
                snap
            });

            executor.run_async(rx).await;
            let snap = driver.await.expect("driver task");
            assert_eq!(snap.count("p2"), 1, "fired token should be in p2");
            assert_eq!(snap.count("p1"), 0, "p1 should be consumed");
        }

        // ===== Out::Timeout conformance: IO-013 c4 + EXEC-022 c2/c3 =====

        // EXEC-022 c3: a timed-out async action whose timeout child is a
        // ForwardInput must forward the consumed input token to the target.
        #[tokio::test]
        async fn async_timeout_forwards_input() {
            use libpetri_core::output::{forward_input, timeout};

            let p_in = Place::<i32>::new("p_in");
            let fwd_out = Place::<i32>::new("fwd_out");

            let t1 = Transition::builder("t1")
                .input(one(&p_in))
                .output(timeout(50, forward_input(&p_in, &fwd_out)))
                .action(async_action(|ctx| async move {
                    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                    Ok(ctx)
                }))
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p_in, Token::at(42, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("fwd_out"), 1, "consumed input forwarded on timeout");
            assert_eq!(*result.peek(&fwd_out).unwrap(), 42, "forwarded value preserved");
            assert_eq!(result.count("p_in"), 0, "input was consumed");
        }

        // IO-013 c4 / EXEC-022 c2: a timed-out async action emits exactly one
        // ActionTimedOut (with the correct budget) and NOT TransitionCompleted.
        #[tokio::test]
        async fn async_timeout_emits_action_timed_out() {
            use libpetri_core::output::{timeout_place, xor};
            use libpetri_event::event_store::InMemoryEventStore;
            use libpetri_event::net_event::NetEvent;

            let p1 = Place::<i32>::new("p1");
            let success = Place::<i32>::new("success");
            let timeout_out = Place::<i32>::new("timeout_out");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(xor(vec![
                    out_place(&success),
                    timeout_place(50, &timeout_out),
                ]))
                .action(async_action(|ctx| async move {
                    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                    Ok(ctx)
                }))
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            executor.run_async(rx).await;

            let events = executor.event_store().events();
            let timed_out: Vec<_> = events
                .iter()
                .filter(|e| matches!(e, NetEvent::ActionTimedOut { .. }))
                .collect();
            assert_eq!(timed_out.len(), 1, "exactly one ActionTimedOut");
            match timed_out[0] {
                NetEvent::ActionTimedOut {
                    transition_name,
                    timeout_ms,
                    ..
                } => {
                    assert_eq!(&**transition_name, "t1");
                    assert_eq!(*timeout_ms, 50);
                }
                _ => unreachable!(),
            }
            assert!(
                !events
                    .iter()
                    .any(|e| matches!(e, NetEvent::TransitionCompleted { .. })),
                "a timed-out action must not also report TransitionCompleted"
            );
        }
    }

    /// \[IO-015\] escape hatch: `skip_output_validation(true)` must actually
    /// reach the firing path. The net below writes to *both* branches of an
    /// `Out::Xor`, which is a violation by default — under the flag it is
    /// accepted and both tokens land.
    ///
    /// Regression: the builder stored the flag but `build()` dropped it, so
    /// the option was silently inert while Java
    /// (`PrecompiledNetExecutor.Builder.skipOutputValidation`) and TypeScript
    /// (`skipOutputValidation`) both honoured it.
    #[test]
    fn skip_output_validation_bypasses_io_015() {
        use libpetri_core::action::sync_action;
        use libpetri_core::output::xor;
        use libpetri_core::petri_net::PetriNet;
        use libpetri_event::event_store::InMemoryEventStore;

        let build_net = || {
            let p = Place::<i32>::new("p");
            let a = Place::<i32>::new("a");
            let b = Place::<i32>::new("b");
            let t = Transition::builder("t1")
                .input(one(&p))
                .output(xor(vec![out_place(&a), out_place(&b)]))
                .action(sync_action(|ctx| {
                    let v = *ctx.input::<i32>("p")?;
                    ctx.output("a", v)?;
                    ctx.output("b", v)?;
                    Ok(())
                }))
                .build();
            let net = PetriNet::builder("test").transition(t).build();
            let mut marking = Marking::new();
            marking.add(&p, Token::at(1, 0));
            (PrecompiledNet::from_compiled(CompiledNet::compile(&net)), marking)
        };

        // Default: the XOR violation is caught, nothing is produced.
        let (prog, marking) = build_net();
        let mut strict = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
            .build();
        let result = strict.run_sync().into_owned();
        assert_eq!(result.count("a"), 0, "default must reject the XOR violation");
        assert_eq!(result.count("b"), 0, "default must reject the XOR violation");

        // Flag set: the same firing is accepted and both branches receive a token.
        let (prog, marking) = build_net();
        let mut lax = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
            .skip_output_validation(true)
            .build();
        let result = lax.run_sync().into_owned();
        assert_eq!(result.count("a"), 1, "skip_output_validation must accept it");
        assert_eq!(result.count("b"), 1, "skip_output_validation must accept it");
        assert!(
            !lax.event_store()
                .events()
                .iter()
                .any(|e| matches!(e, libpetri_event::net_event::NetEvent::TransitionFailed { .. })),
            "skipping validation must not emit an IO-015 failure"
        );
    }
}
