//! `BitmapNetExecutor` — the public type alias surface for the
//! bitmap-storage executor.
//!
//! The 6-phase loop lives in
//! [`Executor`](crate::executor_core::executor::Executor); the bitmap
//! state lives in
//! [`BitmapBackend`](crate::bitmap_backend::BitmapBackend). This module
//! only wires the two together via a type alias + an inherent
//! constructor + the [`ExecutorOptions`] builder type.

use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::petri_net::PetriNet;
use libpetri_event::event_store::EventStore;

use crate::bitmap_backend::BitmapBackend;
use crate::executor_core::executor::Executor;
use crate::marking::Marking;

/// Construction-time options for a [`BitmapNetExecutor`].
#[derive(Default)]
pub struct ExecutorOptions {
    /// Names of places that receive externally-injected tokens (via
    /// `ExecutorSignal::Event` on the async path). Empty by default;
    /// when empty, the sync loop terminates at quiescence.
    pub environment_places: HashSet<Arc<str>>,
    /// Grace band (ms) beyond a hard deadline (`deadline()` / `window()`) before a transition is
    /// force-disabled with a `TransitionTimedOut` event (TIME-013). `None` uses the default
    /// [`DEADLINE_TOLERANCE_MS`](crate::executor_core::deadline) (5ms); `Some(0.0)` is strict.
    /// Should be non-negative. Does not affect `exact()` transitions, enforced softly (TIME-006).
    pub deadline_tolerance_ms: Option<f64>,
}

/// Bitmap-based executor for Coloured Time Petri Nets.
///
/// Generic over `E: EventStore` for zero-cost noop event recording. The
/// sync path (`run_sync`) executes inline without any async runtime;
/// the async path (`run_async`, behind the `tokio` feature) drives
/// concurrent async actions and external event injection.
///
/// This is a type alias over the shared
/// [`Executor`](crate::executor_core::executor::Executor) parameterised
/// by [`BitmapBackend`]. The 6-phase loop, event emission, and action
/// execution live in `Executor`; the bitmap storage, presence/dirty
/// bitmaps, and per-transition enablement flags live in the backend.
pub type BitmapNetExecutor<E> = Executor<BitmapBackend, E>;

impl<E: EventStore> Executor<BitmapBackend, E> {
    /// Compile `net`, load `initial_tokens` into the backend, and wrap
    /// it with a fresh default-constructed event store.
    pub fn new(net: &PetriNet, initial_tokens: Marking, options: ExecutorOptions) -> Self {
        let mut backend = BitmapBackend::new(net, initial_tokens);
        if let Some(ms) = options.deadline_tolerance_ms {
            backend.set_deadline_tolerance_ms(ms);
        }
        let has_environment_places = !options.environment_places.is_empty();
        Executor::from_parts(backend, E::default(), has_environment_places)
    }
}

#[cfg(all(test, feature = "tokio"))]
mod async_tests {
    use super::*;
    use crate::environment::{ExecutorSignal, ExternalEvent};
    use libpetri_core::action::{ActionError, async_action, fork};
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::token::{ErasedToken, Token};
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::{InMemoryEventStore, NoopEventStore};
    use libpetri_event::net_event::NetEvent;

    #[tokio::test]
    async fn async_fork_single_transition() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 42);
    }

    #[tokio::test]
    async fn async_action_produces_output() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let action = async_action(|mut ctx| async move {
            let val: i32 = *ctx.input::<i32>("p1")?;
            ctx.output("p2", val * 10)?;
            Ok(ctx)
        });

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(action)
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 50);
    }

    #[tokio::test]
    async fn async_chain_two_transitions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .action(fork())
            .build();

        let net = PetriNet::builder("chain").transitions([t1, t2]).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(99, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p3"), 1);
        assert_eq!(*executor.marking().peek(&p3).unwrap(), 99);
    }

    #[tokio::test]
    async fn async_event_injection() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new(); // empty — no initial tokens

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        // Inject a token after a short delay, then close the channel
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let token = Token::at(77, 0);
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&token),
            }))
            .unwrap();
            // Drop tx to close the channel and let executor terminate
        });

        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 77);
    }

    #[tokio::test]
    async fn async_with_event_store_records_events() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        let events = executor.event_store().events();
        assert!(!events.is_empty());
        // Should have ExecutionStarted, TransitionStarted, TransitionCompleted, ExecutionCompleted
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionCompleted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionCompleted { .. }))
        );
    }

    #[tokio::test]
    async fn async_action_error_does_not_crash() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let action =
            async_action(|_ctx| async move { Err(ActionError::new("intentional failure")) });

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(action)
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        // Token consumed but no output produced
        assert_eq!(executor.marking().count("p1"), 0);
        assert_eq!(executor.marking().count("p2"), 0);

        // Failure event recorded
        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
        );
    }

    #[tokio::test]
    async fn async_delayed_timing() {
        use libpetri_core::timing::delayed;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(delayed(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(10, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        // Keep channel open long enough for the delayed transition to fire
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 80,
            "delayed(100) should wait ~100ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 10);
    }

    #[tokio::test]
    async fn async_exact_timing() {
        use libpetri_core::timing::exact;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(exact(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(20, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 80,
            "exact(100) should wait ~100ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 20);
    }

    #[tokio::test]
    async fn async_window_timing() {
        use libpetri_core::timing::window;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(window(50, 200))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(30, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(400)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 40,
            "window(50,200) should wait >= ~50ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 30);
    }

    #[tokio::test]
    async fn async_deadline_enforcement() {
        use libpetri_core::action::sync_action;
        use libpetri_core::timing::window;

        let p_slow = Place::<i32>::new("p_slow");
        let p_windowed = Place::<i32>::new("p_windowed");
        let slow_out = Place::<i32>::new("slow_out");
        let windowed_out = Place::<i32>::new("windowed_out");

        // Sync action that busy-waits for 200ms, blocking the executor thread.
        // This prevents the executor from reaching the fire phase for windowed
        // until after its deadline has passed.
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

        // Windowed transition: enabled at start, earliest=50ms, deadline=100ms.
        // Because the slow sync action blocks the executor for 200ms, by the time
        // enforce_deadlines runs again, elapsed (~200ms) > latest (100ms) + tolerance.
        let t_windowed = Transition::builder("windowed")
            .input(one(&p_windowed))
            .output(out_place(&windowed_out))
            .timing(window(50, 100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test")
            .transitions([t_slow, t_windowed])
            .build();

        let mut marking = Marking::new();
        marking.add(&p_slow, Token::at(1, 0));
        marking.add(&p_windowed, Token::at(2, 0));

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(500)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        // Slow fires and completes after 200ms busy-wait
        assert_eq!(executor.marking().count("slow_out"), 1);
        // Windowed should have been disabled by deadline enforcement
        assert_eq!(
            executor.marking().count("windowed_out"),
            0,
            "windowed transition should have been disabled by deadline"
        );

        let events = executor.event_store().events();
        assert!(
            events.iter().any(|e| matches!(e, NetEvent::TransitionTimedOut { transition_name, .. } if &**transition_name == "windowed")),
            "expected TransitionTimedOut event for 'windowed'"
        );
    }

    // Regression for the Marvin exact(45s) "sometimes never fires" bug. Mirror of
    // `async_deadline_enforcement`, but the timed transition uses exact(50). A higher-priority
    // sync action busy-waits 200ms, blocking the executor thread so it cannot run a cycle until
    // well past the [50,50] window. With soft enforcement the exact transition must STILL fire
    // and must NOT be reaped (contrast the window case, which DOES time out).
    #[tokio::test]
    async fn async_exact_survives_busy_executor() {
        use libpetri_core::action::sync_action;
        use libpetri_core::timing::exact;

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

        let mut marking = Marking::new();
        marking.add(&p_slow, Token::at(1, 0));
        marking.add(&p_exact, Token::at(2, 0));

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(500)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert_eq!(
            executor.marking().count("exact_out"),
            1,
            "exact transition must still fire under soft enforcement"
        );
        let events = executor.event_store().events();
        assert!(
            !events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionTimedOut { .. })),
            "exact() must never be force-disabled"
        );
    }

    // A wide `deadline_tolerance_ms` lets a slightly-late HARD deadline still fire (TIME-013).
    // Same busy-executor scenario as `async_deadline_enforcement` (which reaps the window under
    // the default 5ms band), but with a 400ms tolerance the window([50,100]) survives the ~200ms
    // overrun and fires.
    #[tokio::test]
    async fn async_deadline_tolerance_allows_late_fire() {
        use libpetri_core::action::sync_action;
        use libpetri_core::timing::window;

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

        let mut marking = Marking::new();
        marking.add(&p_slow, Token::at(1, 0));
        marking.add(&p_windowed, Token::at(2, 0));

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                deadline_tolerance_ms: Some(400.0),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(500)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert_eq!(
            executor.marking().count("windowed_out"),
            1,
            "wide tolerance lets the slightly-late window transition fire"
        );
        let events = executor.event_store().events();
        assert!(
            !events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionTimedOut { .. })),
            "no timeout within the configured tolerance band"
        );
    }

    #[tokio::test]
    async fn async_multiple_injections() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            for i in 0..5 {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                let token = Token::at(i, 0);
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&token),
                }))
                .unwrap();
            }
            // Drop tx to close channel
        });

        executor.run_async(rx).await;

        assert_eq!(
            executor.marking().count("p2"),
            5,
            "all 5 injected tokens should arrive"
        );
    }

    #[tokio::test]
    async fn async_parallel_execution() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let out1 = Place::<i32>::new("out1");
        let out2 = Place::<i32>::new("out2");
        let out3 = Place::<i32>::new("out3");

        let make_transition = |name: &str, inp: &Place<i32>, outp: &Place<i32>| {
            Transition::builder(name)
                .input(one(inp))
                .output(out_place(outp))
                .action(async_action(|mut ctx| async move {
                    let v: i32 =
                        *ctx.input::<i32>(ctx.transition_name().replace("t", "p").as_str())?;
                    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                    ctx.output(&ctx.transition_name().replace("t", "out"), v)?;
                    Ok(ctx)
                }))
                .build()
        };

        let t1 = make_transition("t1", &p1, &out1);
        let t2 = make_transition("t2", &p2, &out2);
        let t3 = make_transition("t3", &p3, &out3);

        let net = PetriNet::builder("parallel")
            .transitions([t1, t2, t3])
            .build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        marking.add(&p2, Token::at(2, 0));
        marking.add(&p3, Token::at(3, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let start = std::time::Instant::now();
        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;
        let elapsed = start.elapsed().as_millis();

        assert_eq!(executor.marking().count("out1"), 1);
        assert_eq!(executor.marking().count("out2"), 1);
        assert_eq!(executor.marking().count("out3"), 1);
        assert!(
            elapsed < 250,
            "parallel execution should take < 250ms, took {elapsed}ms"
        );
    }

    #[tokio::test]
    async fn async_sequential_chain_order() {
        use std::sync::Mutex;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let p4 = Place::<i32>::new("p4");

        let order: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));

        let make_chain = |name: &str,
                          inp: &Place<i32>,
                          outp: &Place<i32>,
                          id: i32,
                          order: Arc<Mutex<Vec<i32>>>| {
            let inp_name: Arc<str> = Arc::from(inp.name());
            let outp_name: Arc<str> = Arc::from(outp.name());
            Transition::builder(name)
                .input(one(inp))
                .output(out_place(outp))
                .action(async_action(move |mut ctx| {
                    let order = Arc::clone(&order);
                    let inp_name = Arc::clone(&inp_name);
                    let outp_name = Arc::clone(&outp_name);
                    async move {
                        let v: i32 = *ctx.input::<i32>(&inp_name)?;
                        order.lock().unwrap().push(id);
                        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                        ctx.output(&outp_name, v)?;
                        Ok(ctx)
                    }
                }))
                .build()
        };

        let t1 = make_chain("t1", &p1, &p2, 1, Arc::clone(&order));
        let t2 = make_chain("t2", &p2, &p3, 2, Arc::clone(&order));
        let t3 = make_chain("t3", &p3, &p4, 3, Arc::clone(&order));

        let net = PetriNet::builder("chain").transitions([t1, t2, t3]).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p4"), 1);
        let recorded = order.lock().unwrap().clone();
        assert_eq!(recorded, vec![1, 2, 3], "chain should execute in order");
    }

    #[tokio::test]
    async fn async_fork_join() {
        use libpetri_core::output::and;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let p4 = Place::<i32>::new("p4");

        // Fork: p1 -> (p2, p3) via AND output
        let t_fork = Transition::builder("fork")
            .input(one(&p1))
            .output(and(vec![out_place(&p2), out_place(&p3)]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p1")?;
                ctx.output("p2", *v)?;
                ctx.output("p3", *v)?;
                Ok(())
            }))
            .build();

        // Join: (p2, p3) -> p4
        let t_join = Transition::builder("join")
            .input(one(&p2))
            .input(one(&p3))
            .output(out_place(&p4))
            .action(libpetri_core::action::sync_action(|ctx| {
                let a = ctx.input::<i32>("p2")?;
                let b = ctx.input::<i32>("p3")?;
                ctx.output("p4", *a + *b)?;
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("fork_join")
            .transitions([t_fork, t_join])
            .build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 0);
        assert_eq!(executor.marking().count("p3"), 0);
        assert_eq!(executor.marking().count("p4"), 1);
        assert_eq!(*executor.marking().peek(&p4).unwrap(), 10);
    }

    #[tokio::test]
    async fn async_xor_output_branching() {
        use libpetri_core::output::xor;

        let p = Place::<i32>::new("p");
        let left = Place::<i32>::new("left");
        let right = Place::<i32>::new("right");

        let t = Transition::builder("xor_t")
            .input(one(&p))
            .output(xor(vec![out_place(&left), out_place(&right)]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p")?;
                if *v > 0 {
                    ctx.output("left", *v)?;
                } else {
                    ctx.output("right", *v)?;
                }
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("xor_test").transition(t).build();

        // Test positive value goes left
        let mut marking = Marking::new();
        marking.add(&p, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("left"), 1);
        assert_eq!(executor.marking().count("right"), 0);
        assert_eq!(*executor.marking().peek(&left).unwrap(), 42);
    }

    /// Data-dependent loop/exit routing without input predicates (IO-006).
    /// A classifier transition XOR-routes each counter token into exactly one
    /// of two places, and two conflicting transitions consume those places.
    #[tokio::test]
    async fn async_loop_with_conditional_routing() {
        use libpetri_core::output::xor;

        let counter = Place::<i32>::new("counter");
        let below = Place::<i32>::new("below");
        let reached = Place::<i32>::new("reached");
        let done = Place::<i32>::new("done");

        // Classifier: counter -> XOR(below, reached) by value.
        let t_classify = Transition::builder("classify")
            .input(one(&counter))
            .output(xor(vec![out_place(&below), out_place(&reached)]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = *ctx.input::<i32>("counter")?;
                if v < 3 {
                    ctx.output("below", v)?;
                } else {
                    ctx.output("reached", v)?;
                }
                Ok(())
            }))
            .build();

        // Loop transition: below -> counter (increment).
        let t_loop = Transition::builder("loop")
            .input(one(&below))
            .output(out_place(&counter))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("below")?;
                ctx.output("counter", *v + 1)?;
                Ok(())
            }))
            .build();

        // Exit transition: reached -> done.
        let t_exit = Transition::builder("exit")
            .input(one(&reached))
            .output(out_place(&done))
            .action(fork())
            .build();

        let net = PetriNet::builder("loop_net")
            .transitions([t_classify, t_loop, t_exit])
            .build();

        let mut marking = Marking::new();
        marking.add(&counter, Token::at(0, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("done"), 1);
        assert_eq!(*executor.marking().peek(&done).unwrap(), 3);
    }

    #[tokio::test]
    async fn async_delayed_fires_without_injection() {
        use libpetri_core::timing::delayed;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(delayed(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(7, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        // No injections; keep channel open long enough for the delayed transition to fire
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 7);
    }

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
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("timeout_out"), 1);
        assert_eq!(executor.marking().count("success"), 0);
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
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("success"), 1);
        assert_eq!(executor.marking().count("timeout_out"), 0);
    }

    #[tokio::test]
    async fn async_event_store_records_token_added_for_injection() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let token = Token::at(99, 0);
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&token),
            }))
            .unwrap();
        });

        executor.run_async(rx).await;

        let events = executor.event_store().events();
        // Should have TokenAdded for the injected token into p1
        assert!(
            events.iter().any(
                |e| matches!(e, NetEvent::TokenAdded { place_name, .. } if &**place_name == "p1")
            ),
            "expected TokenAdded event for injected token into p1"
        );
        // And also TokenAdded for the output into p2
        assert!(
            events.iter().any(
                |e| matches!(e, NetEvent::TokenAdded { place_name, .. } if &**place_name == "p2")
            ),
            "expected TokenAdded event for output token into p2"
        );
    }

    #[tokio::test]
    async fn async_inhibitor_blocks_in_async() {
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");
        let p_inh = Place::<()>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .action(fork())
            .build();

        let net = PetriNet::builder("inhibitor").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        // Inhibitor should block — token remains in p1, nothing in p2
        assert_eq!(executor.marking().count("p1"), 1);
        assert_eq!(executor.marking().count("p2"), 0);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Inject a token, then drain
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(42, 0)),
            }))
            .unwrap();
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            tx.send(ExecutorSignal::Drain).unwrap();
        });

        executor.run_async(rx).await;

        // The injected token should have been processed
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 42);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Send Drain first, then an event — event should be discarded
            tx.send(ExecutorSignal::Drain).unwrap();
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(99, 0)),
            }))
            .unwrap();
        });

        executor.run_async(rx).await;

        // Event sent after drain should not have been processed
        assert_eq!(executor.marking().count("p2"), 0);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        // Queue events then close — close should discard all pending events
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

        executor.run_async(rx).await;

        // The first event arrives before Close — it gets processed in the first
        // try_recv batch. Close then discards all remaining events.
        // So at most 1 token should be in p2 (the one before Close).
        assert!(executor.marking().count("p2") <= 1);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Drain first, then escalate to close
            tx.send(ExecutorSignal::Drain).unwrap();
            tx.send(ExecutorSignal::Close).unwrap();
        });

        // Executor should terminate — close escalates from drain
        executor.run_async(rx).await;
        // No assertions needed — the test passes if run_async returns
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
                ..Default::default()
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let mut handle = ExecutorHandle::new(tx);
            handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(7, 0)));
            // handle dropped here — RAII sends Drain automatically
        });

        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 7);
    }

    // ===== Out::Timeout conformance: IO-013 c4 + EXEC-022 c2/c3 =====

    // EXEC-022 c3: ForwardInput in a timeout child forwards the consumed
    // input token to the target when the action times out.
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
        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("fwd_out"), 1);
        assert_eq!(*executor.marking().peek(&fwd_out).unwrap(), 42);
        assert_eq!(executor.marking().count("p_in"), 0);
    }

    // IO-013 c4 / EXEC-022 c2: timeout emits exactly one ActionTimedOut with
    // the right budget, and not TransitionCompleted.
    #[tokio::test]
    async fn async_timeout_emits_action_timed_out() {
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
            .action(async_action(|ctx| async move {
                tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                Ok(ctx)
            }))
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());
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
