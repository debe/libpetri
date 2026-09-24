//! \[EXEC-042\] Terminal places, plus the two amendments that shipped with them:
//! \[ENV-014\] AC9 (a parked executor answers a snapshot without waking) and
//! \[TIME-015\] AC11 (an action future completed inside the host wait is
//! admitted on a following cycle).
//!
//! Every runtime AC runs on both backends, and on `run_sync` as well as
//! `run_async` wherever the AC does not need an async action or an
//! injection. Lives in the umbrella crate because it drives the executors,
//! the verifier and core composition together.

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use libpetri::core::action::{fork, sync_action};
use libpetri::core::arc::read;
use libpetri::core::input::one;
use libpetri::core::output::{and, out_place};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::compiled_net::CompiledNet;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;
use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
use libpetri::runtime::precompiled_net::PrecompiledNet;
use libpetri::runtime::termination::TerminationReason;

#[derive(Debug, Clone, Copy)]
enum Backend {
    Bitmap,
    Precompiled,
}

const BACKENDS: [Backend; 2] = [Backend::Bitmap, Backend::Precompiled];

fn marking(tokens: &[&str]) -> Marking {
    let mut m = Marking::new();
    for name in tokens {
        m.add(&Place::<i32>::new(*name), Token::at(1, 0));
    }
    m
}

fn run_sync(backend: Backend, net: &PetriNet, initial: Marking) -> (Marking, TerminationReason) {
    match backend {
        Backend::Bitmap => {
            let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, initial, ExecutorOptions::default());
            let m = ex.run_sync().into_owned();
            (m, ex.termination_reason())
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut ex = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, initial).build();
            let m = ex.run_sync().into_owned();
            (m, ex.termination_reason())
        }
    }
}

/// A → `t1` (priority 10) marks the terminal `done`; `t2` (priority 0) moves
/// `b` → `c`. Both are enabled before the pass; `t1` goes first.
fn same_pass_net(t1_priority: i32) -> PetriNet {
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");
    let c = Place::<i32>::new("c");
    let done = Place::<i32>::new("done");
    PetriNet::builder("same_pass")
        .transition(
            Transition::builder("t1")
                .priority(t1_priority)
                .input(one(&a))
                .output(out_place(&done))
                .action(fork())
                .build(),
        )
        .transition(
            Transition::builder("t2")
                .input(one(&b))
                .output(out_place(&c))
                .action(fork())
                .build(),
        )
        .terminal(&done)
        .build()
}

// ============================================================
//  Declaration
// ============================================================

#[test]
fn terminal_declaration_is_carried_on_the_net() {
    let net = same_pass_net(10);
    assert_eq!(net.terminals().len(), 1);
    assert!(net.is_terminal("done"));
    assert!(!net.is_terminal("c"));
    // A standalone terminal (no arc) is still a place of the net.
    let lone = Place::<i32>::new("lone");
    let net = PetriNet::builder("lone").terminal(&lone).build();
    assert!(net.places().iter().any(|p| p.name() == "lone"));
}

#[test]
fn bind_actions_and_fusion_carry_the_terminals() {
    let bound = same_pass_net(10).bind_actions(&HashMap::new());
    assert!(bound.is_terminal("done"), "bind_actions must keep the terminals");

    // Fusion: a terminal declared on a non-canonical member names the
    // canonical place after the build.
    use libpetri::core::fusion::FusionSet;
    let a = Place::<i32>::new("a");
    let x = Place::<i32>::new("x");
    let y = Place::<i32>::new("y");
    let net = PetriNet::builder("fused")
        .transition(Transition::builder("t").input(one(&a)).output(out_place(&y)).action(fork()).build())
        .place((&x).into())
        .terminal(&y)
        .fuse([FusionSet::builder("xy").member(&x).member(&y).build()])
        .build();
    assert_eq!(net.terminals().iter().map(|p| p.name()).collect::<Vec<_>>(), vec!["x"]);
    assert!(net.places().iter().all(|p| p.name() != "y"));
}

// ============================================================
//  AC1 — a terminal initial marking fires nothing
// ============================================================

#[test]
fn ac1_initial_marking_on_a_terminal_place_fires_nothing_sync() {
    for backend in BACKENDS {
        let (m, reason) = run_sync(backend, &same_pass_net(10), marking(&["a", "b", "done"]));
        assert_eq!(reason, TerminationReason::Terminal, "{backend:?}");
        assert!(reason.is_complete());
        assert_eq!((m.count("a"), m.count("b"), m.count("c"), m.count("done")), (1, 1, 0, 1), "{backend:?}");
    }
}

#[test]
fn a_run_without_terminals_reports_quiescent_and_before_any_run_running() {
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");
    let net = PetriNet::builder("plain")
        .transition(Transition::builder("t").input(one(&a)).output(out_place(&b)).action(fork()).build())
        .build();
    let mut ex = BitmapNetExecutor::<NoopEventStore>::new(&net, marking(&["a"]), ExecutorOptions::default());
    assert_eq!(ex.termination_reason(), TerminationReason::Running);
    let m = ex.run_sync().into_owned();
    assert_eq!(m.count("b"), 1);
    assert_eq!(ex.termination_reason(), TerminationReason::Quiescent);

    let (_, reason) = run_sync(Backend::Precompiled, &net, marking(&["a"]));
    assert_eq!(reason, TerminationReason::Quiescent);
}

// ============================================================
//  AC4 — a sync deposit stops the firing pass
// ============================================================

#[test]
fn ac4_sync_output_marking_a_terminal_stops_the_rest_of_the_pass_sync() {
    // Priority ordering (general path) and equal priority (fast path, index
    // order): both put t1 first in the pass.
    for t1_priority in [10, 0] {
        for backend in BACKENDS {
            let (m, reason) = run_sync(backend, &same_pass_net(t1_priority), marking(&["a", "b"]));
            assert_eq!(reason, TerminationReason::Terminal, "{backend:?} p={t1_priority}");
            assert_eq!(m.count("done"), 1, "{backend:?} p={t1_priority}");
            assert_eq!(
                (m.count("b"), m.count("c")),
                (1, 0),
                "{backend:?} p={t1_priority}: t2 was enabled before the pass and later in its \
                 order, and must not fire once t1's deposit marked the terminal place"
            );
        }
    }
}

// ============================================================
//  AC5 — a terminal place may not be consumed or read
// ============================================================

fn panic_message(f: impl FnOnce()) -> String {
    let err = catch_unwind(AssertUnwindSafe(f)).expect_err("must panic");
    err.downcast_ref::<String>()
        .cloned()
        .or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

#[test]
fn ac5_a_terminal_input_or_read_place_is_rejected_at_build() {
    let done = Place::<i32>::new("done");
    let out = Place::<i32>::new("out");
    let msg = panic_message(|| {
        PetriNet::builder("bad")
            .transition(Transition::builder("eater").input(one(&done)).output(out_place(&out)).action(fork()).build())
            .terminal(&done)
            .build();
    });
    assert!(msg.contains("'done'") && msg.contains("'eater'") && msg.contains("EXEC-042"), "{msg}");

    let a = Place::<i32>::new("a");
    let msg = panic_message(|| {
        PetriNet::builder("bad")
            .transition(
                Transition::builder("reader")
                    .input(one(&a))
                    .read(read(&done))
                    .output(out_place(&out))
                    .action(fork())
                    .build(),
            )
            .terminal(&done)
            .build();
    });
    assert!(msg.contains("'done'") && msg.contains("'reader'") && msg.contains("read-arc"), "{msg}");

    // Inhibiting or producing into a terminal place is fine.
    let _ = same_pass_net(0);
}

// ============================================================
//  AC6 — composition rejects a subnet body with terminals
// ============================================================

#[test]
fn ac6_compose_and_instantiate_reject_a_subnet_body_with_terminals() {
    use libpetri::core::interface::Interface;
    use libpetri::core::subnet_def::SubnetDef;

    let def = SubnetDef::from_net(same_pass_net(0), Interface::builder().build());
    let msg = panic_message(|| {
        let _ = def.instantiate_unit("i1");
    });
    assert!(msg.contains("same_pass") && msg.contains("'done'") && msg.contains("EXEC-042"), "{msg}");

    let msg = panic_message(|| {
        let _ = PetriNet::builder("host").compose_direct(&def).build();
    });
    assert!(msg.contains("compose_direct") && msg.contains("'done'"), "{msg}");
}

// ============================================================
//  Async path
// ============================================================

#[cfg(feature = "tokio")]
mod async_path {
    use super::*;
    use std::collections::HashSet;
    use std::future::pending;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::time::{Duration, Instant};

    use libpetri::core::action::async_action;
    use libpetri::core::context::TransitionContext;
    use libpetri::core::place::EnvironmentPlace;
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::clock::{ClockWait, ExecutorClock, ManualClock};
    use libpetri::runtime::environment::{ExecutorSignal, ExternalEvent};
    use libpetri::runtime::executor_handle::ExecutorHandle;
    use libpetri::runtime::marking::SnapshotResult;
    use tokio::sync::mpsc::{UnboundedReceiver, unbounded_channel};
    use tokio::sync::oneshot;
    use tokio::time::{sleep, timeout};

    type Rx = UnboundedReceiver<ExecutorSignal>;

    /// Runs `net` on `backend` under `run_async`, returns the final marking,
    /// the reason, and the marking read again `settle` after the run returned
    /// — by then any abandoned action has finished, so a late deposit would
    /// show there.
    async fn run_async(
        backend: Backend,
        net: &PetriNet,
        initial: Marking,
        env: &[&str],
        clock: Option<Arc<dyn ExecutorClock>>,
        rx: Rx,
        settle: Duration,
    ) -> (Marking, TerminationReason, Marking) {
        let env_set: HashSet<Arc<str>> = env.iter().map(|s| Arc::from(*s)).collect();
        match backend {
            Backend::Bitmap => {
                let mut opts = ExecutorOptions::default().environment_places(env.iter().copied());
                if let Some(c) = clock {
                    opts = opts.clock(c);
                }
                let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, initial, opts);
                let m = timeout(Duration::from_secs(5), ex.run_async(rx))
                    .await
                    .expect("run_async must return")
                    .into_owned();
                sleep(settle).await;
                (m, ex.termination_reason(), ex.marking().into_owned())
            }
            Backend::Precompiled => {
                let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
                let mut b = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, initial).environment_places(env_set);
                if let Some(c) = clock {
                    b = b.clock(c);
                }
                let mut ex = b.build();
                let m = timeout(Duration::from_secs(5), ex.run_async(rx))
                    .await
                    .expect("run_async must return")
                    .into_owned();
                sleep(settle).await;
                (m, ex.termination_reason(), ex.marking().into_owned())
            }
        }
    }

    fn closed_rx() -> Rx {
        let (tx, rx) = unbounded_channel();
        drop(tx);
        rx
    }

    #[tokio::test]
    async fn ac1_initial_marking_on_a_terminal_place_fires_nothing_async() {
        for backend in BACKENDS {
            let (m, reason, _) =
                run_async(backend, &same_pass_net(10), marking(&["a", "b", "done"]), &[], None, closed_rx(), Duration::ZERO)
                    .await;
            assert_eq!(reason, TerminationReason::Terminal, "{backend:?}");
            assert_eq!((m.count("a"), m.count("b"), m.count("c")), (1, 1, 0), "{backend:?}");
        }
    }

    #[tokio::test]
    async fn ac4_sync_output_marking_a_terminal_stops_the_rest_of_the_pass_async() {
        for t1_priority in [10, 0] {
            for backend in BACKENDS {
                let (m, reason, _) =
                    run_async(backend, &same_pass_net(t1_priority), marking(&["a", "b"]), &[], None, closed_rx(), Duration::ZERO)
                        .await;
                assert_eq!(reason, TerminationReason::Terminal, "{backend:?} p={t1_priority}");
                assert_eq!(
                    (m.count("done"), m.count("b"), m.count("c")),
                    (1, 1, 0),
                    "{backend:?} p={t1_priority}: t2 must not fire after t1's inline deposit"
                );
            }
        }
    }

    /// AC2's net: `split` forks `a` and `b`; `fast` (async, quick) marks the
    /// terminal `done`; `slow` (async) writes `result` only after `release`
    /// — long after the run has ended.
    fn in_flight_net(slow_finished: Arc<AtomicBool>) -> PetriNet {
        let start = Place::<i32>::new("start");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let done = Place::<i32>::new("done");
        let result = Place::<i32>::new("result");
        PetriNet::builder("in_flight")
            .transition(
                Transition::builder("split")
                    .input(one(&start))
                    .output(and(vec![out_place(&a), out_place(&b)]))
                    .action(sync_action(|ctx| {
                        ctx.output("a", 1i32)?;
                        ctx.output("b", 1i32)?;
                        Ok(())
                    }))
                    .build(),
            )
            .transition(
                Transition::builder("fast")
                    .input(one(&a))
                    .output(out_place(&done))
                    .action(async_action(|mut ctx: TransitionContext| async move {
                        sleep(Duration::from_millis(5)).await;
                        ctx.output("done", 1i32)?;
                        Ok(ctx)
                    }))
                    .build(),
            )
            .transition(
                Transition::builder("slow")
                    .input(one(&b))
                    .output(out_place(&result))
                    .action(async_action(move |mut ctx: TransitionContext| {
                        let finished = Arc::clone(&slow_finished);
                        async move {
                            sleep(Duration::from_millis(150)).await;
                            ctx.output("result", 1i32)?;
                            finished.store(true, Ordering::SeqCst);
                            Ok(ctx)
                        }
                    }))
                    .build(),
            )
            .terminal(&done)
            .build()
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn ac2_async_completion_ends_the_run_and_abandons_work_in_flight() {
        for backend in BACKENDS {
            let slow_finished = Arc::new(AtomicBool::new(false));
            let net = in_flight_net(Arc::clone(&slow_finished));
            let started = Instant::now();
            let (m, reason, later) =
                run_async(backend, &net, marking(&["start"]), &[], None, closed_rx(), Duration::from_millis(300)).await;
            assert_eq!(reason, TerminationReason::Terminal, "{backend:?}");
            assert_eq!(m.count("done"), 1, "{backend:?}");
            assert_eq!(m.count("result"), 0, "{backend:?}");
            assert!(
                started.elapsed() >= Duration::from_millis(300),
                "sanity: the settle period elapsed"
            );
            assert!(
                slow_finished.load(Ordering::SeqCst),
                "{backend:?}: the abandoned action must actually have finished during the settle, \
                 or the next assertion checks nothing"
            );
            assert_eq!(
                later.count("result"),
                0,
                "{backend:?}: the abandoned action's late result must never be deposited"
            );
        }
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn ac2_the_run_does_not_wait_for_the_abandoned_action() {
        let net = in_flight_net(Arc::new(AtomicBool::new(false)));
        let started = Instant::now();
        let (_, reason, _) =
            run_async(Backend::Precompiled, &net, marking(&["start"]), &[], None, closed_rx(), Duration::ZERO).await;
        assert_eq!(reason, TerminationReason::Terminal);
        assert!(
            started.elapsed() < Duration::from_millis(120),
            "the run returned after {:?}; it must not wait out the 150ms action",
            started.elapsed()
        );
    }

    /// AC3's net: `inbox` feeds `process`; `cancel` is a terminal environment
    /// place.
    fn cancel_net() -> PetriNet {
        let inbox = EnvironmentPlace::<i32>::new("inbox");
        let cancel = EnvironmentPlace::<i32>::new("cancel");
        let processed = Place::<i32>::new("processed");
        PetriNet::builder("cancellable")
            .transition(
                Transition::builder("process")
                    .input(one(inbox.place()))
                    .output(out_place(&processed))
                    .action(fork())
                    .build(),
            )
            .terminal(cancel.place())
            .build()
    }

    fn ev(place: &str) -> ExternalEvent {
        ExternalEvent { place_name: Arc::from(place), token: ErasedToken::from_typed(&Token::at(7i32, 0)) }
    }

    #[tokio::test]
    async fn ac3_injection_into_a_terminal_environment_place_ends_the_run_and_refuses_the_queue() {
        for backend in BACKENDS {
            let (tx, rx) = unbounded_channel();
            let mut handle = ExecutorHandle::new(tx);
            assert!(handle.inject(Arc::from("cancel"), ev("cancel").token));
            assert!(handle.inject(Arc::from("inbox"), ev("inbox").token), "queued behind the cancel");
            let snapshot = handle.snapshot().expect("request a snapshot behind the cancel");

            let (m, reason, _) =
                run_async(backend, &cancel_net(), Marking::new(), &["inbox", "cancel"], None, rx, Duration::ZERO).await;
            assert_eq!(reason, TerminationReason::Terminal, "{backend:?}");
            assert_eq!(m.count("cancel"), 1, "{backend:?}");
            assert_eq!(
                (m.count("inbox"), m.count("processed")),
                (0, 0),
                "{backend:?}: the event queued behind the terminal injection must be refused"
            );
            let served: SnapshotResult = snapshot.await.expect("a snapshot queued behind the stop is answered");
            assert!(!served.action_in_flight, "{backend:?}");
            assert!(
                !handle.inject(Arc::from("inbox"), ev("inbox").token),
                "{backend:?}: an inject after the terminal stop is refused"
            );
        }
    }

    #[tokio::test]
    async fn ac3_a_terminal_event_mid_batch_refuses_the_rest_of_the_batch() {
        for backend in BACKENDS {
            let (tx, rx) = unbounded_channel();
            let mut handle = ExecutorHandle::new(tx);
            assert!(handle.inject_many(vec![ev("inbox"), ev("cancel"), ev("inbox")]));
            let (m, reason, _) =
                run_async(backend, &cancel_net(), Marking::new(), &["inbox", "cancel"], None, rx, Duration::ZERO).await;
            assert_eq!(reason, TerminationReason::Terminal, "{backend:?}");
            // The first inbox token was admitted with the batch; the run then
            // stopped before `process` could fire on it.
            assert_eq!((m.count("inbox"), m.count("processed")), (1, 0), "{backend:?}");
            drop(handle);
        }
    }

    #[tokio::test]
    async fn a_close_that_truncates_reports_closed_and_an_idle_close_quiescent() {
        // Truncating: a delayed transition is enabled when the close lands.
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let net = PetriNet::builder("slowpoke")
            .transition(
                Transition::builder("later")
                    .timing(libpetri::core::timing::delayed(10_000))
                    .input(one(&a))
                    .output(out_place(&b))
                    .action(fork())
                    .build(),
            )
            .build();
        for backend in BACKENDS {
            let (tx, rx) = unbounded_channel();
            let mut handle = ExecutorHandle::new(tx);
            handle.close();
            let (m, reason, _) = run_async(backend, &net, marking(&["a"]), &[], None, rx, Duration::ZERO).await;
            assert_eq!(reason, TerminationReason::Closed, "{backend:?}");
            assert!(!reason.is_complete());
            assert_eq!(m.count("a"), 1);

            // Idle: nothing enabled, nothing in flight — quiescent, as Java
            // decides it.
            let (tx, rx) = unbounded_channel();
            let mut handle = ExecutorHandle::new(tx);
            handle.close();
            let (_, reason, _) = run_async(backend, &net, Marking::new(), &["a"], None, rx, Duration::ZERO).await;
            assert_eq!(reason, TerminationReason::Quiescent, "{backend:?}");
        }
    }

    #[tokio::test]
    async fn the_owned_entry_point_reports_the_reason() {
        use libpetri::runtime::owned_precompiled::OwnedPrecompiledNet;
        let owned = OwnedPrecompiledNet::compile(&same_pass_net(10));
        let outcome = owned.builder::<NoopEventStore>(marking(&["a", "b"])).run_async_outcome(closed_rx()).await;
        assert_eq!(outcome.termination_reason, TerminationReason::Terminal);
        assert_eq!(outcome.marking.count("c"), 0);
        let outcome = owned.builder::<NoopEventStore>(marking(&["b"])).run_sync_outcome();
        assert_eq!(outcome.termination_reason, TerminationReason::Quiescent);
        assert_eq!(outcome.marking.count("c"), 1);
    }

    // --------------------------------------------------------
    //  ENV-014 AC9 — a parked executor answers without waking
    // --------------------------------------------------------

    /// A host clock whose wait never completes on its own, and which records
    /// that the orchestrator is parked in it.
    #[derive(Debug, Default)]
    struct ParkingClock {
        inner: ManualClock,
        parked: AtomicUsize,
    }

    impl ExecutorClock for ParkingClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, _ready: &dyn Fn() -> bool, _delay_ms: f64) {}
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            self.parked.fetch_add(1, Ordering::SeqCst);
            Box::pin(pending())
        }
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn env014_ac9_a_snapshot_is_served_while_parked_in_the_host_wait() {
        for backend in BACKENDS {
            let clock = Arc::new(ParkingClock::default());
            let (tx, rx) = unbounded_channel();
            let mut handle = ExecutorHandle::new(tx);
            // An env place nothing consumes: the token stays, so the snapshot
            // shows whether it reports the CURRENT marking.
            let inbox = EnvironmentPlace::<i32>::new("inbox");
            let out = Place::<i32>::new("out");
            let net = PetriNet::builder("idle")
                .transition(Transition::builder("never").input(one(&out)).action(fork()).build())
                .place(inbox.place().into())
                .build();
            let run_clock = Arc::clone(&clock) as Arc<dyn ExecutorClock>;
            let task = tokio::spawn(async move {
                run_async(backend, &net, Marking::new(), &["inbox"], Some(run_clock), rx, Duration::ZERO).await
            });

            let wait_parked = |n: usize| {
                let clock = Arc::clone(&clock);
                async move {
                    timeout(Duration::from_secs(5), async {
                        while clock.parked.load(Ordering::SeqCst) < n {
                            sleep(Duration::from_millis(1)).await;
                        }
                    })
                    .await
                    .expect("the orchestrator must park in the host wait");
                }
            };
            wait_parked(1).await;
            assert!(handle.inject(Arc::from("inbox"), ev("inbox").token));
            wait_parked(2).await;
            // Parked again, in a wait that never completes: only the signal
            // race can answer this.
            let reply = handle.snapshot().expect("request");
            let snap = timeout(Duration::from_millis(500), reply)
                .await
                .expect("ENV-014 AC9: a parked executor must answer without its wait completing")
                .expect("reply");
            assert_eq!(snap.marking.get("inbox").map(|q| q.len()), Some(1), "{backend:?}: current marking");
            assert!(!snap.action_in_flight);

            handle.close();
            let (_, reason, _) = task.await.unwrap();
            assert_eq!(reason, TerminationReason::Quiescent, "{backend:?}");
        }
    }

    // --------------------------------------------------------
    //  TIME-015 AC11 — completing an action future inside the wait
    // --------------------------------------------------------

    /// A host that executes actions itself: its wait completes the in-flight
    /// action's future (a oneshot the action awaits) and returns a wait that
    /// never completes on its own.
    #[derive(Debug, Default)]
    struct CompletingClock {
        inner: ManualClock,
        pending: Mutex<Option<oneshot::Sender<i32>>>,
        completed_in_wait: AtomicBool,
        waits: AtomicUsize,
    }

    impl ExecutorClock for CompletingClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, _ready: &dyn Fn() -> bool, _delay_ms: f64) {}
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            self.waits.fetch_add(1, Ordering::SeqCst);
            if let Some(tx) = self.pending.lock().unwrap().take() {
                // Complete the action's future from inside the wait, and
                // return. Nothing here awaits an admission.
                let _ = tx.send(42);
                self.completed_in_wait.store(true, Ordering::SeqCst);
            }
            Box::pin(pending())
        }
    }

    #[tokio::test]
    async fn time015_ac11_an_action_future_completed_inside_the_wait_is_admitted_next_cycle() {
        for backend in BACKENDS {
            let clock = Arc::new(CompletingClock::default());
            let action_clock = Arc::clone(&clock);
            let a = Place::<i32>::new("a");
            let b = Place::<i32>::new("b");
            let net = PetriNet::builder("hosted")
                .transition(
                    Transition::builder("activity")
                        .input(one(&a))
                        .output(out_place(&b))
                        .action(async_action(move |mut ctx: TransitionContext| {
                            let (tx, rx) = oneshot::channel();
                            *action_clock.pending.lock().unwrap() = Some(tx);
                            async move {
                                let v = rx.await.map_err(|_| libpetri::core::action::ActionError::new("dropped"))?;
                                ctx.output("b", v)?;
                                Ok(ctx)
                            }
                        }))
                        .build(),
                )
                .build();
            let (m, reason, _) = run_async(
                backend,
                &net,
                marking(&["a"]),
                &[],
                Some(Arc::clone(&clock) as Arc<dyn ExecutorClock>),
                closed_rx(),
                Duration::ZERO,
            )
            .await;
            assert!(clock.completed_in_wait.load(Ordering::SeqCst), "{backend:?}: completed inside the wait");
            assert_eq!(m.count("b"), 1, "{backend:?}: the result is admitted on a following cycle");
            assert_eq!(reason, TerminationReason::Quiescent, "{backend:?}");
        }
    }
}

// ============================================================
//  AC7 / AC8 — the verifier applies the net's terminals
// ============================================================

#[cfg(feature = "z3")]
mod verification {
    use super::*;
    use libpetri::core::arc::inhibitor;
    use libpetri::verification::marking_state::MarkingStateBuilder;
    use libpetri::verification::property::SmtProperty;
    use libpetri::verification::result::Verdict;
    use libpetri::verification::smt_verifier::{SmtVerifier, z3_available};
    use libpetri::verification::terminal_places::inhibit_on_terminals;

    /// The shared fixture net `terminalForkInFlight`: `fork` → `a` + `b`;
    /// `finish`: `a` → `done`; `work`: `b` → `result`. With `terminal`, `done`
    /// is declared terminal; with `explicit`, the same encoding is written
    /// out by hand instead (inhibitors on every transition).
    fn fork_net(terminal: bool, explicit: bool) -> PetriNet {
        let start = Place::<i32>::new("start");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let done = Place::<i32>::new("done");
        let result = Place::<i32>::new("result");
        let t = |name: &str| {
            let mut tb = Transition::builder(name).action(fork());
            if explicit {
                tb = tb.inhibitor(inhibitor(&done));
            }
            tb
        };
        // Places declared up front so both nets share one place order.
        let mut nb = PetriNet::builder("terminalForkInFlight")
            .places([(&start).into(), (&a).into(), (&b).into(), (&done).into(), (&result).into()])
            .transition(t("fork").input(one(&start)).output(and(vec![out_place(&a), out_place(&b)])).build())
            .transition(t("finish").input(one(&a)).output(out_place(&done)).build())
            .transition(t("work").input(one(&b)).output(out_place(&result)).build());
        if terminal {
            nb = nb.terminal(&done);
        }
        nb.build()
    }

    fn verifier(net: &PetriNet) -> SmtVerifier<'_> {
        SmtVerifier::for_net(net)
            .initial_marking(MarkingStateBuilder::new().tokens("start", 1).build())
            .property(SmtProperty::DeadlockFree)
            .timeout(30_000)
    }

    #[test]
    fn ac7_the_verifier_proves_deadlock_freedom_only_with_the_terminal() {
        if !z3_available() {
            eprintln!("skipping: z3 binary not on PATH");
            return;
        }
        for scg in [0, 50_000] {
            let undeclared = verifier(&fork_net(false, false)).enumeration_max_classes(scg).verify();
            assert!(
                matches!(undeclared.verdict, Verdict::Violated),
                "without the declaration the stranded in-flight work is a DeadlockFree violation \
                 (classes={scg}):\n{}",
                undeclared.report
            );
            let declared = verifier(&fork_net(true, false)).enumeration_max_classes(scg).verify();
            assert!(
                matches!(declared.verdict, Verdict::Proven { .. }),
                "with `done` terminal DeadlockFree must be proven with no sink option \
                 (classes={scg}):\n{}",
                declared.report
            );
        }
    }

    #[test]
    fn ac8_a_net_without_terminals_is_not_rewritten_and_the_rewrite_is_the_explicit_encoding() {
        let plain = fork_net(false, false);
        assert!(inhibit_on_terminals(&plain).is_none(), "no terminals: the original net is verified");

        let declared = verifier(&fork_net(true, false)).encode_scripts();
        let undeclared = verifier(&plain).encode_scripts();
        assert_ne!(declared.horn, undeclared.horn, "the declaration must reach the script");

        // Exactness: the declared net scripts byte-identically to the same
        // encoding written out by the caller.
        let all: Vec<String> = ["start", "a", "b", "done", "result"].iter().map(|s| s.to_string()).collect();
        let explicit_net = fork_net(false, true);
        let explicit = verifier(&explicit_net)
            .sink_places(["done".to_string()])
            .sink_places_when("done", all)
            .encode_scripts();
        assert_eq!(declared.horn, explicit.horn);
        assert_eq!(declared.certificate, explicit.certificate);
    }
}
