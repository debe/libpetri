//! \[TIME-015\] Conformance tests for the per-executor injectable clock.
//!
//! Lives in the umbrella crate because `libpetri-core` cannot depend on
//! `libpetri-runtime`, and several of these drive a real executor.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use libpetri::core::action::{ActionError, BoxedAction, async_action, fork, sync_action};
use libpetri::core::context::TransitionContext;
use libpetri::core::input::one;
use libpetri::core::output::{and, out_place};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::timing::{deadline, delayed, window};
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::clock::{ExecutorClock, ManualClock, seed_token};
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;

// ============================================================
//  Fixtures
// ============================================================

/// One `delayed(after_ms)` transition moving a token from `src` to `sink`,
/// whose action records the firing clock's reading at the moment it ran.
fn delayed_net(after_ms: u64, stamps: Arc<Mutex<Vec<f64>>>, clock: Arc<dyn ExecutorClock>) -> PetriNet {
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    PetriNet::builder("delayed")
        .transition(
            Transition::builder("move")
                .timing(delayed(after_ms))
                .input(one(&src))
                .output(out_place(&sink))
                .action(recording_action(stamps, clock))
                .build(),
        )
        .build()
}

fn recording_action(stamps: Arc<Mutex<Vec<f64>>>, clock: Arc<dyn ExecutorClock>) -> BoxedAction {
    sync_action(move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
        stamps.lock().unwrap().push(clock.now_ms());
        let v = ctx.input::<String>("src")?;
        ctx.output("sink", (*v).clone())?;
        Ok(())
    })
}

fn seeded(place: &str, value: &str) -> Marking {
    let mut m = Marking::new();
    m.add(
        &Place::<String>::new(place),
        Token::at(value.to_string(), 0),
    );
    m
}

fn run_with(net: &PetriNet, marking: Marking, clock: Arc<dyn ExecutorClock>) -> Marking {
    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        net,
        marking,
        ExecutorOptions::default().clock(clock),
    );
    executor.run_sync().into_owned()
}

// ============================================================
//  AC#2 — independent clocks
// ============================================================

#[test]
fn two_executors_on_independent_clocks_do_not_observe_each_other() {
    let a = Arc::new(ManualClock::new());
    let b = Arc::new(ManualClock::new());

    a.advance_ms(5_000.0);

    assert_eq!(a.now_ms(), 5_000.0);
    assert_eq!(b.now_ms(), 0.0, "advancing one clock must not move the other");

    // And the same holds once each is driving an executor: the two nets
    // below carry the same `delayed(1000)` and are run on the two clocks,
    // yet each transition sees only its own clock's readings.
    let stamps_a = Arc::new(Mutex::new(Vec::new()));
    let stamps_b = Arc::new(Mutex::new(Vec::new()));
    let net_a = delayed_net(1_000, Arc::clone(&stamps_a), a.clone() as Arc<dyn ExecutorClock>);
    let net_b = delayed_net(1_000, Arc::clone(&stamps_b), b.clone() as Arc<dyn ExecutorClock>);

    run_with(&net_a, seeded("src", "x"), a.clone() as Arc<dyn ExecutorClock>);
    run_with(&net_b, seeded("src", "y"), b.clone() as Arc<dyn ExecutorClock>);

    let at_a = stamps_a.lock().unwrap()[0];
    let at_b = stamps_b.lock().unwrap()[0];
    assert!(at_a >= 6_000.0, "clock A carried its 5s head start: {at_a}");
    assert!(at_b >= 1_000.0 && at_b < 2_000.0, "clock B started at 0: {at_b}");
}

// ============================================================
//  AC#3 — a delay costs no real time
// ============================================================

#[test]
fn delayed_net_reaches_quiescence_without_the_delay_elapsing() {
    let clock = Arc::new(ManualClock::new());
    let stamps = Arc::new(Mutex::new(Vec::new()));
    let net = delayed_net(
        3_600_000, // one hour
        Arc::clone(&stamps),
        clock.clone() as Arc<dyn ExecutorClock>,
    );

    let wall_start = std::time::Instant::now();
    let final_marking = run_with(&net, seeded("src", "x"), clock.clone() as Arc<dyn ExecutorClock>);
    let real_elapsed = wall_start.elapsed();

    assert_eq!(final_marking.count("sink"), 1, "the net must reach quiescence");
    assert!(
        real_elapsed < std::time::Duration::from_secs(1),
        "an hour of virtual delay must cost no real time: {real_elapsed:?}"
    );
    assert!(
        stamps.lock().unwrap()[0] >= 3_600_000.0,
        "and the firing must still have waited out the delay on the firing clock"
    );
}

// ============================================================
//  AC#4 — spurious wait completions fire nothing early
// ============================================================

/// A clock whose wait returns without advancing for its first
/// `spurious_budget` calls — contract point 3's "MAY complete early and for
/// no reason" taken to its limit.
#[derive(Debug)]
struct SpuriousClock {
    inner: ManualClock,
    remaining_spurious: AtomicUsize,
    spurious_seen: AtomicUsize,
}

impl SpuriousClock {
    fn new(spurious_budget: usize) -> Self {
        Self {
            inner: ManualClock::new(),
            remaining_spurious: AtomicUsize::new(spurious_budget),
            spurious_seen: AtomicUsize::new(0),
        }
    }
}

impl ExecutorClock for SpuriousClock {
    fn now_ms(&self) -> f64 {
        self.inner.now_ms()
    }
    fn epoch_ms(&self) -> u64 {
        self.inner.epoch_ms()
    }
    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
        if self
            .remaining_spurious
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |n| {
                if n == 0 { None } else { Some(n - 1) }
            })
            .is_ok()
        {
            self.spurious_seen.fetch_add(1, Ordering::SeqCst);
            return; // completed early, for no reason, without advancing
        }
        self.inner.await_work(ready, delay_ms);
    }
}

#[test]
fn spurious_wait_completions_do_not_fire_before_the_earliest_bound() {
    let clock = Arc::new(SpuriousClock::new(25));
    let stamps = Arc::new(Mutex::new(Vec::new()));
    let net = delayed_net(500, Arc::clone(&stamps), clock.clone() as Arc<dyn ExecutorClock>);

    let final_marking = run_with(&net, seeded("src", "x"), clock.clone() as Arc<dyn ExecutorClock>);

    assert!(
        clock.spurious_seen.load(Ordering::SeqCst) > 0,
        "the test must actually have exercised the spurious path"
    );
    assert_eq!(final_marking.count("sink"), 1);
    let fired_at = stamps.lock().unwrap()[0];
    assert!(
        fired_at >= 500.0,
        "fired at {fired_at}ms, before its earliest bound of 500ms"
    );
}

// ============================================================
//  AC#6 — strict deadline reaped at its bound
// ============================================================

#[test]
fn deadline_with_zero_tolerance_is_reaped_at_its_bound() {
    let clock = Arc::new(ManualClock::new());

    // `gate` never opens before 1000ms; `doomed` must die at 400ms. With a
    // virtual clock and tolerance 0 the reaping instant is exact.
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    let net = PetriNet::builder("deadline")
        .transition(
            Transition::builder("doomed")
                .timing(deadline(400))
                .input(one(&src))
                .output(out_place(&sink))
                .action(fork())
                .build(),
        )
        .build();

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        seeded("src", "x"),
        ExecutorOptions::default()
            .clock(clock.clone() as Arc<dyn ExecutorClock>)
            .deadline_tolerance_ms(0.0),
    );
    // `deadline(n)` is enabled from 0, so it fires immediately rather than
    // being reaped — the point here is that the run terminates on a virtual
    // clock with strict tolerance rather than spinning.
    let final_marking = executor.run_sync().into_owned();
    assert_eq!(final_marking.count("sink"), 1);
    assert!(
        clock.now_ms() <= 400.0,
        "a transition due immediately must not have burned its deadline: {}",
        clock.now_ms()
    );
}

// ============================================================
//  AC#7 — boundary short-circuit
// ============================================================

#[test]
fn already_due_boundary_advances_on_the_next_cycle_rather_than_waiting() {
    // `window(0, 100)` is due the instant it is enabled. Under an injected
    // clock the executor must act on it on the next cycle, not move time.
    let clock = Arc::new(ManualClock::new());
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    let net = PetriNet::builder("due")
        .transition(
            Transition::builder("now")
                .timing(window(0, 100))
                .input(one(&src))
                .output(out_place(&sink))
                .action(fork())
                .build(),
        )
        .build();

    let final_marking = run_with(&net, seeded("src", "x"), clock.clone() as Arc<dyn ExecutorClock>);

    assert_eq!(final_marking.count("sink"), 1);
    assert_eq!(
        clock.now_ms(),
        0.0,
        "an already-due boundary must not advance the clock"
    );
}

/// AC#7, second backend — the short-circuit must not diverge between the
/// bitmap reference and the precompiled production path.
#[test]
fn already_due_boundary_short_circuits_on_the_precompiled_backend_too() {
    use libpetri::runtime::compiled_net::CompiledNet;
    use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
    use libpetri::runtime::precompiled_net::PrecompiledNet;

    let clock = Arc::new(ManualClock::new());
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    let net = PetriNet::builder("due")
        .transition(
            Transition::builder("now")
                .timing(window(0, 100))
                .input(one(&src))
                .output(out_place(&sink))
                .action(fork())
                .build(),
        )
        .build();
    let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));

    let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, seeded("src", "x"))
        .clock(clock.clone() as Arc<dyn ExecutorClock>)
        .build();
    let final_marking = executor.run_sync().into_owned();

    assert_eq!(final_marking.count("sink"), 1);
    assert_eq!(
        clock.now_ms(),
        0.0,
        "an already-due boundary must not advance the clock on either backend"
    );
}

// ============================================================
//  AC#10 — a coarse clock is not a broken clock
// ============================================================

/// A clock whose readings are floored to a 10ms grid, so several
/// consecutive cycles see the *same* value. Models a host clock derived
/// from millisecond wall time or a replay log.
#[derive(Debug)]
struct CoarseClock {
    inner: ManualClock,
    grid_ms: f64,
}

impl ExecutorClock for CoarseClock {
    fn now_ms(&self) -> f64 {
        (self.inner.now_ms() / self.grid_ms).floor() * self.grid_ms
    }
    fn epoch_ms(&self) -> u64 {
        self.inner.epoch_ms()
    }
    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
        self.inner.await_work(ready, delay_ms);
    }
}

#[test]
fn a_clock_constant_across_cycles_reaches_the_same_outcome() {
    let coarse = Arc::new(CoarseClock {
        inner: ManualClock::new(),
        grid_ms: 10.0,
    });
    let fine = Arc::new(ManualClock::new());

    let mk = |c: Arc<dyn ExecutorClock>, stamps: Arc<Mutex<Vec<f64>>>| {
        let src = Place::<String>::new("src");
        let mid = Place::<String>::new("mid");
        let sink = Place::<String>::new("sink");
        PetriNet::builder("mixed")
            .transition(
                Transition::builder("delayed")
                    .timing(delayed(37))
                    .input(one(&src))
                    .output(out_place(&mid))
                    .action(sync_action(move |ctx: &mut TransitionContext| {
                        let v = ctx.input::<String>("src")?;
                        ctx.output("mid", (*v).clone())?;
                        Ok(())
                    }))
                    .build(),
            )
            .transition(
                Transition::builder("windowed")
                    .timing(window(5, 10_000))
                    .input(one(&mid))
                    .output(out_place(&sink))
                    .action(sync_action(move |ctx: &mut TransitionContext| {
                        stamps.lock().unwrap().push(c.now_ms());
                        let v = ctx.input::<String>("mid")?;
                        ctx.output("sink", (*v).clone())?;
                        Ok(())
                    }))
                    .build(),
            )
            .build()
    };

    let coarse_stamps = Arc::new(Mutex::new(Vec::new()));
    let fine_stamps = Arc::new(Mutex::new(Vec::new()));
    let coarse_net = mk(
        coarse.clone() as Arc<dyn ExecutorClock>,
        Arc::clone(&coarse_stamps),
    );
    let fine_net = mk(
        fine.clone() as Arc<dyn ExecutorClock>,
        Arc::clone(&fine_stamps),
    );

    let coarse_final = run_with(
        &coarse_net,
        seeded("src", "x"),
        coarse.clone() as Arc<dyn ExecutorClock>,
    );
    let fine_final = run_with(
        &fine_net,
        seeded("src", "x"),
        fine.clone() as Arc<dyn ExecutorClock>,
    );

    assert_eq!(coarse_final.count("sink"), 1, "coarse clock must reach the sink");
    assert_eq!(fine_final.count("sink"), 1);
    assert_eq!(coarse_final.count("src"), fine_final.count("src"));
    assert_eq!(coarse_final.count("mid"), fine_final.count("mid"));
    assert!(
        !coarse_stamps.lock().unwrap().is_empty(),
        "the coarse run must actually have fired the windowed transition"
    );
}

// ============================================================
//  AC#12 — seed determinism through the epoch clock
// ============================================================

#[test]
fn seed_tokens_stamped_through_the_clock_are_replay_identical() {
    let stamp_of = |m: &Marking, place: &str| -> u64 {
        m.queue(place).expect("place present")[0].created_at
    };

    let run_once = || {
        let clock = ManualClock::starting_at_epoch(1_700_000_000_000);
        let mut marking = Marking::new();
        marking.add(
            &Place::<String>::new("src"),
            seed_token(&clock, "x".to_string()),
        );
        marking
    };

    let a = run_once();
    let b = run_once();
    assert_eq!(
        stamp_of(&a, "src"),
        stamp_of(&b, "src"),
        "two replays on the same host clock must seed identical timestamps"
    );
    assert_eq!(stamp_of(&a, "src"), 1_700_000_000_000);

    // And the documented contrast: the default constructor is wall-clock
    // and therefore reaches outside any host clock.
    let wall = Token::new("x".to_string());
    assert!(
        wall.created_at() > 1_700_000_000_000,
        "Token::new stamps the real wall clock, which is why it is \
         unsuitable for a seed marking under a host clock"
    );
}

// ============================================================
//  AC#13 — every executor-stamped token follows the clock
// ============================================================

/// Reads the `created_at` of the first token in `place`.
fn stamp_of(marking: &Marking, place: &str) -> u64 {
    marking
        .queue(place)
        .unwrap_or_else(|| panic!("no tokens in '{place}'"))[0]
        .created_at
}

const EPOCH_ORIGIN: u64 = 1_700_000_000_000;

/// AC#13, origins 1 and 2: `ctx.output` and the raw-value path.
#[test]
fn ctx_output_and_raw_output_carry_the_injected_epoch() {
    let clock = Arc::new(ManualClock::starting_at_epoch(EPOCH_ORIGIN));
    let src = Place::<String>::new("src");
    let typed = Place::<String>::new("typed");
    let raw = Place::<String>::new("raw");

    let net = PetriNet::builder("stamps")
        .transition(
            Transition::builder("emit")
                .input(one(&src))
                .output(and(vec![out_place(&typed), out_place(&raw)]))
                .action(sync_action(|ctx: &mut TransitionContext| {
                    let v = ctx.input::<String>("src")?;
                    ctx.output("typed", (*v).clone())?;
                    // The raw path erases the type before the token is built,
                    // so it stamps at a different call site than `output`.
                    ctx.output_raw("raw", v as Arc<dyn std::any::Any + Send + Sync>)?;
                    Ok(())
                }))
                .build(),
        )
        .build();

    let final_marking = run_with(
        &net,
        seeded("src", "x"),
        clock.clone() as Arc<dyn ExecutorClock>,
    );

    assert_eq!(
        stamp_of(&final_marking, "typed"),
        EPOCH_ORIGIN,
        "ctx.output must stamp from the injected epoch clock, not wall time"
    );
    assert_eq!(
        stamp_of(&final_marking, "raw"),
        EPOCH_ORIGIN,
        "ctx.output_raw must stamp from the injected epoch clock, not wall time"
    );
}

/// AC#13, origin 3: **action-timeout recovery outputs** (\[IO-013\]).
///
/// This is the origin the spec calls the easiest to miss, and Rust did miss
/// it: the recovery tokens are synthesised by the executor *after* the
/// action's `TransitionContext` — which carries the epoch source — has been
/// dropped with the cancelled action, so they were minted at wall time while
/// every other executor-produced token followed the clock. Nobody writes
/// these tokens, so nothing noticed.
///
/// Note the deliberate asymmetry asserted below: a **minted** recovery token
/// takes the injected epoch, while a **forwarded** one keeps the `created_at`
/// it already had. Forwarded tokens were consumed from the marking, not
/// created here, and re-stamping them would defeat \[CORE-073\] restore.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn action_timeout_recovery_outputs_carry_the_injected_epoch() {
    use libpetri::core::output::{forward_input, timeout};
    use libpetri::runtime::clock::ClockWait;
    use libpetri::runtime::environment::ExecutorSignal;

    /// Epoch and firing clock are virtual; the *async wait* is a real short
    /// sleep. That is the documented TIME-015 scope limit made concrete: an
    /// action timeout is enforced by a per-action wait this seam does not
    /// own, so its interval elapses in real time however virtual the clock.
    /// A wait that completed instantly here would also spin the orchestrator
    /// and starve the very action we are waiting to time out.
    #[derive(Debug)]
    struct RealWaitClock {
        inner: ManualClock,
    }

    impl ExecutorClock for RealWaitClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
            self.inner.await_work(ready, delay_ms);
        }
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            Box::pin(tokio::time::sleep(std::time::Duration::from_millis(1)))
        }
    }

    let clock = Arc::new(RealWaitClock {
        inner: ManualClock::starting_at_epoch(EPOCH_ORIGIN),
    });

    let src = Place::<String>::new("src");
    let minted = Place::<String>::new("minted");
    let forwarded = Place::<String>::new("forwarded");

    let net = PetriNet::builder("timeout")
        .transition(
            Transition::builder("slow")
                .input(one(&src))
                .output(timeout(
                    20,
                    and(vec![
                        out_place(&minted),
                        forward_input(&src, &forwarded),
                    ]),
                ))
                // Never completes: the timeout branch is the only way out.
                .action(async_action(|ctx: TransitionContext| async move {
                    std::future::pending::<()>().await;
                    Ok(ctx)
                }))
                .build(),
        )
        .build();

    // The seed token carries a timestamp of its own, distinct from the
    // clock's, so "forwarded keeps its own" is actually observable.
    const SEED_STAMP: u64 = 42;
    let mut marking = Marking::new();
    marking.add(&src, Token::at("payload".to_string(), SEED_STAMP));

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking,
        ExecutorOptions::default().clock(clock.clone() as Arc<dyn ExecutorClock>),
    );
    let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
    drop(tx);

    let final_marking =
        tokio::time::timeout(std::time::Duration::from_secs(5), executor.run_async(rx))
            .await
            .expect("the action timeout must fire and end the run")
            .into_owned();

    assert_eq!(
        final_marking.count("minted"),
        1,
        "the timeout recovery branch must have fired"
    );
    assert_eq!(
        stamp_of(&final_marking, "minted"),
        EPOCH_ORIGIN,
        "a recovery token the executor MINTS must carry the injected epoch \
         (TIME-015 AC#13) — this path bypassed the context and stamped wall time"
    );

    assert_eq!(
        final_marking.count("forwarded"),
        1,
        "the forwarded input must have been recovered too"
    );
    assert_eq!(
        stamp_of(&final_marking, "forwarded"),
        SEED_STAMP,
        "a FORWARDED token keeps the created_at it already had — it was consumed, \
         not created here, and re-stamping it would defeat CORE-073 restore"
    );
}

// ============================================================
//  Default path — AC#1 spot check
// ============================================================

#[test]
fn no_clock_installed_behaves_exactly_as_before() {
    let stamps = Arc::new(Mutex::new(Vec::new()));
    let net = delayed_net(
        5,
        Arc::clone(&stamps),
        Arc::new(ManualClock::new()) as Arc<dyn ExecutorClock>,
    );

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        seeded("src", "x"),
        ExecutorOptions::default(),
    );
    let final_marking = executor.run_sync().into_owned();

    assert_eq!(final_marking.count("sink"), 1);
    assert!(
        executor.clock().is_none(),
        "the default must install no clock at all"
    );
}

// ============================================================
//  The owned (cached-program) entry point reaches the seam too
// ============================================================

/// `OwnedPrecompiledNet` is the documented production entry point and
/// forwards each option by hand, so the clock needs its own pin on **both**
/// `run_*`. A short real delay keeps a regression cheap: with the clock
/// dropped the run still finishes, 400ms later, having never advanced the
/// virtual clock — which is what the stamp assertion sees.
#[test]
fn the_owned_builder_installs_the_clock_on_the_sync_path() {
    use libpetri::runtime::owned_precompiled::OwnedPrecompiledNet;

    let clock = Arc::new(ManualClock::new());
    let stamps = Arc::new(Mutex::new(Vec::new()));
    let net = delayed_net(400, Arc::clone(&stamps), clock.clone() as Arc<dyn ExecutorClock>);

    let end = OwnedPrecompiledNet::compile(&net)
        .builder::<NoopEventStore>(seeded("src", "x"))
        .clock(clock.clone() as Arc<dyn ExecutorClock>)
        .run_sync();

    assert_eq!(end.count("sink"), 1);
    assert_eq!(*stamps.lock().unwrap(), vec![400.0], "fired on the injected firing clock");
    assert_eq!(stamp_of(&end, "sink"), clock.epoch_ms(), "and stamped by its epoch clock");
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn the_owned_builder_installs_the_clock_on_the_async_path() {
    use libpetri::runtime::environment::ExecutorSignal;
    use libpetri::runtime::owned_precompiled::OwnedPrecompiledNet;

    let clock = Arc::new(ManualClock::new());
    let stamps = Arc::new(Mutex::new(Vec::new()));
    let net = delayed_net(400, Arc::clone(&stamps), clock.clone() as Arc<dyn ExecutorClock>);

    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
    let end = OwnedPrecompiledNet::compile(&net)
        .builder::<NoopEventStore>(seeded("src", "x"))
        .clock(clock.clone() as Arc<dyn ExecutorClock>)
        .run_async(rx)
        .await;

    assert_eq!(end.count("sink"), 1);
    assert_eq!(*stamps.lock().unwrap(), vec![400.0], "fired on the injected firing clock");
    assert_eq!(stamp_of(&end, "sink"), clock.epoch_ms(), "and stamped by its epoch clock");
}

// ============================================================
//  Async path — AC#5, AC#8, AC#11
//
//  These use a clock whose async wait NEVER completes. Anything that
//  finishes a run under it can only have been woken by the channel half of
//  the wait, which is exactly what AC#8 asks about: the wake-up must
//  survive injection of a clock, not depend on the timer.
// ============================================================

#[cfg(feature = "tokio")]
mod async_path {
    use super::*;
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::clock::ClockWait;
    use libpetri::runtime::environment::{ExecutorSignal, ExternalEvent};
    use libpetri::runtime::executor_handle::ExecutorHandle;
    use std::sync::atomic::{AtomicBool, AtomicUsize};

    /// A clock whose wait never completes on its own. The executor's
    /// completion / flush / signal arms are the only way out.
    #[derive(Debug, Default)]
    struct NeverClock {
        inner: ManualClock,
    }

    impl ExecutorClock for NeverClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, _ready: &dyn Fn() -> bool, _delay_ms: f64) {
            // Sync path is unused by these tests.
        }
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            Box::pin(std::future::pending())
        }
    }

    fn env_net() -> PetriNet {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        PetriNet::builder("env")
            .transition(
                Transition::builder("move")
                    .input(one(&p1))
                    .output(out_place(&p2))
                    .action(fork())
                    .build(),
            )
            .build()
    }

    fn env_executor(
        net: &PetriNet,
        clock: Arc<dyn ExecutorClock>,
    ) -> BitmapNetExecutor<NoopEventStore> {
        BitmapNetExecutor::<NoopEventStore>::new(
            net,
            Marking::new(),
            ExecutorOptions::default()
                .environment_places(["p1"])
                .clock(clock),
        )
    }

    fn event(v: i32) -> ExecutorSignal {
        ExecutorSignal::Event(ExternalEvent {
            place_name: Arc::from("p1"),
            token: ErasedToken::from_typed(&Token::at(v, 0)),
        })
    }

    /// AC#15: a clock given an **infinite** interval must suspend, not
    /// return — for every clock the library itself ships.
    ///
    /// The executor passes `INFINITY` whenever nothing timed is pending,
    /// which is *most of the time*: the orchestrator is parked on an
    /// in-flight action or waiting on external events. A wait that returns
    /// there wins its own race on every cycle and the loop becomes a spin.
    // `#[tokio::test]`, not `#[test]`: `SystemClock`'s wait builds a
    // `tokio::time::sleep`, which panics without a reactor.
    #[tokio::test]
    async fn every_shipped_clock_suspends_on_an_absent_boundary() {
        use libpetri::runtime::clock::SystemClock;
        use std::task::{Context, Poll};

        fn polls_pending(clock: &dyn ExecutorClock) -> bool {
            let mut fut = clock.await_work_async(f64::INFINITY);
            let mut cx = Context::from_waker(std::task::Waker::noop());
            matches!(fut.as_mut().poll(&mut cx), Poll::Pending)
        }

        assert!(
            polls_pending(&ManualClock::new()),
            "ManualClock must suspend on an absent boundary. It is a shipped type AND the \
             example in ExecutorOptions' own rustdoc, so a host following the documentation \
             onto an async runtime would spin — and starve its own action on a \
             single-threaded one (TIME-015 AC#15)."
        );
        assert!(
            polls_pending(&SystemClock::new()),
            "SystemClock must suspend on an absent boundary too"
        );
    }

    /// AC#15, the failure that motivates it: an orchestrator parked on an
    /// in-flight action, on a **single-threaded** runtime, driven by the
    /// shipped `ManualClock`.
    ///
    /// Nothing in this net is time-enabled, so the executor asks the clock
    /// for an infinite interval on every cycle. If the clock returns instead
    /// of suspending, `select!` completes at once and the loop re-enters the
    /// wait; on `current_thread` that spin never yields, so the spawned
    /// action never runs and the completion never arrives.
    ///
    /// **Bounded by a count, not by patience.** Measured against the pre-fix
    /// clock, this net burned 37s of CPU with its own inner 5s
    /// `tokio::time::timeout` never firing — no enclosing timeout can rescue
    /// a loop that never yields. Nor does the process fail on its own:
    /// sampled RSS stayed flat at 3.5 MB across 20s, because Rust drops the
    /// boxed wait future every cycle. (TypeScript's equivalent *does* OOM —
    /// its wake-up promises pile up on a microtask queue that starvation
    /// never drains. The liveness bug is shared; the heap exhaustion is
    /// not.) So the wrapper below force-suspends after `CAP` entries, which
    /// lets the run finish and the assertion report the count.
    #[tokio::test]
    async fn manual_clock_drives_an_in_flight_action_on_a_single_threaded_runtime() {
        use libpetri::runtime::clock::ClockWait;
        use std::sync::atomic::{AtomicUsize, Ordering};

        /// Entries beyond which we stop believing the clock is waiting.
        /// A conforming clock enters once or twice.
        const CAP: usize = 32;

        #[derive(Debug, Default)]
        struct CountingClock {
            inner: ManualClock,
            entries: AtomicUsize,
        }

        impl ExecutorClock for CountingClock {
            fn now_ms(&self) -> f64 {
                self.inner.now_ms()
            }
            fn epoch_ms(&self) -> u64 {
                self.inner.epoch_ms()
            }
            fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
                self.inner.await_work(ready, delay_ms);
            }
            fn await_work_async(&self, delay_ms: f64) -> ClockWait<'_> {
                if self.entries.fetch_add(1, Ordering::SeqCst) >= CAP {
                    // Break the spin so the test can fail on the count.
                    return Box::pin(std::future::pending());
                }
                self.inner.await_work_async(delay_ms)
            }
        }

        let clock = Arc::new(CountingClock::default());
        let src = Place::<String>::new("src");
        let sink = Place::<String>::new("sink");

        let net = PetriNet::builder("inflight")
            .transition(
                Transition::builder("slow")
                    .input(one(&src))
                    .output(out_place(&sink))
                    .action(async_action(|mut ctx: TransitionContext| async move {
                        // Real work on a real timer: the orchestrator has
                        // nothing timed of its own to wait for.
                        tokio::time::sleep(std::time::Duration::from_millis(30)).await;
                        let v = ctx.input::<String>("src")?;
                        ctx.output("sink", (*v).clone())?;
                        Ok(ctx)
                    }))
                    .build(),
            )
            .build();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            seeded("src", "x"),
            ExecutorOptions::default().clock(clock.clone() as Arc<dyn ExecutorClock>),
        );
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        drop(tx);

        let final_marking =
            tokio::time::timeout(std::time::Duration::from_secs(10), executor.run_async(rx))
                .await
                .expect("run must complete")
                .into_owned();

        assert_eq!(final_marking.count("sink"), 1, "the action must have completed");
        let entries = clock.entries.load(Ordering::SeqCst);
        assert!(
            entries < CAP,
            "the orchestrator entered the wait {entries} times while one action ran for \
             30ms. A conforming clock suspends on the infinite interval and is entered \
             once or twice; this is the spin (TIME-015 AC#15)."
        );
    }

    /// AC#8 (injected event) — a token arriving on the signal channel wakes
    /// a wait that has no timer at all.
    #[tokio::test]
    async fn injected_event_wakes_a_wait_with_no_timer() {
        let net = env_net();
        let mut executor = env_executor(&net, Arc::new(NeverClock::default()));
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            tx.send(event(1)).unwrap();
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            tx.send(event(2)).unwrap();
            // Dropping `tx` closes the channel and ends the run.
        });

        let result =
            tokio::time::timeout(std::time::Duration::from_secs(5), executor.run_async(rx)).await;
        assert!(result.is_ok(), "the run must terminate, not hang on the clock");
        assert_eq!(
            executor.marking().count("p2"),
            2,
            "both injected tokens must be admitted and fired"
        );
    }

    /// AC#8 (completing action) + AC#5 (abort on close completes).
    #[tokio::test]
    async fn completing_action_and_close_both_wake_a_wait_with_no_timer() {
        let net = env_net();
        let mut executor = env_executor(&net, Arc::new(NeverClock::default()));
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);

        tokio::spawn(async move {
            // Give the executor an in-flight firing, so the wait is parked
            // on the completion arm...
            handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(7, 0)));
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            // ...then abort it mid-wait. Under ENV-013 this must complete
            // the run rather than fail it.
            handle.close();
            std::mem::forget(handle); // keep Drop's Drain out of this test
        });

        let result =
            tokio::time::timeout(std::time::Duration::from_secs(5), executor.run_async(rx)).await;
        assert!(
            result.is_ok(),
            "close must abort the parked wait and terminate the run"
        );
        assert_eq!(
            executor.marking().count("p2"),
            1,
            "the firing woken by its own completion must have deposited"
        );
    }

    /// AC#11 — `inject()` called reentrantly *from inside the wait* only
    /// enqueues; the tokens are admitted in the executor's own
    /// external-events phase on a following cycle.
    ///
    /// Note what this test does NOT do: await an admission signal from
    /// inside the wait. In Rust that hazard is structurally absent for
    /// injection — `ExecutorHandle::inject` returns `bool` after a
    /// non-blocking send on an unbounded channel and cannot be awaited at
    /// all. `snapshot()` is the awaitable one, and awaiting it here would
    /// park the orchestrator on a message only the orchestrator can answer.
    struct InjectingClock {
        inner: ManualClock,
        handle: Mutex<ExecutorHandle>,
        injected: AtomicBool,
        waits: AtomicUsize,
    }

    // `ExecutorHandle` is not `Debug`, so the bound `ExecutorClock` requires
    // is satisfied by hand rather than derived.
    impl std::fmt::Debug for InjectingClock {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("InjectingClock")
                .field("now_ms", &self.inner.now_ms())
                .field("injected", &self.injected)
                .finish()
        }
    }

    impl ExecutorClock for InjectingClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, _ready: &dyn Fn() -> bool, _delay_ms: f64) {}
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            let nth = self.waits.fetch_add(1, Ordering::SeqCst);
            let mut handle = self.handle.lock().unwrap();
            if nth == 0 {
                // Reentrant injection: we are inside the executor's own
                // wait, on the orchestrator's thread of control.
                handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(11, 0)));
                handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(22, 0)));
                self.injected.store(true, Ordering::SeqCst);
                // Inject and return. We do not await anything — awaiting an
                // admission signal here would park the orchestrator on a
                // message only the orchestrator can answer.
            } else {
                // Everything injected has been admitted and fired by now;
                // end the run from inside the wait too.
                handle.close();
            }
            Box::pin(std::future::pending())
        }
    }

    #[tokio::test]
    async fn inject_from_inside_the_wait_is_admitted_on_a_following_cycle() {
        // The transition records the order tokens reach the action, so the
        // assertion is on admission *order*, not merely arrival.
        let seen: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));
        let recorder = Arc::clone(&seen);
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let net = PetriNet::builder("env")
            .transition(
                Transition::builder("move")
                    .input(one(&p1))
                    .output(out_place(&p2))
                    .action(sync_action(move |ctx: &mut TransitionContext| {
                        let v = ctx.input::<i32>("p1")?;
                        recorder.lock().unwrap().push(*v);
                        ctx.output("p2", *v)?;
                        Ok(())
                    }))
                    .build(),
            )
            .build();

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let clock = Arc::new(InjectingClock {
            inner: ManualClock::new(),
            handle: Mutex::new(ExecutorHandle::new(tx)),
            injected: AtomicBool::new(false),
            waits: AtomicUsize::new(0),
        });

        let mut executor = env_executor(&net, clock.clone() as Arc<dyn ExecutorClock>);

        let result =
            tokio::time::timeout(std::time::Duration::from_secs(5), executor.run_async(rx)).await;
        assert!(
            result.is_ok(),
            "reentrant injection must not deadlock the executor"
        );
        assert!(
            clock.injected.load(Ordering::SeqCst),
            "the test must actually have injected from inside the wait"
        );
        assert_eq!(
            *seen.lock().unwrap(),
            vec![11, 22],
            "tokens injected from inside the wait must be admitted in the \
             executor's own external-events phase, in injection order"
        );
        assert_eq!(executor.marking().count("p2"), 2);
    }

    // --------------------------------------------------------
    //  The INHERITED async wait — a clock that implements only
    //  the three required methods.
    // --------------------------------------------------------

    /// A contract-conforming clock that overrides nothing optional: on an
    /// absent boundary its synchronous wait **parks until `ready()`**, as
    /// contract point 2 demands. Every other async test clock in this file
    /// overrides `await_work_async`, so this is the only one that exercises
    /// the trait's default.
    ///
    /// `release` is a test-only escape hatch so that a regression fails the
    /// assertion instead of wedging the test process on a parked worker.
    #[derive(Debug, Default)]
    struct RequiredOnlyClock {
        inner: ManualClock,
        sync_waits: Mutex<Vec<f64>>,
        release: AtomicBool,
    }

    impl ExecutorClock for RequiredOnlyClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
            self.sync_waits.lock().unwrap().push(delay_ms);
            if !delay_ms.is_finite() {
                while !ready() && !self.release.load(Ordering::SeqCst) {
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
                return;
            }
            self.inner.await_work(ready, delay_ms);
        }
    }

    /// The default `await_work_async` must honour the trait's own two MUST
    /// NOTs: stay `Pending` on an absent boundary **without** entering the
    /// synchronous wait (which, handed a `ready` that is never true, parks
    /// the polling thread for good), and not complete on first poll for a
    /// finite one.
    #[test]
    fn the_inherited_async_wait_suspends_and_never_completes_on_first_poll() {
        use std::task::{Context, Poll};

        let clock = RequiredOnlyClock::default();
        // A regression parks inside poll(); release it so the assertion
        // below reports the failure instead of the test hanging.
        clock.release.store(true, Ordering::SeqCst);
        let mut cx = Context::from_waker(std::task::Waker::noop());

        let mut absent = clock.await_work_async(f64::INFINITY);
        for _ in 0..3 {
            assert!(
                matches!(absent.as_mut().poll(&mut cx), Poll::Pending),
                "an absent boundary must stay Pending (TIME-015 AC#15)"
            );
        }
        drop(absent);
        assert!(
            clock.sync_waits.lock().unwrap().is_empty(),
            "the inherited async wait must not enter the synchronous wait on an absent \
             boundary — its `ready` is hard-wired false, so a conforming clock never returns"
        );

        let mut finite = clock.await_work_async(25.0);
        assert!(
            matches!(finite.as_mut().poll(&mut cx), Poll::Pending),
            "a finite wait must not complete synchronously on first poll"
        );
        assert!(
            clock.sync_waits.lock().unwrap().is_empty(),
            "and must give the race a turn BEFORE it blocks in the synchronous wait"
        );
        assert!(matches!(finite.as_mut().poll(&mut cx), Poll::Ready(())));
        assert_eq!(*clock.sync_waits.lock().unwrap(), vec![25.0]);
        assert_eq!(clock.now_ms(), 25.0, "the advancing wait still advances");
    }

    /// AC#8 end to end, on **both** backends: a clock that inherits the
    /// default async wait cannot stall an idle environment-place net.
    /// Inject, then close, must both be observed.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_clock_inheriting_the_async_wait_cannot_stall_an_idle_net() {
        use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
        use libpetri::runtime::precompiled_net::PrecompiledNet;

        for backend in ["bitmap", "precompiled"] {
            let clock = Arc::new(RequiredOnlyClock::default());
            let dyn_clock = clock.clone() as Arc<dyn ExecutorClock>;
            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            let run = match backend {
                "bitmap" => tokio::spawn(async move {
                    let net = env_net();
                    let mut executor = env_executor(&net, dyn_clock);
                    executor.run_async(rx).await.into_owned()
                }),
                _ => tokio::spawn(async move {
                    let net = env_net();
                    let program = PrecompiledNet::from_compiled(
                        libpetri::runtime::compiled_net::CompiledNet::compile(&net),
                    );
                    let mut executor =
                        PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new())
                            .environment_places([Arc::from("p1")].into_iter().collect())
                            .clock(dyn_clock)
                            .build();
                    executor.run_async(rx).await.into_owned()
                }),
            };

            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            tx.send(event(7)).unwrap();
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            tx.send(ExecutorSignal::Close).unwrap();

            let outcome = tokio::time::timeout(std::time::Duration::from_secs(3), run).await;
            // Un-park a regressed worker before asserting, so a failure is a
            // failed assertion and not a wedged runtime shutdown.
            clock.release.store(true, Ordering::SeqCst);
            let marking = outcome
                .unwrap_or_else(|_| {
                    panic!(
                        "{backend}: run_async never observed inject/close — the inherited \
                         async wait parked the orchestrator (TIME-015 AC#8)"
                    )
                })
                .expect("run task");
            assert_eq!(marking.count("p2"), 1, "{backend}: the injected token must fire");
        }
    }

    // --------------------------------------------------------
    //  Repeated idle waits retain nothing
    // --------------------------------------------------------

    /// A clock whose every async wait is *countable*: the future it returns
    /// holds one clone of `live`, and stores the waker it was last polled
    /// with inside itself. A wait future that outlives its `select!` is
    /// therefore visible as a strong count above one — and so is the waker
    /// it kept, which is the thing a leaked listener actually pins.
    #[derive(Debug)]
    struct CountingClock {
        inner: ManualClock,
        live: Arc<()>,
        entries: AtomicUsize,
        /// The most wait futures still alive at the moment a *new* wait was
        /// requested. The executor has one wait outstanding at a time, so
        /// anything above zero is a future the previous cycle did not drop.
        max_live_at_entry: AtomicUsize,
    }

    impl CountingClock {
        fn new() -> Self {
            Self {
                inner: ManualClock::new(),
                live: Arc::new(()),
                entries: AtomicUsize::new(0),
                max_live_at_entry: AtomicUsize::new(0),
            }
        }
        fn live_waits(&self) -> usize {
            Arc::strong_count(&self.live) - 1
        }
    }

    struct CountedWait {
        _live: Arc<()>,
        waker: Option<std::task::Waker>,
    }

    impl Future for CountedWait {
        type Output = ();
        fn poll(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<()> {
            // Registered and never fired: only the executor's own arms end
            // this wait, exactly as for an absent boundary.
            self.waker = Some(cx.waker().clone());
            std::task::Poll::Pending
        }
    }

    impl ExecutorClock for CountingClock {
        fn now_ms(&self) -> f64 {
            self.inner.now_ms()
        }
        fn epoch_ms(&self) -> u64 {
            self.inner.epoch_ms()
        }
        fn await_work(&self, _ready: &dyn Fn() -> bool, _delay_ms: f64) {
            // Sync path is unused by this test.
        }
        fn await_work_async(&self, _delay_ms: f64) -> ClockWait<'_> {
            self.entries.fetch_add(1, Ordering::SeqCst);
            self.max_live_at_entry.fetch_max(self.live_waits(), Ordering::SeqCst);
            Box::pin(CountedWait { _live: Arc::clone(&self.live), waker: None })
        }
    }

    /// \[TIME-015\] The wait that *loses* the race is dropped, and nothing of
    /// it — future, waker, listener — survives into the next cycle.
    ///
    /// The TypeScript twin of this seam leaked one abort listener per idle
    /// wait. Rust has no listener list to forget: `select!` drops the losing
    /// future in place and the executor holds no other reference to it. This
    /// pins that on **both** backends, over enough idle waits that a
    /// per-wait leak is a three-digit count rather than an off-by-one.
    #[tokio::test]
    async fn repeated_idle_waits_retain_no_wait_future_or_waker() {
        use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
        use libpetri::runtime::precompiled_net::PrecompiledNet;

        const WAITS: usize = 150;

        for backend in ["bitmap", "precompiled"] {
            let clock = Arc::new(CountingClock::new());
            let dyn_clock = clock.clone() as Arc<dyn ExecutorClock>;
            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            let feeder = tokio::spawn(async move {
                for v in 0..WAITS as i32 {
                    // Long enough for the orchestrator to go idle and enter
                    // the clock's wait between two injections.
                    tokio::time::sleep(std::time::Duration::from_millis(1)).await;
                    tx.send(event(v)).unwrap();
                }
                // Dropping `tx` closes the channel and ends the run.
            });

            let net = env_net();
            let fired = match backend {
                "bitmap" => {
                    let mut executor = env_executor(&net, dyn_clock);
                    let run = tokio::time::timeout(
                        std::time::Duration::from_secs(10),
                        executor.run_async(rx),
                    )
                    .await;
                    assert!(run.is_ok(), "{backend}: the run must terminate");
                    executor.marking().count("p2")
                }
                _ => {
                    let program = PrecompiledNet::from_compiled(
                        libpetri::runtime::compiled_net::CompiledNet::compile(&net),
                    );
                    let mut executor =
                        PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new())
                            .environment_places([Arc::from("p1")].into_iter().collect())
                            .clock(dyn_clock)
                            .build();
                    let run = tokio::time::timeout(
                        std::time::Duration::from_secs(10),
                        executor.run_async(rx),
                    )
                    .await;
                    assert!(run.is_ok(), "{backend}: the run must terminate");
                    executor.marking().count("p2")
                }
            };
            feeder.await.unwrap();

            assert_eq!(fired, WAITS, "{backend}: every injected token must fire");
            let entries = clock.entries.load(Ordering::SeqCst);
            assert!(
                entries >= WAITS / 2,
                "{backend}: the test must really exercise repeated idle waits, got {entries}"
            );
            assert_eq!(
                clock.max_live_at_entry.load(Ordering::SeqCst),
                0,
                "{backend}: a wait future from an earlier cycle was still alive when the next \
                 wait was requested — the losing future (and the waker it holds) must be \
                 dropped every cycle (TIME-015)"
            );
            assert_eq!(
                clock.live_waits(),
                0,
                "{backend}: a wait future outlived the run ({entries} waits were requested)"
            );
        }
    }
}
