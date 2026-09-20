//! \[TIME-015\] The per-executor injectable clock seam.
//!
//! An executor reads time from **two** unrelated sources and this module
//! names both, because a single injected `now` cannot serve them:
//!
//! - the **firing clock** — monotonic milliseconds since the executor
//!   started, from which enablement stamps (\[TIME-010\]), elapsed-time
//!   decisions (\[TIME-004\], \[TIME-005\], \[TIME-006\]), deadline
//!   enforcement (\[TIME-013\]) and the wake-up interval are computed;
//! - the **epoch clock** — wall-clock milliseconds since the Unix epoch,
//!   stamping token creation times (\[CORE-011\]) and event timestamps.
//!
//! The seam is **per executor**, never per net: a [`PetriNet`] is immutable
//! and shared across composition (\[MOD-010\]), so a clock attached to one
//! would have to be merged at every compose, and two executors in one
//! process — one on virtual time, one live — need independent clocks.
//!
//! # Reading time is not enough
//!
//! A seam that only supplies `now` leaves the executor sleeping on the real
//! timer: the stamps go virtual while the waiting stays real, and a
//! `delayed(1000)` still costs a real second. [`ExecutorClock`] therefore
//! also owns the executor's wait for the next timing boundary
//! (\[EXEC-001\] step 6).
//!
//! # What the executor guarantees you
//!
//! - **The wake-up half is not yours to carry.** On the async path the wait
//!   is a `tokio::select!` over the completion, flush and signal channels
//!   *raced against* [`ExecutorClock::await_work_async`]. A completing
//!   action, an injected event (\[ENV-005\]) or a close (\[ENV-013\]) wins
//!   that race whatever the clock does, so a clock cannot make the executor
//!   *miss* a wake-up. libpetri does **not** silence its internal wake-up
//!   under an injected clock, so the cross-thread visibility precondition
//!   that delegating to a readiness predicate would impose does not arise.
//!
//!   That guarantee is about the race, and **not** a guarantee that any
//!   clock is safe: a wait that returns immediately instead of suspending
//!   wins its own race every time, and the loop becomes a spin that on a
//!   single-threaded runtime starves the very work it is waiting for. See
//!   contract point 2 — an infinite interval is not a boundary, and the
//!   wait must suspend.
//! - **Your wait may be abandoned.** `select!` drops the losing future, so
//!   `await_work_async` is cancelled mid-poll routinely, including during
//!   shutdown. Cancellation is the abort path and it completes rather than
//!   failing.
//! - **Injection from inside your wait is legal** (\[ENV-003\]).
//!   `ExecutorHandle::inject` only enqueues on an unbounded channel; the
//!   tokens are admitted in the executor's own external-events phase on a
//!   following cycle, never at the point of injection.
//!
//! # Scope limit: action timeouts are not virtualized
//!
//! `timeout(after, recovery)` on an output spec (\[IO-013\]) *is* net-declared
//! timing, but it is enforced by a **per-action** wait, and this seam owns
//! only the executor's single orchestrator wait. So under an injected clock:
//!
//! - the recovery tokens **are** stamped from your [`epoch_ms`] (\[TIME-015\]
//!   AC#13), like every other token the executor produces;
//! - the `after` interval **still elapses in real time**.
//!
//! A net declaring `timeout(…)` is therefore **not fully virtualizable**: a
//! host replaying one waits the real interval, and a `timeout(3_600_000, …)`
//! costs a real hour however virtual the clock. If you need a replay to be
//! instant, that net cannot carry an action timeout.
//!
//! This is a known boundary rather than an oversight. Bringing action
//! timeouts under the seam needs the clock to mediate *every in-flight
//! action's* wait, not one orchestrator wait. And the half-measure is worse
//! than the limit: routing the interval through the injected clock while the
//! action's own wait stayed real would fire the recovery branch at a virtual
//! instant the action never reached, producing a recovery for work that is
//! still running.
//!
//! # What you must guarantee
//!
//! See [`ExecutorClock`]'s contract section. The short version: never go
//! backwards, never require that you went forwards, and either suspend
//! until the boundary or advance to it.
//!
//! [`epoch_ms`]: ExecutorClock::epoch_ms

use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use libpetri_core::token::Token;

/// The future returned by [`ExecutorClock::await_work_async`]. Boxed
/// because the trait is used as `dyn ExecutorClock`; the default (no clock
/// installed) path never constructs one.
pub type ClockWait<'a> = Pin<Box<dyn Future<Output = ()> + Send + 'a>>;

/// A host-supplied time source for one executor (\[TIME-015\]).
///
/// Install with
/// [`ExecutorOptions::clock`](crate::executor::ExecutorOptions::clock) or
/// [`Executor::set_clock`](crate::executor_core::executor::Executor::set_clock).
/// With no clock installed the executor reads [`Instant`] / [`SystemTime`]
/// directly, exactly as it did before this seam existed.
///
/// # Contract
///
/// None of these is checked, and each is silent when violated.
///
/// 1. **Non-decreasing, and not assumed strictly increasing.** [`now_ms`]
///    MUST NOT go backwards — elapsed time is a difference from an
///    enablement stamp, so a backwards step yields a negative elapsed
///    value, re-opens the earliest bound of an already-due transition and
///    can stall the net with no error. The executor for its part does not
///    assume your clock *advances* between two reads: a clock derived from
///    millisecond wall time or a replay log returns the same value across
///    many cycles, and that is normal.
/// 2. **Suspend or advance — and where there is no boundary, suspend.**
///    Given a *finite* interval [`await_work`] MUST either suspend until
///    that boundary or advance the clock to it; a clock that advances only
///    on demand, paired with a wait that does neither, spins forever.
///
///    **An infinite interval is not a boundary, and neither of those
///    applies to it.** The executor passes [`f64::INFINITY`] whenever
///    nothing timed is pending — which is *most of the time*: the
///    orchestrator is parked on an in-flight action, or waiting on external
///    events. There is no instant to advance to, so the wait MUST **suspend
///    until woken**. Returning is non-conforming: the executor re-enters at
///    once and the loop becomes a spin. On a single-threaded runtime that
///    spin starves the very work the wait exists for, so the net does not
///    merely burn a core — it stops making progress, and **no enclosing
///    timeout can rescue it, because nothing yields**. Test your clock
///    against `f64::INFINITY` explicitly; it is the case a first reading of
///    this contract is least likely to survive.
/// 3. **Spurious completion permitted — but not as a steady state.**
///    [`await_work`] MAY return early and for no reason: the executor
///    re-checks its boundary conditions every cycle and never treats "the
///    wait returned" as "the boundary is reached", so *an occasional*
///    spurious return costs a cycle and nothing else.
///
///    This permission is not a licence to return always. A wait that
///    returns on every call is not spuriously completing, it is not
///    waiting — and it is indistinguishable from the spin described in
///    point 2. The two read as compatible and are not: point 2 governs.
/// 4. **Abort completes, not fails.** The wait is dropped or returns
///    normally on shutdown; it must not panic there. Shutdown is precisely
///    where a failing wait escapes unobserved.
/// 5. **A readiness signal is time-free.** The `ready` predicate handed to
///    [`await_work`] is cheap, repeatable and side-effect free, and your
///    implementation MUST NOT consult a clock to decide whether to keep
///    waiting — that reintroduces the real clock behind the seam.
///
/// [`now_ms`]: ExecutorClock::now_ms
/// [`await_work`]: ExecutorClock::await_work
pub trait ExecutorClock: Send + Sync + fmt::Debug {
    /// **Firing clock.** Monotonically non-decreasing milliseconds since
    /// this executor started. The origin is arbitrary but must be stable
    /// for the executor's lifetime — only differences are meaningful.
    fn now_ms(&self) -> f64;

    /// **Epoch clock.** Wall-clock milliseconds since the Unix epoch, used
    /// for token `created_at` (\[CORE-011\]) and event timestamps. Unrelated
    /// to [`now_ms`](Self::now_ms)'s origin; a host that needs the two to
    /// agree across a replay should derive both from one logical source.
    fn epoch_ms(&self) -> u64;

    /// Owns the executor's synchronous wait for the next timing boundary.
    ///
    /// `delay_ms` is the firing-clock interval until that boundary, or
    /// [`f64::INFINITY`] when there is none. `ready` reports whether the
    /// executor already has work to do; it is cheap, repeatable and
    /// side-effect free, and consults no clock.
    ///
    /// Return when `ready()` is true, when `delay_ms` has elapsed on this
    /// clock, or spuriously. `delay_ms <= 0.0` means the boundary is
    /// already due: return without waiting so the next cycle acts on it.
    ///
    /// **`delay_ms == f64::INFINITY` means there is no boundary — suspend
    /// until woken rather than returning.** Returning here turns the
    /// executor's loop into a spin (contract point 2).
    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64);

    /// Owns the executor's asynchronous wait for the next timing boundary.
    ///
    /// The returned future is **raced** against the executor's completion,
    /// flush and signal channels, so it is routinely dropped before
    /// completing — that is the abort path and it must be cancel-safe.
    ///
    /// Two things this future MUST NOT do, both of which defeat suspension
    /// as surely as returning early does:
    ///
    /// - **complete synchronously on first poll** — the runtime never gets
    ///   a turn, and on a single-threaded runtime the orchestrator starves
    ///   the action it is waiting for;
    /// - **block the calling thread** — that parks a worker the runtime
    ///   needs for that same action.
    ///
    /// As on the synchronous path, `f64::INFINITY` means there is no
    /// boundary: return a future that stays `Pending` and let the
    /// executor's own wake-up arms win the race.
    ///
    /// # The default
    ///
    /// Safe for any clock that implements only the three required methods:
    ///
    /// - on an absent boundary it returns a future that stays `Pending`, and
    ///   never enters [`await_work`](Self::await_work) — the synchronous
    ///   wait's `ready` has nothing to observe here, so a conforming clock
    ///   handed `f64::INFINITY` would park the polling worker for good and
    ///   the executor's inject / snapshot / close arms would never run again;
    /// - on a finite one it yields `Pending` **once**, so the executor's
    ///   other arms get their turn first, and only then runs
    ///   [`await_work`](Self::await_work) with a `ready` that is always
    ///   false.
    ///
    /// That second step is exact for a clock that *advances* to the
    /// boundary. A clock that really sleeps still blocks a runtime worker
    /// for the finite interval — the default cannot know better — so **a
    /// clock that suspends in real time SHOULD override this** with a
    /// runtime-native sleep, as [`SystemClock`] does.
    fn await_work_async(&self, delay_ms: f64) -> ClockWait<'_> {
        if !delay_ms.is_finite() {
            return Box::pin(std::future::pending());
        }
        Box::pin(async move {
            YieldOnce(false).await;
            self.await_work(&|| false, delay_ms)
        })
    }
}

/// `Pending` exactly once, then `Ready` — a runtime-agnostic
/// `yield_now`, so [`ExecutorClock::await_work_async`]'s default needs no
/// `tokio` gate and the trait keeps one shape under every feature set.
struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<()> {
        if self.0 {
            return std::task::Poll::Ready(());
        }
        self.0 = true;
        cx.waker().wake_by_ref();
        std::task::Poll::Pending
    }
}

/// Stamps a **fresh** token through `clock`'s epoch source (\[TIME-015\],
/// AC#12).
///
/// An initial marking (\[CORE-072\]) is built before any executor exists, so
/// no seam reaches it: [`Token::new`] stamps wall-clock time and therefore
/// differs per replay attempt *inside the marking*. Seed through this
/// instead and two replays on the same host clock produce identical
/// timestamps.
///
/// This deliberately does not re-stamp tokens you already hold — that would
/// defeat [`CORE-073`] restore, which preserves `created_at` on purpose. For
/// those, use [`Token::at`] with the timestamp you want to keep.
///
/// [`CORE-073`]: crate::marking::Marking
pub fn seed_token<T: Send + Sync + 'static>(clock: &dyn ExecutorClock, value: T) -> Token<T> {
    Token::at(value, clock.epoch_ms())
}

/// The wall-clock reference implementation of [`ExecutorClock`].
///
/// Reads the same sources the executor reads with no clock installed, so it
/// is useful as a base to delegate to. One difference worth knowing:
/// `run_sync` with **no** clock spins between timed boundaries, whereas
/// under `SystemClock` it genuinely sleeps. That is a strict improvement,
/// not the byte-identical default — which is why the default is *no clock*
/// rather than this one.
#[derive(Debug)]
pub struct SystemClock {
    start: Instant,
}

impl SystemClock {
    /// Starts a wall clock whose firing origin is now.
    pub fn new() -> Self {
        Self {
            start: Instant::now(),
        }
    }
}

impl Default for SystemClock {
    fn default() -> Self {
        Self::new()
    }
}

impl ExecutorClock for SystemClock {
    fn now_ms(&self) -> f64 {
        self.start.elapsed().as_secs_f64() * 1000.0
    }

    fn epoch_ms(&self) -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64
    }

    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
        if ready() || !(delay_ms > 0.0) {
            return;
        }
        let capped = if delay_ms.is_finite() { delay_ms } else { 60_000.0 };
        std::thread::sleep(Duration::from_secs_f64(capped / 1000.0));
    }

    #[cfg(feature = "tokio")]
    fn await_work_async(&self, delay_ms: f64) -> ClockWait<'_> {
        let capped = if delay_ms.is_finite() {
            delay_ms.max(0.0) as u64
        } else {
            60_000
        };
        Box::pin(tokio::time::sleep(Duration::from_millis(capped)))
    }
}

/// Smallest virtual step [`ManualClock`] will take when asked to advance to
/// a boundary, so a backend that ever reports a `0.0` interval cannot stall
/// a virtual run. Matches the floor the executor's previous test-only
/// virtual clock applied.
const MANUAL_MIN_STEP_MS: f64 = 0.5;

/// How often a [`ManualClock`] parked on an *absent* boundary re-checks the
/// readiness predicate. Only the synchronous path parks — the asynchronous
/// one suspends as a `Pending` future and needs no poll at all.
const MANUAL_PARK_POLL_MS: u64 = 5;

/// A host-driven clock that never consults the operating system.
///
/// Both time bases advance together, which is what \[TIME-015\] recommends
/// for a host that needs firing time and epoch time to agree across a
/// replay. Time moves in exactly two ways:
///
/// - the host calls [`advance_ms`](Self::advance_ms);
/// - the executor's wait reaches a timing boundary, and the clock jumps
///   straight to it (contract point 2's "advance" option).
///
/// Everything else is frozen, so a net full of `delayed`, `window` and
/// `deadline` transitions runs to quiescence in negligible real time and
/// bit-for-bit reproducibly.
#[derive(Debug)]
pub struct ManualClock {
    state: Mutex<ManualState>,
    /// Signalled by [`ManualClock::advance_ms`] so a wait parked on an
    /// *absent* boundary can be woken by the host rather than polling.
    woken: Condvar,
}

#[derive(Debug)]
struct ManualState {
    now_ms: f64,
    epoch_origin_ms: u64,
}

impl ManualClock {
    /// A clock at firing time `0.0` and epoch time `0`.
    pub fn new() -> Self {
        Self::starting_at_epoch(0)
    }

    /// A clock at firing time `0.0` whose epoch readings start at
    /// `epoch_origin_ms` and advance with it.
    pub fn starting_at_epoch(epoch_origin_ms: u64) -> Self {
        Self {
            state: Mutex::new(ManualState {
                now_ms: 0.0,
                epoch_origin_ms,
            }),
            woken: Condvar::new(),
        }
    }

    /// Moves both time bases forward by `delta_ms`. Negative deltas are
    /// ignored — contract point 1 forbids going backwards.
    pub fn advance_ms(&self, delta_ms: f64) {
        if !(delta_ms > 0.0) {
            return;
        }
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        state.now_ms += delta_ms;
        drop(state);
        self.woken.notify_all();
    }

    /// The current firing-clock reading.
    pub fn elapsed_ms(&self) -> f64 {
        self.state
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .now_ms
    }
}

impl Default for ManualClock {
    fn default() -> Self {
        Self::new()
    }
}

impl ExecutorClock for ManualClock {
    fn now_ms(&self) -> f64 {
        self.elapsed_ms()
    }

    fn epoch_ms(&self) -> u64 {
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        state.epoch_origin_ms + state.now_ms as u64
    }

    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
        if ready() {
            return;
        }
        if delay_ms.is_finite() {
            // A boundary exists. `delay_ms <= 0` means it is already due:
            // return so the next cycle acts on it (the short-circuit).
            if delay_ms > 0.0 {
                self.advance_ms(delay_ms.max(MANUAL_MIN_STEP_MS));
            }
            return;
        }

        // No boundary at all, so neither "advance to it" nor "suspend until
        // it" has an instant to name — and returning here is what makes the
        // loop a spin (TIME-015 contract point 2, AC#15). Park instead,
        // waking on `advance_ms` or on the readiness predicate. The timeout
        // is what makes `ready()` observable at all: it can become true
        // without the clock moving, and nothing else signals this condvar.
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        while !ready() {
            let (next, _) = self
                .woken
                .wait_timeout(guard, Duration::from_millis(MANUAL_PARK_POLL_MS))
                .unwrap_or_else(|e| e.into_inner());
            guard = next;
        }
    }

    /// Overridden rather than inherited, deliberately.
    ///
    /// The inherited default would be correct here — it suspends on an
    /// absent boundary and yields once before a finite one — but it reaches
    /// the boundary through the synchronous [`await_work`](ExecutorClock::await_work),
    /// lock and readiness check included. This advances directly and yields
    /// through the runtime. On the async path the suspension is a `Pending`
    /// future the executor's own wake-up arms race against, which costs no
    /// thread.
    #[cfg(feature = "tokio")]
    fn await_work_async(&self, delay_ms: f64) -> ClockWait<'_> {
        if !delay_ms.is_finite() {
            // Suspend. The completion / flush / signal arms of the
            // executor's `select!` are the wake-up.
            return Box::pin(std::future::pending());
        }
        if delay_ms > 0.0 {
            self.advance_ms(delay_ms.max(MANUAL_MIN_STEP_MS));
        }
        // Yield rather than completing on first poll: an async wait that
        // never returns `Pending` gives the runtime no turn, and on a
        // single-threaded runtime the orchestrator starves the action it is
        // waiting for.
        Box::pin(tokio::task::yield_now())
    }
}
