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

/// How often a [`SteppedClock`] parked on the synchronous path re-checks
/// the readiness predicate. The predicate can turn true without the clock
/// moving, and nothing signals the condvar when it does.
const STEPPED_PARK_POLL_MS: u64 = 5;

/// A clock that only the host moves, and that tells the host when the
/// executor has stopped to wait for it.
///
/// [`ManualClock`] jumps to each boundary by itself, which suits a run that
/// should finish as fast as possible. `SteppedClock` never does: time moves
/// only when the host calls [`advance_ms`](Self::advance_ms). The executor
/// parks in its wait until then, and the host can ask whether it has parked
/// through the settle methods. That makes the host the scheduler. A test or
/// a replay driver can advance by a chosen step, wait for the net to settle
/// at the new instant, inspect it, and step again.
///
/// # How a wait behaves
///
/// Each [`now_ms`](ExecutorClock::now_ms) call records the reading, and the
/// next wait measures its interval from that reading. A wait whose boundary
/// is already due returns at once. Any other wait, including one with an
/// infinite interval, parks until the host advances the clock by any amount
/// (or, on the synchronous path, until the executor has work). It does not
/// wait for the advance to reach the boundary. The executor recomputes its
/// boundary on every cycle, so a short advance costs one cycle and the wait
/// parks again.
///
/// # Settling
///
/// [`settle_after`](Self::settle_after) runs a host action (an advance, an
/// inject), then waits until the executor parks again or the run is marked
/// finished. "Parked" means the **orchestrator** is waiting on this clock.
/// It says nothing about in-flight actions: on the async path the executor
/// also parks while an action runs, so a settle can return with work still
/// in flight. A host that needs the action's outputs settles again after
/// the action completes, or waits on the action itself.
///
/// # One clock per run
///
/// A run that ends does not park, so a settle waiting on it would only time
/// out. The host must call [`mark_finished`](Self::mark_finished) when the
/// executor's run method returns. The finished flag is sticky and the park
/// counter never resets, so create a new `SteppedClock` for each run rather
/// than reusing one.
#[derive(Debug)]
pub struct SteppedClock {
    state: Mutex<SteppedState>,
    /// Signalled by [`SteppedClock::advance_ms`]. The synchronous wait
    /// parks on it.
    advanced: Condvar,
    /// Signalled when the executor parks and when the run is marked
    /// finished. Synchronous settle waiters park on it.
    settled: Condvar,
    /// The async twin of `advanced`, awaited by `await_work_async`.
    #[cfg(feature = "tokio")]
    advanced_async: tokio::sync::Notify,
    /// The async twin of `settled`, awaited by `settled_after`.
    #[cfg(feature = "tokio")]
    settled_async: tokio::sync::Notify,
}

#[derive(Debug)]
struct SteppedState {
    now_ms: f64,
    epoch_origin_ms: u64,
    /// The value the last [`ExecutorClock::now_ms`] call returned. The
    /// executor reads the clock once per cycle and hands the wait an
    /// interval measured from that reading.
    last_read_ms: f64,
    /// Bumped by every advance. A wait ends when it changes.
    generation: u64,
    /// True while the executor is inside a wait on this clock.
    parked: bool,
    /// Bumped each time the executor parks. Settle compares it against a
    /// snapshot to tell a fresh park from one that predates the host action.
    park_count: u64,
    finished: bool,
}

impl SteppedState {
    /// True when the boundary `delay_ms` after the last reading has been
    /// reached. False for an infinite or NaN interval.
    fn is_due(&self, delay_ms: f64) -> bool {
        self.last_read_ms + delay_ms <= self.now_ms
    }
}

impl SteppedClock {
    /// A clock at firing time `0.0` and epoch time `0`.
    pub fn new() -> Self {
        Self::starting_at_epoch(0)
    }

    /// A clock at firing time `0.0` whose epoch readings start at
    /// `epoch_origin_ms` and advance with it.
    pub fn starting_at_epoch(epoch_origin_ms: u64) -> Self {
        Self {
            state: Mutex::new(SteppedState {
                now_ms: 0.0,
                epoch_origin_ms,
                last_read_ms: 0.0,
                generation: 0,
                parked: false,
                park_count: 0,
                finished: false,
            }),
            advanced: Condvar::new(),
            settled: Condvar::new(),
            #[cfg(feature = "tokio")]
            advanced_async: tokio::sync::Notify::new(),
            #[cfg(feature = "tokio")]
            settled_async: tokio::sync::Notify::new(),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, SteppedState> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Moves both time bases forward by `delta_ms` and wakes a parked wait.
    /// Zero, negative and NaN deltas are ignored: contract point 1 forbids
    /// going backwards, and a zero step would wake the executor for nothing.
    pub fn advance_ms(&self, delta_ms: f64) {
        if !(delta_ms > 0.0) {
            return;
        }
        let mut state = self.lock();
        state.now_ms += delta_ms;
        state.generation += 1;
        drop(state);
        self.advanced.notify_all();
        #[cfg(feature = "tokio")]
        self.advanced_async.notify_waiters();
    }

    /// The current firing-clock reading. Unlike
    /// [`ExecutorClock::now_ms`] this does not count as the executor's
    /// reading, so hosts should call this one.
    pub fn elapsed_ms(&self) -> f64 {
        self.lock().now_ms
    }

    /// True while the executor is parked in a wait on this clock.
    pub fn is_parked(&self) -> bool {
        self.lock().parked
    }

    /// How many times the executor has parked on this clock.
    pub fn park_count(&self) -> u64 {
        self.lock().park_count
    }

    /// True once [`mark_finished`](Self::mark_finished) has been called.
    pub fn is_finished(&self) -> bool {
        self.lock().finished
    }

    /// Records that the run has ended and releases every settle waiter.
    ///
    /// A run that ends does not park again, so without this a settle
    /// waiting on the final step would only time out. Call it when the
    /// executor's run method returns. The flag is sticky.
    pub fn mark_finished(&self) {
        let mut state = self.lock();
        state.finished = true;
        drop(state);
        self.notify_settled();
    }

    /// Waits until the executor is parked or the run is finished. Returns
    /// at once if either already holds, and returns `false` if `timeout`
    /// passes first (`None` waits indefinitely).
    ///
    /// A parked flag can be stale right after a host action: the executor
    /// may not yet have woken from the wait the action ended. Use
    /// [`settle_after`](Self::settle_after) to settle after an action, and
    /// this method only to wait for the first park of a run.
    pub fn settle(&self, timeout: Option<Duration>) -> bool {
        self.wait_settled(|s| s.parked || s.finished, timeout)
    }

    /// Runs `f`, then waits until the executor parks again or the run is
    /// finished. Returns `false` if `timeout` passes first (`None` waits
    /// indefinitely).
    ///
    /// "Again" means a park that began after `f` started, so a park that
    /// was already in place when `f` ran does not count. That is what
    /// makes the result trustworthy after an advance: the advance ends the
    /// current park, and only the next one reflects the new instant. If `f`
    /// does not wake the executor at all (it changes nothing the executor
    /// watches), no new park comes and this times out.
    ///
    /// `f` runs on the calling thread with no lock held, so it may call
    /// [`advance_ms`](Self::advance_ms) or inject into the executor.
    pub fn settle_after(&self, f: impl FnOnce(), timeout: Option<Duration>) -> bool {
        let before = self.park_count();
        f();
        self.settle_since(before, timeout)
    }

    /// Waits until the executor parks with a [`park_count`](Self::park_count)
    /// past `park_count`, or the run is finished. Returns `false` if
    /// `timeout` passes first (`None` waits indefinitely).
    ///
    /// This is [`settle_after`](Self::settle_after) split in two, for a host
    /// that cannot hand its action over as a closure: read `park_count()`,
    /// run the action, then call this with the reading.
    pub fn settle_since(&self, park_count: u64, timeout: Option<Duration>) -> bool {
        self.wait_settled(
            |s| s.finished || (s.parked && s.park_count > park_count),
            timeout,
        )
    }

    /// The async form of [`settle`](Self::settle), for a host on a tokio
    /// runtime. It suspends rather than blocking the thread.
    #[cfg(feature = "tokio")]
    pub async fn settled(&self, timeout: Option<Duration>) -> bool {
        self.wait_settled_async(|s| s.parked || s.finished, timeout).await
    }

    /// The async form of [`settle_after`](Self::settle_after). It suspends
    /// rather than blocking the thread, so a host may await it on the same
    /// single-threaded runtime that drives the executor.
    #[cfg(feature = "tokio")]
    pub async fn settled_after(&self, f: impl FnOnce(), timeout: Option<Duration>) -> bool {
        let before = self.park_count();
        f();
        self.settled_since(before, timeout).await
    }

    /// The async form of [`settle_since`](Self::settle_since).
    #[cfg(feature = "tokio")]
    pub async fn settled_since(&self, park_count: u64, timeout: Option<Duration>) -> bool {
        self.wait_settled_async(
            |s| s.finished || (s.parked && s.park_count > park_count),
            timeout,
        )
        .await
    }

    fn wait_settled(&self, done: impl Fn(&SteppedState) -> bool, timeout: Option<Duration>) -> bool {
        let deadline = timeout.map(|t| Instant::now() + t);
        let mut state = self.lock();
        loop {
            if done(&state) {
                return true;
            }
            state = match deadline {
                None => self.settled.wait(state).unwrap_or_else(|e| e.into_inner()),
                Some(deadline) => {
                    let now = Instant::now();
                    if now >= deadline {
                        return false;
                    }
                    self.settled
                        .wait_timeout(state, deadline - now)
                        .unwrap_or_else(|e| e.into_inner())
                        .0
                }
            };
        }
    }

    #[cfg(feature = "tokio")]
    async fn wait_settled_async(
        &self,
        done: impl Fn(&SteppedState) -> bool,
        timeout: Option<Duration>,
    ) -> bool {
        let wait = async {
            loop {
                let mut notified = std::pin::pin!(self.settled_async.notified());
                // Register before checking, so a park between the check and
                // the await still wakes this waiter.
                notified.as_mut().enable();
                let done_now = {
                    let state = self.lock();
                    done(&state)
                };
                if done_now {
                    return;
                }
                notified.await;
            }
        };
        match timeout {
            None => {
                wait.await;
                true
            }
            Some(timeout) => tokio::time::timeout(timeout, wait).await.is_ok(),
        }
    }

    /// Marks the executor parked and wakes settle waiters. Called with the
    /// state lock held, so a waiter cannot check between the two.
    fn park_locked(&self, state: &mut SteppedState) {
        state.parked = true;
        state.park_count += 1;
        self.notify_settled();
    }

    fn notify_settled(&self) {
        self.settled.notify_all();
        #[cfg(feature = "tokio")]
        self.settled_async.notify_waiters();
    }
}

impl Default for SteppedClock {
    fn default() -> Self {
        Self::new()
    }
}

/// Clears [`SteppedState::parked`] when an async wait completes or is
/// dropped. The executor's `select!` drops the losing wait routinely, and a
/// parked flag left behind would let a settle return while the executor is
/// busy.
#[cfg(feature = "tokio")]
struct SteppedParkGuard<'a>(&'a SteppedClock);

#[cfg(feature = "tokio")]
impl Drop for SteppedParkGuard<'_> {
    fn drop(&mut self) {
        self.0.lock().parked = false;
    }
}

impl ExecutorClock for SteppedClock {
    /// Returns the current reading and records it as the executor's last
    /// reading, the origin of the next wait's interval.
    fn now_ms(&self) -> f64 {
        let mut state = self.lock();
        state.last_read_ms = state.now_ms;
        state.now_ms
    }

    fn epoch_ms(&self) -> u64 {
        let state = self.lock();
        state.epoch_origin_ms + state.now_ms as u64
    }

    fn await_work(&self, ready: &dyn Fn() -> bool, delay_ms: f64) {
        if ready() {
            return;
        }
        let mut state = self.lock();
        if state.is_due(delay_ms) {
            return;
        }
        // Not due, or no boundary at all (contract point 2). Either way only
        // the host can move time, so park until it does. Any advance ends
        // the park, since the executor recomputes its boundary each cycle.
        let generation = state.generation;
        self.park_locked(&mut state);
        while state.generation == generation && !ready() {
            let (next, _) = self
                .advanced
                .wait_timeout(state, Duration::from_millis(STEPPED_PARK_POLL_MS))
                .unwrap_or_else(|e| e.into_inner());
            state = next;
        }
        state.parked = false;
    }

    /// Overridden so the async wait suspends on a [`tokio::sync::Notify`]
    /// rather than blocking a runtime worker in the synchronous wait.
    ///
    /// A due boundary yields once and completes. Any other wait is a future
    /// that parks until the next advance. The executor's own completion,
    /// flush and signal arms wake it for everything else, so no readiness
    /// predicate is needed here.
    ///
    /// The future registers for the advance notification before it checks
    /// whether an advance already happened, so an advance between this call
    /// and the first poll is not lost. If one did happen, the future yields
    /// once before completing. An advance that lands after the check but
    /// before the await completes the future on its first poll, which is
    /// the one way it does so; it is caused by a real advance and cannot
    /// repeat into a spin.
    #[cfg(feature = "tokio")]
    fn await_work_async(&self, delay_ms: f64) -> ClockWait<'_> {
        let generation = {
            let state = self.lock();
            if state.is_due(delay_ms) {
                return Box::pin(tokio::task::yield_now());
            }
            state.generation
        };
        Box::pin(async move {
            let mut notified = std::pin::pin!(self.advanced_async.notified());
            notified.as_mut().enable();
            let parked = {
                let mut state = self.lock();
                if state.generation == generation {
                    self.park_locked(&mut state);
                    true
                } else {
                    false
                }
            };
            if !parked {
                // Advanced since the call: the executor should recompute,
                // but not before the runtime gets a turn.
                tokio::task::yield_now().await;
                return;
            }
            let _guard = SteppedParkGuard(self);
            notified.await;
        })
    }
}

#[cfg(test)]
mod stepped_clock_tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::mpsc;

    const SETTLE: Option<Duration> = Some(Duration::from_secs(5));

    /// Parks `clock.await_work` on a thread, `waits` times in a row with no
    /// boundary, and reports each return on the channel.
    fn park_on_thread(clock: &Arc<SteppedClock>, waits: usize) -> mpsc::Receiver<()> {
        let (tx, rx) = mpsc::channel();
        let clock = Arc::clone(clock);
        std::thread::spawn(move || {
            for _ in 0..waits {
                clock.await_work(&|| false, f64::INFINITY);
                if tx.send(()).is_err() {
                    return;
                }
            }
        });
        rx
    }

    #[test]
    fn advance_wakes_a_sync_park() {
        let clock = Arc::new(SteppedClock::new());
        let returned = park_on_thread(&clock, 1);
        assert!(clock.settle(SETTLE), "the wait parks");
        assert!(clock.is_parked());
        assert!(
            returned.recv_timeout(Duration::from_millis(50)).is_err(),
            "an infinite interval suspends rather than returning (contract point 2)"
        );
        clock.advance_ms(1.0);
        returned.recv_timeout(Duration::from_secs(5)).expect("the advance ends the park");
        assert!(!clock.is_parked(), "leaving the wait clears parked");
        assert_eq!(clock.park_count(), 1);
    }

    #[test]
    fn any_advance_ends_a_finite_wait_before_its_boundary() {
        let clock = Arc::new(SteppedClock::new());
        assert_eq!(clock.now_ms(), 0.0);
        let (tx, rx) = mpsc::channel();
        let waiter = Arc::clone(&clock);
        std::thread::spawn(move || {
            waiter.await_work(&|| false, 100.0);
            tx.send(()).unwrap();
        });
        assert!(clock.settle(SETTLE));
        clock.advance_ms(30.0);
        rx.recv_timeout(Duration::from_secs(5))
            .expect("the wait returns on any advance so the executor recomputes");
        assert_eq!(clock.elapsed_ms(), 30.0, "the clock never jumps to the boundary itself");
    }

    #[test]
    fn due_boundary_returns_without_parking() {
        let clock = SteppedClock::new();
        assert_eq!(clock.now_ms(), 0.0);
        clock.advance_ms(10.0);
        clock.await_work(&|| false, 10.0);
        clock.await_work(&|| false, 0.0);
        clock.await_work(&|| false, -1.0);
        assert_eq!(clock.park_count(), 0, "a due boundary never parks");
    }

    #[test]
    fn interval_is_measured_from_the_last_reading() {
        let clock = SteppedClock::new();
        clock.advance_ms(10.0);
        // The executor has not read the clock since the advance, so a
        // 10 ms boundary measured from the reading at 0 is due.
        clock.await_work(&|| false, 10.0);
        assert_eq!(clock.park_count(), 0);
        assert_eq!(clock.now_ms(), 10.0);
        assert!(!clock.lock().is_due(10.0), "measured from the reading at 10, it is not");
    }

    #[test]
    fn readiness_releases_a_sync_park() {
        let clock = Arc::new(SteppedClock::new());
        let ready = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel();
        {
            let clock = Arc::clone(&clock);
            let ready = Arc::clone(&ready);
            std::thread::spawn(move || {
                clock.await_work(&|| ready.load(Ordering::SeqCst), f64::INFINITY);
                tx.send(()).unwrap();
            });
        }
        assert!(clock.settle(SETTLE));
        ready.store(true, Ordering::SeqCst);
        rx.recv_timeout(Duration::from_secs(5)).expect("the poll observes readiness");
        assert_eq!(clock.elapsed_ms(), 0.0, "readiness does not move time");
        assert!(!clock.is_parked());
    }

    #[test]
    fn advance_ignores_non_positive_and_nan_deltas() {
        let clock = SteppedClock::starting_at_epoch(1_000);
        clock.advance_ms(0.0);
        clock.advance_ms(-5.0);
        clock.advance_ms(f64::NAN);
        assert_eq!(clock.elapsed_ms(), 0.0);
        assert_eq!(clock.lock().generation, 0, "an ignored delta wakes nobody");
        clock.advance_ms(2_500.0);
        assert_eq!(clock.elapsed_ms(), 2_500.0);
        assert_eq!(clock.epoch_ms(), 3_500, "epoch time advances with firing time");
    }

    #[test]
    fn settle_times_out_when_nothing_parks() {
        let clock = SteppedClock::new();
        assert!(!clock.settle(Some(Duration::from_millis(20))));
        assert!(!clock.settle_after(|| clock.advance_ms(5.0), Some(Duration::from_millis(20))));
    }

    #[test]
    fn mark_finished_releases_a_settle_waiter() {
        let clock = Arc::new(SteppedClock::new());
        let (tx, rx) = mpsc::channel();
        {
            let clock = Arc::clone(&clock);
            std::thread::spawn(move || {
                tx.send(clock.settle(None)).unwrap();
            });
        }
        assert!(rx.recv_timeout(Duration::from_millis(50)).is_err(), "nothing has parked yet");
        clock.mark_finished();
        assert!(rx.recv_timeout(Duration::from_secs(5)).expect("released"));
        assert!(clock.settle_after(|| clock.advance_ms(1.0), Some(Duration::from_millis(1))));
    }

    #[test]
    fn settle_is_immediate_when_already_parked() {
        let clock = Arc::new(SteppedClock::new());
        let _returned = park_on_thread(&clock, 1);
        assert!(clock.settle(SETTLE));
        assert!(clock.settle(Some(Duration::ZERO)), "an existing park satisfies settle");
        clock.advance_ms(1.0);
    }

    #[test]
    fn settle_after_waits_for_a_new_park() {
        let clock = Arc::new(SteppedClock::new());
        let returned = park_on_thread(&clock, 2);
        assert!(clock.settle(SETTLE));
        assert!(
            !clock.settle_after(|| {}, Some(Duration::from_millis(30))),
            "the park in place before the action does not count"
        );
        assert!(clock.settle_after(|| clock.advance_ms(1.0), SETTLE), "the advance unparks, the next wait reparks");
        assert_eq!(clock.park_count(), 2);
        returned.recv_timeout(Duration::from_secs(5)).unwrap();
        clock.advance_ms(1.0);
        returned.recv_timeout(Duration::from_secs(5)).unwrap();
        assert!(!clock.is_parked());
    }

    #[cfg(feature = "tokio")]
    mod async_wait {
        use super::*;
        use std::task::{Context, Poll, Waker};

        fn poll(fut: &mut ClockWait<'_>) -> Poll<()> {
            fut.as_mut().poll(&mut Context::from_waker(Waker::noop()))
        }

        #[test]
        fn pending_until_advance() {
            let clock = SteppedClock::new();
            clock.now_ms();
            for delay in [100.0, f64::INFINITY] {
                let mut wait = clock.await_work_async(delay);
                assert!(poll(&mut wait).is_pending(), "delay {delay}: first poll suspends");
                assert!(poll(&mut wait).is_pending(), "delay {delay}: no advance, still suspended");
                assert!(clock.is_parked());
                clock.advance_ms(1.0);
                assert!(poll(&mut wait).is_ready(), "delay {delay}: the advance completes it");
                assert!(!clock.is_parked(), "completing clears parked");
            }
            assert_eq!(clock.park_count(), 2);
        }

        #[test]
        fn dropped_wait_clears_parked() {
            let clock = SteppedClock::new();
            let mut wait = clock.await_work_async(f64::INFINITY);
            assert!(poll(&mut wait).is_pending());
            assert!(clock.is_parked());
            drop(wait);
            assert!(!clock.is_parked(), "a wait the select! drops does not stay parked");
        }

        #[test]
        fn advance_before_first_poll_is_not_lost() {
            let clock = SteppedClock::new();
            let mut wait = clock.await_work_async(f64::INFINITY);
            clock.advance_ms(1.0);
            assert!(poll(&mut wait).is_pending(), "never complete on the first poll");
            assert!(poll(&mut wait).is_ready(), "the earlier advance is seen");
            assert_eq!(clock.park_count(), 0, "it never parked");
        }

        #[test]
        fn due_boundary_yields_once() {
            let clock = SteppedClock::new();
            clock.now_ms();
            let mut wait = clock.await_work_async(0.0);
            assert!(poll(&mut wait).is_pending(), "never complete on the first poll");
            assert!(poll(&mut wait).is_ready());
            assert_eq!(clock.park_count(), 0);
        }

        #[tokio::test]
        async fn settled_after_sees_the_repark() {
            let clock = Arc::new(SteppedClock::new());
            let parker = {
                let clock = Arc::clone(&clock);
                tokio::spawn(async move {
                    clock.await_work_async(f64::INFINITY).await;
                    clock.await_work_async(f64::INFINITY).await;
                })
            };
            assert!(clock.settled(SETTLE).await);
            assert!(
                !clock.settled_after(|| {}, Some(Duration::from_millis(30))).await,
                "the park in place before the action does not count"
            );
            assert!(clock.settled_after(|| clock.advance_ms(1.0), SETTLE).await);
            assert_eq!(clock.park_count(), 2);
            clock.advance_ms(1.0);
            parker.await.unwrap();
            assert!(!clock.is_parked());
            assert!(!clock.settled(Some(Duration::from_millis(20))).await, "times out");
            clock.mark_finished();
            assert!(clock.settled(Some(Duration::ZERO)).await);
        }
    }
}
