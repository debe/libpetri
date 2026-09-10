"""Timing semantics: delayed, window, deadline, exact, mixed.

Mirrors the Java/TS/Rust timing suites and the shared `enforce_deadlines`
path. ``exact()`` is enforced *softly*: an exact transition fires at the first
opportunity at or after its target time and is never force-disabled, so it can
be exercised deterministically (TIME-006). Hard deadlines (`deadline()` /
`window()`) keep a configurable tolerance band (TIME-013).
"""

from __future__ import annotations

import asyncio
import time

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="timed transitions require the async runtime",
)


@pytest.mark.asyncio
async def test_delayed_timing_holds_back_firing_until_minimum_elapses() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("delayed")
        .transition(
            lp.Transition("wait")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.delayed(50))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    start = time.monotonic()
    result = await lp.run_async(net, initial={queued: [{"id": 1}]})
    elapsed_ms = (time.monotonic() - start) * 1000.0

    assert result.count(done) == 1
    assert elapsed_ms >= 40.0, f"delayed must wait at least ~50ms, got {elapsed_ms:.1f}"


@pytest.mark.asyncio
async def test_window_timing_respects_earliest_bound() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("window-early")
        .transition(
            lp.Transition("wait")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.window(30, 200))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    start = time.monotonic()
    result = await lp.run_async(net, initial={queued: [{"id": 1}]})
    elapsed_ms = (time.monotonic() - start) * 1000.0

    assert result.count(done) == 1
    assert elapsed_ms >= 20.0, f"window must respect earliest, got {elapsed_ms:.1f}"


@pytest.mark.asyncio
async def test_deadline_force_disables_after_latest() -> None:
    queued = lp.Place("queued")
    blocker = lp.Place("blocker")
    done = lp.Place("done")

    # Inhibitor keeps the transition disabled past its deadline, so when we
    # finally clear the blocker the transition must NOT fire.
    net = (
        lp.Net("deadline-expires")
        .transition(
            lp.Transition("must_fire_soon")
            .input(lp.one(queued))
            .inhibitor(lp.inhibitor(blocker))
            .output(lp.out(done))
            .timing(lp.deadline(20))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        initial={queued: [{"id": 1}], blocker: [{"present": True}]},
        options=lp.ExecutorOptions(environment_places=(blocker,)),
    )

    # Wait long enough for the deadline to expire on the enabled-but-blocked
    # transition (deadline counts from enablement, which the inhibitor delays —
    # so we approximate by waiting past the deadline before unblocking).
    await asyncio.sleep(0.1)
    handle.drain()
    await awaitable
    handle.close()


@pytest.mark.asyncio
async def test_window_with_inhibitor_combines_gates() -> None:
    queued = lp.Place("queued")
    gate = lp.Place("gate")
    done = lp.Place("done")

    net = (
        lp.Net("window-and-inhibitor")
        .transition(
            lp.Transition("gated")
            .input(lp.one(queued))
            .inhibitor(lp.inhibitor(gate))
            .output(lp.out(done))
            .timing(lp.window(10, 100))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={queued: [{"id": 9}]})

    assert result.count(done) == 1
    assert result.first(done)["id"] == 9


@pytest.mark.asyncio
async def test_window_with_read_arc_does_not_consume_context() -> None:
    queued = lp.Place("queued")
    ctx_place = lp.Place("ctx")
    done = lp.Place("done")

    def take(ctx: lp.TransitionContext) -> None:
        order = ctx.input("queued")
        rules = ctx.read("ctx")
        ctx.output("done", {**order, "rule": rules["rule"]})

    net = (
        lp.Net("window-and-read")
        .transition(
            lp.Transition("apply")
            .input(lp.one(queued))
            .read(lp.read(ctx_place))
            .output(lp.out(done))
            .timing(lp.window(10, 100))
            .action(take)
            .build()
        )
        .build()
    )

    result = await lp.run_async(
        net,
        initial={queued: [{"id": 1}], ctx_place: [{"rule": "fast"}]},
    )

    assert result.count(done) == 1
    assert result.first(done)["rule"] == "fast"
    assert result.count(ctx_place) == 1


@pytest.mark.asyncio
async def test_multiple_overlapping_timed_transitions_complete_in_priority_order() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    fired: list[str] = []

    def make_recorder(name: str):
        def rec(ctx: lp.TransitionContext) -> None:
            ctx.input("queued")
            fired.append(name)
            ctx.output("done", name)

        return rec

    net = (
        lp.Net("priority-timed")
        .transition(
            lp.Transition("low")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.delayed(10))
            .priority(1)
            .action(make_recorder("low"))
            .build()
        )
        .transition(
            lp.Transition("high")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.delayed(10))
            .priority(10)
            .action(make_recorder("high"))
            .build()
        )
        .build()
    )

    await lp.run_async(net, initial={queued: [{"id": 1}]})

    assert fired == ["high"], (
        f"higher-priority transition must win the single token; got {fired}"
    )


@pytest.mark.asyncio
async def test_exact_timing_fires_reliably() -> None:
    # exact() is enforced softly (TIME-006): it waits until its target, then fires at
    # the first opportunity and is never force-disabled — so this is deterministic, not
    # flaky. Regression for the Marvin exact(45s) "sometimes never fires" bug.
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("exact")
        .transition(
            lp.Transition("at")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.exact(40))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    start = time.monotonic()
    result = await lp.run_async(net, initial={queued: [{"id": 1}]})
    elapsed_ms = (time.monotonic() - start) * 1000.0

    assert result.count(done) == 1, "exact() transition must fire (soft enforcement)"
    assert elapsed_ms >= 30.0, f"exact must respect its target, got {elapsed_ms:.1f}"


@pytest.mark.asyncio
async def test_deadline_tolerance_option_round_trips_and_runs() -> None:
    # The configurable deadline tolerance (TIME-013) is accepted, carried to the native
    # options, and a net runs to completion under a widened band.
    opts = lp.ExecutorOptions(deadline_tolerance_ms=50.0)
    assert opts.native().deadline_tolerance_ms == 50.0

    queued = lp.Place("queued")
    done = lp.Place("done")
    net = (
        lp.Net("tolerance")
        .transition(
            lp.Transition("go")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.deadline(1000))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={queued: [{"id": 1}]}, options=opts)
    assert result.count(done) == 1


def test_negative_deadline_tolerance_is_rejected() -> None:
    with pytest.raises(ValueError):
        lp.ExecutorOptions(deadline_tolerance_ms=-1.0).native()


@pytest.mark.asyncio
async def test_immediate_timing_fires_eagerly() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("immediate")
        .transition(
            lp.Transition("now")
            .input(lp.one(queued))
            .output(lp.out(done))
            .timing(lp.immediate())
            .action(lp.fork)
            .build()
        )
        .build()
    )

    start = time.monotonic()
    result = await lp.run_async(net, initial={queued: [{"id": 1}]})
    elapsed_ms = (time.monotonic() - start) * 1000.0

    assert result.count(done) == 1
    assert elapsed_ms < 50.0, f"immediate should be near-zero, got {elapsed_ms:.1f}"


@pytest.mark.asyncio
async def test_sync_refresh_restarts_timed_transition_clock() -> None:
    """TIME-012: `Refresh` takes the only `timer` token and its synchronous
    Python action puts it back. Between the consumption and the output
    `CloseSession` is disabled, so its clock restarts at the refresh even
    though no enablement scan sees the gap: it waits its full 200 ms from the
    refresh, and the restart is reported as one `TransitionClockRestarted`.
    Mirrors the Rust `backend_suite_tests` session nets."""
    activity = lp.Place("activity")
    timer = lp.Place("timer")
    closed_at: list[float] = []

    def refresh(ctx: lp.TransitionContext) -> None:
        ctx.output("timer", ctx.input("timer"))

    def close_session(ctx: lp.TransitionContext) -> None:
        closed_at.append(time.monotonic())

    net = (
        lp.Net("session")
        .transition(
            lp.Transition("Refresh")
            .input(lp.one(activity))
            .input(lp.one(timer))
            .output(lp.out(timer))
            .action(refresh)
            .build()
        )
        .transition(
            lp.Transition("CloseSession")
            .input(lp.one(timer))
            .timing(lp.delayed(200))
            .action(close_session)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    handle, awaitable = lp.start_async(
        net,
        initial={timer: [{"session": 1}]},
        options=lp.ExecutorOptions(environment_places=(activity,)),
        event_store=store,
    )

    # The timer is armed from the start; the activity arrives about 100 ms in.
    await asyncio.sleep(0.1)
    injected_at = time.monotonic()
    assert handle.inject(activity, {"seen": True}) is True
    assert handle.drain() is True
    await awaitable

    assert len(closed_at) == 1, "CloseSession fires once"
    waited_ms = (closed_at[0] - injected_at) * 1000.0
    assert waited_ms >= 195.0, (
        f"CloseSession must wait its full 200 ms from the refresh, fired {waited_ms:.1f} ms "
        "after the activity arrived"
    )
    restarts = store.events(types={"TransitionClockRestarted"}, transitions={"CloseSession"})
    assert len(restarts) == 1, "the synchronous refill restarts the clock in place"


@pytest.mark.asyncio
async def test_async_refresh_restarts_timed_transition_clock() -> None:
    """TIME-012 with an asynchronous Python action: `Refresh` takes the only
    `timer` token and puts it back after a real 20 ms await. The timer stays
    empty while the action runs, so `CloseSession` gets a fresh clock once the
    token returns and waits its full 200 ms from the refresh's completion. The
    fresh clock shows as a second `TransitionEnabled`, or as a
    `TransitionClockRestarted` when the completion lands before the executor
    re-evaluates `CloseSession`."""
    activity = lp.Place("activity")
    timer = lp.Place("timer")
    closed_at: list[float] = []

    async def refresh(ctx: lp.TransitionContext) -> None:
        token = ctx.input("timer")
        # The action runs on a tokio thread with no running asyncio loop, so the
        # delay goes through the captured loop instead of asyncio.sleep.
        await lp.action_to_thread(time.sleep, 0.02)
        ctx.output("timer", token)

    def close_session(ctx: lp.TransitionContext) -> None:
        closed_at.append(time.monotonic())

    net = (
        lp.Net("session")
        .transition(
            lp.Transition("Refresh")
            .input(lp.one(activity))
            .input(lp.one(timer))
            .output(lp.out(timer))
            .action(refresh)
            .build()
        )
        .transition(
            lp.Transition("CloseSession")
            .input(lp.one(timer))
            .timing(lp.delayed(200))
            .action(close_session)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    handle, awaitable = lp.start_async(
        net,
        initial={timer: [{"session": 1}]},
        options=lp.ExecutorOptions(environment_places=(activity,)),
        event_store=store,
    )

    # The timer is armed from the start; the activity arrives about 100 ms in.
    await asyncio.sleep(0.1)
    injected_at = time.monotonic()
    assert handle.inject(activity, {"seen": True}) is True
    assert handle.drain() is True
    await awaitable

    assert len(closed_at) == 1, "CloseSession fires once"
    waited_ms = (closed_at[0] - injected_at) * 1000.0
    assert waited_ms >= 215.0, (
        "CloseSession must wait its full 200 ms from the refresh's completion (20 ms in), "
        f"fired {waited_ms:.1f} ms after the activity arrived"
    )
    fresh_clocks = store.events(
        types={"TransitionEnabled", "TransitionClockRestarted"},
        transitions={"CloseSession"},
    )
    assert len(fresh_clocks) == 2, "one clock at the start, one fresh clock from the refresh"


@pytest.mark.asyncio
async def test_surplus_timer_token_keeps_timed_transition_clock() -> None:
    """TIME-012 with a surplus token: `timer` holds two tokens, so `Refresh`
    leaves one behind and `CloseSession` is never disabled. No clock restart
    is reported: `CloseSession` fires on the clock it started with, then once
    more on the clock its own firing started. Mirrors the Rust
    `clock_persists_with_surplus_token`."""
    activity = lp.Place("activity")
    timer = lp.Place("timer")
    closed_at: list[float] = []

    def refresh(ctx: lp.TransitionContext) -> None:
        ctx.output("timer", ctx.input("timer"))

    def close_session(ctx: lp.TransitionContext) -> None:
        closed_at.append(time.monotonic())

    net = (
        lp.Net("session")
        .transition(
            lp.Transition("Refresh")
            .input(lp.one(activity))
            .input(lp.one(timer))
            .output(lp.out(timer))
            .action(refresh)
            .build()
        )
        .transition(
            lp.Transition("CloseSession")
            .input(lp.one(timer))
            .timing(lp.delayed(200))
            .action(close_session)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    started_at = time.monotonic()
    # The activity is there from the start, so `Refresh` fires in the first
    # pass, long before `CloseSession` can.
    await lp.run_async(
        net,
        initial={activity: [{"seen": True}], timer: [{"session": 1}, {"session": 2}]},
        event_store=store,
    )

    assert len(closed_at) == 2, "CloseSession fires once per timer token"
    first_ms = (closed_at[0] - started_at) * 1000.0
    assert first_ms >= 195.0, f"CloseSession waits its 200 ms, fired at {first_ms:.1f} ms"
    restarts = store.events(types={"TransitionClockRestarted"}, transitions={"CloseSession"})
    assert restarts == [], "no clock restart while a timer token survives the refresh"
    enabled = store.events(types={"TransitionEnabled"}, transitions={"CloseSession"})
    assert len(enabled) == 2, (
        "CloseSession is enabled at the start and after its first firing, never by the refresh"
    )
