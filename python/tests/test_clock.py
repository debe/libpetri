"""[TIME-015] Host clocks: `ManualClock` and `SteppedClock` through
`ExecutorOptions(clock=...)`.

Mirrors the Rust stepped-clock suite in `backend_suite_tests.rs`: a stepped
run fires nothing until the host advances, a hard deadline is reaped exactly
at its bound under tolerance 0, and an inject followed by a settle sees the
executor catch up.
"""

from __future__ import annotations

import asyncio
import threading
import time

import pytest

import libpetri as lp

SETTLE_S = 5.0
ORIGIN = 1_700_000_000_000


def _timed_net(name: str, timing: lp.Timing) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    net = (
        lp.Net(name)
        .transition(
            lp.Transition("T")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .timing(timing)
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return net, p_in, p_out


def _env_net(name: str) -> tuple[lp.BuiltNet, lp.Place]:
    """`Admit` moves an injected token from the environment place `in` to `out`."""
    p_env = lp.Place("in")
    out = lp.Place("out")
    net = (
        lp.Net(name)
        .transition(
            lp.Transition("Admit").input(lp.one(p_env)).output(lp.out(out)).action(lp.fork).build()
        )
        .build()
    )
    return net, p_env


def _events(store: lp.InMemoryEventStore, kind: str, transition: str) -> list[lp.NetEvent]:
    return [e for e in store.events() if e.type == kind and e.transition_name == transition]


# ---------------------------------------------------------------------------
# Construction and options
# ---------------------------------------------------------------------------


def test_clocks_start_at_their_epoch_origin() -> None:
    for cls in (lp.ManualClock, lp.SteppedClock):
        clock = cls(ORIGIN)
        assert clock.now_ms() == 0.0
        assert clock.epoch_ms() == ORIGIN
        clock.advance_ms(250)
        assert clock.now_ms() == clock.elapsed_ms() == 250.0
        assert clock.epoch_ms() == ORIGIN + 250
        clock.advance_ms(0)
        assert clock.now_ms() == 250.0
        with pytest.raises(ValueError):
            clock.advance_ms(-1)
        with pytest.raises(ValueError):
            clock.advance_ms(float("nan"))


def test_clock_option_rejects_other_types() -> None:
    with pytest.raises(TypeError, match="clock must be"):
        lp.ExecutorOptions(clock=object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="clock must be"):
        lp._libpetri.ExecutorOptions(clock=time.monotonic)  # type: ignore[arg-type]


def test_native_options_carry_the_same_clock() -> None:
    clock = lp.SteppedClock()
    native = lp.ExecutorOptions(clock=clock).native()
    clock.advance_ms(42)
    assert isinstance(native.clock, lp.SteppedClock)
    assert native.clock.now_ms() == 42.0
    assert lp.ExecutorOptions().native().clock is None


def test_settle_timeout_must_be_non_negative() -> None:
    clock = lp.SteppedClock()
    with pytest.raises(ValueError):
        clock.settle(-1.0)
    assert clock.settle(0.01) is False


# ---------------------------------------------------------------------------
# ManualClock
# ---------------------------------------------------------------------------


def test_manual_clock_runs_a_long_delay_in_no_real_time() -> None:
    clock = lp.ManualClock(ORIGIN)
    net, p_in, p_out = _timed_net("manual", lp.delayed(10_000))

    started = time.monotonic()
    result = lp.run_sync(
        net, initial={p_in: ["job"]}, options=lp.ExecutorOptions(clock=clock)
    )
    elapsed_s = time.monotonic() - started

    assert result.tokens(p_out) == ("job",)
    assert elapsed_s < 1.0, f"virtual delay took {elapsed_s:.2f}s of real time"
    assert clock.now_ms() == 10_000.0
    # The output is stamped from the clock's epoch at the instant it fired.
    assert result.timestamps(p_out) == (ORIGIN + 10_000,)
    assert clock.epoch_ms() == ORIGIN + 10_000


@pytest.mark.skipif(not lp.HAS_TOKIO, reason="requires the async runtime")
async def test_manual_clock_on_the_async_path() -> None:
    clock = lp.ManualClock(ORIGIN)
    net, p_in, p_out = _timed_net("manual-async", lp.delayed(10_000))

    started = time.monotonic()
    result = await lp.run_async(
        net, initial={p_in: ["job"]}, options=lp.ExecutorOptions(clock=clock)
    )

    assert time.monotonic() - started < 1.0
    assert result.timestamps(p_out) == (ORIGIN + 10_000,)


def test_manual_clock_stamps_legacy_initial_tokens_and_keeps_structured_ones() -> None:
    clock = lp.ManualClock(ORIGIN)
    clock.advance_ms(5)
    held = lp.Place("held")
    other = lp.Place("other")
    net = (
        lp.Net("stamps")
        .transition(
            lp.Transition("never")
            .input(lp.one(other))
            .inhibitor(lp.inhibitor(held))
            .output(lp.out(other))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    result = lp.run_sync(
        net,
        initial={held: ["legacy", {"value": "restored", "created_at": 123}]},
        options=lp.ExecutorOptions(clock=clock),
    )
    assert dict(zip(result.tokens(held), result.timestamps(held))) == {
        "legacy": ORIGIN + 5,
        "restored": 123,
    }


# ---------------------------------------------------------------------------
# SteppedClock: synchronous host
# ---------------------------------------------------------------------------


def test_stepped_sync_run_waits_for_the_host() -> None:
    clock = lp.SteppedClock(ORIGIN)
    net, p_in, p_out = _timed_net("stepped-sync", lp.delayed(1000))
    store = lp.InMemoryEventStore()
    results: list[lp.MarkingView] = []

    runner = threading.Thread(
        target=lambda: results.append(
            lp.run_sync(
                net,
                initial={p_in: ["job"]},
                options=lp.ExecutorOptions(clock=clock),
                event_store=store,
            )
        )
    )
    runner.start()
    try:
        assert clock.settle(SETTLE_S) is True
        assert clock.is_parked()
        assert _events(store, "TransitionStarted", "T") == []
        assert clock.settle_after(lambda: clock.advance_ms(999), SETTLE_S) is True
        assert _events(store, "TransitionStarted", "T") == []
        assert clock.settle_after(lambda: clock.advance_ms(1), SETTLE_S) is True
    finally:
        if runner.is_alive() and not clock.is_finished():
            clock.advance_ms(1_000_000)
        runner.join(SETTLE_S)

    assert not runner.is_alive()
    assert clock.is_finished()
    (result,) = results
    assert result.tokens(p_out) == ("job",)
    assert result.timestamps(p_out) == (ORIGIN + 1000,)
    # Released by the end of the run, so a late settle does not hang.
    assert clock.settle(0.0) is True


def test_settle_after_propagates_the_action_error() -> None:
    clock = lp.SteppedClock()

    def boom() -> None:
        raise KeyError("from the action")

    with pytest.raises(KeyError, match="from the action"):
        clock.settle_after(boom, SETTLE_S)


def test_a_stepped_clock_serves_one_run() -> None:
    clock = lp.ManualClock()
    net, p_in, _ = _timed_net("reuse", lp.immediate())
    options = lp.ExecutorOptions(clock=clock)
    lp.run_sync(net, initial={p_in: [1]}, options=options)
    lp.run_sync(net, initial={p_in: [1]}, options=options)  # a ManualClock may be reused

    stepped = lp.SteppedClock()
    options = lp.ExecutorOptions(clock=stepped)
    lp.run_sync(net, initial={p_in: [1]}, options=options)
    assert stepped.is_finished()
    with pytest.raises(ValueError, match="single-use"):
        lp.run_sync(net, initial={p_in: [1]}, options=options)


def test_a_rejected_run_does_not_use_up_the_clock() -> None:
    clock = lp.SteppedClock()
    net, p_in, _ = _timed_net("rejected", lp.immediate())
    options = lp.ExecutorOptions(clock=clock)
    with pytest.raises(TypeError):
        lp.run_sync(net, initial={p_in: [1]}, options=options, event_store=object())
    assert not clock.is_finished()
    lp.run_sync(net, initial={p_in: [1]}, options=options)
    assert clock.is_finished()


# ---------------------------------------------------------------------------
# SteppedClock: asynchronous host
# ---------------------------------------------------------------------------

async_only = pytest.mark.skipif(not lp.HAS_TOKIO, reason="requires the async runtime")


@async_only
async def test_stepped_async_nothing_fires_before_the_advance() -> None:
    clock = lp.SteppedClock(ORIGIN)
    net, p_in, p_out = _timed_net("stepped-async", lp.delayed(1000))
    store = lp.InMemoryEventStore()
    _handle, done = lp.start_async(
        net,
        initial={p_in: ["job"]},
        options=lp.ExecutorOptions(clock=clock),
        event_store=store,
    )

    assert await clock.asettle(SETTLE_S) is True
    assert _events(store, "TransitionStarted", "T") == []
    assert await clock.asettle_after(lambda: clock.advance_ms(500), SETTLE_S) is True
    assert _events(store, "TransitionStarted", "T") == []

    assert await clock.asettle_after(lambda: clock.advance_ms(500), SETTLE_S) is True
    assert len(_events(store, "TransitionCompleted", "T")) == 1

    result = await done
    assert result.tokens(p_out) == ("job",)
    assert result.timestamps(p_out) == (ORIGIN + 1000,)
    assert clock.is_finished()


@async_only
@pytest.mark.parametrize(("step", "reaped"), [(120.0, False), (120.001, True)])
async def test_stepped_deadline_reaped_exactly_at_bound(step: float, reaped: bool) -> None:
    clock = lp.SteppedClock()
    net, p_in, p_out = _timed_net("window", lp.window(50, 120))
    store = lp.InMemoryEventStore()
    _handle, done = lp.start_async(
        net,
        initial={p_in: ["job"]},
        options=lp.ExecutorOptions(clock=clock, deadline_tolerance_ms=0),
        event_store=store,
    )

    assert await clock.asettle(SETTLE_S) is True
    assert await clock.asettle_after(lambda: clock.advance_ms(step), SETTLE_S) is True
    result = await done

    timed_out = _events(store, "TransitionTimedOut", "T")
    if reaped:
        assert [e.timestamp for e in timed_out] == [120]
        assert _events(store, "TransitionStarted", "T") == []
        assert result.count(p_in) == 1
    else:
        assert timed_out == []
        assert result.tokens(p_out) == ("job",)


@async_only
async def test_stepped_inject_then_settle() -> None:
    p_env = lp.Place("in")
    mid = lp.Place("mid")
    out = lp.Place("out")
    net = (
        lp.Net("inject")
        .transition(
            lp.Transition("Admit").input(lp.one(p_env)).output(lp.out(mid)).action(lp.fork).build()
        )
        .transition(
            lp.Transition("Late")
            .input(lp.one(mid))
            .output(lp.out(out))
            .timing(lp.delayed(500))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    clock = lp.SteppedClock(ORIGIN)
    clock.advance_ms(10)
    store = lp.InMemoryEventStore()
    handle, done = lp.start_async(
        net,
        options=lp.ExecutorOptions(clock=clock, environment_places=(p_env,)),
        event_store=store,
    )

    assert await clock.asettle(SETTLE_S) is True
    assert await clock.asettle_after(lambda: handle.inject(p_env, "job"), SETTLE_S) is True
    assert len(_events(store, "TransitionCompleted", "Admit")) == 1
    assert _events(store, "TransitionStarted", "Late") == []
    mid_now = (await handle.snapshot()).marking
    # Admit's output is stamped from the clock.
    assert mid_now.timestamps(mid) == (ORIGIN + 10,)

    assert await clock.asettle_after(lambda: clock.advance_ms(500), SETTLE_S) is True
    assert len(_events(store, "TransitionCompleted", "Late")) == 1

    handle.drain()
    result = await done
    assert result.tokens(out) == ("job",)
    assert result.timestamps(out) == (ORIGIN + 510,)
    assert clock.is_finished()


@async_only
async def test_injected_tokens_are_stamped_from_the_clock() -> None:
    # `Gated` never fires (`gate` stays empty), so injected tokens stay in
    # `in` with the created_at the handle gave them.
    p_env = lp.Place("in")
    gate = lp.Place("gate")
    out = lp.Place("out")
    net = (
        lp.Net("inject-stamps")
        .transition(
            lp.Transition("Gated")
            .input(lp.one(p_env))
            .input(lp.one(gate))
            .output(lp.out(out))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    clock = lp.SteppedClock(ORIGIN)
    clock.advance_ms(7)
    handle, done = lp.start_async(
        net, options=lp.ExecutorOptions(clock=clock, environment_places=(p_env,))
    )
    assert await clock.asettle(SETTLE_S) is True
    assert await clock.asettle_after(lambda: handle.inject(p_env, 1), SETTLE_S)
    clock.advance_ms(3)
    assert await clock.asettle_after(lambda: handle.inject_many(p_env, [2, 3]), SETTLE_S)
    snap = (await handle.snapshot()).marking
    assert snap.tokens(p_env) == (1, 2, 3)
    assert snap.timestamps(p_env) == (ORIGIN + 7, ORIGIN + 10, ORIGIN + 10)
    handle.drain()
    await done


@async_only
async def test_asettle_returns_when_the_run_ends() -> None:
    clock = lp.SteppedClock()
    net, p_in, _ = _timed_net("ends", lp.delayed(100))
    _handle, done = lp.start_async(
        net, initial={p_in: [1]}, options=lp.ExecutorOptions(clock=clock)
    )
    assert await clock.asettle(SETTLE_S) is True
    # The run ends without parking again; only `mark_finished` releases this.
    assert await clock.asettle_after(lambda: clock.advance_ms(100), SETTLE_S) is True
    await done
    assert clock.is_finished()
    assert await clock.asettle(0.0) is True


@async_only
async def test_closing_the_run_releases_a_settle_waiter() -> None:
    net, p_env = _env_net("closed")
    clock = lp.SteppedClock()
    handle, done = lp.start_async(
        net, options=lp.ExecutorOptions(clock=clock, environment_places=(p_env,))
    )
    assert await clock.asettle(SETTLE_S) is True
    assert await clock.asettle_after(handle.close, SETTLE_S) is True
    await done
    assert clock.is_finished()


@async_only
async def test_a_stepped_clock_in_use_cannot_start_a_second_run() -> None:
    net, p_env = _env_net("in-use")
    clock = lp.SteppedClock()
    options = lp.ExecutorOptions(clock=clock, environment_places=(p_env,))
    handle, done = lp.start_async(net, options=options)
    with pytest.raises(ValueError, match="single-use"):
        lp.start_async(net, options=options)
    handle.close()
    await done


@pytest.mark.skipif(not lp.HAS_TOKIO, reason="requires the tokio feature")
def test_a_start_that_fails_before_running_leaves_the_clock_usable() -> None:
    net, p_env = _env_net("no-loop")
    clock = lp.SteppedClock()
    options = lp.ExecutorOptions(clock=clock, environment_places=(p_env,))
    # No asyncio loop is running here, so no run can start.
    with pytest.raises(RuntimeError):
        lp.start_async(net, options=options)
    assert not clock.is_finished()

    async def run() -> None:
        handle, done = lp.start_async(net, options=options)
        handle.close()
        await done

    asyncio.run(run())
    assert clock.is_finished()


@async_only
async def test_flushed_tokens_are_stamped_from_the_clock() -> None:
    go = lp.Place("go")
    chunk = lp.Place("chunk")
    seen = lp.Place("seen")

    async def stream(ctx: lp.TransitionContext) -> None:
        ctx.input("go")
        ctx.output("chunk", 1)
        ctx.flush()
        ctx.output("seen", "done")

    net = (
        lp.Net("flush-stamps")
        .transition(
            lp.Transition("stream")
            .input(lp.one(go))
            .output(lp.and_(lp.out(chunk), lp.out(seen)))
            .action(stream)
            .build()
        )
        .build()
    )
    clock = lp.ManualClock(ORIGIN)
    clock.advance_ms(3)
    result = await lp.run_async(
        net, initial={go: [True]}, options=lp.ExecutorOptions(clock=clock)
    )
    assert result.timestamps(chunk) == (ORIGIN + 3,)
    assert result.timestamps(seen) == (ORIGIN + 3,)
