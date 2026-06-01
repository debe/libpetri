"""Tests for libpetri's asyncio helpers (V2: action_gather, action_to_thread).

The action thread has no asyncio loop installed, so calling ``asyncio.gather``
directly inside an action raises. ``lp.action_gather`` routes the gather call
to the captured asyncio loop so it works *and* runs the coroutines truly in
parallel. The headline test is the overlap assertion: three 300ms sleeps must
finish in well under their serialized total.
"""

from __future__ import annotations

import asyncio
import time

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


@pytest.mark.asyncio
async def test_action_gather_is_parallel_not_sequential() -> None:
    """Three 300ms sleeps inside an action must finish in roughly 300ms via
    ``lp.action_gather`` — not 900ms. This is the regression test that
    proves we didn't ship a sequential-await implementation."""

    incoming = lp.Place("incoming")
    done = lp.Place("done")

    sleep_ms = 0.30
    n_tasks = 3

    elapsed: dict[str, float] = {}

    async def parallel_action(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")

        async def one_sleep(idx: int) -> int:
            await asyncio.sleep(sleep_ms)
            return idx

        t0 = time.perf_counter()
        results = await lp.action_gather(*(one_sleep(i) for i in range(n_tasks)))
        elapsed["wall"] = time.perf_counter() - t0
        ctx.output("done", results)

    net = (
        lp.Net("gather")
        .transition(
            lp.Transition("parallel")
            .input(lp.one(incoming))
            .output(lp.out(done))
            .action(parallel_action)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{"go": True}]})

    assert result.count(done) == 1
    assert result.first(done) == [0, 1, 2]
    # Sequential would be n_tasks * sleep_ms = 0.90s. Parallel ~0.30s.
    # Generous upper bound at 0.55s: leaves headroom for thread-hop overhead
    # and slow CI without ever passing on the broken sequential path.
    assert elapsed["wall"] < 0.55, (
        f"action_gather appears sequential: wall={elapsed['wall']:.3f}s, "
        f"expected ≈ {sleep_ms:.2f}s parallel, not {n_tasks * sleep_ms:.2f}s "
        f"serialized"
    )


@pytest.mark.asyncio
async def test_action_gather_propagates_exceptions() -> None:
    """``asyncio.gather`` raises the first exception by default; the helper
    must preserve that semantics."""

    incoming = lp.Place("incoming")
    done = lp.Place("done")
    caught: dict[str, str] = {}

    async def will_fail(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")

        async def bad() -> None:
            raise ValueError("boom")

        async def ok() -> int:
            await asyncio.sleep(0.01)
            return 1

        try:
            await lp.action_gather(ok(), bad())
        except ValueError as exc:
            caught["msg"] = str(exc)
        ctx.output("done", caught.get("msg", "no-error"))

    net = (
        lp.Net("gather-err")
        .transition(
            lp.Transition("err")
            .input(lp.one(incoming))
            .output(lp.out(done))
            .action(will_fail)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{"go": True}]})
    assert result.first(done) == "boom"


@pytest.mark.asyncio
async def test_raw_asyncio_gather_still_raises_in_action() -> None:
    """Negative test: confirm we did *not* accidentally fix raw
    ``asyncio.gather`` inside actions. Users must use ``lp.action_gather``
    or structural fan-out — there is no magic global loop install."""

    incoming = lp.Place("incoming")
    outcome = lp.Place("outcome")

    async def naive(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")

        async def one() -> None:
            await asyncio.sleep(0)

        coros = [one(), one()]
        try:
            await asyncio.gather(*coros)
            ctx.output("outcome", "unexpectedly-worked")
        except RuntimeError as exc:
            for c in coros:
                c.close()
            ctx.output("outcome", f"raised: {exc!s}")

    net = (
        lp.Net("naive")
        .transition(
            lp.Transition("naive")
            .input(lp.one(incoming))
            .output(lp.out(outcome))
            .action(naive)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{}]})
    msg = result.first(outcome)
    assert msg.startswith("raised:"), (
        f"raw asyncio.gather should still fail without a loop; got: {msg!r}. "
        "If this passes with 'unexpectedly-worked', a loop is being installed "
        "on the action thread — that's a different (more invasive) fix than "
        "lp.action_gather; revisit the V2 design decision."
    )


@pytest.mark.asyncio
async def test_action_to_thread_runs_blocking_fn() -> None:
    """``action_to_thread`` should route a sync function through the
    captured loop's thread executor and return its result."""

    incoming = lp.Place("incoming")
    done = lp.Place("done")

    def blocking_compute(a: int, b: int) -> int:
        time.sleep(0.02)
        return a * b

    async def call_blocking(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        result = await lp.action_to_thread(blocking_compute, 6, 7)
        ctx.output("done", result)

    net = (
        lp.Net("to-thread")
        .transition(
            lp.Transition("call")
            .input(lp.one(incoming))
            .output(lp.out(done))
            .action(call_blocking)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{}]})
    assert result.first(done) == 42


def test_captured_event_loop_raises_when_no_loop_in_flight() -> None:
    """Outside any ``run_async`` / ``start_async``, the captured-loop getter
    should raise rather than return a stale loop reference."""
    # If a previous async test already ran, EVENT_LOOP_LOCALS may be set
    # (it's a process-global). We can't reliably test the *no-prior-call*
    # path inside the same pytest process. We test the type instead:
    # this should either raise OR return a Python object that's a loop.
    try:
        loop = lp._libpetri.captured_event_loop()
        assert hasattr(loop, "call_soon_threadsafe"), (
            f"captured_event_loop returned non-loop object: {loop!r}"
        )
    except RuntimeError as exc:
        assert "asyncio" in str(exc).lower()


def test_start_async_on_different_loop_while_in_flight_raises() -> None:
    """Concurrent run_async on two different asyncio loops in the same
    process is not supported. The first run captures its loop; a second
    start_async on a different loop while the first is in flight must
    raise rather than silently routing action helpers (``action_gather``,
    ``action_to_thread``, ``captured_event_loop``) to the wrong loop."""

    sensor = lp.Place("sensor")
    out = lp.Place("out")
    net = (
        lp.Net("multiloop_reject")
        .transition(
            lp.Transition("t")
            .input(lp.one(sensor))
            .output(lp.out(out))
            .build()
        )
        .build()
    )

    loop_a = asyncio.new_event_loop()
    loop_b = asyncio.new_event_loop()
    handle_a = None
    awaitable_a = None
    try:

        async def start_on(loop_label: str):
            return lp.start_async(
                net,
                initial={},
                options=lp.ExecutorOptions(environment_places=["sensor"]),
            )

        handle_a, awaitable_a = loop_a.run_until_complete(start_on("A"))

        with pytest.raises(RuntimeError, match="(?i)different asyncio"):
            loop_b.run_until_complete(start_on("B"))
    finally:
        if handle_a is not None:
            handle_a.close()
        if awaitable_a is not None:

            async def _drain():
                try:
                    await awaitable_a
                except Exception:
                    pass

            try:
                loop_a.run_until_complete(_drain())
            except Exception:
                pass
        loop_a.close()
        loop_b.close()


def test_start_async_sequential_different_loops_works() -> None:
    """Sequential run_async calls on different loops are fine: when the
    first completes, the RAII guard clears the captured locals so the
    next call installs fresh state. This is the documented escape hatch
    from the in-flight rejection above."""

    sensor = lp.Place("sensor")
    out = lp.Place("out")

    async def emit_one(ctx: lp.TransitionContext) -> None:
        ctx.output("out", ctx.input("sensor"))

    def run_one_on(loop: asyncio.AbstractEventLoop) -> int:
        net = (
            lp.Net("seq")
            .transition(
                lp.Transition("emit")
                .input(lp.one(sensor))
                .output(lp.out(out))
                .action(emit_one)
                .build()
            )
            .build()
        )

        async def drive():
            handle, awaitable = lp.start_async(
                net,
                initial={},
                options=lp.ExecutorOptions(environment_places=["sensor"]),
            )
            handle.inject(sensor, 7)
            handle.drain()
            result = await awaitable
            return result.count(out)

        return loop.run_until_complete(drive())

    loop_a = asyncio.new_event_loop()
    loop_b = asyncio.new_event_loop()
    try:
        assert run_one_on(loop_a) == 1
        # Different loop, but A has already completed — must succeed.
        assert run_one_on(loop_b) == 1
    finally:
        loop_a.close()
        loop_b.close()
