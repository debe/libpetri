import asyncio

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


@pytest.mark.asyncio
async def test_run_async_awaits_python_coroutine_action() -> None:
    incoming = lp.Place("incoming")
    approved = lp.Place("approved")

    async def approve(ctx: lp.TransitionContext) -> None:
        order = ctx.input("incoming")
        await asyncio.sleep(0)
        ctx.output("approved", {**order, "approved": True})

    net = (
        lp.Net("async")
        .transition(
            lp.Transition("approve")
            .input(lp.one(incoming))
            .output(lp.out(approved))
            .action(approve)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{"id": 1}]})

    assert result.count(approved) == 1
    assert result.first(approved)["approved"] is True


@pytest.mark.asyncio
async def test_start_async_exposes_handle_for_environment_injection() -> None:
    sensor = lp.Place("sensor")
    observed = lp.Place("observed")

    net = (
        lp.Net("environment")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(observed))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )

    assert handle.inject(sensor, {"reading": 7}) is True
    assert handle.drain() is True

    result = await awaitable

    assert result.count(observed) == 1
    assert result.first(observed)["reading"] == 7
    assert handle.drained is True
