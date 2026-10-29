"""IO-014: an ``out`` leaf under a timeout branch deposits a token the executor mints,
which carries no value. Python reads it as ``None`` everywhere a token crosses the
boundary: the final marking, a mid-run snapshot, a downstream action's input, and a
token event. Up to 7.3.0 each of these raised "Expected python.object token, found ()".
"""

import asyncio
import json

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="timeout branches need the tokio async path",
)


async def _slow(ctx: lp.TransitionContext) -> None:
    await lp.action_on_loop(asyncio.sleep(2))
    ctx.output("done", ctx.input("start"))


def _net(*extra: lp.BuiltTransition) -> lp.BuiltNet:
    start, done, timed_out = lp.Place("start"), lp.Place("done"), lp.Place("timed_out")
    net = lp.Net("timeout-unit").transition(
        lp.Transition("slow")
        .input(lp.one(start))
        .output(lp.xor(lp.out(done), lp.timeout(20, lp.out(timed_out))))
        .action(_slow)
        .build()
    )
    for t in extra:
        net = net.transition(t)
    return net.build()


@pytest.mark.asyncio
async def test_the_final_marking_holds_none() -> None:
    result = await lp.run_async(_net(), initial={"start": ["job"]})
    assert result.tokens("timed_out") == (None,)
    assert result.snapshot()["timed_out"][0]["value"] is None


@pytest.mark.asyncio
async def test_a_mid_run_snapshot_holds_none() -> None:
    keepalive = lp.Place("keepalive")
    handle, awaitable = lp.start_async(
        _net(),
        initial={"start": ["job"]},
        options=lp.ExecutorOptions(environment_places=(keepalive,)),
    )
    snap = await handle.snapshot()
    for _ in range(100):
        if snap.marking.count("timed_out") == 1:
            break
        await asyncio.sleep(0.01)
        snap = await handle.snapshot()
    assert snap.marking.tokens("timed_out") == (None,)
    handle.drain()
    await awaitable


@pytest.mark.asyncio
async def test_a_snapshot_stored_as_json_restores_and_resumes() -> None:
    # CORE-073 across a process boundary: the timeout token survives JSON and a
    # resumed run consumes it.
    timed_out = await lp.run_async(_net(), initial={"start": ["job"]})
    stored = json.dumps(timed_out.snapshot())

    recover = (
        lp.Transition("recover")
        .input(lp.one(lp.Place("timed_out")))
        .output(lp.out(lp.Place("recovered")))
        .action(lp.fork)
        .build()
    )
    resumed = await lp.run_async(_net(recover), initial=json.loads(stored))
    assert resumed.tokens("recovered") == (None,)
    assert resumed.count("timed_out") == 0


@pytest.mark.asyncio
async def test_a_downstream_action_reads_none() -> None:
    seen: list[object] = []

    def record(ctx: lp.TransitionContext) -> None:
        value = ctx.input("timed_out")
        seen.append(value)
        ctx.output("recovered", value)

    recover = (
        lp.Transition("recover")
        .input(lp.one(lp.Place("timed_out")))
        .output(lp.out(lp.Place("recovered")))
        .action(record)
        .build()
    )
    result = await lp.run_async(_net(recover), initial={"start": ["job"]})
    assert seen == [None]
    assert result.tokens("recovered") == (None,)


@pytest.mark.asyncio
async def test_a_token_event_carries_none() -> None:
    store = lp.InMemoryEventStore(capture_tokens=True)
    await lp.run_async(_net(), initial={"start": ["job"]}, event_store=store)
    [added] = store.events(types={"TokenAdded"}, places={"timed_out"})
    assert "token" in added.payload()
    assert added.payload()["token"] is None
    assert added.token is None
