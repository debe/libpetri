"""Tests for ``ctx.flush()`` mid-action token publishing (V3).

The contract: each ``ctx.flush()`` call publishes the currently-buffered
outputs immediately, so a downstream transition can observe them while
the upstream action is still running. Without flush, all outputs from
one action arrive together at completion — fine for atomic operations,
useless for streaming chunks.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


@pytest.mark.asyncio
async def test_flush_publishes_chunks_mid_action() -> None:
    """A streaming action that emits 5 chunks via ``ctx.flush()`` between
    each chunk; a downstream consumer counts them. The action waits for a
    barrier token *after* the third chunk, so on the consumer side we
    must observe at least 3 chunks before the action completes."""

    stream_in = lp.Place("stream_in")
    chunk = lp.Place("chunk")
    barrier = lp.Place("barrier")
    counted = lp.Place("counted")
    seen = lp.Place("seen")

    # Reach into a closure via the marking: count each consumed chunk
    # by emitting one "counted" token per chunk.
    def count_one(ctx: lp.TransitionContext) -> None:
        v = ctx.input("chunk")
        ctx.output("counted", v)

    chunks_published: list[int] = []

    async def stream(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("stream_in")
        for i in range(5):
            ctx.output("chunk", i)
            ctx.flush()
            chunks_published.append(i)
            # Tiny yield so the executor picks up the flush before we
            # produce the next chunk. Tests the contract; not strictly
            # required for correctness.
            await asyncio.sleep(0)  # tokio yield; lets executor process flush
        ctx.output("seen", "all-done")

    net = (
        lp.Net("flush")
        .transition(
            lp.Transition("stream")
            .input(lp.one(stream_in))
            .output(lp.and_(lp.out(chunk), lp.out(seen)))
            .action(stream)
            .build()
        )
        .transition(
            lp.Transition("count")
            .input(lp.one(chunk))
            .output(lp.out(counted))
            .action(count_one)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    result = await lp.run_async(
        net,
        initial={stream_in: [{"go": True}]},
        event_store=store,
    )

    assert result.count(counted) == 5
    assert result.first(seen) == "all-done"

    # Ordering check: TokenAdded events for `chunk` must interleave with
    # TransitionStarted for `count`. If outputs were buffered to action
    # end, all 5 `chunk` TokenAdded events would appear before any
    # `count` TransitionStarted event.
    timeline = [
        (ev.type, ev.place_name or ev.transition_name)
        for ev in store.events()
        if ev.type in {"TokenAdded", "TransitionStarted"}
    ]
    chunk_added_indices = [
        i for i, (t, n) in enumerate(timeline) if t == "TokenAdded" and n == "chunk"
    ]
    count_started_indices = [
        i for i, (t, n) in enumerate(timeline) if t == "TransitionStarted" and n == "count"
    ]
    # At least one `count` start must occur before the last `chunk` add.
    assert chunk_added_indices and count_started_indices
    assert min(count_started_indices) < max(chunk_added_indices), (
        f"All chunk TokenAdded events landed before any count TransitionStarted — "
        f"flush appears to be buffering until action end. Timeline: {timeline!r}"
    )


@pytest.mark.asyncio
async def test_flush_keeps_already_flushed_tokens_after_action_fails() -> None:
    """Atomicity contract from the verdict: flushed tokens stay even if
    the action subsequently raises."""

    stream_in = lp.Place("stream_in")
    chunk = lp.Place("chunk")
    seen = lp.Place("seen")
    counted = lp.Place("counted")

    def count(ctx: lp.TransitionContext) -> None:
        v = ctx.input("chunk")
        ctx.output("counted", v)

    async def will_fail(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("stream_in")
        ctx.output("chunk", 1)
        ctx.flush()
        ctx.output("chunk", 2)
        ctx.flush()
        await asyncio.sleep(0)  # tokio yield
        raise RuntimeError("intentional")

    net = (
        lp.Net("flush-fail")
        .transition(
            lp.Transition("stream")
            .input(lp.one(stream_in))
            .output(lp.and_(lp.out(chunk), lp.out(seen)))
            .action(will_fail)
            .build()
        )
        .transition(
            lp.Transition("count")
            .input(lp.one(chunk))
            .output(lp.out(counted))
            .action(count)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={stream_in: [{"go": True}]})

    # Two flushed chunks were observed by `count` and turned into
    # `counted` tokens. The third (the `seen` output spec branch) never
    # fires because the action errored before it could emit.
    assert result.count(counted) == 2
    assert result.count(seen) == 0


def test_flush_raises_under_sync_execution() -> None:
    """``ctx.flush()`` from a sync action raises — the sync executor
    has no out-of-band channel to deliver flushes through."""

    stream_in = lp.Place("stream_in")
    chunk = lp.Place("chunk")
    sink = lp.Place("sink")

    captured: dict[str, str] = {}

    def passthrough(ctx: lp.TransitionContext) -> None:
        v = ctx.input("chunk")
        ctx.output("sink", v)

    def stream_sync(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("stream_in")
        ctx.output("chunk", 1)
        try:
            ctx.flush()
        except RuntimeError as exc:
            captured["err"] = str(exc)

    net = (
        lp.Net("sync-flush")
        .transition(
            lp.Transition("stream")
            .input(lp.one(stream_in))
            .output(lp.out(chunk))
            .action(stream_sync)
            .build()
        )
        .transition(
            lp.Transition("count")
            .input(lp.one(chunk))
            .output(lp.out(sink))
            .action(passthrough)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={stream_in: [{"go": True}]})
    assert "err" in captured
    assert "async execution" in captured["err"]
    # The buffered token still flushes at action end (the standard
    # behaviour), so the sink still receives it.
    assert result.count(sink) == 1


async def _late_flush(ending: str) -> tuple[list[str], lp.MarkingView]:
    """EXEC-022 line 4, CONC-003 line 2: ``slow`` keeps its ``ctx``; once its
    firing ended (``ending``: the budget ran out, or the action returned), the
    sync ``after`` buffers one token to ``leak`` on the kept ``ctx`` and
    flushes it."""
    stash: list[lp.TransitionContext] = []
    outcome: list[str] = []

    async def slow(ctx: lp.TransitionContext) -> None:
        stash.append(ctx)
        if ending == "timeout":
            await lp.action_on_loop(asyncio.sleep(2))
        else:
            ctx.output("ended", 1)

    def after(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("ended")
        stash[0].output("leak", 1)
        try:
            stash[0].flush()
            outcome.append("published")
        except RuntimeError as exc:
            outcome.append(str(exc))

    leak, ended = lp.Place("leak"), lp.Place("ended")
    branch = lp.timeout(20, lp.out(ended)) if ending == "timeout" else lp.out(ended)
    net = (
        lp.Net("late-flush")
        .transition(
            lp.Transition("slow")
            .input(lp.one(lp.Place("start")))
            .output(lp.xor(lp.out(leak), branch))
            .action(slow)
            .build()
        )
        .transition(lp.Transition("after").input(lp.one(ended)).action(after).build())
        .build()
    )
    result = await lp.run_async(net, initial={"start": ["job"]})
    return outcome, result


@pytest.mark.asyncio
async def test_a_flush_after_the_timeout_is_refused_exec_022() -> None:
    outcome, result = await _late_flush("timeout")
    assert len(outcome) == 1 and "EXEC-022" in outcome[0], outcome
    assert result.count("leak") == 0


@pytest.mark.asyncio
async def test_a_flush_after_the_action_returned_is_refused_exec_022() -> None:
    outcome, result = await _late_flush("return")
    assert len(outcome) == 1 and "EXEC-022" in outcome[0], outcome
    assert result.count("leak") == 0
