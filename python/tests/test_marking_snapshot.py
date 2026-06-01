"""Marking snapshot / restore round-trips preserving Token.created_at."""

from __future__ import annotations

import asyncio
import time

import pytest

import libpetri as lp

requires_tokio = pytest.mark.skipif(
    not lp.HAS_TOKIO, reason="ExecutorHandle.snapshot requires tokio"
)


def _build_forward_net() -> lp.BuiltNet:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    return (
        lp.Net("snapshot-net")
        .transition(
            lp.Transition("t")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(lp.fork)
            .build()
        )
        .build()
    )


def test_run_sync_returns_structured_marking_with_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["hello"]})

    assert marking["p_out"] == ("hello",)
    timestamps = marking.timestamps("p_out")
    assert len(timestamps) == 1
    assert isinstance(timestamps[0], int)
    assert timestamps[0] > 0


def test_snapshot_roundtrip_preserves_token_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["one", "two"]})

    snapshot = marking.snapshot()
    restored = lp.MarkingView.from_snapshot(snapshot)

    assert restored.to_dict() == marking.to_dict()
    for place in marking.places():
        assert restored.timestamps(place) == marking.timestamps(place)


def test_passing_marking_view_as_initial_preserves_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["v"]})

    # Note when token entered the marking.
    [token_ts] = marking.timestamps("p_out")

    # Wait long enough that any reassignment to now() would be detectable.
    time.sleep(0.05)

    # Now restore via the structured form (passing the view itself).
    # In this run there are no inputs and no enabled transitions, so the
    # executor terminates with the same marking it started with.
    restored = lp.run_sync(net, initial=marking)

    [restored_ts] = restored.timestamps("p_out")
    assert restored_ts == token_ts, (
        "ExecutorHandle and Marking save/restore must preserve token "
        "created_at; got "
        f"{restored_ts} != {token_ts}"
    )


def test_legacy_value_only_init_still_works_and_stamps_now() -> None:
    net = _build_forward_net()
    before_ms = int(time.time() * 1000)
    marking = lp.run_sync(net, initial={"p_in": ["legacy"]})
    after_ms = int(time.time() * 1000) + 1

    [ts] = marking.timestamps("p_out")
    assert before_ms <= ts <= after_ms


def test_from_snapshot_accepts_explicit_structured_form() -> None:
    structured = {
        "p_out": [
            {"value": "alpha", "created_at": 1_000_000},
            {"value": "beta", "created_at": 2_000_000},
        ]
    }
    view = lp.MarkingView.from_snapshot(structured)
    assert view["p_out"] == ("alpha", "beta")
    assert view.timestamps("p_out") == (1_000_000, 2_000_000)


def test_constructor_auto_detects_structured_vs_legacy() -> None:
    legacy = lp.MarkingView({"p": [1, 2, 3]})
    assert legacy["p"] == (1, 2, 3)
    # legacy timestamps are filled with a single fallback `now`
    assert len(set(legacy.timestamps("p"))) == 1

    structured = lp.MarkingView(
        {"p": [{"value": 10, "created_at": 100}, {"value": 20, "created_at": 200}]}
    )
    assert structured["p"] == (10, 20)
    assert structured.timestamps("p") == (100, 200)


def test_snapshot_handles_empty_marking() -> None:
    empty = lp.MarkingView()
    assert empty.snapshot() == {}
    assert lp.MarkingView.from_snapshot({}).to_dict() == {}


@requires_tokio
@pytest.mark.asyncio
async def test_executor_handle_snapshot_returns_live_marking() -> None:
    # Net with an environment place — keeps the executor alive while we
    # request a mid-execution snapshot.
    p_env = lp.Place("p_env")
    p_seen = lp.Place("p_seen")
    net = (
        lp.Net("env-net")
        .transition(
            lp.Transition("forward")
            .input(lp.one(p_env))
            .output(lp.out(p_seen))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))

    handle, awaitable = lp.start_async(net, options=options)
    try:
        handle.inject(p_env, "ping")
        # Give the executor a moment to fire `forward`.
        await asyncio.sleep(0.05)
        mid = await handle.snapshot()
        assert mid["p_seen"] == ("ping",)
        assert isinstance(mid.timestamps("p_seen")[0], int)
    finally:
        handle.drain()
        await awaitable


@requires_tokio
@pytest.mark.asyncio
async def test_executor_handle_snapshot_rejected_after_close() -> None:
    p_env = lp.Place("p_env")
    net = (
        lp.Net("env-noop")
        .transition(
            lp.Transition("noop")
            .input(lp.one(p_env))
            .action(lp.passthrough)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))
    handle, awaitable = lp.start_async(net, options=options)
    handle.close()
    await awaitable
    with pytest.raises(RuntimeError):
        await handle.snapshot()
