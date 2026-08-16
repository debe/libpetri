"""Regressions for the backend-divergence fixes in the Rust runtime.

Python runs the precompiled backend only, so each scenario was a live
user-visible bug here. Mirrors Rust `backend_suite_tests::{read_and_reset_same_place,
duplicate_input_place_rejected_at_compile, unknown_place_initial_tokens_retained,
unknown_place_warns_once_per_place, unknown_places::*}` — EXEC-013 AC4,
CORE-030 AC3, CORE-072 AC3/AC4.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp


# ---------- read + reset on one place (EXEC-013 AC4) --------------------


def test_read_and_reset_on_same_place_observes_pre_reset_token() -> None:
    trigger = lp.Place("trigger")
    store = lp.Place("store")
    done = lp.Place("done")

    def capture(ctx: lp.TransitionContext) -> None:
        ctx.output("done", {"seen": ctx.read("store")["v"]})

    net = (
        lp.Net("read-reset")
        .transition(
            lp.Transition("snapshot_and_clear")
            .input(lp.one(trigger))
            .read(lp.read(store))
            .reset(lp.reset(store))
            .output(lp.out(done))
            .action(capture)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={trigger: [{"go": True}], store: [{"v": 1}, {"v": 2}]},
    )

    assert result.count(done) == 1
    assert result.first(done)["seen"] == 1, "read must observe the pre-reset front token"
    assert result.count(store) == 0, "reset must drain the place after the read"


# ---------- duplicate input arcs rejected at compile (CORE-030 AC3) -----


def test_two_one_input_arcs_on_same_place_rejected_at_compile() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("dup-inputs")
        .transition(
            lp.Transition("double_take")
            .input(lp.one(queued))
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    with pytest.raises(lp.StructureError, match="two input arcs"):
        lp.compile(net)


# ---------- undeclared-place token retention (CORE-072 AC3) -------------


def test_initial_tokens_on_undeclared_place_retained() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")
    ghost = lp.Place("ghost")

    net = (
        lp.Net("ghost-initial")
        .transition(
            lp.Transition("forward")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={queued: [{"id": 1}], ghost: [{"v": 99}]},
    )

    assert result.count(done) == 1
    assert result.count(ghost) == 1, "tokens on an uncompiled place must survive the run"
    assert result.first(ghost)["v"] == 99


def test_undeclared_place_warns_once_per_place() -> None:
    """CORE-072 AC4: one WARN log-message event per distinct place, whatever
    the token count. Retention (AC3) does not depend on it — the default
    no-op store drops the event and the tokens still survive."""
    queued = lp.Place("queued")
    done = lp.Place("done")
    ghost = lp.Place("ghost")
    spectre = lp.Place("spectre")

    net = (
        lp.Net("ghost-warn")
        .transition(
            lp.Transition("forward")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    result = lp.run_sync(
        net,
        initial={
            queued: [{"id": 1}],
            ghost: [{"v": 1}, {"v": 2}, {"v": 3}],
            spectre: [{"v": 4}],
        },
        event_store=store,
    )

    warnings = store.events(types={"LogMessage"})
    assert len(warnings) == 2, "one warning per place, not per token"
    payloads = [ev.payload() for ev in warnings]
    assert {p["level"] for p in payloads} == {"WARN"}
    assert {p["transition_name"] for p in payloads} == {""}
    assert sorted(p["message"] for p in payloads) == [
        "unknown place 'ghost': tokens are retained in the marking but inert "
        "(the net declares no arc on it)",
        "unknown place 'spectre': tokens are retained in the marking but inert "
        "(the net declares no arc on it)",
    ]
    assert result.count(ghost) == 3


# Producing into an undeclared place has no Python-reachable seam: ``ctx.output``
# rejects any place the transition does not declare, and every declared output
# place is part of the net. It is covered directly against both Rust backends in
# `backend_suite_tests::unknown_places::produce_unknown_place_retained_on_both_backends`.


@pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="injection requires the async runtime",
)
@pytest.mark.asyncio
async def test_injected_tokens_on_undeclared_place_retained() -> None:
    sensor = lp.Place("sensor")
    captured = lp.Place("captured")
    ghost = lp.Place("ghost")

    net = (
        lp.Net("ghost-inject")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(captured))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor, ghost)),
        event_store=store,
    )

    await asyncio.sleep(0.02)
    assert handle.inject(sensor, {"reading": 1}) is True
    assert handle.inject(ghost, {"v": 7}) is True
    assert handle.drain() is True

    result = await awaitable

    assert result.count(captured) == 1
    assert result.count(ghost) == 1, "injection into an uncompiled place must be retained"
    assert result.first(ghost)["v"] == 7

    warnings = store.events(types={"LogMessage"})
    assert len(warnings) == 1, "the injection seam warns once (CORE-072 AC4)"
    assert "unknown place 'ghost'" in warnings[0].payload()["message"]
