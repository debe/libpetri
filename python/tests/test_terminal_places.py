"""[EXEC-042] Terminal places through the Python binding.

Rides on the Rust runtime (see ``rust/libpetri/tests/exec042_terminal_places.rs``
for the per-backend conformance suite). These tests pin the Python surface:
``NetBuilder.terminal``, ``Net.terminals``, ``termination_reason`` on the run
result and on the async handle, the build and composition rejections, and the
verifier applying a net's own terminals.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp


def _same_pass_net(t1_priority: int = 10) -> lp.BuiltNet:
    """``t1`` marks the terminal ``done``; ``t2`` moves ``b`` to ``c``. Both are
    enabled before the pass, ``t1`` first."""
    a, b, c, done = lp.Place("a"), lp.Place("b"), lp.Place("c"), lp.Place("done")
    return (
        lp.Net("same_pass")
        .transition(
            lp.Transition("t1").priority(t1_priority).input(lp.one(a)).output(lp.out(done)).action(lp.fork).build()
        )
        .transition(lp.Transition("t2").input(lp.one(b)).output(lp.out(c)).action(lp.fork).build())
        .terminal(done)
        .build()
    )


def test_the_declaration_is_carried_on_the_net() -> None:
    net = _same_pass_net()
    assert [p.name for p in net.terminals] == ["done"]
    # A place name works as well as a Place.
    lone = lp.Net("lone").terminal("halt").build()
    assert [p.name for p in lone.terminals] == ["halt"]
    assert "halt" in [p.name for p in lone.places]


def test_ac1_a_terminal_initial_marking_fires_nothing() -> None:
    result = lp.run_sync(_same_pass_net(), initial={"a": [1], "b": [1], "done": [1]})
    assert result.termination_reason == "terminal"
    assert (result.count("a"), result.count("b"), result.count("c")) == (1, 1, 0)


@pytest.mark.parametrize("t1_priority", [10, 0])
def test_ac4_a_sync_deposit_stops_the_firing_pass(t1_priority: int) -> None:
    result = lp.run_sync(_same_pass_net(t1_priority), initial={"a": [1], "b": [1]})
    assert result.termination_reason == "terminal"
    assert result.count("done") == 1
    assert (result.count("b"), result.count("c")) == (1, 0), "t2 must not fire after t1 marked the terminal"


def test_a_run_without_terminals_is_quiescent() -> None:
    a, b = lp.Place("a"), lp.Place("b")
    net = lp.Net("plain").transition(lp.Transition("t").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build()).build()
    result = lp.run_sync(net, initial={a: [1]})
    assert result.termination_reason == "quiescent"
    assert result.count(b) == 1
    # A view no run returned has no reason; a copy keeps the run's.
    assert lp.MarkingView({"a": [1]}).termination_reason is None
    assert lp.MarkingView(result).termination_reason == "quiescent"


def test_ac5_a_terminal_that_is_consumed_or_read_is_rejected_at_build() -> None:
    done, out, a = lp.Place("done"), lp.Place("out"), lp.Place("a")
    eater = lp.Transition("eater").input(lp.one(done)).output(lp.out(out)).action(lp.fork).build()
    with pytest.raises(lp.StructureError, match="eater"):
        lp.Net("bad").transition(eater).terminal(done).build()
    reader = lp.Transition("reader").input(lp.one(a)).read(lp.read(done)).output(lp.out(out)).action(lp.fork).build()
    with pytest.raises(lp.StructureError, match="read-arc"):
        lp.Net("bad").transition(reader).terminal(done).build()


def test_ac6_composing_a_subnet_whose_body_declares_a_terminal_is_rejected() -> None:
    subnet = lp.SubnetDef.from_net(_same_pass_net(), lp.Interface().build())
    with pytest.raises(lp.StructureError, match="EXEC-042"):
        lp.NetBuilder("host").compose("i1", subnet, {}).build()


# ---------- async -----------------------------------------------------------

async_only = pytest.mark.skipif(not lp.HAS_TOKIO, reason="requires the async runtime")


@async_only
async def test_ac2_an_async_completion_ends_the_run_and_abandons_work_in_flight() -> None:
    start, a, b = lp.Place("start"), lp.Place("a"), lp.Place("b")
    done, result_p = lp.Place("done"), lp.Place("result")

    async def fast(ctx: lp.TransitionContext) -> None:
        ctx.output("done", 1)

    async def slow(ctx: lp.TransitionContext) -> None:
        await asyncio.sleep(0.3)
        ctx.output("result", 1)

    net = (
        lp.Net("in_flight")
        .transition(lp.Transition("split").input(lp.one(start)).output(lp.and_(a, b)).action(lp.fork).build())
        .transition(lp.Transition("fast").input(lp.one(a)).output(lp.out(done)).action(fast).build())
        .transition(lp.Transition("slow").input(lp.one(b)).output(lp.out(result_p)).action(slow).build())
        .terminal(done)
        .build()
    )
    handle, awaitable = lp.start_async(net, initial={start: [1]})
    assert handle.termination_reason == "running"
    loop = asyncio.get_running_loop()
    began = loop.time()
    result = await asyncio.wait_for(awaitable, timeout=5)
    assert loop.time() - began < 0.25, "the run must not wait for the abandoned action"
    assert result.termination_reason == "terminal"
    assert handle.termination_reason == "terminal"
    assert result.count(done) == 1
    assert result.count(result_p) == 0, "the abandoned action's result never appears"


@async_only
async def test_ac3_injecting_into_a_terminal_environment_place_ends_the_run() -> None:
    inbox, cancel, processed = lp.Place("inbox"), lp.Place("cancel"), lp.Place("processed")
    net = (
        lp.Net("cancellable")
        .transition(lp.Transition("process").input(lp.one(inbox)).output(lp.out(processed)).action(lp.fork).build())
        .terminal(cancel)
        .build()
    )
    handle, awaitable = lp.start_async(net, options=lp.ExecutorOptions(environment_places=(inbox, cancel)))
    assert handle.inject(cancel, "stop") is True
    assert handle.inject(inbox, "late") is True  # queued behind the cancel
    result = await asyncio.wait_for(awaitable, timeout=5)
    assert result.termination_reason == "terminal"
    assert handle.termination_reason == "terminal"
    assert (result.count(inbox), result.count(processed)) == (0, 0), "the queued event is refused"
    assert handle.inject(inbox, "after") is False


@async_only
async def test_a_close_with_work_enabled_reports_closed() -> None:
    a, b = lp.Place("a"), lp.Place("b")
    net = (
        lp.Net("slowpoke")
        .transition(lp.Transition("later").timing(lp.delayed(10_000)).input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .build()
    )
    handle, awaitable = lp.start_async(net, initial={a: [1]})
    handle.close()
    result = await asyncio.wait_for(awaitable, timeout=5)
    assert result.termination_reason == "closed"
    assert handle.termination_reason == "closed"


# ---------- verification ------------------------------------------------------


def _terminal_fork(terminal: bool) -> lp.BuiltNet:
    """The shared fixture net ``terminalForkInFlight``."""
    start, a, b = lp.Place("start"), lp.Place("a"), lp.Place("b")
    done, result_p = lp.Place("done"), lp.Place("result")
    builder = (
        lp.Net("terminalForkInFlight")
        .transition(lp.Transition("fork").input(lp.one(start)).output(lp.and_(a, b)).action(lp.fork).build())
        .transition(lp.Transition("finish").input(lp.one(a)).output(lp.out(done)).action(lp.fork).build())
        .transition(lp.Transition("work").input(lp.one(b)).output(lp.out(result_p)).action(lp.fork).build())
    )
    if terminal:
        builder = builder.terminal(done)
    return builder.build()


@pytest.mark.skipif(not lp.HAS_Z3 or not lp.z3_available(), reason="needs the z3 feature and binary")
def test_ac7_the_verifier_applies_the_nets_own_terminals() -> None:
    undeclared = lp.verify(_terminal_fork(False), lp.deadlock_free(), initial_marking={"start": 1}, timeout_ms=30_000)
    assert undeclared.verdict == "violated", undeclared.report
    declared = lp.verify(_terminal_fork(True), lp.deadlock_free(), initial_marking={"start": 1}, timeout_ms=30_000)
    assert declared.verdict == "proven", declared.report


def test_export_draws_a_terminal_place_in_the_terminal_style() -> None:
    dot = lp.dot_export(_terminal_fork(True))
    line = next(ln for ln in dot.splitlines() if ln.strip().startswith("p_done"))
    assert "#d6d8db" in line and "doublecircle" in line, line
