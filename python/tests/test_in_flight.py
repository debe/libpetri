"""In-flight actions and the atomic-firing premise of verification (VER-004).

The executor consumes a firing's inputs when its action starts and deposits its
outputs when the action completes. With an asynchronous action other transitions
fire in between. ``start: req + inhibitor(busy) -> busy`` is the usual
one-at-a-time guard: atomically ``busy`` never holds two tokens, but with two
requests and a slow action the executor starts the second while the first is in
flight (the Rust runtime starts a transition again while it is in flight; Java and
TypeScript do not). Mirrors ``rust/libpetri/tests/inflight_atomicity.rs``.
"""

from __future__ import annotations

import time

import libpetri as lp
import pytest



def _guard_net():
    req, busy = lp.Place("req"), lp.Place("busy")

    async def slow(ctx: lp.TransitionContext) -> None:
        await lp.action_to_thread(time.sleep, 0.05)
        ctx.output("busy", True)

    start = (
        lp.Transition("start")
        .input(lp.one(req))
        .inhibitor(lp.inhibitor(busy))
        .output(lp.out(busy))
        .action(slow)
        .build()
    )
    return lp.Net("inflight-guard").transition(start).build(), req, busy


@pytest.mark.asyncio
@pytest.mark.skipif(not lp.HAS_TOKIO, reason="wheel built without tokio async support")
async def test_the_executor_starts_the_guarded_transition_twice() -> None:
    net, req, busy = _guard_net()
    result = await lp.run_async(net, initial={req: [1, 2]})
    assert result.count(busy) == 2


@pytest.mark.parametrize("enumeration", [None, 0])
@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_the_verifier_splits_the_guarded_transition(enumeration) -> None:
    if not lp.z3_available():
        pytest.skip("no usable z3 executable")
    net, _, _ = _guard_net()
    result = lp.verify(
        net,
        lp.place_bound("busy", 1),
        initial_marking={"req": 2},
        enumeration_max_classes=enumeration,
        timeout_ms=30_000,
    )
    assert result.verdict == "violated", result.report
    assert "In-flight actions (VER-004): start is verified in two steps" in result.report


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_assume_atomic_firing_restores_the_atomic_verdict() -> None:
    if not lp.z3_available():
        pytest.skip("no usable z3 executable")
    net, _, _ = _guard_net()
    result = lp.verify(
        net,
        lp.place_bound("busy", 1),
        initial_marking={"req": 2},
        assume_atomic_firing=True,
        timeout_ms=30_000,
    )
    assert result.verdict == "proven", result.report
    assert "ASSUMPTION: every firing is atomic (the assume-atomic-firing option)" in result.report
    split = lp.encode_smt_scripts(net, lp.place_bound("busy", 1), initial_marking={"req": 2})
    atomic = lp.encode_smt_scripts(
        net, lp.place_bound("busy", 1), initial_marking={"req": 2}, assume_atomic_firing=True
    )
    assert split["horn"] != atomic["horn"]


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_the_open_net_verifier_splits_too() -> None:
    net, _, _ = _guard_net()
    contract = (
        lp.OpenNetContract.builder()
        .initial_tokens("req", 2)
        .expect("busy", 1, "busy")
        .rest("req")
        .build()
    )
    split = lp.verify_open_net(net, contract, smt=False)
    assert split.verdict == "violated", split.report
    assert "In-flight actions (VER-004): start is verified in two steps" in split.report
    atomic = lp.verify_open_net(net, contract, smt=False, assume_atomic_firing=True)
    assert atomic.verdict == "proven", atomic.report


# ==================== witnesses of the fix round (2026-09-30) ====================
# Mirrors the ``verdicts`` witnesses of ``rust/libpetri/tests/inflight_atomicity.rs``.
# The verifier reads the net's structure, so every action here is ``lp.fork``.

needs_z3 = pytest.mark.skipif(
    not (lp.HAS_Z3 and lp.z3_available()), reason="z3 feature not enabled or no usable z3 executable"
)


def _t(name, inputs, output, *, inhibitor=None, priority=None, timing=None):
    b = lp.Transition(name)
    for p in inputs:
        b = b.input(lp.one(lp.Place(p)))
    if inhibitor is not None:
        b = b.inhibitor(lp.inhibitor(lp.Place(inhibitor)))
    if priority is not None:
        b = b.priority(priority)
    if timing is not None:
        b = b.timing(timing)
    return b.output(lp.out(lp.Place(output))).action(lp.fork).build()


def _net(name, *transitions, terminal=None):
    b = lp.Net(name)
    for t in transitions:
        b = b.transition(t)
    if terminal is not None:
        b = b.terminal(terminal)
    return b.build()


def _nu_pair(join_priority=0):
    """``MINT: SEED -> X, Y`` writes one fresh name into both (declared a mint), and
    ``JOIN`` joins ``X`` and ``Y`` by name into ``J``, so Route B decides the net."""
    x, y = lp.Place("X"), lp.Place("Y")
    mint = lp.Transition("MINT").input(lp.one(lp.Place("SEED"))).output(lp.and_(x, y)).action(lp.fork).build()
    join = (
        lp.Transition("JOIN")
        .priority(join_priority)
        .input(lp.one(x))
        .input(lp.one(y))
        .match_spec(lp.match_spec([(x, lambda v: v), (y, lambda v: v)]))
        .output(lp.out(lp.Place("J")))
        .action(lp.fork)
        .build()
    )
    return mint, join


def _terminal_abandon_net():
    """F1. ``t: a -> ok`` and ``f: s -> done``, ``done`` terminal. When ``f`` completes
    first the terminal stop abandons ``t`` in flight: ``a`` and ``ok`` both end empty."""
    return _net("terminal-abandon", _t("t", ["a"], "ok"), _t("f", ["s"], "done"), terminal="done")


@needs_z3
@pytest.mark.parametrize("enumeration", [None, 0])
def test_a_quiescent_count_sees_the_action_a_terminal_stop_abandons(enumeration) -> None:
    def run(waived_by=None):
        return lp.verify(
            _terminal_abandon_net(),
            lp.quiescent_count(["a", "ok"], 1, 1, waived_by=waived_by),
            initial_marking={"a": 1, "s": 1},
            enumeration_max_classes=enumeration,
            timeout_ms=30_000,
        )

    result = run()
    assert result.verdict == "violated", result.report
    assert (
        "a terminal place stops the net without waiting for an action in flight (EXEC-042) "
        "and the property's lower bound counts a place one of them deposits into"
    ) in result.report
    # A lower bound the terminal waives needs no split: the terminal rest is excused.
    waived = run(waived_by=["done"])
    assert waived.verdict == "proven", waived.report


def _verify_conflict(net, initial, atomic):
    return lp.verify(
        net,
        lp.unreachable(["bad"]),
        initial_marking={**initial, "SEED": 1},
        mint_transitions=["MINT"],
        priority_semantics="conflict",
        assume_atomic_firing=atomic,
        timeout_ms=30_000,
    )


def _conflict_feeder_net():
    """F2 (a). ``t: a -> p``, ``H: p + b -> ok`` priority 10, ``L: b + inhibitor(a) -> bad``
    priority 0. While ``t`` is in flight ``a`` is empty and ``p`` not yet marked, so ``L``
    fires."""
    return _net(
        "conflict-feeder",
        _t("t", ["a"], "p"),
        _t("H", ["p", "b"], "ok", priority=10),
        _t("L", ["b"], "bad", inhibitor="a"),
        *_nu_pair(),
    )


@needs_z3
def test_conflict_priority_splits_the_feeder_of_a_pruner() -> None:
    result = _verify_conflict(_conflict_feeder_net(), {"a": 1, "b": 1}, False)
    assert result.verdict == "violated", result.report
    assert "In-flight actions (VER-004): t, H are verified in two steps" in result.report
    assert "conflict priority (NU-052) reads whether a pruning transition is enabled" in result.report
    atomic = _verify_conflict(_conflict_feeder_net(), {"a": 1, "b": 1}, True)
    assert atomic.verdict == "proven", atomic.report
    assert "ASSUMPTION: every firing is atomic" in atomic.report


def _long_action_net():
    """F3. ``t: a -> p`` ``deadline(20)``, ``h: p + b -> ok`` ``deadline(20)``,
    ``v: b -> bad`` ``delayed(60)``. An action of ``t`` still running at 60 ms lets
    ``v`` take ``b``."""
    return _net(
        "long-action",
        _t("t", ["a"], "p", timing=lp.deadline(20)),
        _t("h", ["p", "b"], "ok", timing=lp.deadline(20)),
        _t("v", ["b"], "bad", timing=lp.delayed(60)),
        *_nu_pair(),
    )


@needs_z3
def test_route_b_under_assume_no_reaping_names_its_instant_actions() -> None:
    def run(strict):
        return lp.verify(
            _long_action_net(),
            lp.unreachable(["bad"]),
            initial_marking={"a": 1, "b": 1, "SEED": 1},
            mint_transitions=["MINT"],
            assume_no_reaping=strict,
            timeout_ms=30_000,
        )

    strict = run(True)
    assert strict.verdict == "proven", strict.report
    assert (
        "ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its "
        "latest bound, and an action takes no time, i.e. an on-time executor with atomic firings."
    ) in strict.report
    assert "sound AND complete" not in strict.report, strict.report
    assert "exact only for an on-time executor whose actions take no time" in strict.report
    default = run(False)
    assert default.verdict == "violated", default.report


@needs_z3
def test_a_split_verdict_names_flush_and_a_restart() -> None:
    net, _, _ = _guard_net()
    result = lp.verify(net, lp.place_bound("busy", 1), initial_marking={"req": 2}, timeout_ms=30_000)
    assert result.verdict == "violated", result.report
    assert (
        "In-flight actions (VER-004): the outputs of a split transition are read as landing "
        "together when its action completes; an action that calls ctx.flush() publishes some of "
        "them earlier, which this verdict does not model."
    ) in result.report
    assert (
        "NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is "
        "still in flight (inflight:start marked). The Rust executor starts a transition again "
        "while its action runs; the Java and TypeScript executors never do, so on them this "
        "counterexample may be a false alarm."
    ) in result.report
    # A counterexample without a restart carries no such note: ``t: p + go -> p`` fires
    # once, and ``u: q + inhibitor(p) -> r`` fires while it is in flight.
    inhibited = _net(
        "inflight-inhibitor",
        _t("t", ["p", "go"], "p", priority=1),
        _t("u", ["q"], "r", inhibitor="p"),
    )
    result = lp.verify(inhibited, lp.unreachable(["r"]), initial_marking={"p": 1, "q": 1, "go": 1}, timeout_ms=30_000)
    assert result.verdict == "violated", result.report
    assert "NOTE (CONC-002)" not in result.report, result.report


@needs_z3
def test_the_open_net_verifier_names_flush_and_a_restart() -> None:
    net, _, _ = _guard_net()
    contract = lp.OpenNetContract.builder().initial_tokens("req", 2).expect("busy", 1, "busy").rest("req").build()
    result = lp.verify_open_net(net, contract, smt=False)
    assert result.verdict == "violated", result.report
    assert "an action that calls ctx.flush() publishes some of them earlier" in result.report
    assert "NOTE (CONC-002): the counterexample starts 'start' again" in result.report, result.report
