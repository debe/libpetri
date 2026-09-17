"""VER-018 state-equation phase, VER-019 firing bound and VER-002 QuiescentCount.

Mirrors ``typescript/tests/verification/state-equation-phase.test.ts`` and
``quiescent-count.test.ts`` through the binding, which rides the Rust pipeline.
Every solver-backed call opts out of the VER-017 enumeration route: these nets'
graphs close, so it would decide them before any phase ran.
"""

import math
from typing import TypedDict

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

needs_z3 = pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable")


class _Solver(TypedDict):
    """Spread into ``verify``; a TypedDict lets a type checker match each key to its keyword."""

    enumeration_max_classes: int
    timeout_ms: int


SOLVER: _Solver = {"enumeration_max_classes": 0, "timeout_ms": 30_000}


def _t(name):
    return lp.Transition(name).action(lp.fork)


def _join_with_skip():
    """The join of a compiled workflow: `route` sends data down one arm and an empty
    marker down the other; `merge_start` takes both readies with ``all(hasdata)``,
    `merge_skip` both readies under ``inhibitor(hasdata)``. The marking equation
    admits the skip after a data token arrived, stranding `hasdata`; only the
    inhibitor rules that out."""
    p = {n: lp.Place(n) for n in (
        "start", "aData", "aEmpty", "bData", "bEmpty", "hasdata", "ready0", "ready1", "done", "skipped",
    )}
    net = (
        lp.Net("joinWithSkip")
        .transition(
            _t("route").input(lp.one(p["start"]))
            .output(lp.xor(lp.and_(p["aData"], p["bEmpty"]), lp.and_(p["aEmpty"], p["bData"]))).build()
        )
        .transition(_t("armAData").input(lp.one(p["aData"])).output(lp.and_(p["hasdata"], p["ready0"])).build())
        .transition(_t("armAEmpty").input(lp.one(p["aEmpty"])).output(lp.out(p["ready0"])).build())
        .transition(_t("armBData").input(lp.one(p["bData"])).output(lp.and_(p["hasdata"], p["ready1"])).build())
        .transition(_t("armBEmpty").input(lp.one(p["bEmpty"])).output(lp.out(p["ready1"])).build())
        .transition(
            _t("mergeStart").input(lp.one(p["ready0"])).input(lp.one(p["ready1"]))
            .input(lp.all_tokens(p["hasdata"])).output(lp.out(p["done"])).build()
        )
        .transition(
            _t("mergeSkip").input(lp.one(p["ready0"])).input(lp.one(p["ready1"]))
            .inhibitor(lp.inhibitor(p["hasdata"])).output(lp.out(p["skipped"])).build()
        )
        .build()
    )
    return p, net, {"start": 1}


def _queue_and_bundle(n, cancellable=False):
    """A producer fires up to `n` times into `q` until the signal arrives, and the
    bundler takes ``all(q)`` with the signal. With `cancellable` the signal may
    never come, stranding the queue."""
    p = {name: lp.Place(name) for name in ("budget", "q", "src", "s", "out", "cancelled")}
    net = (
        lp.Net(f"queue{n}")
        .transition(
            _t("produce").input(lp.one(p["budget"])).inhibitor(lp.inhibitor(p["s"]))
            .inhibitor(lp.inhibitor(p["out"])).output(lp.out(p["q"])).build()
        )
        .transition(_t("signal").input(lp.one(p["src"])).output(lp.out(p["s"])).build())
        .transition(
            _t("bundle").input(lp.all_tokens(p["q"])).input(lp.one(p["s"])).output(lp.out(p["out"])).build()
        )
        .transition(
            _t("bundleEmpty").input(lp.one(p["s"])).inhibitor(lp.inhibitor(p["q"])).output(lp.out(p["out"])).build()
        )
    )
    if cancellable:
        net = net.transition(_t("cancel").input(lp.one(p["src"])).output(lp.out(p["cancelled"])).build())
    return p, net.build(), {"budget": n, "src": 1}


# ---------- VER-018 state-equation phase ------------------------------------


@needs_z3
def test_state_equation_phase_proves_the_join_with_the_inequality_the_inhibitor_makes_inductive():
    p, net, m0 = _join_with_skip()
    result = lp.verify(net, lp.deadlock_free(), initial_marking=m0, sink_places=[p["done"], p["skipped"]], **SOLVER)
    assert result.verdict == "proven", result.report
    assert result.method == "state-equation"
    assert "Refinement (inductive): hasdata <= ready0 + ready1" in result.report
    assert "Certificate check: PASSED (init, consecution, safety)" in result.report
    assert result.discovered_invariants == ["hasdata <= ready0 + ready1"]


@needs_z3
def test_both_phases_off_keep_the_verdict_the_fixpoint_query_reaches():
    p, net, m0 = _join_with_skip()
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking=m0,
        sink_places=[p["done"], p["skipped"]],
        state_equation_phase=False,
        firing_bound=False,
        **SOLVER,
    )
    assert result.verdict == "proven", result.report
    assert result.method == "IC3/PDR"
    assert "VER-018" not in result.report


@needs_z3
def test_state_equation_phase_finds_the_queue_the_cancelled_signal_strands():
    p, net, m0 = _queue_and_bundle(3, cancellable=True)
    result = lp.verify(
        net, lp.deadlock_free(), initial_marking=m0, sink_places=[p["out"], p["budget"], p["cancelled"]], **SOLVER
    )
    assert result.verdict == "violated", result.report
    assert result.counterexample_confirmed is True
    assert result.counterexample_transitions[-1] == "cancel"
    assert result.counterexample_trace[-1].get("q", 0) > 0


def test_encode_smt_scripts_reports_the_phase_query_and_none_when_the_phase_is_off():
    p, net, m0 = _join_with_skip()
    sinks = [p["done"], p["skipped"]]
    on = lp.encode_smt_scripts(net, lp.deadlock_free(), initial_marking=m0, sink_places=sinks)
    query = on["state_equation"]
    assert isinstance(query, str) and "; State-equation phase (VER-018)" in query
    off = lp.encode_smt_scripts(
        net, lp.deadlock_free(), initial_marking=m0, sink_places=sinks, state_equation_phase=False
    )
    assert off["state_equation"] is None
    # The phase leaves the HORN query alone; only the VER-016 `state_equation` keyword shapes it.
    assert off["horn"] == on["horn"]


# ---------- VER-019 firing bound --------------------------------------------


@needs_z3
def test_firing_bound_proves_the_queue_by_a_bounded_model_check():
    p, net, m0 = _queue_and_bundle(3)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking=m0,
        sink_places=[p["out"], p["budget"]],
        state_equation_phase=False,
        **SOLVER,
    )
    assert result.verdict == "proven", result.report
    assert result.method == "bounded-model-check"
    assert "Bound: 5 firings" in result.report
    assert "Certificate check: not applicable (bounded model check to the firing bound)" in result.report


@needs_z3
def test_firing_bound_names_what_an_unbounded_net_repeats_and_leaves_it_to_the_fixpoint_query():
    places = [lp.Place(f"p{i}") for i in range(3)]
    net = lp.Net("ring")
    for i in range(3):
        net = net.transition(_t(f"t{i}").input(lp.one(places[i])).output(lp.out(places[(i + 1) % 3])).build())
    result = lp.verify(
        net.build(),
        lp.place_bound(places[0], 1),
        initial_marking={"p0": 1},
        linear_bound=False,
        state_equation_phase=False,
        **SOLVER,
    )
    assert result.verdict == "proven", result.report
    assert "no firing bound — the marking equation lets t0, t1, t2 repeat; not attempted" in result.report
    assert result.method == "IC3/PDR"


# ---------- VER-002 QuiescentCount ------------------------------------------


def _jobs_net(*, refund=True, abort=False):
    """Two jobs share a budget of two: `start` takes a unit, `finish` refunds it. With
    `abort` a running job may stop the run instead, keeping its unit; `start` is
    inhibited by `halt`."""
    budget, done, halt, jobs, running = (lp.Place(n) for n in ("budget", "done", "halt", "jobs", "running"))
    net = (
        lp.Net("jobs")
        .transition(
            _t("start").input(lp.one(jobs)).input(lp.one(budget)).inhibitor(lp.inhibitor(halt))
            .output(lp.out(running)).build()
        )
        .transition(
            _t("finish").input(lp.one(running))
            .output(lp.and_(budget, done) if refund else lp.out(done)).build()
        )
    )
    if abort:
        net = net.transition(_t("abort").input(lp.one(running)).output(lp.out(halt)).build())
    return net.build()


JOBS_M0 = {"jobs": 2, "budget": 2}


def test_quiescent_count_validates_its_bounds_and_describes_itself():
    with pytest.raises(ValueError, match=r"0 <= min <= max"):
        lp.quiescent_count(["budget"], 2, 1)
    with pytest.raises(ValueError):
        lp.quiescent_count(["budget"], -1, 1)
    with pytest.raises(ValueError):
        lp.quiescent_count(["budget"], 0, 1.5)
    # math.inf is a max, never a min.
    with pytest.raises(ValueError):
        lp.quiescent_count(["budget"], math.inf, math.inf)  # pyright: ignore[reportArgumentType]
    assert (
        lp.quiescent_count([lp.Place("budget")], 2, 2, waived_by=[lp.Place("halt")]).description()
        == "Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked"
    )
    assert (
        lp.quiescent_count(["budget", "done"], 1, math.inf).description()
        == "Quiescent count: at least 1 across {budget, done}"
    )
    assert lp.quiescent_count(["budget"], 1, float("inf")).description() == "Quiescent count: at least 1 across {budget}"


def test_quiescent_count_on_the_enumeration_route_proves_a_refund_and_finds_a_kept_unit():
    count = lp.quiescent_count(["budget"], 2, 2, waived_by=["halt"])
    proven = lp.verify(_jobs_net(), count, initial_marking=JOBS_M0)
    assert proven.verdict == "proven", proven.report
    assert proven.route == "enumeration"

    kept = lp.verify(_jobs_net(refund=False), count, initial_marking=JOBS_M0)
    assert kept.verdict == "violated", kept.report
    assert kept.counterexample_trace[-1].get("budget", 0) < 2


def test_quiescent_count_waives_the_lower_bound_while_the_marker_is_marked_and_only_then():
    waived = lp.verify(
        _jobs_net(abort=True), lp.quiescent_count(["budget"], 2, 2, waived_by=["halt"]), initial_marking=JOBS_M0
    )
    assert waived.verdict == "proven", waived.report
    strict = lp.verify(_jobs_net(abort=True), lp.quiescent_count(["budget"], 2, 2), initial_marking=JOBS_M0)
    assert strict.verdict == "violated", strict.report
    assert strict.counterexample_trace[-1].get("halt", 0) > 0


@needs_z3
def test_quiescent_count_is_decided_by_the_state_equation_phase_proof_and_witness():
    count = lp.quiescent_count(["budget"], 2, 2, waived_by=["halt"])
    proven = lp.verify(_jobs_net(abort=True), count, initial_marking=JOBS_M0, **SOLVER)
    assert proven.verdict == "proven", proven.report
    assert proven.method == "state-equation"

    kept = lp.verify(_jobs_net(refund=False), count, initial_marking=JOBS_M0, **SOLVER)
    assert kept.verdict == "violated", kept.report
    assert kept.counterexample_confirmed is True


@needs_z3
def test_quiescent_count_is_decided_by_ic3_too_when_the_phases_are_off():
    count = lp.quiescent_count(["budget"], 2, 2, waived_by=["halt"])

    def verify(net):
        return lp.verify(
            net, count, initial_marking=JOBS_M0, state_equation_phase=False, firing_bound=False, **SOLVER
        )

    proven = verify(_jobs_net(abort=True))
    assert proven.verdict == "proven", proven.report
    assert proven.method == "IC3/PDR"

    kept = verify(_jobs_net(refund=False))
    assert kept.verdict == "violated", kept.report


def test_quiescent_count_over_a_place_the_net_does_not_declare_is_refused():
    result = lp.verify(_jobs_net(), lp.quiescent_count(["ghost"], 1, 1), initial_marking=JOBS_M0)
    assert result.verdict == "unknown"
    assert "'ghost'" in str(result.reason)
