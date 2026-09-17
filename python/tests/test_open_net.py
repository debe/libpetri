"""VER-022 open-net verification against a contract.

Mirrors ``typescript/tests/verification/open-net.test.ts`` through the binding. The
subnet under test is a node gadget in the shape n8n-libpetri compiles: one input
edge carrying data or empty, one output with two outgoing edges, a shared budget
and a halt::

    X/start: one(X/in) one(_budget) one(X/idle) inhibitor(_halt) -> X/running
    X/run:   one(X/running) -> and( xor( and( xor(and(e1/data, e2/data), and(e1/empty, e2/empty)), X/routed ),
                                         and(_halt, _budget) ),
                                    X/idle )
    X/done:  one(X/routed) -> and(_budget, X/done)
    X/skip:  one(X/in_empty) inhibitor(_halt) -> and(e1/empty, e2/empty, X/skipped)

The report is the Rust one, which is byte-identical to the TypeScript reference's.
"""

import math

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

needs_z3 = pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable")

P = {
    key: lp.Place(name)
    for key, name in {
        "in": "X/in", "in_empty": "X/in_empty", "idle": "X/idle", "budget": "_budget", "halt": "_halt",
        "running": "X/running", "routed": "X/routed", "done": "X/done", "skipped": "X/skipped",
        "e1_data": "e1/data", "e1_empty": "e1/empty", "e2_data": "e2/data", "e2_empty": "e2/empty",
        "trace": "X/trace",
    }.items()
}


def _gadget(*, skip_forgets_e2=False, leak=False, spin=False, no_refund=False):
    def t(name):
        return lp.Transition(name).action(lp.fork)

    start = (
        t("X/start").input(lp.one(P["in"])).input(lp.one(P["budget"])).input(lp.one(P["idle"]))
        .inhibitor(lp.inhibitor(P["halt"])).output(lp.out(P["running"])).build()
    )
    routes = lp.xor(lp.and_(P["e1_data"], P["e2_data"]), lp.and_(P["e1_empty"], P["e2_empty"]))
    success = lp.and_(routes, P["routed"], P["trace"]) if leak else lp.and_(routes, P["routed"])
    run = (
        t("X/run").input(lp.one(P["running"]))
        .output(lp.and_(lp.xor(success, lp.and_(P["halt"], P["budget"])), P["idle"])).build()
    )
    done = (
        t("X/done").input(lp.one(P["routed"]))
        .output(lp.out(P["done"]) if no_refund else lp.and_(P["budget"], P["done"])).build()
    )
    skip = (
        t("X/skip").input(lp.one(P["in_empty"])).inhibitor(lp.inhibitor(P["halt"]))
        .output(
            lp.and_(P["e1_empty"], P["skipped"]) if skip_forgets_e2
            else lp.and_(P["e1_empty"], P["e2_empty"], P["skipped"])
        )
        .build()
    )
    net = lp.Net("X").transition(start).transition(run).transition(done).transition(skip)
    if spin:
        net = net.transition(t("X/spin").input(lp.one(P["running"])).output(lp.out(P["running"])).build())
    return net.build()


def _contract(*, terminal=True, budget=1, termination=True):
    """The node contract as n8n-libpetri states it, for a budget of `budget`."""
    builder = (
        lp.OpenNetContract.builder()
        .initial_marking({P["idle"]: 1, P["budget"]: budget})
        .arrive(1, P["in"], P["in_empty"])
        .arrive_at_most(1, P["halt"])
        .expect("e1", 1, P["e1_data"], P["e1_empty"])
        .expect("e2", 1, P["e2_data"], P["e2_empty"])
        .expect("idle", 1, P["idle"])
        .expect("budget", budget, P["budget"])
        .expect("history", 1, P["done"], P["skipped"])
    )
    if terminal:
        builder.terminal(P["halt"], P["in"], P["in_empty"])
    if not termination:
        builder.require_termination(False)
    return builder.build()


# ---------- the contract ----------------------------------------------------


def test_the_contract_is_validated_as_it_is_built():
    with pytest.raises(ValueError, match="duplicate clause name 'a'"):
        lp.OpenNetContract.builder().expect("a", 1, "p").expect("a", 1, "q")
    with pytest.raises(ValueError, match="a clause needs a name"):
        lp.OpenNetContract.builder().expect("", 1, "p")
    with pytest.raises(ValueError, match="names no place"):
        lp.OpenNetContract.builder().arrive(1)
    with pytest.raises(ValueError, match="0 <= min <= max"):
        lp.OpenNetContract.builder().expect_between("a", 2, 1, "p")
    # An arrival bound is finite: it is the runtime cap and the width of the claim.
    with pytest.raises(ValueError, match="so it is finite"):
        lp.OpenNetContract.builder().arrive_between(0, math.inf, "p")
    # A refused step leaves what was declared before it in place.
    builder = lp.OpenNetContract.builder().expect("kept", 1, "p")
    with pytest.raises(ValueError):
        builder.expect("kept", 1, "q")
    assert builder.build().places() == ["p"]


def test_the_contract_describes_itself_the_way_the_report_prints_it():
    contract = _contract()
    assert contract.requires_termination is True
    assert contract.places()[:4] == ["X/idle", "_budget", "X/in", "X/in_empty"]
    assert "  Terminal: when _halt: X/in, X/in_empty" in contract.describe()
    unbounded = lp.OpenNetContract.builder().expect_between("any", 1, math.inf, "p").build()
    assert "  At quiescence: any = at least 1 across {p}" in unbounded.describe()


def test_an_initial_marking_keeps_its_dict_order_into_the_port_trace():
    # zeta before alpha, as the dict lists them: not code-point order.
    net = lp.Net("N").transition(
        lp.Transition("take").action(lp.fork).input(lp.one(lp.Place("zeta"))).input(lp.one(lp.Place("alpha")))
        .output(lp.out(lp.Place("done"))).build()
    ).build()
    contract = lp.OpenNetContract.builder().initial_marking({"zeta": 1, "alpha": 1}).expect("done", 2, "done").build()
    assert contract.places() == ["zeta", "alpha", "done"]
    r = lp.verify_open_net(net, contract, smt=False)
    assert r.verdict == "violated", r.report
    assert r.violations[0].port_trace[0].changes == [("zeta", -1), ("alpha", -1), ("done", 1)]
    assert "\n      1. take  zeta -1, alpha -1, done +1\n" in r.report
    assert list(r.closed_marking.items()) == [("zeta", 1), ("alpha", 1)]


# ---------- graph route -----------------------------------------------------


def test_graph_route_proves_a_well_formed_gadget_halts_included():
    r = lp.verify_open_net(_gadget(), _contract())
    assert r.verdict == "proven", r.report
    assert r.route == "enumeration"
    assert r.graph_complete is True
    assert r.violations == []
    assert r.inductive_invariant is None


def test_graph_route_names_the_edge_a_broken_skip_leaves_with_its_port_trace():
    r = lp.verify_open_net(_gadget(skip_forgets_e2=True), _contract())
    assert r.verdict == "violated", r.report
    assert [v.subject for v in r.violations] == ["e2"]
    e2 = r.violations[0]
    assert e2.kind == "clause"
    assert e2.detail == "exactly 1 across {e2/data, e2/empty} at quiescence, found 0"
    assert e2.confirmed is True
    # The port trace ends at the quiescent marking: the arrival, then the skip that
    # wrote e1's empty and nothing for e2.
    steps = [(s.transition, s.environment) for s in e2.port_trace]
    assert steps[0] == ("env:arrive[0]:X/in_empty", "arrival")
    assert ("X/skip", None) in steps
    skip = next(s for s in e2.port_trace if s.transition == "X/skip")
    assert ("e1/empty", 1) in skip.changes
    assert all(place != "e2/empty" for place, _ in skip.changes)
    assert e2.markings[-1].get("e2/empty", 0) == 0


def test_graph_route_reports_a_run_that_never_comes_to_rest_as_a_lasso():
    r = lp.verify_open_net(_gadget(spin=True), _contract())
    assert [v.kind for v in r.violations] == ["termination"], r.report
    v = r.violations[0]
    assert v.cycle_start is not None
    assert v.transitions[v.cycle_start:] == ["X/spin"]
    assert v.markings[v.cycle_start] == v.markings[-1]
    assert "Firing sequence: env:arrive[0]:X/in, X/start, then repeating X/spin" in r.report

    waived = lp.verify_open_net(_gadget(spin=True), _contract(termination=False))
    assert waived.verdict == "proven", waived.report


def test_a_graph_that_does_not_close_is_unknown_without_the_smt_route_and_says_why():
    r = lp.verify_open_net(_gadget(), _contract(), max_classes=3, smt=False)
    assert r.verdict == "unknown"
    assert r.reason == "the state-class graph did not close within 3 classes, and the SMT route is disabled"


# ---------- SMT route -------------------------------------------------------


@needs_z3
def test_smt_route_proves_the_gadget_and_decides_termination_by_a_firing_bound():
    r = lp.verify_open_net(_gadget(), _contract(), max_classes=0)
    assert r.verdict == "proven", r.report
    assert r.route == "smt"
    assert "=== SMT route ===" in r.report
    assert "State-class graph: skipped (class budget 0)" in r.report
    assert "  [termination] Firing bound (VER-019): every run has at most 5 firings" in r.report
    # The proof evidence is the conjunction of the parts' invariants, not nothing.
    assert r.inductive_invariant is not None and "[stranding]" in r.inductive_invariant


@needs_z3
def test_smt_route_decides_a_lower_bound_above_1_through_the_quiescent_count():
    r = lp.verify_open_net(_gadget(), _contract(budget=2), max_classes=0)
    assert r.verdict == "proven", r.report
    assert (
        "[budget] Quiescent count: exactly 2 across {_budget}; lower bound waived while {_halt} is marked: proven"
        in r.report
    )


@needs_z3
def test_smt_route_names_the_broken_edge_too():
    r = lp.verify_open_net(_gadget(skip_forgets_e2=True), _contract(termination=False), max_classes=0)
    assert r.verdict == "violated", r.report
    assert r.route == "smt"
    assert "e2" in [v.subject for v in r.violations]


@needs_z3
def test_smt_route_names_the_stranded_place_with_the_same_widening_the_graph_applies():
    r = lp.verify_open_net(_gadget(leak=True), _contract(termination=False), max_classes=0)
    assert r.verdict == "violated", r.report
    assert [(v.kind, v.subject) for v in r.violations] == [("stranded", "X/trace")]
    assert "X/trace holds a token at quiescence" in r.violations[0].detail


@needs_z3
def test_smt_route_skips_a_count_clause_no_marking_can_fail_and_says_so():
    anything = (
        lp.OpenNetContract.builder()
        .initial_marking({P["idle"]: 1, P["budget"]: 1})
        .arrive(1, P["in"], P["in_empty"])
        .arrive_at_most(1, P["halt"])
        .expect("e1", 1, P["e1_data"], P["e1_empty"])
        .expect("e2", 1, P["e2_data"], P["e2_empty"])
        .expect("idle", 1, P["idle"])
        .expect("budget", 1, P["budget"])
        # Between 0 and infinity across the history places: every marking satisfies it.
        .expect_between("history", 0, math.inf, P["done"], P["skipped"])
        .terminal(P["halt"], P["in"], P["in_empty"])
        .require_termination(False)
        .build()
    )
    r = lp.verify_open_net(_gadget(), anything, max_classes=0)
    assert r.verdict == "proven", r.report
    assert "[history] any number across {X/done, X/skipped} at quiescence: proven (no query needed)" in r.report


@needs_z3
def test_smt_route_leaves_termination_undecided_when_no_firing_bound_exists():
    r = lp.verify_open_net(_gadget(spin=True), _contract(), max_classes=0)
    assert r.verdict == "unknown", r.report
    assert "termination: no firing bound: the marking equation lets X/spin repeat" in r.reason


# ---------- a ν-net skips the name-blind graph (VER-022 AC9) -----------------


def _two_mints():
    """Two independent mints give ``COL_A`` and ``COL_B`` different names, so the ν-join can
    never fire and both strand. The state-class graph ignores the match, fires the join anyway,
    and used to report this contract proven by enumeration — a false proof."""
    seed_a, seed_b = lp.Place("SEED_A"), lp.Place("SEED_B")
    col_a, col_b, out = lp.Place("COL_A"), lp.Place("COL_B"), lp.Place("OUT")
    mint_a = lp.Transition("MINT_A").input(lp.one(seed_a)).output(lp.out(col_a)).action(lp.fork).build()
    mint_b = lp.Transition("MINT_B").input(lp.one(seed_b)).output(lp.out(col_b)).action(lp.fork).build()
    join = (
        lp.Transition("JOIN")
        .input(lp.one(col_a))
        .input(lp.one(col_b))
        .match_spec(lp.match_spec([(col_a, lambda m: m), (col_b, lambda m: m)]))
        .output(lp.out(out))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("twoMints").transition(mint_a).transition(mint_b).transition(join).build()
    contract = lp.OpenNetContract.builder().initial_marking({seed_a: 1, seed_b: 1}).rest(out).build()
    return net, contract


@needs_z3
def test_a_nu_net_is_not_proven_by_the_name_blind_graph():
    net, contract = _two_mints()
    r = lp.verify_open_net(net, contract)
    assert r.verdict == "violated", r.report
    assert r.route == "smt"
    assert r.class_count == 0
    assert (
        "State-class graph: skipped (the closed net declares match (ν-join) transitions, which the graph does not model)"
        in r.report
    )


def test_a_nu_net_with_the_smt_route_disabled_is_unknown_and_says_why():
    net, contract = _two_mints()
    r = lp.verify_open_net(net, contract, smt=False)
    assert r.verdict == "unknown"
    assert "the state-class graph was skipped: the closed net declares match (ν-join) transitions" in r.reason
