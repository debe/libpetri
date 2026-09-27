"""MOD-051: ``verify_subnet`` keywords forwarded to each per-property verification,
``arrivals(k)`` on a port, the ν options, and ``SubnetDef.bind_actions``."""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _forwarder(action=lp.fork):
    inp = lp.Place("in")
    out = lp.Place("out")
    t = lp.Transition("forward").input(lp.one(inp)).output(lp.out(out))
    if action is not None:
        t = t.action(action)
    return (
        lp.SubnetDef("Forward")
        .transition(t.build())
        .input_port("in", inp)
        .output_port("out", out)
        .build()
    )


def _harness(*props):
    h = lp.VerificationHarness().input("in", lambda: "x")
    for p in props:
        h = h.property(p)
    return h


def _only(result):
    [entry] = result.property_results()
    return entry.result


def test_arrivals_bounds_what_a_port_receives():
    r = _only(lp.verify_subnet(_forwarder(), _harness(lp.place_bound("harness_out_out", 2)), environment_mode=lp.arrivals(2)))
    assert r.verdict == "proven", r.report
    r = _only(lp.verify_subnet(_forwarder(), _harness(lp.place_bound("harness_out_out", 1)), environment_mode=lp.arrivals(2)))
    assert r.verdict == "violated", r.report


def test_forwarded_keywords_reach_every_per_property_verifier():
    result = lp.verify_subnet(
        _forwarder(),
        _harness(lp.place_bound("harness_out_out", 2), lp.place_bound("harness_out_out", 3)),
        environment_mode=lp.arrivals(2),
        total_budget_ms=0,
    )
    for entry in result.property_results():
        assert entry.result.verdict == "unknown"
        assert entry.result.reason == "total verification budget of 0 ms exhausted during net preparation"


def test_a_forwarded_sink_changes_a_quiescence_verdict():
    stranded = _only(lp.verify_subnet(_forwarder(), _harness(lp.deadlock_free()), environment_mode=lp.arrivals(1)))
    assert stranded.verdict == "violated", stranded.report
    sunk = _only(
        lp.verify_subnet(
            _forwarder(),
            _harness(lp.deadlock_free()),
            environment_mode=lp.arrivals(1),
            sink_places=["harness_out_out"],
        )
    )
    assert sunk.verdict == "proven", sunk.report


def _fig13b():
    """PNID Fig. 13(b) as a subnet: ``a: R -> P1, OR`` mints a case, ``b: P1 -> B1,
    B2`` relays it, the joins ``c: B1, OR -> R`` / ``d: B2, OR -> R`` refund the
    input port ``R``. In BASE the relay reads as a fresh mint and the joins never
    fire, so ``B2`` stays within 2; with carrier ``P1`` in EXTENDED it passes 2."""
    r, p1, o, b1, b2 = (lp.Place(n) for n in ("R", "P1", "OR", "B1", "B2"))

    def join(name, branch):
        return (
            lp.Transition(name)
            .input(lp.one(branch))
            .input(lp.one(o))
            .match_spec(lp.match_spec([(branch, lambda m: m), (o, lambda m: m)]))
            .output(lp.out(r))
            .action(lp.fork)
            .build()
        )

    return (
        lp.SubnetDef("Fig13b")
        .transition(lp.Transition("a").input(lp.one(r)).output(lp.and_(p1, o)).action(lp.fork).build())
        .transition(lp.Transition("b").input(lp.one(p1)).output(lp.and_(b1, b2)).action(lp.fork).build())
        .transition(join("c", b1))
        .transition(join("d", b2))
        .input_port("R", r)
        .build()
    )


def test_nu_options_reach_the_per_property_verifier():
    """MOD-051 AC7: without the ν options the subnet is verified in BASE, a
    different model; the forwarded options change the verdict."""
    harness = lp.VerificationHarness().input("R", lambda: "r").property(lp.place_bound("sut/B2", 2))
    base = _only(lp.verify_subnet(_fig13b(), harness, environment_mode=lp.arrivals(2)))
    assert base.verdict == "proven", base.report
    harness = lp.VerificationHarness().input("R", lambda: "r").property(lp.place_bound("sut/B2", 2))
    extended = _only(
        lp.verify_subnet(
            _fig13b(),
            harness,
            environment_mode=lp.arrivals(2),
            fragment_mode="extended",
            carrier_places=["sut/P1"],
            nu_max_classes=2_000,
        )
    )
    assert extended.verdict == "violated", extended.report
    assert extended.route == "nu-scg"


def test_bind_actions_on_a_definition_returns_a_new_definition():
    """MOD-051 AC8: the bound definition verifies (its transition now produces);
    the receiver still carries passthrough and is refused (CORE-043)."""
    unbound = _forwarder(action=None)
    bound = unbound.bind_actions({"forward": lp.fork})
    assert bound is not unbound
    assert [p.name for p in bound.ports()] == [p.name for p in unbound.ports()]
    r = _only(lp.verify_subnet(bound, _harness(lp.place_bound("harness_out_out", 2)), environment_mode=lp.arrivals(2)))
    assert r.verdict == "proven", r.report
    with pytest.raises(lp.StructureError):
        lp.verify_subnet(unbound, _harness(lp.place_bound("harness_out_out", 2)))
