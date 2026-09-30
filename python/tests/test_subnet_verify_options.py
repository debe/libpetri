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


def _fig13b_mint():
    """``a: R -> P1, OR`` of :func:`_fig13b`."""
    r, p1, o = lp.Place("R"), lp.Place("P1"), lp.Place("OR")
    return lp.Transition("a").input(lp.one(r)).output(lp.and_(p1, o)).action(lp.fork).build()


def _fig13b():
    """PNID Fig. 13(b) as a subnet: ``a: R -> P1, OR`` mints a case, ``b: P1 -> B1,
    B2`` relays it, the joins ``c: B1, OR -> R`` / ``d: B2, OR -> R`` refund the
    input port ``R``, so ``B2`` passes 2. In BASE the relay is no declared mint
    (NU-010), so the net stays off the ν routes and the bound is not proven; with
    carrier ``P1`` in EXTENDED Route B finds the violation."""
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
        .transition(_fig13b_mint())
        .transition(lp.Transition("b").input(lp.one(p1)).output(lp.and_(b1, b2)).action(lp.fork).build())
        .transition(join("c", b1))
        .transition(join("d", b2))
        .input_port("R", r)
        .build()
    )


def test_nu_options_reach_the_per_property_verifier():
    """MOD-051 AC7: without the ν options the subnet is verified in BASE, a
    different model; the forwarded options change the verdict. Read as a fresh
    mint, the relay ``b`` would keep the joins from firing and prove the bound
    falsely; ``b`` is no declared mint (NU-010), so BASE does not read it so."""
    harness = lp.VerificationHarness().input("R", lambda: "r").property(lp.place_bound("sut/B2", 2))
    base = _only(
        lp.verify_subnet(_fig13b(), harness, environment_mode=lp.arrivals(2), mint_transitions=["sut/a"])
    )
    assert base.verdict != "proven", base.report
    harness = lp.VerificationHarness().input("R", lambda: "r").property(lp.place_bound("sut/B2", 2))
    extended = _only(
        lp.verify_subnet(
            _fig13b(),
            harness,
            environment_mode=lp.arrivals(2),
            fragment_mode="extended",
            carrier_places=["sut/P1"],
            mint_transitions=["sut/a"],
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


def _nu_options(**kw):
    return dict(
        environment_mode=lp.arrivals(2),
        fragment_mode="extended",
        carrier_places=["sut/P1"],
        nu_max_classes=2_000,
        **kw,
    )


def _b2_harness():
    return lp.VerificationHarness().input("R", lambda: "r").property(lp.place_bound("sut/B2", 2))


def test_a_subnet_transition_declares_its_sut_name_as_a_mint():
    """A ``Transition`` of the subnet is read as ``sut/<its name>``, the name the harness
    gives it. Before, it was passed as ``a``, which is no transition of the synthetic net."""
    a = _fig13b_mint()
    by_object = _only(lp.verify_subnet(_fig13b(), _b2_harness(), **_nu_options(mint_transitions=[a])))
    assert by_object.verdict == "violated", by_object.report
    assert by_object.route == "nu-scg"
    by_name = _only(lp.verify_subnet(_fig13b(), _b2_harness(), **_nu_options(mint_transitions=["sut/a"])))
    assert by_name.verdict == by_object.verdict
    unprefixed = _only(lp.verify_subnet(_fig13b(), _b2_harness(), **_nu_options(mint_transitions=["a"])))
    assert unprefixed.verdict == "unknown", unprefixed.report
    assert unprefixed.reason == "declared mint transition 'a' not in the net (NU-010)"


def test_a_single_string_is_not_a_list_of_mints():
    with pytest.raises(TypeError, match="not a single string"):
        lp.verify_subnet(_fig13b(), _b2_harness(), **_nu_options(mint_transitions="sut/a"))


def _reapable_forwarder():
    """``forward: in -> out`` with ``window(3, 5)``: a late executor reaps it and rests
    holding the input (TIME-013)."""
    inp, out = lp.Place("in"), lp.Place("out")
    t = lp.Transition("forward").input(lp.one(inp)).output(lp.out(out)).timing(lp.window(3, 5)).action(lp.fork).build()
    return lp.SubnetDef("Reapable").transition(t).input_port("in", inp).output_port("out", out).build()


def test_assume_no_reaping_reaches_the_per_property_verifier():
    def run(**kw):
        return _only(
            lp.verify_subnet(
                _reapable_forwarder(),
                _harness(lp.deadlock_free()),
                environment_mode=lp.arrivals(1),
                sink_places=["harness_out_out"],
                **kw,
            )
        )

    reaped = run()
    assert reaped.verdict == "violated", reaped.report
    strict = run(assume_no_reaping=True)
    assert strict.verdict == "proven", strict.report
    assert "ASSUMPTION: no transition is reaped (the assume-no-reaping option)" in strict.report


def _guard_subnet():
    """``start: in + inhibitor(busy) -> busy``: atomically ``busy`` never holds two
    tokens; split, the second start runs while the first is in flight (VER-004)."""
    inp, busy = lp.Place("in"), lp.Place("busy")
    t = lp.Transition("start").input(lp.one(inp)).inhibitor(lp.inhibitor(busy)).output(lp.out(busy)).action(lp.fork).build()
    return lp.SubnetDef("Guard").transition(t).input_port("in", inp).build()


def test_assume_atomic_firing_reaches_the_per_property_verifier():
    def run(**kw):
        return _only(
            lp.verify_subnet(
                _guard_subnet(), _harness(lp.place_bound("sut/busy", 1)), environment_mode=lp.arrivals(2), **kw
            )
        )

    split = run()
    assert split.verdict == "violated", split.report
    assert "In-flight actions (VER-004): sut/start is verified in two steps" in split.report
    atomic = run(assume_atomic_firing=True)
    assert atomic.verdict == "proven", atomic.report
    assert "ASSUMPTION: every firing is atomic (the assume-atomic-firing option)" in atomic.report
