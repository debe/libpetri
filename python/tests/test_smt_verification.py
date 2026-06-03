"""VER-006: SMT verification environment-injection soundness.

Regression for the bug where ``verify`` vacuously reported safety bounds as
``proven`` on nets with environment places (env columns could only be consumed,
never produced, so the reachable set froze at the initial marking). The core fix
lives in the Rust verifier; here we exercise it through the Python binding and the
newly exposed ``environment_mode`` selector.

Gated on ``lp.HAS_Z3`` — the SMT path requires the wheel built with the ``z3``
feature (pyproject's maturin config enables ``full`` which includes it).
"""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _env_source_net():
    """env IN -> T -> OUT."""
    in_p = lp.Place("IN")
    out = lp.Place("OUT")
    net = (
        lp.Net("env-source")
        .transition(
            lp.Transition("T").input(lp.one(in_p)).output(lp.out(out)).action(lp.fork).build()
        )
        .build()
    )
    return in_p, out, net


@pytest.mark.parametrize("k", [0, 1, 5])
def test_always_available_injects_place_bound_violated(k):
    # AlwaysAvailable lets IN be injected without bound, so OUT grows without
    # bound: place_bound(OUT, k) is violated for every finite k.
    _in, out, net = _env_source_net()
    result = lp.verify(
        net,
        lp.place_bound(out, k),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report


def test_bounded_gates_by_multiplicity():
    # T2 needs EXACTLY 2 tokens from env IN per firing. bounded(1) starves it
    # (OUT stays 0 -> proven); always_available feeds it (OUT unbounded -> violated).
    # Also exercises the env-aware P-invariant: the closed-net law IN + 2*OUT = 0
    # must be discarded so OUT is not vacuously pinned.
    def build():
        in_p = lp.Place("IN")
        out = lp.Place("OUT")
        return out, (
            lp.Net("env-mult")
            .transition(
                lp.Transition("T2")
                .input(lp.exactly(2, in_p))
                .output(lp.out(out))
                .action(lp.fork)
                .build()
            )
            .build()
        )

    out, net = build()
    bounded1 = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.bounded(1),
        timeout_ms=15_000,
    )
    assert bounded1.verdict == "proven", bounded1.report

    out, net = build()
    always = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert always.verdict == "violated", always.report


def test_ignore_mode_with_env_places_downgrades_to_unknown():
    # Ignore mode does not model injection; a "proven" here would be vacuous.
    # The default (no environment_mode) is also Ignore, so both must be unknown.
    _in, out, net = _env_source_net()

    explicit = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        environment_mode=lp.ignore(),
        timeout_ms=15_000,
    )
    assert explicit.verdict == "unknown", explicit.report

    default = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        timeout_ms=15_000,
    )
    assert default.verdict == "unknown", default.report


def test_control_closed_net_place_bound_stays_sound():
    # The defect is env-specific: closed-net place_bound must stay sound.
    a = lp.Place("A")
    b = lp.Place("B")
    net = (
        lp.Net("closed-cycle")
        .transition(lp.Transition("AtoB").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .transition(lp.Transition("BtoA").input(lp.one(b)).output(lp.out(a)).action(lp.fork).build())
        .build()
    )

    # Note: verify() defaults the initial marking to empty; place_bound on an
    # all-empty closed net is trivially proven, which is still a sound result.
    safe = lp.verify(net, lp.place_bound(b, 1), timeout_ms=15_000)
    assert safe.verdict == "proven", safe.report
