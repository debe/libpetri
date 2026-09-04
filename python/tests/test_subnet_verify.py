"""MOD-051: verifying a subnet in isolation through the Python binding.

Python had no coverage of ``verify_subnet`` at all, and the empty Python column
for MOD-051 in ``spec/coverage-matrix.md`` recorded that. These tests close it,
and pin the behaviour that was broken until the harness carried an environment
mode: ``verify_subnet`` allocates a synthetic environment place per input port,
so under ``ignore()`` VER-006 downgrades every proof to ``unknown`` and a subnet
with an input port can never be proven.

Gated on ``lp.HAS_Z3`` like the other SMT tests.
"""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _gated_subnet():
    """A subnet whose output is gated on a permit that is never seeded.

    ``accept`` needs both an inbound request and a ``slots`` permit. The harness
    seeds no initial marking, so ``slots`` stays empty and ``accepted`` is
    unreachable however much the environment injects into the input port. That
    makes ``place_bound(accepted, 0)`` provable, and provable *only* when
    injection is actually modelled.
    """
    request = lp.Place("REQUEST")
    slots = lp.Place("SLOTS")
    accepted = lp.Place("ACCEPTED")

    def accept(ctx: lp.TransitionContext) -> None:
        ctx.output("ACCEPTED", ctx.input("REQUEST"))

    return (
        lp.SubnetDef("Gated")
        .transition(
            lp.Transition("accept")
            .input(lp.one(request))
            .input(lp.one(slots))
            .output(lp.out(accepted))
            .action(accept)
            .build()
        )
        .input_port("request", request)
        .output_port("accepted", accepted)
        .build()
    )


def test_verify_subnet_proves_the_gated_bound_by_default() -> None:
    """The default environment mode is ``always_available()``, so the bound is
    proven: it holds for any environment, not merely for one that stays quiet."""
    subnet = _gated_subnet()

    harness = (
        lp.VerificationHarness()
        .input("request", lambda: {"v": 1})
        .property(lp.place_bound("harness_out_accepted", 0))
    )

    result = lp.verify_subnet(subnet, harness)

    results = result.property_results()
    assert len(results) == 1
    verdict = results[0].result
    assert verdict.verdict == "proven", verdict.report


def test_verify_subnet_under_ignore_cannot_prove() -> None:
    """VER-006's vacuity guard: with injection unmodelled the same query is
    refused rather than certified. This is what the default used to do."""
    subnet = _gated_subnet()

    harness = (
        lp.VerificationHarness()
        .input("request", lambda: {"v": 1})
        .property(lp.place_bound("harness_out_accepted", 0))
    )

    result = lp.verify_subnet(subnet, harness, environment_mode=lp.ignore())

    verdict = result.property_results()[0].result
    assert verdict.verdict == "unknown", verdict.report
    assert "not modeled" in verdict.report or "vacuous" in verdict.report


def test_verify_subnet_accepts_a_bounded_environment() -> None:
    """``bounded(k)`` is the mode that expresses MOD-051 AC3's "the harness's
    input generators bound the input behavior"."""
    subnet = _gated_subnet()

    harness = (
        lp.VerificationHarness()
        .input("request", lambda: {"v": 1})
        .property(lp.place_bound("harness_out_accepted", 0))
    )

    result = lp.verify_subnet(subnet, harness, environment_mode=lp.bounded(1))

    verdict = result.property_results()[0].result
    assert verdict.verdict == "proven", verdict.report
