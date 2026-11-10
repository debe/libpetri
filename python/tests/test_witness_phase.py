"""VER-025 bounded witness phase through the binding.

The phase is the Rust verifier's; these tests pin what the binding carries: the
``witness_depth`` keyword of ``verify`` and ``encode_smt_scripts``, its default of 8,
``0`` disabling the phase, the error for a negative depth, the ``"witness"`` script,
and the report lines of the two shared fixtures on ``envBoundedPair``
(``env-bounded-witness-violated`` and ``env-bounded-deep-witness-violated``).
"""

import inspect

import libpetri as lp
import pytest

from test_verdict_parity import _net

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

needs_z3 = pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable")

HEADER = "  Bounded witness phase (VER-025):\n"
NO_RUN_8 = HEADER + "    Status: no run of at most 8 steps reaches a violation (not a proof)\n"
FIXPOINT_VIOLATED = "Result: property violated (Spacer UNSAT"


def _verify(bound, **kw):
    """``envBoundedPair``: ``e`` injected under ``bounded(2)``, ``t: e -> p1``. ``p1``
    exceeds ``bound`` after ``bound + 1`` injections and as many firings of ``t``."""
    net, marking, env = _net("envBoundedPair")
    return lp.verify(net, lp.place_bound("p1", bound), initial_marking=marking, timeout_ms=30_000, **env, **kw)


def _scripts(**kw):
    net, marking, env = _net("envBoundedPair")
    return lp.encode_smt_scripts(net, lp.place_bound("p1", 1), initial_marking=marking, **env, **kw)


def _without_elapsed(report):
    return "\n".join(line for line in report.split("\n") if not line.startswith("Elapsed: "))


def test_the_depth_defaults_to_8():
    assert inspect.signature(lp.verify).parameters["witness_depth"].default == 8
    assert inspect.signature(lp.encode_smt_scripts).parameters["witness_depth"].default == 8


@needs_z3
def test_the_phase_is_on_by_default_and_reports_the_run_with_two_injections():
    result = _verify(1)
    assert result.verdict == "violated", result.report
    assert result.counterexample_confirmed is True, result.report
    assert HEADER + "    Status: a run of 4 steps reaches a violation (replayed; depth 8)\n" in result.report
    assert sorted(result.counterexample_transitions) == ["inject(e)", "inject(e)", "t", "t"], result.report
    assert len(result.counterexample_trace) == 5, result.report
    # The phase's run is the verdict: the fixpoint query was never sent.
    assert "Spacer" not in result.report, result.report


@needs_z3
def test_a_violation_past_the_depth_is_left_to_the_fixpoint_query():
    result = _verify(4)
    assert result.verdict == "violated", result.report
    assert NO_RUN_8 + FIXPOINT_VIOLATED in result.report, result.report
    assert result.counterexample_confirmed is True, result.report
    assert len(result.counterexample_transitions) == 10, result.report

    # A larger depth asks for the run itself.
    deeper = _verify(4, witness_depth=10)
    assert deeper.verdict == "violated", deeper.report
    assert HEADER + "    Status: a run of 10 steps reaches a violation (replayed; depth 10)\n" in deeper.report
    assert "Spacer" not in deeper.report, deeper.report


@needs_z3
def test_witness_depth_zero_is_the_pipeline_without_the_phase():
    off = _verify(1, witness_depth=0)
    assert off.verdict == "violated", off.report
    assert "VER-025" not in off.report, off.report
    assert FIXPOINT_VIOLATED in off.report, off.report

    # Where the phase finds no run, it adds its two report lines and nothing else.
    off, on = _verify(4, witness_depth=0), _verify(4)
    assert "VER-025" not in off.report, off.report
    assert (off.verdict, off.route) == (on.verdict, on.route)
    assert off.counterexample_transitions == on.counterexample_transitions
    assert _without_elapsed(off.report) == _without_elapsed(on.report.replace(NO_RUN_8, ""))


def test_a_negative_witness_depth_is_an_argument_error():
    net, marking, env = _net("envBoundedPair")
    prop = lp.place_bound("p1", 1)
    with pytest.raises(ValueError, match=r"^witness_depth must be non-negative, got -1$"):
        lp.verify(net, prop, initial_marking=marking, witness_depth=-1, **env)
    with pytest.raises(ValueError, match=r"^witness_depth must be non-negative, got -3$"):
        lp.encode_smt_scripts(net, prop, initial_marking=marking, witness_depth=-3, **env)


def test_encode_smt_scripts_reports_the_witness_query_at_the_depth():
    script = _scripts()["witness"]
    assert script.startswith("; Bounded run (VER-019): 8 steps of the exact step relation from M0, idle\n")
    # One transition and one injection: selectors 0 and 1, idling 2, and the
    # injection guarded below its bound.
    assert "(assert (and (>= s0 0) (<= s0 2)))\n" in script
    assert "(assert (=> (= s0 1) (< 0 2)))\n" in script
    assert _scripts(witness_depth=8)["witness"] == script
    assert _scripts(witness_depth=12)["witness"].startswith("; Bounded run (VER-019): 12 steps ")
    # Disabled, there is no query to report; nothing else in the mapping moves.
    off = _scripts(witness_depth=0)
    assert off["witness"] is None
    assert {k: v for k, v in off.items() if k != "witness"} == {
        k: v for k, v in _scripts().items() if k != "witness"
    }
