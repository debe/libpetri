"""Pin tests for output-spec runtime behavior (V6).

Documents which output-spec rules are enforced at runtime today and which
are documentation-only. See `docs/output-spec.md` for the full story.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _net_with_output(spec, action) -> lp.BuiltNet:
    incoming = lp.Place("incoming")
    return (
        lp.Net("t-output")
        .transition(
            lp.Transition("t")
            .input(lp.one(incoming))
            .output(spec)
            .action(action)
            .build()
        )
        .build()
    )


def test_out_accepts_zero_emissions() -> None:
    """``lp.out(P)`` allows the action to emit nothing to P."""
    out_p = lp.Place("out_p")

    def emit_nothing(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        # intentionally do not emit to out_p

    net = _net_with_output(lp.out(out_p), emit_nothing)
    result = lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert result.count(out_p) == 0


def test_out_accepts_multiple_emissions_to_same_place() -> None:
    """``lp.out(P)`` allows the action to emit N tokens to P. No
    ``out_many(P)`` distinction needed."""
    out_p = lp.Place("out_p")

    def emit_three(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("out_p", 1)
        ctx.output("out_p", 2)
        ctx.output("out_p", 3)

    net = _net_with_output(lp.out(out_p), emit_three)
    result = lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert result.count(out_p) == 3
    assert tuple(result["out_p"]) == (1, 2, 3)


def test_output_many_to_out_accepted() -> None:
    """``ctx.output_many(P, xs)`` against ``lp.out(P)`` works."""
    out_p = lp.Place("out_p")

    def emit_many(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output_many("out_p", [10, 20, 30])

    net = _net_with_output(lp.out(out_p), emit_many)
    result = lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert tuple(result["out_p"]) == (10, 20, 30)


def test_undeclared_output_place_raises() -> None:
    """Writing to a place not mentioned in the spec is the one rule that
    *is* enforced at runtime."""
    out_p = lp.Place("out_p")
    captured: dict[str, str] = {}

    def write_undeclared(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        try:
            ctx.output("not_declared", 1)
        except Exception as exc:
            captured["err"] = type(exc).__name__ + ": " + str(exc)

    net = _net_with_output(lp.out(out_p), write_undeclared)
    lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert "ValueError" in captured["err"]
    assert "not_declared" in captured["err"]


def test_and_partial_emission_is_accepted_at_runtime() -> None:
    """``lp.and_(out(A), out(B))`` declares both — runtime accepts
    emitting only to A. Documentation-only, not enforced."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_only_a(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        # b not emitted

    net = _net_with_output(lp.and_(lp.out(a), lp.out(b)), emit_only_a)
    result = lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert result.count(a) == 1
    assert result.count(b) == 0


def test_xor_both_branches_emitted_is_accepted_at_runtime() -> None:
    """``lp.xor(out(A), out(B))`` declares "exactly one" — runtime
    accepts both. Documentation-only, not enforced."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_both(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        ctx.output("b", 2)

    net = _net_with_output(lp.xor(lp.out(a), lp.out(b)), emit_both)
    result = lp.run_sync(net, initial={lp.Place("incoming"): [{"v": 1}]})
    assert result.count(a) == 1
    assert result.count(b) == 1


def test_skip_output_validation_flag_is_currently_a_noop() -> None:
    """The ``skip_output_validation`` flag on ``ExecutorOptions`` is
    preserved for API compatibility but doesn't change runtime behavior
    today. Same emissions under either setting."""
    a = lp.Place("a")
    incoming = lp.Place("incoming")

    def emit_one(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 42)

    net = (
        lp.Net("noop-flag")
        .transition(
            lp.Transition("t")
            .input(lp.one(incoming))
            .output(lp.out(a))
            .action(emit_one)
            .build()
        )
        .build()
    )
    result_strict = lp.run_sync(
        net,
        initial={incoming: [{"v": 1}]},
        options=lp.ExecutorOptions(skip_output_validation=False),
    )
    result_skip = lp.run_sync(
        net,
        initial={incoming: [{"v": 1}]},
        options=lp.ExecutorOptions(skip_output_validation=True),
    )
    assert result_strict.count(a) == 1
    assert result_skip.count(a) == 1
