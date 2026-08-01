"""Pin tests for output-spec runtime behavior (V6).

Documents which output-spec rules are enforced at runtime today and which
are documentation-only. See `docs/output-spec.md` for the full story.

As of [IO-015] the *shape* rules — AND completeness and XOR exclusivity —
are enforced by the Rust runtime the binding rides on. A violating firing
deposits nothing and does not restore its consumed inputs; it surfaces as
a `TransitionFailed` event whose error names `[IO-015]`. Per-place
*multiplicity* is still unchecked.
"""

from __future__ import annotations

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


def _run(net, *, options=None):
    """Runs `net` with one token in `incoming`, returning (marking, events)."""
    store = lp.InMemoryEventStore()
    marking = lp.run_sync(
        net,
        initial={lp.Place("incoming"): [{"v": 1}]},
        options=options,
        event_store=store,
    )
    return marking, list(store.events())


def _io_015_failures(events) -> list[str]:
    return [
        e.payload()["error"]
        for e in events
        if e.type == "TransitionFailed" and "[IO-015]" in e.payload()["error"]
    ]


def test_out_with_no_emission_is_rejected() -> None:
    """``lp.out(P)`` requires the action to write to P. Emitting nothing
    violates the declared spec."""
    out_p = lp.Place("out_p")

    def emit_nothing(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        # intentionally do not emit to out_p

    marking, events = _run(_net_with_output(lp.out(out_p), emit_nothing))
    assert marking.count(out_p) == 0
    assert _io_015_failures(events), "expected an [IO-015] TransitionFailed"


def test_out_accepts_multiple_emissions_to_same_place() -> None:
    """``lp.out(P)`` allows the action to emit N tokens to P. [IO-015]
    validates *which* places were written, never how many tokens each
    received, so no ``out_many(P)`` distinction is needed."""
    out_p = lp.Place("out_p")

    def emit_three(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("out_p", 1)
        ctx.output("out_p", 2)
        ctx.output("out_p", 3)

    marking, events = _run(_net_with_output(lp.out(out_p), emit_three))
    assert marking.count(out_p) == 3
    assert tuple(marking["out_p"]) == (1, 2, 3)
    assert not _io_015_failures(events)


def test_output_many_to_out_accepted() -> None:
    """``ctx.output_many(P, xs)`` against ``lp.out(P)`` works."""
    out_p = lp.Place("out_p")

    def emit_many(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output_many("out_p", [10, 20, 30])

    marking, _ = _run(_net_with_output(lp.out(out_p), emit_many))
    assert tuple(marking["out_p"]) == (10, 20, 30)


def test_undeclared_output_place_raises() -> None:
    """Writing to a place not mentioned in the spec is rejected eagerly,
    at the ``ctx.output`` call rather than at completion."""
    out_p = lp.Place("out_p")
    captured: dict[str, str] = {}

    def write_undeclared(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        try:
            ctx.output("not_declared", 1)
        except Exception as exc:
            captured["err"] = type(exc).__name__ + ": " + str(exc)
        ctx.output("out_p", 1)

    _run(_net_with_output(lp.out(out_p), write_undeclared))
    assert "ValueError" in captured["err"]
    assert "not_declared" in captured["err"]


def test_and_partial_emission_is_rejected() -> None:
    """``lp.and_(out(A), out(B))`` declares both, so emitting only to A
    fails the firing — and A does not receive its token either."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_only_a(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        # b not emitted

    marking, events = _run(
        _net_with_output(lp.and_(lp.out(a), lp.out(b)), emit_only_a)
    )
    assert marking.count(a) == 0, "a violating firing deposits nothing at all"
    assert marking.count(b) == 0
    assert _io_015_failures(events)


def test_xor_both_branches_emitted_is_rejected() -> None:
    """``lp.xor(out(A), out(B))`` declares "exactly one" — emitting to
    both is a violation and neither branch receives a token."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_both(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        ctx.output("b", 2)

    marking, events = _run(
        _net_with_output(lp.xor(lp.out(a), lp.out(b)), emit_both)
    )
    assert marking.count(a) == 0
    assert marking.count(b) == 0
    assert _io_015_failures(events)


def test_skip_output_validation_bypasses_the_check() -> None:
    """``skip_output_validation=True`` on ``ExecutorOptions`` accepts a
    firing that the default configuration rejects — the same escape hatch
    Java and TypeScript expose."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_both(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        ctx.output("b", 2)

    net = _net_with_output(lp.xor(lp.out(a), lp.out(b)), emit_both)

    strict, strict_events = _run(net)
    assert strict.count(a) == 0
    assert _io_015_failures(strict_events)

    lax, lax_events = _run(
        net, options=lp.ExecutorOptions(skip_output_validation=True)
    )
    assert lax.count(a) == 1
    assert lax.count(b) == 1
    assert not _io_015_failures(lax_events)
