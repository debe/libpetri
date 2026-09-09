"""Pin tests for output-spec runtime behavior (V6).

Documents which output-spec rules are enforced at runtime today and which
are documentation-only. See `docs/output-spec.md` for the full story.

As of [IO-015] the *shape* rules — AND completeness and XOR exclusivity —
are enforced by the Rust runtime the binding rides on. A violating firing
deposits nothing and does not restore its consumed inputs; it surfaces as
a `TransitionFailed` event whose error names `[IO-015]`. Per-place
*multiplicity* is not a rule: writing several tokens to a place the spec
names once conforms and every token lands, but the firing exceeds what the
branch-enumerating analyses model, so [IO-016] AC4 has the runtime emit one
`LogMessage` diagnostic per transition saying so.
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


# ---------- [IO-016] AC4: several tokens into a place named once -----------


def _run_with(net, incoming_tokens):
    """Runs `net` with `incoming_tokens` in `incoming`, returning (marking, events)."""
    store = lp.InMemoryEventStore()
    marking = lp.run_sync(
        net,
        initial={lp.Place("incoming"): incoming_tokens},
        event_store=store,
    )
    return marking, list(store.events())


def _log_messages(events):
    return [e for e in events if e.type == "LogMessage"]


def test_multiplicity_warns_once_per_transition() -> None:
    """Writing two tokens to the one place the spec names conforms — [IO-015]
    reads the produced SET — and both land on every firing. The diagnostic is
    emitted once per transition, not once per firing."""
    out_p = lp.Place("out_p")

    def emit_two(ctx: lp.TransitionContext) -> None:
        v = ctx.input("incoming")
        ctx.output("out_p", v * 10 + 1)
        ctx.output("out_p", v * 10 + 2)

    marking, events = _run_with(_net_with_output(lp.out(out_p), emit_two), [1, 2, 3])
    assert marking.count(out_p) == 6, "both tokens land on every firing"
    assert not _io_015_failures(events)

    warnings = _log_messages(events)
    assert len(warnings) == 1, "three firings, one diagnostic"
    payload = warnings[0].payload()
    # KNOWN GAP against [IO-016] AC4: the clause also requires logger
    # `libpetri.runtime`, which TypeScript pins. `NetEvent::LogMessage` in
    # rust/libpetri-event carries no `logger` field, so neither Rust nor this
    # binding can expose one; the other three clauses are pinned below.
    assert payload["level"] == "WARN"
    assert payload["transition_name"] == "t"
    assert payload["message"] == (
        "'t': wrote more than one token to a place its output spec names once "
        "(out_p: 2); branch-enumerating analyses model one token per named place, "
        "so this firing exceeds what they explore (IO-016)"
    )


def test_multiplicity_names_every_repeated_place() -> None:
    """Through a composite spec every repeated place is named with its count, in
    produced (first-write) order."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_several(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("incoming")
        ctx.output("a", 1)
        ctx.output("a", 2)
        ctx.output("a", 3)
        ctx.output("b", 1)
        ctx.output("b", 2)

    marking, events = _run_with(
        _net_with_output(lp.and_(lp.out(a), lp.out(b)), emit_several), [{"v": 1}]
    )
    assert marking.count(a) == 3
    assert marking.count(b) == 2
    warnings = _log_messages(events)
    assert len(warnings) == 1
    assert "(a: 3, b: 2)" in warnings[0].payload()["message"]


def test_multiplicity_is_silent_for_one_token_per_named_place() -> None:
    """One token per named place is exactly what the analyses model: no event."""
    a = lp.Place("a")
    b = lp.Place("b")

    def emit_one_each(ctx: lp.TransitionContext) -> None:
        v = ctx.input("incoming")
        ctx.output("a", v)
        ctx.output("b", v)

    marking, events = _run_with(_net_with_output(lp.and_(lp.out(a), lp.out(b)), emit_one_each), [1, 2])
    assert marking.count(a) == 2
    assert marking.count(b) == 2
    assert _log_messages(events) == []
