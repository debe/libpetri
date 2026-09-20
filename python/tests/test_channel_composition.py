"""MOD-021 channel composition from Python, and its MOD-031 alias merge.

Channel composition (**MOD-021**) fuses a caller-side transition with an
instance-side transition the subnet exports as a *channel*, producing one
transition that runs both actions in a single firing. It was unreachable from
Python until ``NetBuilder.compose`` / ``compose_instance`` gained the optional
``channel_bindings`` argument — ports were the only binding kind the binding
exposed.

The alias-merge tests below cover **MOD-031 AC#10**: where one side's
declared→actual correspondence maps a place to *itself*, that entry carries no
assertion and must lose to the other side's real mapping rather than
manufacturing a conflict. Only two differing **non-identity** mappings for one
declared place are a genuine conflict.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _worker() -> tuple[lp.BuiltSubnetDef, lp.BuiltTransition]:
    """A subnet whose ``attempt`` transition is exported as channel ``go``.

    Its action references the *declared* place names, so it only works after
    composition if the correspondence survives the channel merge.
    """
    p, q = lp.Place("P"), lp.Place("Q")

    def work(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("P")  # author-declared name
        ctx.output("Q", {**msg, "worked": True})

    attempt = (
        lp.Transition("attempt")
        .input(lp.one(p))
        .output(lp.out(q))
        .action(work)
        .build()
    )
    subnet = (
        lp.SubnetDef("Worker")
        .place(p)
        .place(q)
        .transition(attempt)
        .input_port("p", p)
        .output_port("q", q)
        .channel("go", attempt)
        .build()
    )
    return subnet, attempt


def test_channel_composition_fuses_caller_and_instance() -> None:
    """MOD-021: the two sides become one transition that runs both actions in
    a single firing, and the instance action still resolves its declared
    places."""
    worker, _ = _worker()
    host_in, host_out, audit = lp.Place("H_IN"), lp.Place("H_OUT"), lp.Place("AUDIT")

    def log(ctx: lp.TransitionContext) -> None:
        ctx.output("AUDIT", {"seen": True})

    caller = lp.Transition("gate").output(lp.out(audit)).action(log).build()

    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .place(audit)
        .compose("w", worker, {"p": host_in, "q": host_out}, {"go": caller})
        .build()
    )

    # One fused transition under the caller's name — not two.
    assert [t.name for t in net.transitions] == ["gate"]

    result = lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert result.first(host_out) == {"v": 1, "worked": True}, "instance action ran"
    assert result.count(audit) == 1, "caller action ran in the same firing"


def test_identity_alias_yields_to_non_identity_on_merge() -> None:
    """MOD-031 AC#10, positive: caller-side ``P -> P`` merged against
    instance-side ``P -> H`` succeeds and yields ``P -> H``.

    The caller declares an inhibitor on a host place literally named ``P``,
    which records an *identity* entry, plus an inhibitor on ``w/Q`` which the
    port binding rewrites — so the caller's correspondence is mixed and
    survives rather than being dropped whole. The instance side maps the same
    declared ``P`` to the bound host place ``H``.

    ``P`` is deliberately reachable only as an *inhibitor*, never an input:
    the binding's lookup tries the literal name first, so if ``P`` were an
    input the action would find it directly and never consult the
    correspondence — the test would pass whatever the merge decided. As
    written, a merge yielding ``P -> P`` makes ``ctx.input("P")`` fail and
    nothing reaches ``H_OUT``.
    """
    worker, _ = _worker()
    h, h_out, audit = lp.Place("H"), lp.Place("H_OUT"), lp.Place("AUDIT")
    decoy = lp.Place("P")  # same name as the subnet's declared place
    inst_q = lp.Place("w/Q")  # rewritten by the port binding

    def log(ctx: lp.TransitionContext) -> None:
        ctx.output("AUDIT", {"seen": True})

    caller = (
        lp.Transition("gate")
        .inhibitor(lp.inhibitor(decoy))
        .inhibitor(lp.inhibitor(inst_q))
        .output(lp.out(audit))
        .action(log)
        .build()
    )

    net = (
        lp.NetBuilder("Host")
        .place(h)
        .place(h_out)
        .place(audit)
        .place(decoy)
        .compose("w", worker, {"p": h, "q": h_out}, {"go": caller})
        .build()
    )

    result = lp.run_sync(net, initial={h: [{"v": 1}]})
    assert result.first(h_out) == {"v": 1, "worked": True}, (
        "declared 'P' must resolve through the merged correspondence to the "
        "bound host place, not to the identically-named decoy"
    )
    assert result.count(audit) == 1
    assert result.count(decoy) == 0, "the decoy was never a token source"


def test_two_differing_non_identity_aliases_still_conflict() -> None:
    """MOD-031 AC#10, negative: two *real* mappings for one declared place are
    a genuine ambiguity and must still be rejected.

    Built by using an already-composed transition as the caller side — it
    carries the author-keyed correspondence ``P -> X1`` from its own
    composition — and fusing it against a second instance whose correspondence
    maps the same declared ``P`` to ``X2``. Neither is an identity, so there is
    no rule that resolves them.

    **Both** ``P`` and ``Q`` are ambiguous here, and the diagnostic must name
    both, sorted. An earlier version of this test bound ``q`` to a shared place
    so that only ``P`` conflicted — a workaround for the merge reporting an
    arbitrary one of N, because it walks a hash map. That was a real defect and
    it is fixed; the test now covers the fix instead of avoiding it, and asserts
    the message is identical across repeated runs.
    """
    worker, _ = _worker()

    x1, y1 = lp.Place("X1"), lp.Place("Y1")
    x2, y2 = lp.Place("X2"), lp.Place("Y2")

    def provoke() -> str:
        first = (
            lp.NetBuilder("First")
            .place(x1)
            .place(y1)
            .compose("a", worker, {"p": x1, "q": y1})
            .build()
        )
        caller = next(t for t in first.transitions if t.name == "a/attempt")
        with pytest.raises(lp.StructureError) as excinfo:
            (
                lp.NetBuilder("Second")
                .place(x2)
                .place(y2)
                .compose("b", worker, {"p": x2, "q": y2}, {"go": caller})
                .build()
            )
        return str(excinfo.value)

    message = provoke()
    assert "MOD-031" in message, message
    assert "2 declared places" in message, f"must count the conflicts: {message}"
    for name in ("'P'", "'Q'", "X1", "X2", "Y1", "Y2"):
        assert name in message, f"must name {name}: {message}"
    assert message.index("'P'") < message.index("'Q'"), (
        f"conflicts must be listed sorted: {message}"
    )

    # Identical input, identical diagnostic — the property the hash-order fix
    # buys, and the one whose absence made this test flaky.
    assert all(provoke() == message for _ in range(8)), "diagnostic varies run to run"
