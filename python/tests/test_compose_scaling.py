"""`NetBuilder.compose` must stay linear in the number of composed instances.

`compose` used to rebuild the whole net on every call — cloning the accumulated
places and transitions and running a full `build()` — so composing n instances
cost O(n²). Per-instance cost doubled as n doubled: 70 µs at n=25 up to 655 µs
at n=400, which is ~262 ms to compose a 400-step workflow and projects to
seconds at a few thousand. The builder now threads one accumulating
`PetriNetBuilder`, as the Rust, TypeScript and Java builders always have, so
each `compose` costs the size of the instance and validation runs once at
`build()`.

This pins the *shape* rather than an absolute number, so it survives a slower
or busier machine: a quadratic shows up as per-instance cost growing with n
(4x the work for 4x the instances), whatever the constant.
"""

from __future__ import annotations

import time

import pytest

import libpetri as lp

SMALL = 50
LARGE = 200
REPEATS = 5

# A quadratic would put this at ~4.0 (LARGE/SMALL). Real measurements on the
# linear implementation sit at ~1.0; the threshold is deliberately slack so
# only a genuine change in complexity trips it.
MAX_GROWTH = 2.0


def _step_subnet() -> lp.BuiltSubnetDef:
    p, q = lp.Place("P"), lp.Place("Q")
    return (
        lp.SubnetDef("Step")
        .place(q)
        .transition(
            lp.Transition("t")
            .input(lp.one(p))
            .output(lp.out(q))
            .action(lp.fork)
            .build()
        )
        .input_port("i", p)
        .output_port("o", q)
        .build()
    )


def _compose_chain_us_per_instance(n: int) -> float:
    """Best-of-REPEATS wall time per composed instance, in microseconds."""
    step = _step_subnet()
    places = [lp.Place(f"p{i}") for i in range(n + 1)]

    best = float("inf")
    for _ in range(REPEATS):
        start = time.perf_counter()
        builder = lp.NetBuilder("Chain")
        for place in places:
            builder = builder.place(place)
        for i in range(n):
            builder = builder.compose(
                f"s{i}", step, {"i": places[i], "o": places[i + 1]}
            )
        builder.build()
        best = min(best, time.perf_counter() - start)
    return best / n * 1_000_000


def test_compose_cost_per_instance_does_not_grow_with_net_size() -> None:
    _compose_chain_us_per_instance(10)  # warm up allocators and caches

    small = _compose_chain_us_per_instance(SMALL)
    large = _compose_chain_us_per_instance(LARGE)
    growth = large / small

    assert growth < MAX_GROWTH, (
        f"compose looks super-linear: {small:.1f} us/instance at n={SMALL} but "
        f"{large:.1f} us/instance at n={LARGE} ({growth:.2f}x). A per-call "
        f"rebuild of the accumulated net would show ~{LARGE / SMALL:.0f}x here."
    )


def test_composed_chain_is_correct_at_scale() -> None:
    """The fast path must still produce the same net: a token entering the
    head of a 200-instance chain reaches the tail."""
    n = 200
    step = _step_subnet()
    places = [lp.Place(f"p{i}") for i in range(n + 1)]

    builder = lp.NetBuilder("Chain")
    for place in places:
        builder = builder.place(place)
    for i in range(n):
        builder = builder.compose(f"s{i}", step, {"i": places[i], "o": places[i + 1]})
    net = builder.build()

    assert len([t for t in net.transitions]) == n
    result = lp.run_sync(net, initial={places[0]: [{"v": 1}]})
    assert result.count(places[n]) == 1, "the token must traverse the whole chain"
    assert result.count(places[0]) == 0


def test_build_is_repeatable_and_leaves_the_builder_usable() -> None:
    """`build()` clones the accumulated builder rather than consuming it, so a
    caller can build, keep composing, and build again."""
    step = _step_subnet()
    a, b, c = lp.Place("a"), lp.Place("b"), lp.Place("c")

    builder = (
        lp.NetBuilder("Growing")
        .place(a)
        .place(b)
        .place(c)
        .compose("s0", step, {"i": a, "o": b})
    )
    first = builder.build()
    assert [t.name for t in first.transitions] == ["s0/t"]

    builder = builder.compose("s1", step, {"i": b, "o": c})
    second = builder.build()
    assert [t.name for t in second.transitions] == ["s0/t", "s1/t"]
    assert [t.name for t in first.transitions] == ["s0/t"], "earlier net unchanged"


def test_unknown_port_name_is_reported_at_the_compose_call() -> None:
    """Port-name validation stays eager.

    The merge is where the expensive work happens, but an unknown port name is
    an authoring mistake and must be reported at the `compose` call that made
    it — not deferred to `build()`, where the caller has lost the call site.
    """
    step = _step_subnet()
    a, b = lp.Place("a"), lp.Place("b")

    builder = lp.NetBuilder("Host").place(a).place(b)
    with pytest.raises(lp.StructureError) as excinfo:
        builder.compose("s0", step, {"nope": a, "o": b})
    assert "nope" in str(excinfo.value), str(excinfo.value)

    # And the builder survived: the failure was caught before the accumulated
    # net was moved into the merge.
    net = builder.compose("s0", step, {"i": a, "o": b}).build()
    assert [t.name for t in net.transitions] == ["s0/t"]


def test_builder_reports_clearly_after_a_failed_merge() -> None:
    """A failure *inside the merge* discards the partially-composed net.

    This is a deliberate consequence of threading one accumulating builder:
    the core's builder methods consume and return it, so a merge that unwinds
    takes the builder with it. Rather than leave a half-merged net in place,
    the `NetBuilder` reports that it is unusable and says why.

    Note the contrast with an unknown port name, which is validated *before*
    the builder moves and therefore leaves it intact — see
    `test_unknown_port_name_is_reported_at_the_compose_call`. Merge-time
    failures are structural contradictions in the net, not typos, so starting
    over is the honest outcome.
    """
    p, q = lp.Place("P"), lp.Place("Q")

    def work(ctx: lp.TransitionContext) -> None:
        ctx.output("Q", ctx.input("P"))

    attempt = (
        lp.Transition("attempt")
        .input(lp.one(p))
        .output(lp.out(q))
        .action(work)
        .build()
    )
    worker = (
        lp.SubnetDef("Worker")
        .place(p)
        .place(q)
        .transition(attempt)
        .input_port("p", p)
        .output_port("q", q)
        .channel("go", attempt)
        .build()
    )

    x1, y1 = lp.Place("X1"), lp.Place("Y1")
    first = (
        lp.NetBuilder("First")
        .place(x1)
        .place(y1)
        .compose("a", worker, {"p": x1, "q": y1})
        .build()
    )
    conflicting_caller = next(t for t in first.transitions if t.name == "a/attempt")

    x2, y2 = lp.Place("X2"), lp.Place("Y2")
    builder = lp.NetBuilder("Second").place(x2).place(y2)
    with pytest.raises(lp.StructureError):
        builder.compose("b", worker, {"p": x2, "q": y2}, {"go": conflicting_caller})

    with pytest.raises(ValueError) as excinfo:
        builder.build()
    assert "unusable" in str(excinfo.value), str(excinfo.value)
    assert "fresh NetBuilder" in str(excinfo.value), str(excinfo.value)
