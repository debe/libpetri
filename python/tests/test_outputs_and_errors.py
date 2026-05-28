"""Output specs (AND / XOR / fork) plus error handling.

Mirrors Java `ForkJoinTests` / `XorOutputTests` and Rust
`precompiled_executor::tests::{sync_fork_chain, action_error_does_not_crash}`.
"""

from __future__ import annotations

import pytest

import libpetri as lp


# ---------- AND / fork --------------------------------------------------


def test_and_output_duplicates_token_to_each_branch() -> None:
    queued = lp.Place("queued")
    left = lp.Place("left")
    right = lp.Place("right")

    def fan_out(ctx: lp.TransitionContext) -> None:
        order = ctx.input("queued")
        ctx.output("left", order)
        ctx.output("right", order)

    net = (
        lp.Net("and-output")
        .transition(
            lp.Transition("split")
            .input(lp.one(queued))
            .output(lp.and_(lp.out(left), lp.out(right)))
            .action(fan_out)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(left) == 1
    assert result.count(right) == 1
    assert result.first(left)["id"] == result.first(right)["id"] == 1


def test_and_output_with_three_branches() -> None:
    queued = lp.Place("queued")
    a = lp.Place("a")
    b = lp.Place("b")
    c = lp.Place("c")

    def triple(ctx: lp.TransitionContext) -> None:
        v = ctx.input("queued")
        for p in ("a", "b", "c"):
            ctx.output(p, v)

    net = (
        lp.Net("and3")
        .transition(
            lp.Transition("split3")
            .input(lp.one(queued))
            .output(lp.and_(lp.out(a), lp.out(b), lp.out(c)))
            .action(triple)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [99]})

    assert result.count(a) == result.count(b) == result.count(c) == 1


# ---------- XOR ---------------------------------------------------------


def test_xor_output_fires_exactly_one_branch_chosen_by_callback() -> None:
    queued = lp.Place("queued")
    approved = lp.Place("approved")
    rejected = lp.Place("rejected")

    def decide(ctx: lp.TransitionContext) -> None:
        order = ctx.input("queued")
        target = "approved" if order["ok"] else "rejected"
        ctx.output(target, order)

    net = (
        lp.Net("xor-output")
        .transition(
            lp.Transition("decide")
            .input(lp.one(queued))
            .output(lp.xor(lp.out(approved), lp.out(rejected)))
            .action(decide)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1, "ok": True}]})

    assert result.count(approved) == 1 and result.count(rejected) == 0


def test_xor_output_picks_error_branch() -> None:
    queued = lp.Place("queued")
    approved = lp.Place("approved")
    rejected = lp.Place("rejected")

    def decide(ctx: lp.TransitionContext) -> None:
        order = ctx.input("queued")
        target = "approved" if order["ok"] else "rejected"
        ctx.output(target, order)

    net = (
        lp.Net("xor-error")
        .transition(
            lp.Transition("decide")
            .input(lp.one(queued))
            .output(lp.xor(lp.out(approved), lp.out(rejected)))
            .action(decide)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 2, "ok": False}]})

    assert result.count(rejected) == 1 and result.count(approved) == 0


# ---------- transitions with no output ---------------------------------


def test_transition_with_no_output_spec_is_a_sink() -> None:
    queued = lp.Place("queued")

    def consume(ctx: lp.TransitionContext) -> None:
        ctx.input("queued")  # consume, emit nothing

    net = (
        lp.Net("sink")
        .transition(
            lp.Transition("eat")
            .input(lp.one(queued))
            .action(consume)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(queued) == 0


# ---------- multiple outputs to same place -----------------------------


def test_output_many_accumulates_multiple_tokens_on_same_place() -> None:
    seed = lp.Place("seed")
    bucket = lp.Place("bucket")

    def fan(ctx: lp.TransitionContext) -> None:
        ctx.input("seed")
        ctx.output_many("bucket", [1, 2, 3, 4])

    net = (
        lp.Net("output-many")
        .transition(
            lp.Transition("emit")
            .input(lp.one(seed))
            .output(lp.out(bucket))
            .action(fan)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={seed: [True]})

    assert result.count(bucket) == 4


# ---------- error handling ---------------------------------------------


def test_callback_action_raising_aborts_the_firing_without_output() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    def boom(ctx: lp.TransitionContext) -> None:
        raise RuntimeError("intentional callback failure")

    net = (
        lp.Net("boom")
        .transition(
            lp.Transition("explode")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(boom)
            .build()
        )
        .build()
    )

    # Sync-path callback errors are surfaced via the event store (not raised)
    # so the executor keeps draining the rest of the net. The failed firing
    # produces no output.
    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(done) == 0


def test_non_callable_action_rejected_with_type_error() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    with pytest.raises(TypeError):
        (
            lp.Transition("bad")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(42)  # not callable
            .build()
        )


def test_output_to_undeclared_place_aborts_the_firing() -> None:
    queued = lp.Place("queued")
    declared = lp.Place("declared")

    def mis_emit(ctx: lp.TransitionContext) -> None:
        ctx.input("queued")
        ctx.output("undeclared", {"oops": True})

    net = (
        lp.Net("undeclared-output")
        .transition(
            lp.Transition("bad")
            .input(lp.one(queued))
            .output(lp.out(declared))
            .action(mis_emit)
            .build()
        )
        .build()
    )

    # `ctx.output("undeclared", ...)` raises PyValueError from the callback;
    # that bubbles up as an ActionError event and the firing is aborted —
    # no token appears on `declared`.
    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(declared) == 0
