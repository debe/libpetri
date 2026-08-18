"""Inhibitor, read, and reset arc semantics.

Mirrors the scenarios from Java `BitmapNetExecutorTest::{InhibitorArcTests,
ReadArcTests, ResetArcTests}` and Rust
`precompiled_executor::tests::{sync_inhibitor_blocks, read_arc_does_not_consume,
reset_arc_removes_all_tokens}`.
"""

from __future__ import annotations

import libpetri as lp


def _emit_three(ctx: lp.TransitionContext) -> None:
    for value in [1, 2, 3]:
        ctx.output("data", value)


def _seed_data_net():
    """Net with a `seed -> emit -> data` transition that fills `data` with 3 tokens."""
    seed = lp.Place("seed")
    data = lp.Place("data")
    return (
        seed,
        data,
        lp.Net("seed-data")
        .transition(
            lp.Transition("emit")
            .input(lp.one(seed))
            .output(lp.out(data))
            .action(_emit_three)
            .build()
        )
        .build(),
    )


# ---------- inhibitor ----------------------------------------------------


def test_inhibitor_blocks_firing_when_blocker_has_tokens() -> None:
    queued = lp.Place("queued")
    blocker = lp.Place("blocker")
    done = lp.Place("done")

    net = (
        lp.Net("inhibitor-block")
        .transition(
            lp.Transition("guarded")
            .input(lp.one(queued))
            .inhibitor(lp.inhibitor(blocker))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net, initial={queued: [{"id": 1}], blocker: [{"present": True}]}
    )

    assert result.count(done) == 0, "transition must not fire while blocker has tokens"
    assert result.count(queued) == 1, "input token must remain"
    assert result.count(blocker) == 1, "inhibitor arc must not consume"


def test_inhibitor_allows_firing_when_blocker_empty() -> None:
    queued = lp.Place("queued")
    blocker = lp.Place("blocker")
    done = lp.Place("done")

    net = (
        lp.Net("inhibitor-clear")
        .transition(
            lp.Transition("guarded")
            .input(lp.one(queued))
            .inhibitor(lp.inhibitor(blocker))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 7}]})

    assert result.count(done) == 1
    assert result.first(done)["id"] == 7


# ---------- read --------------------------------------------------------


def test_read_arc_tests_presence_without_consuming() -> None:
    queued = lp.Place("queued")
    config = lp.Place("config")
    done = lp.Place("done")

    def use_config(ctx: lp.TransitionContext) -> None:
        order = ctx.input("queued")
        cfg = ctx.read("config")
        ctx.output("done", {**order, "tier": cfg["tier"]})

    net = (
        lp.Net("read")
        .transition(
            lp.Transition("apply")
            .input(lp.one(queued))
            .read(lp.read(config))
            .output(lp.out(done))
            .action(use_config)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={queued: [{"id": 1}], config: [{"tier": "gold"}]},
    )

    assert result.count(done) == 1
    assert result.first(done)["tier"] == "gold"
    assert result.count(config) == 1, "read arc must not consume"


def test_read_arc_blocks_when_place_empty() -> None:
    queued = lp.Place("queued")
    config = lp.Place("config")
    done = lp.Place("done")

    net = (
        lp.Net("read-blocks")
        .transition(
            lp.Transition("apply")
            .input(lp.one(queued))
            .read(lp.read(config))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(done) == 0, "must wait for config token"
    assert result.count(queued) == 1


def test_read_arc_shared_by_multiple_transitions() -> None:
    a_in = lp.Place("a_in")
    b_in = lp.Place("b_in")
    flag = lp.Place("flag")
    a_done = lp.Place("a_done")
    b_done = lp.Place("b_done")

    net = (
        lp.Net("shared-read")
        .transition(
            lp.Transition("ta")
            .input(lp.one(a_in))
            .read(lp.read(flag))
            .output(lp.out(a_done))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("tb")
            .input(lp.one(b_in))
            .read(lp.read(flag))
            .output(lp.out(b_done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={a_in: [{"id": "a"}], b_in: [{"id": "b"}], flag: [{"on": True}]},
    )

    assert result.count(a_done) == 1 and result.count(b_done) == 1
    assert result.count(flag) == 1, "shared read must leave flag intact"


# ---------- reset -------------------------------------------------------


def test_reset_arc_clears_all_tokens_on_firing() -> None:
    seed, data, _ = _seed_data_net()
    trigger = lp.Place("trigger")
    cleared = lp.Place("cleared")

    net = (
        lp.Net("reset-clears")
        .transition(
            lp.Transition("emit")
            .input(lp.one(seed))
            .output(lp.out(data))
            .action(_emit_three)
            .build()
        )
        .transition(
            lp.Transition("reset_data")
            .input(lp.one(trigger))
            .reset(lp.reset(data))
            .output(lp.out(cleared))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={seed: [{"start": True}], trigger: [{"go": True}]},
    )

    # `emit` and `reset_data` are both enabled at the start, so they fire in the same
    # pass — and `emit`'s three tokens are deposited by its synchronous action *during*
    # that pass. Per EXEC-003 AC5 a drain takes only what the pass began with, so the
    # reset clears the (empty) place and the three tokens land in the next cycle, with
    # nothing left to clear them. TypeScript has always behaved this way (its outputs
    # resolve on a promise, so they were never there when the reset ran); this test used
    # to pin the Rust/Java inline-deposit artifact, which is the divergence AC5 closes.
    assert result.count(data) == 3, "same-pass deposits outlive a reset in that pass"
    assert result.count(cleared) == 1
