"""Input-arc cardinality: one, exactly(N), all_tokens, at_least(N).

Mirrors Rust `precompiled_executor::tests::{exactly_cardinality_consumes_n,
all_cardinality_consumes_everything, at_least_blocks_insufficient,
at_least_fires_with_enough}` and Java `CardinalityTests`.
"""

from __future__ import annotations

import libpetri as lp


def _make_batch_net(input_spec):
    """Single transition `batch -> drain` with the given input spec."""
    batch = lp.Place("batch")
    drained = lp.Place("drained")

    def drain_action(ctx: lp.TransitionContext) -> None:
        tokens = ctx.inputs("batch")
        ctx.output("drained", {"count": len(tokens), "items": tokens})

    net = (
        lp.Net("batch")
        .transition(
            lp.Transition("drain")
            .input(input_spec(batch))
            .output(lp.out(drained))
            .action(drain_action)
            .build()
        )
        .build()
    )
    return batch, drained, net


def test_exactly_consumes_in_chunks_of_n() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.exactly(2, p))

    result = lp.run_sync(net, initial={batch: [1, 2, 3, 4]})

    # exactly(2) with 4 tokens fires twice; each firing consumes 2.
    assert result.count(drained) == 2
    for token in result.tokens(drained):
        assert token["count"] == 2
    assert result.count(batch) == 0


def test_exactly_leaves_remainder_when_not_divisible() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.exactly(2, p))

    result = lp.run_sync(net, initial={batch: [1, 2, 3]})

    # 3 tokens / chunk size 2 → fires once, 1 remains
    assert result.count(drained) == 1
    assert result.first(drained)["count"] == 2
    assert result.count(batch) == 1


def test_exactly_blocks_when_fewer_than_n_tokens() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.exactly(3, p))

    result = lp.run_sync(net, initial={batch: [1]})

    assert result.count(drained) == 0
    assert result.count(batch) == 1


def test_all_tokens_consumes_every_token() -> None:
    batch, drained, net = _make_batch_net(lp.all_tokens)

    result = lp.run_sync(net, initial={batch: [10, 20, 30]})

    assert result.count(drained) == 1
    assert result.first(drained)["count"] == 3
    assert result.count(batch) == 0


def test_all_tokens_against_empty_place_does_not_fire() -> None:
    batch, drained, net = _make_batch_net(lp.all_tokens)

    result = lp.run_sync(net, initial={})

    assert result.count(drained) == 0


def test_at_least_blocks_when_insufficient() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.at_least(3, p))

    result = lp.run_sync(net, initial={batch: [1, 2]})

    assert result.count(drained) == 0
    assert result.count(batch) == 2


def test_at_least_fires_once_consuming_every_available_token() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.at_least(2, p))

    result = lp.run_sync(net, initial={batch: [1, 2, 3, 4]})

    # at_least(N) only requires N+ as an enablement gate; firing then consumes
    # everything currently in the place (semantics shared with all_tokens).
    assert result.count(drained) == 1
    assert result.first(drained)["count"] == 4
    assert result.count(batch) == 0


def test_at_least_with_exactly_minimum_tokens_fires_once() -> None:
    batch, drained, net = _make_batch_net(lambda p: lp.at_least(3, p))

    result = lp.run_sync(net, initial={batch: [1, 2, 3]})

    assert result.count(drained) == 1
    assert result.first(drained)["count"] == 3
    assert result.count(batch) == 0


def test_one_consumes_a_single_token() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("one")
        .transition(
            lp.Transition("take")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}, {"id": 2}]})

    # `one` fires twice given two tokens; each firing produces one output.
    assert result.count(done) == 2
    assert result.count(queued) == 0


def test_combined_input_specs_on_one_transition() -> None:
    headers = lp.Place("headers")
    body = lp.Place("body")
    done = lp.Place("done")

    def merge(ctx: lp.TransitionContext) -> None:
        h = ctx.input("headers")
        b_tokens = ctx.inputs("body")
        ctx.output("done", {"header": h, "body": b_tokens})

    net = (
        lp.Net("combined")
        .transition(
            lp.Transition("merge")
            .input(lp.one(headers))
            .input(lp.exactly(2, body))
            .output(lp.out(done))
            .action(merge)
            .build()
        )
        .build()
    )

    result = lp.run_sync(
        net,
        initial={headers: [{"k": "v"}], body: [1, 2, 3]},
    )

    assert result.count(done) == 1
    assert result.first(done)["header"] == {"k": "v"}
    assert len(result.first(done)["body"]) == 2
    assert result.count(body) == 1
