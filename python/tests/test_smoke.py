import libpetri as lp


def build_linear_net():
    queued = lp.Place("queued")
    done = lp.Place("done")
    net = (
        lp.Net("smoke")
        .transition(
            lp.Transition("accept")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return queued, done, net


def test_sync_smoke_execution_and_export() -> None:
    queued, done, net = build_linear_net()

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(queued) == 0
    assert result.count(done) == 1
    assert result.first(done)["id"] == 1

    dot = lp.dot_export(net)
    assert "digraph" in dot
    assert "accept" in dot


def test_marking_view_helpers_accept_place_instances() -> None:
    queued, done, net = build_linear_net()

    result = lp.run_sync(net, initial={queued: [{"id": 1}, {"id": 2}]})

    assert result.has_tokens(done)
    assert result.count(done) == 2
    assert result.tokens(done)[0]["id"] == 1
    assert result.to_dict()["done"][1]["id"] == 2


def test_passthrough_action_consumes_without_emitting() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")
    net = (
        lp.Net("passthrough")
        .transition(
            lp.Transition("drop")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.passthrough)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(queued) == 0
    assert result.count(done) == 0
