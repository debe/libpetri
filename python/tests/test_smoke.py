import pytest

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
    """``passthrough`` consumes its input and produces nothing (it is a sink)."""
    queued = lp.Place("queued")
    net = (
        lp.Net("passthrough")
        .transition(
            lp.Transition("drop")
            .input(lp.one(queued))
            .action(lp.passthrough)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={queued: [{"id": 1}]})

    assert result.count(queued) == 0
    # No token was emitted anywhere — the marking is empty, not merely "done" is empty.
    assert result.to_dict() == {}


# ---------------------------------------------------------------- CORE-043


def _output_declaring_passthrough_net(action=None):
    queued = lp.Place("queued")
    done = lp.Place("done")
    builder = lp.Transition("drop").input(lp.one(queued)).output(lp.out(done))
    if action is not None:
        builder = builder.action(action)
    return lp.Net("core043").transition(builder.build()).build()


def test_compile_rejects_builder_default_passthrough() -> None:
    """No action at all means the passthrough default."""
    net = _output_declaring_passthrough_net()

    with pytest.raises(lp.StructureError) as exc:
        net.compile()

    assert "'drop'" in str(exc.value)


def test_compile_rejects_explicitly_bound_passthrough() -> None:
    net = _output_declaring_passthrough_net(lp.passthrough)

    with pytest.raises(lp.StructureError) as exc:
        net.compile()

    assert "'drop'" in str(exc.value)


def test_run_sync_rejects_output_declaring_passthrough() -> None:
    """The rejection must reach Python as an exception on the run path too."""
    queued = lp.Place("queued")
    net = _output_declaring_passthrough_net()

    with pytest.raises(lp.StructureError):
        lp.run_sync(net, initial={queued: [{"id": 1}]})


def test_compile_accepts_passthrough_sink() -> None:
    queued = lp.Place("queued")
    net = (
        lp.Net("sink")
        .transition(
            lp.Transition("drop")
            .input(lp.one(queued))
            .action(lp.passthrough)
            .build()
        )
        .build()
    )

    assert net.compile() is not None


def test_verify_rejects_output_declaring_passthrough() -> None:
    """Verification rejects the same nets execution rejects."""
    net = _output_declaring_passthrough_net()

    with pytest.raises(lp.StructureError) as exc:
        lp.verify(net, lp.deadlock_free())

    assert "'drop'" in str(exc.value)


# ------------------------------------------------- consumed-token release (FFI)


def test_consumed_tokens_release_without_aborting() -> None:
    """A sink consumes its tokens and releases them cleanly.

    The executor owns a token once it has consumed it (no rollback, EXEC-031) and
    releases it from inside ``Python::detach``, so this is the smallest net that
    exercises a detached decref. pyo3's reference pool queues those and drains them on
    the next attach; building with ``--cfg=pyo3_disable_reference_pool`` instead turns
    them into a hard abort, which is why this repo does not set that flag.
    """
    queued = lp.Place("queued")
    net = (
        lp.Net("sink")
        .transition(
            lp.Transition("drop").input(lp.one(queued)).action(lp.passthrough).build()
        )
        .build()
    )

    # Several tokens, so the release loop runs more than once.
    result = lp.run_sync(net, initial={queued: [{"id": i} for i in range(5)]})

    assert result.count(queued) == 0
    assert result.to_dict() == {}
