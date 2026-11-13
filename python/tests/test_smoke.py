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


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_core_043_conflict_split_of_a_passthrough_sink_is_not_refused() -> None:
    """CORE-043: verification fails exactly when compiling the submitted net does. Under
    conflict priority (NU-052) the split forces the sink pruner ``grab`` and gives its
    start half an output place; that derived net used to be refused for an output spec
    ``grab`` never declared. Mirrors Rust
    ``core043_conflict_split_of_a_passthrough_sink_is_not_refused``."""
    source, x, taken, a, b, merged = (lp.Place(n) for n in ("source", "X", "taken", "A", "B", "merged"))
    net = (
        lp.Net("core043_conflict_sink")
        .transition(lp.Transition("fork").input(lp.one(source)).output(lp.and_(a, b)).action(lp.fork).build())
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda v: v), (b, lambda v: v)]))
            .output(lp.out(merged))
            .action(lp.fork)
            .build()
        )
        .transition(lp.Transition("grab").input(lp.one(x)).priority(10).build())
        .transition(lp.Transition("take").input(lp.one(x)).output(lp.out(taken)).action(lp.fork).build())
        .build()
    )
    assert net.compile() is not None
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"source": 1, "X": 1},
        sink_places=["merged", "taken"],
        mint_transitions=["fork"],
        priority_semantics="conflict",
    )
    assert result.route == "nu-scg", result.report


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


# ---------------------------------------------------------------- CORE-021


def test_core_021_ac2_transition_read_back_equals_itself() -> None:
    """CORE-021 AC2: a transition is equal to itself. ``net.transitions`` hands out a
    fresh wrapper on every access, so equality and hashing must follow the transition's
    identity, not the wrapper object's."""
    accept = (
        lp.Transition("accept")
        .input(lp.one(lp.Place("queued")))
        .output(lp.out(lp.Place("done")))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("core021").transition(accept).build()

    assert net.transitions[0] == net.transitions[0]
    assert hash(net.transitions[0]) == hash(net.transitions[0])
    assert net.transitions[0] == accept
    assert len({net.transitions[0], net.transitions[0], accept}) == 1
    # AC1: two builds of one description are two transitions.
    first = lp.Transition("P").build()
    second = lp.Transition("P").build()
    assert first != second
    assert accept != "accept"
