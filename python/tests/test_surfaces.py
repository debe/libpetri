import libpetri as lp
import pytest


def build_composed_net():
    source = lp.Place("source")
    sink = lp.Place("sink")
    child_in = lp.Place("child_in")
    child_out = lp.Place("child_out")

    subnet = (
        lp.SubnetDef("pass_through")
        .place(child_in)
        .place(child_out)
        .transition(
            lp.Transition("forward")
            .input(lp.one(child_in))
            .output(lp.out(child_out))
            .action(lp.fork)
            .build()
        )
        .input_port("in", child_in)
        .output_port("out", child_out)
        .build()
    )

    net = (
        lp.Net("parent")
        .place(source)
        .place(sink)
        .compose("child", subnet, {"in": source, "out": sink})
        .build()
    )

    return source, sink, subnet, net


def test_composition_surface_runs_end_to_end() -> None:
    source, sink, _subnet, net = build_composed_net()

    result = lp.run_sync(net, initial={source: [{"id": 1}]})

    assert result.count(sink) == 1
    assert result.first(sink)["id"] == 1


def test_verification_surface_maps_results() -> None:
    _source, sink, _subnet, net = build_composed_net()

    result = lp.verify(net, lp.place_bound(sink, 5))

    if lp.HAS_Z3:
        # With z3 the verifier returns proven / violated / unknown depending on
        # structural analysis. Don't pin to one — just confirm the mapping shape.
        assert result.verdict in {"proven", "violated", "unknown"}
    else:
        assert result.verdict == "unknown"
        assert result.reason == "z3 feature not enabled"


@pytest.mark.skipif(not lp.HAS_DEBUG, reason="wheel built without debug support")
def test_debug_bridge_translates_json_callbacks() -> None:
    _source, _sink, _subnet, net = build_composed_net()

    handler = lp.DebugProtocolHandler()
    messages: list[dict[str, object]] = []

    handler.register_session("py-session", net, tags={"suite": "python"})
    handler.connect("client-1", messages.append)
    handler.send(
        "client-1",
        {
            "type": "listSessions",
            "limit": 10,
            "activeOnly": False,
            "tagFilter": {"suite": "python"},
        },
    )

    session_lists = [msg for msg in messages if msg.get("type") == "sessionList"]
    assert session_lists, messages

    sessions = session_lists[0]["sessions"]
    assert isinstance(sessions, list)
    assert sessions[0]["sessionId"] == "py-session"
    assert sessions[0]["tags"]["suite"] == "python"


@pytest.mark.skipif(not lp.HAS_DEBUG, reason="wheel built without debug support")
def test_session_tags_are_ordered_independently_of_the_process() -> None:
    """Both routes a host reads tags by — the `SessionSummary` object and the
    JSON frame — in ascending key order rather than hash order. Twelve
    scrambled keys: a randomised container passes one time in 12!."""
    _source, _sink, _subnet, net = build_composed_net()
    tags = {k: f"v-{k}" for k in ["k07", "k11", "k02", "k09", "k00", "k05", "k10", "k03", "k08", "k01", "k06", "k04"]}

    handler = lp.DebugProtocolHandler()
    handler.register_session("tagged", net, tags=tags)

    [summary] = handler.list_sessions()
    assert summary.tags == tags
    assert list(summary.tags) == sorted(tags)

    messages: list[dict[str, object]] = []
    handler.connect("client-1", messages.append)
    handler.send("client-1", {"type": "listSessions", "limit": 10, "activeOnly": False})
    [frame] = [m for m in messages if m.get("type") == "sessionList"]
    assert list(frame["sessions"][0]["tags"]) == sorted(tags)
