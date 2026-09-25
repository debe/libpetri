"""VER-017: the state-space cache of the bounded enumeration route.

``verify(..., state_space_cache=cache)`` builds the state-class graph of a net and
initial marking once and reads every later query off it. The binding clones the
net on every call, so these tests also pin that the cache keys on the net's
structure: a clone, or a copy built the same way, must hit.

Every query here is decided (or declined) by enumeration before any solver
runs; the truncation test falls through to the SMT pipeline, but asserts only on
the enumeration lines written before it.
"""

import threading

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

REUSED = "Bounded state-space enumeration: reused cached state space ("
CACHED_TRUNCATION = "Bounded state-space enumeration: cached truncation at "


def _pipeline(n, *, priority=0, terminal=False):
    """``p0 -> t0 -> p1 -> ... -> pn``: ``n + 1`` classes from one token in ``p0``."""
    builder = lp.Net(f"pipeline{n}")
    for i in range(n):
        t = (
            lp.Transition(f"t{i}")
            .input(lp.one(lp.Place(f"p{i}")))
            .output(lp.out(lp.Place(f"p{i + 1}")))
            .action(lp.fork)
        )
        if i == 0 and priority:
            t = t.priority(priority)
        builder = builder.transition(t.build())
    if terminal:
        builder = builder.terminal(f"p{n}")
    return builder.build()


def _verify(net, *, cache=None, sinks=("p6",), marking=None, prop=None, **kw):
    return lp.verify(
        net,
        prop if prop is not None else lp.deadlock_free(),
        initial_marking=marking if marking is not None else {"p0": 1},
        sink_places=list(sinks),
        state_space_cache=cache,
        **kw,
    )


def _body(result):
    """The report without the cache's line and the timing line."""
    return [
        line
        for line in result.report.splitlines()
        if not line.startswith(REUSED) and not line.startswith("Elapsed:")
    ]


def _assert_same_answer(cached, fresh):
    assert cached.verdict == fresh.verdict
    assert cached.route == fresh.route
    assert cached.counterexample_trace == fresh.counterexample_trace
    assert cached.counterexample_transitions == fresh.counterexample_transitions
    assert cached.counterexample_confirmed == fresh.counterexample_confirmed
    assert _body(cached) == _body(fresh)


def test_repeated_queries_build_once_and_answer_as_without_the_cache():
    net = _pipeline(6)
    cache = lp.StateSpaceCache()
    assert len(cache) == 0 and cache.build_count == 0

    first = _verify(net, cache=cache)
    assert first.verdict == "proven", first.report
    assert REUSED not in first.report
    assert cache.build_count == 1 and len(cache) == 1

    # Without the sink, the token resting in p6 is stranded: a violation, read
    # off the same graph.
    marking = {"p0": 1}
    proven = _verify(net, cache=cache)
    violated = _verify(net, cache=cache, sinks=())
    bound = _verify(net, cache=cache, sinks=(), prop=lp.place_bound("p6", 1))
    assert cache.build_count == 1, "later queries must not build"
    for result in (proven, violated, bound):
        assert result.route == "enumeration", result.report
        assert (
            "Bounded state-space enumeration: reused cached state space (7 classes) (VER-017).\n"
            "=== Bounded state-space enumeration (VER-017) ==="
        ) in result.report
    assert violated.verdict == "violated"
    assert violated.counterexample_transitions == [f"t{i}" for i in range(6)]
    assert violated.counterexample_confirmed is True

    _assert_same_answer(proven, _verify(net, marking=marking))
    _assert_same_answer(violated, _verify(net, sinks=()))
    _assert_same_answer(bound, _verify(net, sinks=(), prop=lp.place_bound("p6", 1)))


def test_a_rebuilt_copy_of_the_net_hits():
    cache = lp.StateSpaceCache()
    _verify(_pipeline(6), cache=cache)
    again = _verify(_pipeline(6), cache=cache)
    assert cache.build_count == 1
    assert REUSED in again.report


def test_a_different_marking_or_net_misses():
    cache = lp.StateSpaceCache()
    _verify(_pipeline(6), cache=cache)
    two = _verify(_pipeline(6), cache=cache, marking={"p0": 2})
    assert cache.build_count == 2 and REUSED not in two.report
    other = _verify(_pipeline(6, priority=5), cache=cache)
    assert cache.build_count == 3 and REUSED not in other.report
    assert len(cache) == 3


def test_a_net_with_terminals_hits():
    net = _pipeline(4, terminal=True)
    cache = lp.StateSpaceCache()
    _verify(net, cache=cache, sinks=())
    second = _verify(net, cache=cache, sinks=())
    assert cache.build_count == 1
    assert REUSED in second.report
    _assert_same_answer(second, _verify(net, sinks=()))


def test_a_cached_truncation_declines_smaller_budgets():
    net = _pipeline(6)  # 7 classes
    cache = lp.StateSpaceCache()
    _verify(net, cache=cache, enumeration_max_classes=3, timeout_ms=15_000)
    assert cache.build_count == 1
    smaller = _verify(net, cache=cache, enumeration_max_classes=2, timeout_ms=15_000)
    assert cache.build_count == 1
    assert (
        "Bounded state-space enumeration: cached truncation at 2 classes (VER-017); "
        "verifying via the SMT pipeline.\n"
        "Bounded state-space enumeration truncated at 2 classes (VER-017); "
        "verifying via the SMT pipeline.\n"
    ) in smaller.report
    closed = _verify(net, cache=cache)  # a larger budget builds and replaces it
    assert cache.build_count == 2
    assert closed.route == "enumeration" and CACHED_TRUNCATION not in closed.report
    assert len(cache) == 1


def test_parallel_queries_build_once():
    net = _pipeline(3000)
    cache = lp.StateSpaceCache()
    start = threading.Barrier(8)
    results = [None] * 8

    def query(i):
        start.wait()
        results[i] = _verify(net, cache=cache, sinks=("p3000",))

    threads = [threading.Thread(target=query, args=(i,)) for i in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert cache.build_count == 1
    assert all(r.verdict == "proven" for r in results)


def test_clear_drops_every_entry():
    cache = lp.StateSpaceCache()
    _verify(_pipeline(6), cache=cache)
    cache.clear()
    assert len(cache) == 0
    again = _verify(_pipeline(6), cache=cache)
    assert REUSED not in again.report
    assert cache.build_count == 2


def test_without_a_cache_nothing_is_reported():
    result = _verify(_pipeline(6))
    assert REUSED not in result.report and CACHED_TRUNCATION not in result.report


def test_a_witness_starts_at_the_callers_listing_of_the_marking():
    """The first state of a witness is the caller's marking in the caller's order,
    cached or not (VER-017). The binding once read the dict into a ``HashMap``,
    so that order was random per call and a cached witness could differ from a
    fresh one on nothing but the listing."""
    names = [f"q{i}" for i in range(8)]
    builder = lp.Net("independent")
    for n in names:
        builder = builder.transition(
            lp.Transition(f"t_{n}")
            .input(lp.one(lp.Place(n)))
            .output(lp.out(lp.Place(f"{n}_done")))
            .action(lp.fork)
            .build()
        )
    net = builder.build()
    marking = {n: 1 for n in reversed(names)}  # not code-point order
    cache = lp.StateSpaceCache()
    for _ in range(3):
        for c in (None, cache):
            result = lp.verify(
                net, lp.deadlock_free(), initial_marking=marking, state_space_cache=c
            )
            assert result.verdict == "violated", result.report
            assert result.route == "enumeration", result.report
            assert list(result.counterexample_trace[0].items()) == list(marking.items())
    assert cache.build_count == 1


def _variant(kind):
    """``a -> t -> b`` plus the one structural feature ``kind`` names."""
    a, b, c = lp.Place("a"), lp.Place("b"), lp.Place("c")
    t = lp.Transition("t").action(lp.fork)
    t = t.input(lp.exactly(2, a) if kind == "exactly" else lp.one(a))
    if kind == "xor":
        t = t.output(lp.xor(b, c))
    elif kind == "and":
        t = t.output(lp.and_(b, c))
    else:
        t = t.output(lp.out(b))
    if kind == "inhibitor":
        t = t.inhibitor(lp.inhibitor(c))
    if kind == "read":
        t = t.read(lp.read(c))
    if kind == "reset":
        t = t.reset(lp.reset(c))
    return lp.Net("variant").transition(t.build()).build()


@pytest.mark.parametrize(
    "kind", ["exactly", "xor", "and", "inhibitor", "read", "reset"]
)
def test_each_structural_difference_the_binding_carries_misses(kind):
    """The fingerprint is taken of the net the binding built from Python, so every
    arc kind and cardinality a Python builder sets must reach it."""
    cache = lp.StateSpaceCache()
    marking = {"a": 2, "c": 1}
    lp.verify(_variant("base"), lp.deadlock_free(), initial_marking=marking,
              state_space_cache=cache)
    cached = lp.verify(_variant(kind), lp.deadlock_free(), initial_marking=marking,
                       state_space_cache=cache)
    assert cache.build_count == 2, cached.report
    assert REUSED not in cached.report
    _assert_same_answer(
        cached, lp.verify(_variant(kind), lp.deadlock_free(), initial_marking=marking)
    )


def test_nets_differing_only_in_their_python_action_share_an_entry():
    """The graph never runs an action, so a Python callable is not part of the key:
    a net rebuilt with another action hits, and answers as a fresh query does."""

    async def other(ctx):
        ctx.output("b", None)

    def net(action):
        return (
            lp.Net("n")
            .transition(
                lp.Transition("t")
                .input(lp.one(lp.Place("a")))
                .output(lp.out(lp.Place("b")))
                .action(action)
                .build()
            )
            .build()
        )

    cache = lp.StateSpaceCache()
    lp.verify(net(lp.fork), lp.deadlock_free(), initial_marking={"a": 1},
              state_space_cache=cache)
    again = lp.verify(net(other), lp.deadlock_free(), initial_marking={"a": 1},
                      state_space_cache=cache)
    assert cache.build_count == 1
    assert REUSED in again.report
    _assert_same_answer(
        again, lp.verify(net(other), lp.deadlock_free(), initial_marking={"a": 1})
    )


def test_a_wrong_cache_type_names_the_argument():
    with pytest.raises(TypeError, match="state_space_cache"):
        _verify(_pipeline(2), cache=object(), sinks=("p2",))


def test_the_cache_is_not_picklable_and_is_falsy_when_empty():
    """A cache holds graphs in Rust memory the caller owns; it does not travel."""
    import pickle

    cache = lp.StateSpaceCache()
    assert not cache and repr(cache) == "StateSpaceCache(entries=0, builds=0)"
    with pytest.raises(TypeError):
        pickle.dumps(cache)
