"""MarkingCache — periodic snapshots for fast seek/replay."""

from __future__ import annotations

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_ARCHIVE,
    reason="wheel built without `archive` feature (MarkingCache lives in libpetri-debug)",
)


def _build_chain() -> tuple[lp.Place, lp.Place, lp.BuiltNet]:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    net = (
        lp.Net("cache-net")
        .transition(
            lp.Transition("t")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return p_in, p_out, net


def test_compute_at_zero_returns_empty_state() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    cache = lp.MarkingCache()
    state = cache.compute_at(store, 0)
    assert state.marking == {}
    assert state.enabled_transitions == []
    assert state.in_flight_transitions == []


def test_compute_at_end_matches_final_marking_shape() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    cache = lp.MarkingCache()
    state = cache.compute_at(store, len(store))
    # After the chain fires, the only place with tokens is p_out.
    assert state.marking.get("p_out", 0) == 1


def test_invalidate_clears_cache_but_keeps_correctness() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    cache = lp.MarkingCache()
    first = cache.compute_at(store, len(store))
    cache.invalidate()
    second = cache.compute_at(store, len(store))
    assert first.marking == second.marking
    assert sorted(first.enabled_transitions) == sorted(second.enabled_transitions)


def test_compute_at_is_idempotent_at_intermediate_index() -> None:
    """compute_at twice at the same intermediate index yields equal state.

    Exercises cache reuse: the second call returns from a cached snapshot
    instead of replaying from event 0, but must produce a state structurally
    equal to the first call.
    """
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v1"]}, event_store=store)
    lp.run_sync(net, initial={p_in: ["v2"]}, event_store=store)

    cache = lp.MarkingCache()
    total = len(store)
    half = total // 2

    first = cache.compute_at(store, half)
    second = cache.compute_at(store, half)

    assert first.marking == second.marking
    assert sorted(first.enabled_transitions) == sorted(second.enabled_transitions)
    assert sorted(first.in_flight_transitions) == sorted(
        second.in_flight_transitions
    )


def test_compute_at_traverses_state_between_zero_and_end() -> None:
    """At least one intermediate index must differ from the end state.

    A degenerate replay that always returns the end marking would silently
    pass `test_compute_at_end_matches_final_marking_shape`. This guards
    against that: replay actually moves through state.
    """
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    cache = lp.MarkingCache()
    end_marking = cache.compute_at(store, len(store)).marking

    differing_indices = [
        i
        for i in range(1, len(store))
        if cache.compute_at(store, i).marking != end_marking
    ]
    assert differing_indices, (
        "compute_at returned the end marking at every intermediate index — "
        "either replay is degenerate or the test fixture is too short"
    )


def test_compute_at_out_of_bounds_clamps_to_end() -> None:
    """An index past the stream length clamps to the end state, not a panic."""
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    cache = lp.MarkingCache()
    end = cache.compute_at(store, len(store)).marking
    beyond = cache.compute_at(store, len(store) + 50).marking
    assert beyond == end


def test_compute_at_counts_multiple_tokens_in_one_place() -> None:
    """Two runs into the same store accumulate two tokens in p_out."""
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["a"]}, event_store=store)
    lp.run_sync(net, initial={p_in: ["b"]}, event_store=store)

    cache = lp.MarkingCache()
    state = cache.compute_at(store, len(store))
    assert state.marking.get("p_out", 0) == 2
