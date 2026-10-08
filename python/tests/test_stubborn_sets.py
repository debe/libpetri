"""VER-024: stubborn-set reduction of the enumeration route.

``fork: start -> s0_0 ... s(k-1)_0``, then per subnet ``i`` a cycle (or, with
``chain``, a chain ending in ``s(i)_n``) ``s(i)_j -> s(i)_(j+1)``."""

import re

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _forked(k, n, chain):
    b = lp.Net(f"fork-{k}x{n}")
    b = b.transition(
        lp.Transition("fork")
        .input(lp.one(lp.Place("start")))
        .output(lp.and_(*[lp.out_place(lp.Place(f"s{i}_0")) for i in range(k)]))
        .action(lp.fork)
        .build()
    )
    for i in range(k):
        for j in range(n):
            to = f"s{i}_{j + 1}" if chain else f"s{i}_{(j + 1) % n}"
            b = b.transition(
                lp.Transition(f"t{i}_{j}")
                .input(lp.one(lp.Place(f"s{i}_{j}")))
                .output(lp.out(lp.Place(to)))
                .action(lp.fork)
                .build()
            )
    return b.build()


def _classes(result):
    return int(re.search(r"State classes: (\d+)", result.report).group(1))


def test_independent_cycles_close_in_one_plus_n_classes():
    net = _forked(3, 4, chain=False)
    reduced = lp.verify(net, lp.deadlock_free(), initial_marking={"start": 1})
    full = lp.verify(net, lp.deadlock_free(), initial_marking={"start": 1}, partial_order_reduction=False)
    assert reduced.verdict == "proven", reduced.report
    assert full.verdict == "proven", full.report
    assert reduced.route == "enumeration"
    assert _classes(reduced) == 1 + 4
    assert _classes(full) == 1 + 4**3
    assert "Stubborn-set reduction (VER-024): on" in reduced.report
    assert "Stubborn-set reduction" not in full.report


def test_every_dead_marking_is_kept():
    net = _forked(3, 3, chain=True)
    violated = lp.verify(net, lp.deadlock_free(), initial_marking={"start": 1})
    assert violated.verdict == "violated", violated.report
    assert len(violated.counterexample_transitions) == 1 + 3 * 3
    proven = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"start": 1},
        sink_places=[f"s{i}_3" for i in range(3)],
    )
    assert proven.verdict == "proven", proven.report
