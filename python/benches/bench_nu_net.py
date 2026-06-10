"""ν-net firing-check benchmarks (spec NU-020/040).

Mirrors the Rust ``nu_*`` / ``owned_nu_*`` benches and the TS/Java ν-net suites.
A ``match_spec`` join is enabled only when a single correlation name is present
in every correlated input; finding it re-builds a ``name -> {count, oldest}``
index over EVERY token in each correlated input on each enablement check. So
draining a deep pool re-indexes the shrinking pool every fire (≈ O(k·depth²)).
``test_plain_join_drain`` is the identical-topology baseline with no match_spec,
so the gap to ``test_nu_join_drain`` is the pure ν firing-check tax.

These run on ``compiled.run_sync`` — the owned precompiled path — so they line up
with the Rust ``owned_nu_*`` numbers (FFI overhead shows up as the delta).

NU-021 (input-arc guards) has no scenario here: the Python ``one()`` exposes no
guard predicate; that cost is covered by the byte-identical match engine in the
Rust/TS suites (``nu_join_drain_guarded``).
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _drain_marking(inputs: list[lp.Place], depth: int):
    """Seed each correlated input with ``depth`` distinct, mutually-correlating cids.

    Tokens carry distinct, increasing ``created_at`` (structured form) — exactly
    like the Rust bench's ``Token::at(.., j)`` — so the oldest-token tie-break
    follows insertion order. Bare-dict tokens would all share one ``now_millis``
    timestamp, forcing the tie-break to lexicographic name order (c0, c1, c10,
    c100, …), which diverges from ring insertion order and makes the matched
    consume scan O(position) — a pathological worst case, not the realistic one
    where produced tokens already have distinct timestamps.
    """
    return {
        p: [{"value": {"cid": f"c{j}"}, "created_at": j} for j in range(depth)]
        for p in inputs
    }


@pytest.mark.parametrize("depth", [10, 50, 100, 200, 500])
def test_nu_join_drain(benchmark, nu_join_drain_net, depth) -> None:
    net, inputs, _merged = nu_join_drain_net(2)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial=_drain_marking(inputs, depth)))


@pytest.mark.parametrize("depth", [10, 50, 100, 200, 500])
def test_plain_join_drain(benchmark, plain_join_drain_net, depth) -> None:
    net, inputs, _merged = plain_join_drain_net()
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial=_drain_marking(inputs, depth)))


@pytest.mark.parametrize("arity", [4, 8])
def test_nu_join_drain_arity(benchmark, nu_join_drain_net, arity) -> None:
    net, inputs, _merged = nu_join_drain_net(arity)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial=_drain_marking(inputs, 100)))


@pytest.mark.parametrize("groups", [10, 50, 100])
def test_nu_scatter_gather(benchmark, nu_scatter_gather_net, groups) -> None:
    net, source, _budget = nu_scatter_gather_net(False)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={source: [0] * groups}))


@pytest.mark.parametrize("groups", [10, 50, 100])
def test_nu_scatter_gather_budgeted(benchmark, nu_scatter_gather_net, groups) -> None:
    net, source, budget = nu_scatter_gather_net(True)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={source: [0] * groups, budget: [0]}))
