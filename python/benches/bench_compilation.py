"""Compilation-cost benchmarks.

Measures the Python-side cost of building a Net and compiling it through to
the runtime-ready CompiledNet, independent of execution. Mirrors the Rust
`compilation/{N}` / `owned_compilation/{N}` benches but splits the two stages
(net construction vs. compilation) so the contribution of each is visible.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _build_linear_chain_inline(n: int) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    places = [lp.Place(f"p{i}") for i in range(n + 1)]
    builder = lp.Net("chain")
    for i in range(n):
        builder = builder.transition(
            lp.Transition(f"t{i}")
            .input(lp.one(places[i]))
            .output(lp.out(places[i + 1]))
            .action(lp.fork)
            .build()
        )
    return builder.build(), places[0], places[n]


@pytest.mark.parametrize("n", [10, 50, 100, 500])
def test_build_net_linear_chain(benchmark, n) -> None:
    """Pure Python net construction cost (excludes compilation)."""
    benchmark(lambda: _build_linear_chain_inline(n))


@pytest.mark.parametrize("n", [10, 50, 100, 500])
def test_compile_linear_chain(benchmark, n) -> None:
    """Cost of `lp.compile(net)` on top of an already-built net."""
    net, _start, _end = _build_linear_chain_inline(n)
    benchmark(lambda: lp.compile(net))


@pytest.mark.parametrize("n", [10, 50, 100, 500])
def test_build_and_compile_linear_chain(benchmark, n) -> None:
    """End-to-end: build + compile, mirroring the Rust `owned_compilation/N` bench."""
    benchmark(lambda: lp.compile(_build_linear_chain_inline(n)[0]))
