"""DOT export benchmarks.

Measures `lp.dot_export(net)` cost across net sizes. Python-specific:
Rust has no analogous bench for DOT export, but Python users routinely use
DOT for notebook visualization so a baseline is worth tracking.
"""

from __future__ import annotations

import pytest

import libpetri as lp


@pytest.mark.parametrize("n", [10, 50, 100, 500])
def test_dot_export_linear_chain(benchmark, linear_chain_net, n) -> None:
    net, _start, _end = linear_chain_net(n)
    benchmark(lambda: lp.dot_export(net))


def test_dot_export_complex_workflow(benchmark, complex_workflow_net) -> None:
    net, _start, _response = complex_workflow_net
    benchmark(lambda: lp.dot_export(net))
