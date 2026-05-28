"""Token payload-size sweep: GIL refcount + allocation cost per token.

Fixed-length linear chain (N=20) using `lp.fork` so each transition fires with
one input and produces one output token. The token VALUE varies — each token
that crosses the FFI boundary is wrapped in a `Py<PyAny>` (Arc + refcount
bump). Larger / more complex payloads cost more.

Reading the numbers:
- Flat scaling across kinds  → refcount/GIL dominates allocation
- Growth with payload size   → Python-side allocation dominates GIL traffic

In practice most payloads (small dict, medium dict) sit close to each other
because they're just `dict` objects — only the *reference* crosses the GIL.
The bytes sweep exposes the path where Python actually allocates new objects
(buffer copies for output).
"""

from __future__ import annotations

import pytest

import libpetri as lp

CHAIN_LENGTH = 20


def _build_chain(n: int) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    places = [lp.Place(f"p{i}") for i in range(n + 1)]
    builder = lp.Net("payload_chain")
    for i in range(n):
        builder = builder.transition(
            lp.Transition(f"t{i}")
            .input(lp.one(places[i]))
            .output(lp.out(places[i + 1]))
            .action(lp.fork)
            .build()
        )
    return builder.build(), places[0], places[n]


def _payload(kind: str):
    if kind == "int":
        return 42
    if kind == "small_dict":
        return {"id": 1}
    if kind == "medium_dict":
        return {f"key_{i}": i for i in range(10)}
    if kind == "large_dict_nested":
        return {
            f"section_{i}": {
                f"field_{j}": {"v": j, "metadata": [j, i, j * i]}
                for j in range(5)
            }
            for i in range(20)
        }
    if kind == "bytes_1k":
        return b"x" * 1024
    if kind == "bytes_64k":
        return b"x" * (64 * 1024)
    raise ValueError(f"unknown payload kind: {kind}")


@pytest.mark.parametrize(
    "kind",
    [
        "int",
        "small_dict",
        "medium_dict",
        "large_dict_nested",
        "bytes_1k",
        "bytes_64k",
    ],
)
def bench_payload(benchmark, kind) -> None:
    net, start, _end = _build_chain(CHAIN_LENGTH)
    compiled = lp.compile(net)
    value = _payload(kind)
    benchmark(lambda: compiled.run_sync(initial={start: [value]}))
