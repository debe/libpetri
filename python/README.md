# libpetri for Python

[![PyPI](https://img.shields.io/pypi/v/libpetri)](https://pypi.org/project/libpetri/)
[![Python](https://img.shields.io/pypi/pyversions/libpetri)](https://pypi.org/project/libpetri/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](https://github.com/debe/libpetri/blob/main/LICENSE)

Python bindings for libpetri's Rust runtime. Build Coloured Time Petri Nets with a Python API and execute them on the precompiled Tokio backend through PyO3.

See the [project README](https://github.com/debe/libpetri#why-a-petri-net) for the motivation and an order workflow using every arc type, concurrent actions, and timeout routing.

## Install

```bash
pip install libpetri
```

Python 3.11 or newer is required. Published wheels contain the Rust extension; no Rust toolchain is needed for normal installation.

## Quick start

```python
import libpetri as lp

input_place = lp.Place("input")
output_place = lp.Place("output")

def uppercase(ctx: lp.TransitionContext) -> None:
    ctx.output("output", ctx.input("input").upper())

net = (
    lp.Net("example")
    .transition(
        lp.Transition("uppercase")
        .input(lp.one(input_place))
        .output(lp.out(output_place))
        .action(uppercase)
        .build()
    )
    .build()
)

result = lp.run_sync(net, initial={input_place: ["hello"]})
print(result.first(output_place))  # HELLO
```

## Execution and concurrency

Python exposes one production path backed by Rust's owned precompiled net. The executor releases the GIL while running and reacquires it only for Python callbacks.

`run_async` accepts `async def` actions. Their awaits are bridged to the loop captured by the caller, but the Tokio worker invoking the callback does not itself have a running asyncio loop. Calls such as `asyncio.create_task()` or `asyncio.get_running_loop()` inside an action therefore fail. Prefer structural fan-out into several transitions; use `lp.action_gather(...)` when several Python awaitables genuinely belong inside one action, and `lp.action_to_thread(...)` for blocking functions.

Outputs are normally published atomically when an action returns. In an async action, `ctx.flush()` publishes the current batch early so downstream transitions can run while the action continues. Published batches are not rolled back if the action later fails.

## Capabilities

- Input, output, read, inhibitor, and reset arcs.
- Immediate, deadline, delayed, window, and exact timing.
- AND/XOR/timeout routing and input forwarding.
- Reusable subnets, typed interfaces, composition, and place fusion.
- Environment events, event stores, debug protocol, and DOT export.
- ν-net fresh identities and correlated joins.
- Structural, timed, and SMT verification through the Rust engine where available.

## SMT verification needs a `z3` executable

The wheel ships the SMT verifier compiled in, but it does not bundle a solver. `verify()` runs the `z3` executable found on `PATH` (or named by `LIBPETRI_Z3`), version 4.8.0 or newer; `libpetri.z3_available()` tells you whether one resolves, and without it every verification returns `unknown` with a reason naming the command. Set `LIBPETRI_SMT_DUMP` to a directory to keep every SMT-LIB2 script and solver reply.

## Token typing

The package ships `.pyi` stubs and `py.typed`, so net construction is IDE- and type-checker-friendly. Token values cross the FFI as Python objects, however: unlike Java, TypeScript, and Rust, Python cannot enforce a place's token type at runtime. Validate data at system boundaries before adding it to a marking.

## Build and test from source

```bash
python -m pip install -e '.[dev]'
maturin develop
pytest
```

The extension manifest lives in `rust/libpetri-py`. Do not build it as an ordinary Cargo workspace binary; maturin supplies the required Python-extension linkage.

## Project links

- [Language-agnostic specification](https://github.com/debe/libpetri/blob/main/spec/00-index.md) — 208 active requirements
- [Lean soundness and backend-refinement proofs](https://github.com/debe/libpetri/blob/main/lean/README.md)
- [Changelog](https://github.com/debe/libpetri/blob/main/CHANGELOG.md)
- [Benchmarks](https://github.com/debe/libpetri/tree/main/python/benches)
- [Apache License 2.0](https://github.com/debe/libpetri/blob/main/LICENSE)
