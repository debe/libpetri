# libpetri

[![PyPI](https://img.shields.io/pypi/v/libpetri)](https://pypi.org/project/libpetri/)
[![Python](https://img.shields.io/pypi/pyversions/libpetri)](https://pypi.org/project/libpetri/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](https://github.com/libpetri/libpetri/blob/main/LICENSE)

**Python bindings for the libpetri Coloured Time Petri Net engine.**

Compose typed Petri nets in Python, run them on the Rust executor through PyO3.
Full surface parity with the Java, TypeScript, and Rust implementations — same
arc types, timing modes, composition primitives, formal-verification API,
debug protocol, and DOT export.

## Install

```bash
pip install libpetri
```

Wheels are published for CPython 3.11, 3.12, 3.13 on Linux / macOS / Windows
(x86-64 and arm64).

## Quick example

```python
import libpetri as lp

request  = lp.Place("Request")
response = lp.Place("Response")

def process(ctx: lp.TransitionContext) -> None:
    req = ctx.input("Request")
    ctx.output("Response", f"Processed: {req}")

net = (
    lp.Net("Example")
    .transition(
        lp.Transition("Process")
        .input(lp.one(request))
        .output(lp.out(response))
        .timing(lp.deadline(5000))
        .action(process)
        .build()
    )
    .build()
)

result = lp.run_sync(net, initial={request: ["hello"]})
print(result.first(response))  # → "Processed: hello"
```

Async callbacks work the same way; `lp.run_async` drives `async def` actions
on tokio, releasing the GIL between awaits:

```python
import asyncio, libpetri as lp

async def main() -> None:
    incoming = lp.Place("incoming")
    approved = lp.Place("approved")

    async def approve(ctx: lp.TransitionContext) -> None:
        order = ctx.input("incoming")
        await asyncio.sleep(0)  # any awaitable works
        ctx.output("approved", {**order, "approved": True})

    net = (
        lp.Net("orders")
        .transition(
            lp.Transition("approve")
            .input(lp.one(incoming))
            .output(lp.out(approved))
            .action(approve)
            .build()
        )
        .build()
    )

    result = await lp.run_async(net, initial={incoming: [{"id": 1}]})
    print(result.first(approved))  # → {'id': 1, 'approved': True}

asyncio.run(main())
```

## What you get

- **Full runtime** — sync + async execution, environment-place injection, all
  five arc kinds (input / output / inhibitor / read / reset), all five timing
  modes, priority + FIFO scheduling.
- **Composition** — `SubnetDef` with typed ports + channels, `compose(...)`
  via structural rewrite, port bindings, instance prefixes.
- **Formal verification** — SMT/IC3 properties (deadlock-free, mutual
  exclusion, place bound, unreachable) through Z3 when the wheel ships with
  the `z3` system library available.
- **Debug protocol** — same JSON wire format as the Java / TypeScript
  implementations; pair with the libpetri debug-ui for live inspection.
- **DOT / Graphviz export** — `lp.dot_export(net)`.
- **Typed and IDE-friendly** — ships with `.pyi` stubs and `py.typed`; IDE
  autocomplete and `mypy --strict` work out of the box.

## A note on token typing

The Java, TypeScript, and Rust implementations enforce `Place[T]` at compile
time. The Python binding stores tokens as `Py<PyAny>` across the FFI boundary
— net *structure* (arcs, transitions, composition) is still validated, but
token *runtime types* are not. A place named `"order"` will accept dicts,
integers, or strings interchangeably. This is intentional: Python has no
static generics across the FFI. Validate at your boundary (Pydantic,
dataclasses, `isinstance`) and only put validated values into markings.

## Links

- [Source / specification / sibling implementations](https://github.com/libpetri/libpetri)
- [Spec (183 requirements, 11 files)](https://github.com/libpetri/libpetri/tree/main/spec)
- [CHANGELOG](https://github.com/libpetri/libpetri/blob/main/CHANGELOG.md)
- [Benchmarks](https://github.com/libpetri/libpetri/tree/main/python/benches)

[Apache License 2.0](https://github.com/libpetri/libpetri/blob/main/LICENSE)
