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

## Writing async actions

Libpetri drives Python `async def` actions from a tokio worker thread.
Awaits inside the coroutine resolve against the asyncio loop that was
running when you called `lp.run_async` / `lp.start_async`, but the worker
thread itself does not run an asyncio loop. That means **synchronous
asyncio APIs called inside an action raise `RuntimeError: no running
event loop`**:

```python
async def action(ctx):
    # ❌ all of these raise inside a libpetri action:
    await asyncio.gather(tool_a(), tool_b())
    asyncio.create_task(work())
    loop = asyncio.get_running_loop()
    await asyncio.wait_for(slow(), timeout=1.0)
```

Use **structural fan-out** as the primary parallelism pattern — fire N
transitions in parallel from one FanOut, let the marking be the join:

```python
# Net structure: FanOut → (tool_a_transition || tool_b_transition) → Join
# Each tool transition is its own action; the executor schedules them
# in parallel. No asyncio.gather needed.
```

For the case where you genuinely need to await N coroutines inside one
action (e.g. dispatching to LangChain `BaseTool._arun` calls), use
`lp.action_gather`:

```python
import libpetri as lp

async def dispatch_tools(ctx):
    calls = ctx.input("TOOL_CALLS")
    # action_gather schedules on the captured asyncio loop, where
    # gather() works. Real parallelism: three 300ms tools finish in
    # ~300ms, not 900ms.
    results = await lp.action_gather(*(_arun(c) for c in calls))
    ctx.output("TOOL_RESULTS", results)
```

For blocking sync work (file I/O, blocking SDK calls), use
`lp.action_to_thread`:

```python
async def write_file(ctx):
    data = ctx.input("data")
    await lp.action_to_thread(Path("out.bin").write_bytes, data)
    ctx.output("done", True)
```

Exceptions raised by awaited coroutines are thrown back into your action
via `coro.throw`, so `try`/`except` inside the action works the same as
inside a regular asyncio task.

### Streaming chunks with `ctx.flush()`

By default, all `ctx.output(...)` calls within one action firing are
buffered and published together when the action returns. For long-running
async actions that need to stream tokens (LLM chunks, byte streams), call
`ctx.flush()` to publish the buffered outputs *now*:

```python
async def stream_chunks(ctx):
    async for chunk in llm.astream(request):
        ctx.output("TOKEN_STREAM", chunk)
        ctx.flush()
        await asyncio.sleep(0)  # yield so downstream transitions can run
```

Each `ctx.flush()` is its own published event boundary — already-flushed
tokens stay in the marking even if the action later raises. `ctx.flush()`
raises `RuntimeError` from a sync action (`run_sync`); use async
execution. The `await asyncio.sleep(0)` after each flush is the
recommended cooperative yield so the executor's main loop can process the
flush and let downstream transitions run while you're still streaming.

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
