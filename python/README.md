# libpetri for Python

[![PyPI](https://img.shields.io/pypi/v/libpetri)](https://pypi.org/project/libpetri/)
[![Python](https://img.shields.io/pypi/pyversions/libpetri)](https://pypi.org/project/libpetri/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](https://github.com/debe/libpetri/blob/main/LICENSE)

Python bindings for libpetri's Rust runtime. Build Coloured Time Petri Nets with a Python API and execute them on the precompiled Tokio backend through PyO3.

The [project README](https://github.com/debe/libpetri#readme) walks through one agent turn as a net: reading it, running it, and checking it with the verifier.

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

Outputs are normally published atomically when an action returns. In an async action, `ctx.flush()` publishes the current batch early so downstream transitions can run while the action continues. Published batches are not rolled back if the action later fails. The verifier does not model `ctx.flush()`: it reads the outputs of a transition it verifies in two steps (VER-004) as landing together when the action completes, and the report of such a verdict says so.

### Running asyncio code on the host loop

`lp.action_on_loop(coro)` schedules a coroutine on the loop captured by `run_async` / `start_async` and returns an awaitable for its result. Inside that coroutine the loop is running, so `asyncio.get_running_loop()`, `asyncio.create_task()` and libraries built on them work. Use it when an action calls asyncio code that has to run on the host's loop:

```python
async def call_tool(ctx: lp.TransitionContext) -> None:
    request = ctx.input("request")
    reply = await lp.action_on_loop(client.send(request))  # client bound to the host loop
    ctx.output("reply", reply)
```

## Event stores

`event_store=` on `run_sync`, `run_async` and `start_async` takes an `lp.InMemoryEventStore` or any object with an `append(event)` method (`lp.EventStoreProtocol`). A store written in Python can wrap another one, and a chain can end in an `InMemoryEventStore` through its `append`:

```python
class Logging:
    def __init__(self, inner: lp.InMemoryEventStore) -> None:
        self.inner = inner

    def append(self, event: lp.NetEvent) -> None:
        print(event.type, event.transition_name)
        self.inner.append(event)

memory = lp.InMemoryEventStore()
handle, done = lp.start_async(net, initial=..., event_store=Logging(memory))
await done                    # every event has reached append() by now
assert handle.event_store_error is None
```

- `append` runs on a libpetri thread, never on the executor's thread, and sees the events of one run in order. Events are handed over in batches with one GIL acquisition per batch.
- Every event has been delivered by the time `run_sync` returns or the run's awaitable resolves.
- An exception from `append` does not stop the run. It is logged to the `libpetri` logger, later events are still delivered, and on an async run the first one is kept on `ExecutorHandle.event_store_error`. A sync run has no handle, so there it is only logged.
- Two optional members are read once when the run starts, as an attribute or a zero-argument method. `is_enabled` set to false turns event recording off for the run. `captures_tokens` is described next.

### Token capture

By default events carry no token values. To get them on `TokenAdded` and `TokenRemoved`, ask for them on the outermost store: `lp.InMemoryEventStore(capture_tokens=True)`, or a list of place names to capture only those places. A Python store sets a `captures_tokens` attribute with the same meaning. The value is `event.token`, the same object that sits in the marking (not a copy), and `None` when it was not captured:

```python
store = lp.InMemoryEventStore(capture_tokens=["order"])
lp.run_sync(net, initial={"order": [order]}, event_store=store)
taken = [e for e in store.events() if e.type == "TokenRemoved" and e.place_name == "order"]
assert taken[0].token is order
```

## Clocks

By default a run reads wall time. `ExecutorOptions(clock=...)` gives it a virtual clock instead (TIME-015). Both clocks are implemented in Rust; a clock written in Python is not supported, because the executor reads its clock on every cycle and would take the GIL each time.

- **`lp.ManualClock(epoch_origin_ms=0)`** jumps to each timing boundary by itself. A net full of `delayed`, `window` and `deadline` transitions runs to the end in negligible real time, and the same inputs give the same timestamps on every run. Use it for replays and fast tests. It can be reused across runs.
- **`lp.SteppedClock(epoch_origin_ms=0)`** moves only when you call `advance_ms`. The executor parks until then, and `settle` waits until it has parked again, so a test can step time and then check what fired:

```python
clock = lp.SteppedClock()
handle, done = lp.start_async(
    net,
    initial={"queued": [job]},
    options=lp.ExecutorOptions(
        clock=clock, deadline_tolerance_ms=0, environment_places=("events",)
    ),
    event_store=store,
)
await clock.asettle(5.0)                                   # the first park
await clock.asettle_after(lambda: clock.advance_ms(1000), 5.0)
# a delayed(1000) transition has fired by now
await clock.asettle_after(lambda: handle.inject("events", item), 5.0)
```

Both clocks have `advance_ms(ms)`, `now_ms()` (alias `elapsed_ms()`) and `epoch_ms()`. `SteppedClock` adds `is_parked()`, `is_finished()`, `park_count()` and four ways to wait:

- `settle(timeout_s=None)` blocks until the executor is parked or the run has ended. Use it for the first park.
- `settle_after(action, timeout_s=None)` calls `action()` and then blocks until a park that started after it, or the end of the run. After an advance or an inject, use this form: the parked flag can still describe the park your action just ended.
- `asettle(timeout_s=None)` and `asettle_after(action, timeout_s=None)` are the awaitable forms. They suspend the task instead of blocking the thread, so they can run on the loop that drives the run. `asettle_after` calls `action` right away, before it returns the awaitable.

Each returns `True` when settled and `False` when `timeout_s` seconds pass first. The blocking forms release the GIL; call them from a different thread than the one inside `run_sync`. "Parked" describes the orchestrator only: an `async def` action that is still running is not waited for.

Points to know:

- **A `SteppedClock` serves one run.** When the run ends, however it ends, the clock is marked finished and every settle call returns `True`. Passing it to a second run raises `ValueError`.
- **Set `deadline_tolerance_ms=0` with a `SteppedClock`.** The default 5 ms tolerance lets a hard deadline (`deadline()`, `window()`) fire up to 5 ms late. With 0, a `window(50, 120)` transition still fires when you advance to exactly 120 and is reaped when you advance to 120.001.
- **Timestamps follow the clock.** Tokens created during the run, legacy `initial` values, and values passed to `handle.inject` / `inject_many` are stamped from `clock.epoch_ms()`. Structured `initial` tokens (`{"value": v, "created_at": ms}`, as `MarkingView.snapshot()` produces) keep their own `created_at`.
- **Action timeouts are not virtual.** `lp.timeout(after, ...)` on an output spec still waits `after` milliseconds of real time; the clock only stamps the recovery tokens.

## Capabilities

- Input, output, read, inhibitor, and reset arcs.
- Immediate, deadline, delayed, window, and exact timing.
- AND/XOR/timeout routing and input forwarding.
- Reusable subnets, typed interfaces, composition, and place fusion.
- Environment events, event stores, debug protocol, and DOT export.
- ν-net fresh identities and correlated joins.
- Marking snapshot and restore through `initial=`. `await handle.snapshot()` returns a `SnapshotResult` (`.marking`, `.is_restore_point`): check the flag, then pass `.marking` as `initial=` — handing over the result itself is a `TypeError` that says so.
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

- [Language-agnostic specification](https://github.com/debe/libpetri/blob/main/spec/00-index.md) — 224 active requirements
- [Lean soundness and backend-refinement proofs](https://github.com/debe/libpetri/blob/main/lean/README.md)
- [Changelog](https://github.com/debe/libpetri/blob/main/CHANGELOG.md)
- [Benchmarks](https://github.com/debe/libpetri/tree/main/python/benches)
- [Apache License 2.0](https://github.com/debe/libpetri/blob/main/LICENSE)
