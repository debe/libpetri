# Python notes (>=3.11, PyO3 over the Rust runtime)

Only the things that change a design decision. Everything in `SKILL.md` still applies.

## Python is a binding, not a fourth implementation

The semantics are Rust's, including name-only `Place` equality and the presence of mid-action publication. When you check a cross-language design decision, check it against Rust, not against a separate Python model.

## Actions run on Tokio threads with no running asyncio loop

This is the rule that surprises everyone. `asyncio.gather`, `create_task`, `ensure_future`, `wait`, `as_completed`, `shield` and `wait_for` all **raise at construction** inside an action, because there is no running loop to bind to. Plain `await coro` and `asyncio.sleep` are fine.

For concurrency, do not reach for asyncio. Fan out **structurally**: emit N tokens, let N transitions fire in parallel, and join by cardinality or by a ν match. That is faster, it is visible to the verifier, and it is the reason you chose this model.

Watch third-party libraries that build futures internally. Prefer the coroutine-level entry point over a wrapper that constructs tasks for you.

## Async-first entry points are mandatory for I/O nets

Use `start_async` / `ainvoke` / `astream`. The synchronous entry point occupies the calling thread with the executor loop, so there is no loop left to drive awaits, and every I/O transition serialises the net. Treat the synchronous form as a shim for small demos, REPL exploration and structural unit tests.

## Observability is Rust-side and batched

Subscriptions are batched and filtered inside Rust. There are no per-event Python callbacks, by design: a callback per event would take the GIL on the hot path. Express observability as filtered subscriptions, not as a callback per event.

## Keep the ν key projection trivial

The key projection is a Python callable evaluated under the GIL for each candidate token, on the enablement path. Attribute access or a dict lookup is fine. Anything heavier taxes every enablement check of every matched transition, on every cycle.

## Available here (and in Rust) but not in Java or TypeScript

Marking snapshot and restore, and executor snapshot. Checkpoint and resume designs port to Rust and Python only.
