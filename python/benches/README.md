# libpetri Python benchmark suite

This directory mirrors the Rust criterion benchmarks in
`rust/benches/benches/` and adds Python-specific scenarios that exercise the
GIL boundary.

Built on [`pytest-benchmark`](https://pytest-benchmark.readthedocs.io/).

## Running

Install dev dependencies (includes `pytest-benchmark`):

```bash
cd python
pip install -e ".[dev]"
```

Run the whole suite (the `--override-ini=testpaths=benches` is needed because
the main `pyproject.toml` keeps `testpaths = ["tests"]` so the regular
`pytest` invocation doesn't pick up benches):

```bash
pytest benches/ --benchmark-only \
    --benchmark-disable-gc \
    --benchmark-warmup=off \
    --override-ini="testpaths=benches"
```

Run a single bench file or function:

```bash
pytest benches/bench_executor.py --benchmark-only --override-ini="testpaths=benches"
pytest benches/bench_gil_callback.py::bench_chain_sync_callback --benchmark-only --override-ini="testpaths=benches"
```

Emit machine-readable JSON for trending or dashboards:

```bash
pytest benches/ --benchmark-only --benchmark-json=results.json --override-ini="testpaths=benches"
```

Benchmarks are **not** run in CI (per-PR or per-push). They're noisy and the
existing CI Python job only runs the functional tests.

## What each file measures

### `bench_executor.py`
Mirrors `rust/benches/benches/executor.rs` and `owned_executor.rs`. All
scenarios use `lp.fork` as the action so the benchmark crosses the FFI
boundary but does **not** re-enter Python during execution. Use these to
compare against the matching Rust `owned_*` benchmarks for FFI overhead.

Benchmarks:
- `bench_single_passthrough` → Rust `owned_single_passthrough`
- `bench_sync_linear_chain[N]` → Rust `owned_sync_linear_chain/N`
- `bench_parallel_fan_out[F]` → Rust `owned_parallel_fan_out/F`
- `bench_async_linear_chain[N]` → Rust `owned_async_linear_chain/N`
- `bench_async_fan_out[F]` → (no Rust counterpart; gap in Rust suite)
- `bench_complex_workflow_8t_13p` → Rust `precompiled_complex_workflow/8t_13p`

### `bench_compilation.py`
Splits net build vs. compile so the contribution of each is visible:
- `bench_build_net_linear_chain[N]` — pure Python `Net(...).transition(...)....build()`.
- `bench_compile_linear_chain[N]` — `lp.compile(net)` on top.
- `bench_build_and_compile_linear_chain[N]` — end-to-end (mirrors Rust `owned_compilation/N`).

### `bench_export.py`
Python-only. Measures `lp.dot_export(net)` cost across net sizes. Rust has no
analogous bench — DOT is more often a Python notebook workflow.

### `bench_gil_callback.py`
The three-way comparison that's the centerpiece of the Python suite. For
each chain length N ∈ {5, 10, 20, 50, 100}:

- `bench_chain_fork[N]` — Rust built-in action; the GIL is **not** re-entered during execution.
- `bench_chain_sync_callback[N]` — a Python `def f(ctx): ctx.output(...)` runs on every transition fire. Each fire = 1× `Python::attach` + token clone + Python call.
- `bench_chain_async_callback[N]` — a Python `async def f(ctx): ctx.output(...)`. Each fire = `Python::attach` + `pyo3_async_runtimes::into_future_with_locals` + asyncio scheduling.

Interpretation:
- `(sync_callback / fork) - 1` ≈ GIL re-acquire + token clone per fire.
- `(async_callback / sync) - 1` ≈ asyncio scheduling + future-into-py overhead per fire.

Observed at N=50 on dev hardware: fork ≈ 270 µs, sync_callback ≈ 750 µs (2.7×), async_callback ≈ 5100 µs (6.8× sync).

### `bench_payload_size.py`
Chain length fixed at N=20, `lp.fork` action. Payload kinds:
`int`, `small_dict`, `medium_dict`, `large_dict_nested`, `bytes_1k`,
`bytes_64k`.

Useful finding: with `lp.fork` (no Python callback), all payload kinds
benchmark at essentially the same cost. **Tokens cross the FFI boundary by
reference, not by deep copy** — the Py<PyAny> is just a refcount bump, so
payload size is irrelevant to the executor's hot path. The cost only varies
when a Python callback explicitly serializes or copies the data.

If you need to expose data-size-dependent cost, write the action as a
Python callback that reads `ctx.input(...)` and constructs a new payload —
that's the scenario where `bytes_64k` will visibly cost more than `int`.

### `bench_env_injection.py`
Measures `ExecutorHandle.inject(place, value)` throughput end-to-end:
Python → mpsc send → executor wakeup → transition fire → token in sink.

Parametrized over N injections ∈ {100, 1000, 10000}. Divide total time by N
for the per-event cost (the path real production users hit on every sensor
event / inbound webhook / message-queue arrival).

### `bench_nu_net.py`
Measures the ν-net correlated-join firing-check cost — the work a join with a
`MatchSpec` does to select the matching name on each enablement check. All
actions are `lp.fork` (no per-transition Python callback), so the numbers
isolate the Rust matcher rather than the GIL.

Parametrized scenarios:
- `test_nu_join_drain[depth]` (depth ∈ {10, 50, 100, 200, 500}) — drain a k=2
  correlated join over a pool of `depth` distinct names.
- `test_plain_join_drain[depth]` — structurally identical join with **no**
  `MatchSpec`; the delta against `nu_join_drain` is the pure ν tax.
- `test_nu_join_drain_arity[arity]` (arity ∈ {4, 8}) — wider joins at fixed depth.
- `test_nu_scatter_gather[groups]` and `test_nu_scatter_gather_budgeted[groups]`
  (groups ∈ {10, 50, 100}) — end-to-end fork → join; the budgeted variant caps
  live correlation groups with a `Budget` place (NU-040).

Mirrors the Rust ν benches in `rust/benches/benches/executor.rs`.

## Comparing to Rust

Run the matching Rust bench:

```bash
cd rust
cargo bench -p libpetri-benches --bench owned_executor -- "owned_sync_linear_chain/100$" --measurement-time 1
cargo bench -p libpetri-benches --bench executor -- "precompiled_sync_linear_chain/100$" --measurement-time 1
```

Then run the Python counterpart:

```bash
cd python
pytest benches/bench_executor.py::bench_sync_linear_chain --benchmark-only \
    --override-ini="testpaths=benches" -k "[100]"
```

Stacked together, you get the cost breakdown:
- `precompiled_sync_linear_chain/100` — Rust optimal (cached `PrecompiledNet`).
- `owned_sync_linear_chain/100` — Rust through the FFI-safe entry point. After the 2026-05-27 PrecompiledNet refactor (caches the program on `OwnedPrecompiledNet`), this is within ~2% of precompiled.
- `bench_sync_linear_chain[100]` — Python through `lp.run_sync`. Overhead vs. owned is the marking dict construction (`marking_from_python`) and dict result construction (`marking_to_python`).
- `bench_chain_sync_callback[100]` — same Python entry point, but with a per-transition Python callback. Overhead vs. fork is GIL re-acquire + token clone per transition fire.

## Fixtures

`conftest.py` exposes the fixtures used by the bench files:

- `linear_chain_net` — `_build(n) -> (net, start_place, end_place)`.
- `fan_out_net` — `_build(fan) -> (net, source_place, sink_place)`.
- `complex_workflow_net` — already-built 8-transition / 13-place workflow with XOR, inhibitors, priorities, and read arcs (mirrors Rust `build_complex_workflow`).
- `nu_join_drain_net` / `plain_join_drain_net` / `nu_scatter_gather_net` — ν-net join builders (with and without `MatchSpec`, plus the budgeted scatter/gather) for `bench_nu_net.py`.
- `benchmark_async` — helper that drives a coroutine factory on a dedicated event loop (pytest-benchmark only times sync callables natively).
