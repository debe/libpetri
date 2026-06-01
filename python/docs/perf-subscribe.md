# Subscribe path throughput

Measured on the libpetri-py 2.8.0 release wheel (CPython 3.12, Linux,
release-mode build). The bench is `python/benches/bench_subscribe.py`:
one transition emits N=10,000 tokens into a place, one subscriber drains
them through the configured mode. End-to-end wall time → events/sec.

## Measured numbers

| Mode | Wall time (10k events) | Events/sec | Notes |
|---|---:|---:|---|
| `subscribe(batch_size=256)` | ~10.5 ms | ~950k/s | Throughput-oriented. |
| `subscribe(batch_size=64)`  | ~14.0 ms | ~700k/s | Throughput-oriented. |
| `subscribe(batch_size=16)`  | ~28.8 ms | ~350k/s | Mixed. |
| `subscribe(batch_size=1, batch_timeout_ms=0)` | ~308 ms | ~32k/s | Unary, with `PyList[1]` wrapper per yield. |
| `subscribe_stream(...)` | ~318 ms | ~31k/s | Unary, single `NetEvent` per yield. |

(Numbers vary ±10% run-to-run; treat as ballpark.)

## Recommendations

### Token streaming (LLM chunks, byte streams, BIDI bridges)

Use `subscribe_stream(...)`. Per-event latency is the same as
`subscribe(batch_size=1)` but the consumer code is cleaner:

```python
sub = store.subscribe_stream(types={"TokenAdded"}, places={"TOKEN_STREAM"})
async for event in sub:
    yield project_chunk(event)  # one event, no list-of-one
```

Throughput tops out at ~30–35k events/sec. Below the original 50k/sec
target, but the bottleneck is the per-`__anext__` pyo3-async-runtimes
future round-trip, not the list wrapper — `subscribe_stream` and
`subscribe(batch_size=1)` measure within 5% of each other. If your
upstream produces more than ~30k chunks/sec sustained, batch instead.

### Throughput-oriented consumers (logging sink, metrics aggregator)

Use `subscribe(batch_size=64, batch_timeout_ms=10)` or higher. At
`batch_size=256` the path runs at ~950k events/sec — limited only by the
producer.

### When to use each

| Consumer goal | Mode | Why |
|---|---|---|
| One event per yield, lowest per-event latency, cleanest code | `subscribe_stream(...)` | No `len(batch)` indirection; per-event delivery. |
| Throughput, can tolerate small batching latency | `subscribe(batch_size=N)` | One PyList allocation per N events instead of per event. |
| Hybrid (responsive but not per-event) | `subscribe(batch_size=8, batch_timeout_ms=20)` | Returns up to 8 events, or partial after 20 ms — bounded latency for streaming UIs. |
