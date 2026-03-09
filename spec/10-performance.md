# 10 — Performance

This document specifies scaling requirements, benchmark expectations, and performance-related design constraints.

---

## Scaling Requirements

#### PERF-001: Linear Scaling

**Priority:** MUST

Execution time scales linearly with the number of transitions in the net. There MUST be no quadratic or worse blowup in the orchestrator loop.

**Acceptance Criteria:**
1. A net with 2N transitions takes approximately 2× the orchestrator time of a net with N transitions (for equivalent workloads).
2. No O(n²) iteration over all transitions on each cycle (dirty set ensures only affected transitions are re-evaluated).

**Depends on:** [CONC-005]
**Test derivation:** Benchmark chain nets of 5, 50, and 500 transitions; verify near-linear scaling of orchestrator overhead.

---

#### PERF-002: Enablement Check O(W)

**Priority:** MUST

Individual transition enablement checks are O(W) where W = ceil(numPlaces / word_size). Word size is implementation-defined (32-bit or 64-bit). For nets with fewer than 64 places, this is O(1).

**Acceptance Criteria:**
1. Enablement check for a single transition does not iterate over arcs.
2. Check is constant-time for nets with < 64 places.
3. Check scales with word count for larger nets.

**Depends on:** [CONC-004]
**Test derivation:** Benchmark enablement check on nets of varying sizes; verify constant-time for small nets.

---

#### PERF-003: Dirty Set O(affected)

**Priority:** MUST

Each orchestrator cycle re-evaluates only the transitions affected by token changes since the last cycle. The cost is O(D) where D is the number of dirty transitions, not O(T) where T is the total transition count.

**Acceptance Criteria:**
1. Adding a token to a place with 3 connected transitions causes exactly 3 re-evaluations.
2. Transitions connected to unchanged places are not re-evaluated.

**Depends on:** [CONC-005]
**Test derivation:** Net with 50 transitions; token change affects 3; verify only 3 re-evaluated (via instrumentation or timing).

---

#### PERF-004: Lock-Free Hot Path

**Priority:** MUST

The completion signaling path (action completing → orchestrator notified) uses lock-free data structures. No mutex/lock acquisition on the hot path.

**Acceptance Criteria:**
1. Completion queue is lock-free (CAS-based, channel-based, or similar).
2. Wake-up signal does not require acquiring a contended lock.

**Depends on:** [CONC-006]
**Test derivation:** 100 concurrent action completions; verify no lock contention in profiler.

---

## Noop Event Store

#### PERF-010: Noop Event Store Zero-Cost

**Priority:** MUST

When the noop event store is used (isEnabled() returns false), the executor MUST skip event object creation entirely. No allocation occurs for events that will be discarded.

**Acceptance Criteria:**
1. Executor checks isEnabled() before creating event objects.
2. With noop store, no event objects are allocated.
3. Measurable performance difference between noop and in-memory stores under load.

**Depends on:** [EVT-022]
**Test derivation:** Benchmark same net with noop vs in-memory store; verify noop is faster (no allocation overhead).

---

## Inline Execution

#### PERF-011: Inline Action Optimization

**Priority:** SHOULD

Synchronous actions (passthrough, simple transforms) that complete immediately SHOULD be executed inline on the orchestrator thread, avoiding task dispatch overhead.

**Acceptance Criteria:**
1. Passthrough action executes without spawning a task.
2. Chain of N passthrough transitions completes with overhead proportional to N, not N × task_spawn_cost.

**Depends on:** [CONC-011]
**Test derivation:** Chain of 100 passthrough transitions; measure total time; verify sub-millisecond per transition.

---

## Benchmark Suite

#### PERF-020: Benchmark Suite

**Priority:** MUST

Each implementation MUST include a benchmark suite covering the following scenarios:

1. **Single passthrough**: One transition with passthrough action.
2. **Linear chain**: Sequence of N transitions (for N = 5, 10, 50, 100, 500).
3. **Parallel branches**: Multiple independent branches firing concurrently.
4. **Sync-only chain**: Chain of synchronous actions (inline execution path).
5. **Async chain**: Chain of actions with async work (task dispatch path).
6. **Mixed net**: Combination of sync and async actions.

**Acceptance Criteria:**
1. Benchmarks are executable as part of the build/test pipeline.
2. Results are reproducible (low variance).
3. Benchmarks cover both sync-inline and async-dispatch paths.

**Test derivation:** Run benchmark suite; verify all scenarios execute without errors.

---

#### PERF-021: Target Performance Ranges

**Priority:** SHOULD

The following ranges are reference targets, not hard requirements. They represent expected performance for a reasonably optimized implementation on modern hardware:

| Scenario | Target | Notes |
|----------|--------|-------|
| Single passthrough | < 10µs | Minimum overhead per transition |
| Chain of 5 | < 50µs | ~10µs per hop |
| Chain of 10 | < 100µs | ~10µs per hop |
| Chain of 50 | < 500µs | Orchestration overhead per cycle |
| Complex workflow (~50 transitions) | < 500µs per orchestration cycle | Real-world target |

These targets assume:
- Passthrough/sync actions (no async I/O)
- Warm JVM / optimized build
- No event store overhead (noop store)

**Acceptance Criteria:**
1. Implementations document their actual performance against these targets.
2. Significant deviations (> 10×) are investigated and documented.

**Test derivation:** Run benchmarks; record results; compare against targets.

---

#### PERF-022: Regression Detection

**Priority:** MUST

Benchmarks MUST be runnable in CI pipelines for regression detection. A significant performance regression (e.g., > 20% slowdown) should be flagged.

**Acceptance Criteria:**
1. Benchmark suite can run in CI.
2. Results can be compared against baseline.
3. Regressions are detectable (via comparison tool or threshold check).

**Test derivation:** Introduce artificial slowdown; verify CI detects regression.

---

## Memory Efficiency

#### PERF-030: Bitmap Memory Efficiency

**Priority:** MUST

The bitmap executor uses compact representations:
- Place presence: 1 bit per place per bitmap word
- Transition masks: 1 word array per transition
- Dirty set: 1 bit per transition

For a net with P places and T transitions:
- Presence bitmap: ceil(P / word_size) words
- Per-transition masks: ~3 × ceil(P / word_size) words (needs, inhibitor, reset)
- Dirty set: ceil(T / word_size) words

**Acceptance Criteria:**
1. Memory usage is proportional to P × T / word_size, not P × T.
2. A net with 100 places and 50 transitions uses < 1KB for bitmaps.

**Test derivation:** Compile a 100-place, 50-transition net; verify bitmap memory usage.

---

#### PERF-031: Token Storage Efficiency

**Priority:** SHOULD

Token storage should be efficient for the common case where places hold 0-5 tokens. Implementations SHOULD avoid excessive pre-allocation.

**Acceptance Criteria:**
1. Empty places consume minimal memory.
2. Places with few tokens use compact sequential storage (e.g., array-backed deque or array).

**Test derivation:** Create marking with 100 places, 3 tokens each; verify memory usage is reasonable.

---

## Flat-Array Executor Performance

#### PERF-040: Flat-Array Memory Layout

**Priority:** SHOULD

The precompiled executor SHOULD use a flat-array memory layout with no hash map lookups on the hot path. Per-transition data is stored in parallel arrays of length T (transition count) indexed by transition ID. Token storage uses ring buffers indexed by place ID. In-flight transition tracking uses arrays indexed by transition ID.

**Acceptance Criteria:**
1. No hash map lookups occur during the execution loop (consume, fire, complete, enable).
2. Per-transition timing, priority, masks, and opcodes are in parallel arrays.
3. Token access is by integer place ID, not by place object lookup.
4. In-flight tracking is by integer transition ID, not by transition object lookup.

**Depends on:** [CONC-020]
**Test derivation:** Profile execution of a 100-transition net; verify no hash map operations on the hot path.

---

#### PERF-041: Precompiled Executor Target Speedup

**Priority:** SHOULD

The precompiled flat-array executor SHOULD achieve 2–4× speedup on synchronous chains compared to the bitmap executor. This target assumes passthrough/sync actions, warm runtime, and noop event store.

Benchmark scenarios SHOULD include precompiled executor results alongside bitmap executor results [PERF-020] for direct comparison.

**Acceptance Criteria:**
1. Benchmark suite includes precompiled executor variants for chain scenarios.
2. Precompiled executor achieves measurable speedup over bitmap executor on sync chains.
3. Results are documented alongside bitmap executor benchmarks.

**Depends on:** [CONC-020], [PERF-020]
**Test derivation:** Run sync chain benchmarks with both executors; compare throughput.

---

#### PERF-042: Sparse Enablement Masks

**Priority:** SHOULD

Enablement masks SHOULD use a sparse representation to avoid scanning zero words in large nets. Three cases:
- **Empty** (sentinel value): skip the check entirely (e.g., transition with no input places or no inhibitors)
- **Single-word** (fast path): store word index + mask value; one AND + one compare operation
- **Multi-word sparse**: store only non-zero word indices and their mask values; iterate only non-zero entries

This avoids scanning W words when most are zero (common in large, sparse nets).

**Acceptance Criteria:**
1. Empty masks are detected and skipped with no computation.
2. Single-word masks use one AND + one compare (no loop).
3. Multi-word sparse masks iterate only non-zero words.
4. Enablement results are identical to full-width bitmap checks.

**Depends on:** [CONC-004], [CONC-020]
**Test derivation:** Net with 200 places where each transition touches 2–3 places; verify sparse check matches full bitmap check and is faster.
