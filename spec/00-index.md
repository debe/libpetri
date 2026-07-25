# CTPN Technical Requirements Specification

## Purpose

This specification defines the **observable contract** of the Coloured Time Petri Net (CTPN) engine — what the engine guarantees, not how any particular language implements it. It exists for:

1. **AI verification** — ask "does implementation X still match spec Y?"
2. **Test derivation** — every requirement maps to testable criteria
3. **Cross-implementation consistency** — all three languages agree on behavior
4. **Living documentation** — single source of truth for the engine contract

## Implementations

| Implementation | Language | Location | Runtime | Maturity |
|---|---|---|---|---|
| **libpetri-java** | Java 25 | `java/` | Virtual threads | Production |
| **libpetri-ts** | TypeScript | `typescript/` | JS event loop + Promises | Production |
| **libpetri-rs** | Rust 1.85+ | `rust/` | Tokio async | v0.1.0 |
| **libpetri-py** | Python ≥3.11 | `python/` (binds Rust) | Tokio async via PyO3 | Beta |

## Spec Philosophy

- **Language-agnostic**: Requirements describe *what*, not *how*. No Java types, Rust traits, or TypeScript interfaces appear in requirement text.
- **Verifiable**: Every requirement has acceptance criteria that can be tested.
- **Traceable**: Requirements use `[PREFIX-NNN]` cross-references.
- **Implementation notes** appear only where runtime behavior necessarily diverges (e.g., bitmap word size: 64-bit in Java, 32-bit in TypeScript/Rust).

---

## Spec Files

| File | Prefix | Scope | Req Count |
|------|--------|-------|-----------|
| [01-core-model.md](01-core-model.md) | CORE | Places, tokens, transitions, arcs, net construction, actions, context, marking | 34 |
| [02-input-output-specs.md](02-input-output-specs.md) | IO | Input cardinality, composite output routing, validation | 14 |
| [03-timing.md](03-timing.md) | TIME | Firing intervals, clock semantics, deadline enforcement | 11 |
| [04-execution-model.md](04-execution-model.md) | EXEC | Orchestrator loop, scheduling, token consumption, failure, quiescence | 15 |
| [05-concurrency.md](05-concurrency.md) | CONC | Single-threaded orchestrator, bitmap executor, precompiled flat-array executor, async actions, wake-up | 18 |
| [06-environment-places.md](06-environment-places.md) | ENV | External event injection, implicit long-running behavior, executor lifecycle | 13 |
| [07-verification.md](07-verification.md) | VER | SMT/IC3, state class graph, structural analysis | 11 |
| [08-events-observability.md](08-events-observability.md) | EVT | Event types, event store, log capture | 23 |
| [09-export.md](09-export.md) | EXP | Graph export, formal interchange | 17 |
| [10-performance.md](10-performance.md) | PERF | Scaling, benchmarks, memory efficiency, flat-array executor performance | 14 |
| [11-modular-composition.md](11-modular-composition.md) | MOD | Open-net subnet definition, instantiation, port composition, channel fusion, action binding per instance, place fusion | 26 |
| [12-nu-nets.md](12-nu-nets.md) | NU | Token name identity, fresh-name minting (ν-binder/fork), join by name equality, bounded-budget decidability ledger | 12 |
| **Total** | | | **208** |

> **IO-006** (Input Guard Predicate) was removed (see [IO-006]); it is retained as a
> struck-through tombstone for traceability and is **excluded** from the active count.
> Counts above are active requirements only.

---

## Alphabetical Cross-Reference Index

### CONC — Concurrency
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| CONC-001 | Orchestrator Thread Ownership | MUST | — |
| CONC-002 | Non-Blocking Action Dispatch | MUST | — |
| CONC-003 | Happens-Before Guarantee | MUST | — |
| CONC-004 | Bitmap-Based Enablement Check | MUST | — |
| CONC-005 | Dirty Set Optimization | MUST | — |
| CONC-006 | Lock-Free Completion Signaling | MUST | — |
| CONC-007 | Compiled Net Representation | MUST | — |
| CONC-008 | Multi-Phase Enablement | MUST | — |
| CONC-010 | Orchestrator Wake-Up | MUST | — |
| CONC-011 | Inline Synchronous Execution | SHOULD | — |
| CONC-012 | Concurrent Action Limit | MAY | — |
| CONC-020 | Precompiled Net Representation | SHOULD | CONC-007 |
| CONC-021 | Opcode-Based Consume Operations | SHOULD | — |
| CONC-022 | Flat-Array Token Storage | SHOULD | CORE-013 |
| CONC-023 | Priority-Partitioned Ready Queues | SHOULD | EXEC-002 |
| CONC-024 | Precomputed Timing Arrays | SHOULD | — |
| CONC-025 | Lazy Marking Synchronization | SHOULD | — |
| CONC-026 | Optional Output Validation Skip | MAY | — |

### CORE — Core Model
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| CORE-001 | Place Definition | MUST | — |
| CORE-002 | Place Identity | MUST | — |
| CORE-003 | Place Type Safety | MUST | — |
| CORE-010 | Token Immutability | MUST | — |
| CORE-011 | Token Creation | MUST | — |
| CORE-012 | Unit Token | MUST | — |
| CORE-013 | Token FIFO Ordering | MUST | CORE-001 |
| CORE-020 | Transition Definition | MUST | IO-001, IO-010, TIME-001 |
| CORE-021 | Transition Identity | MUST | — |
| CORE-022 | Transition Enablement | MUST | IO-001–004, CORE-030–032 |
| CORE-030 | Input Arc | MUST | — |
| CORE-031 | Inhibitor Arc | MUST | — |
| CORE-032 | Read Arc | MUST | — |
| CORE-033 | Read Arc Multi-Reader | MUST | CORE-032 |
| CORE-034 | Reset Arc | MUST | — |
| CORE-035 | Output Arc | MUST | — |
| CORE-036 | Arc Semantics Summary | MUST | — |
| CORE-040 | Net Builder | MUST | — |
| CORE-041 | Net Immutability | MUST | — |
| CORE-042 | Action Binding Separation | MUST | — |
| CORE-050 | Transition Action | MUST | — |
| CORE-051 | Passthrough Action | MUST | — |
| CORE-052 | Fork Action | SHOULD | — |
| CORE-053 | Transform Action | SHOULD | — |
| CORE-054 | Produce Action | SHOULD | — |
| CORE-060 | Context Input Access | MUST | CORE-050 |
| CORE-061 | Context Read Access | MUST | CORE-032 |
| CORE-062 | Context Output Access | MUST | CORE-035 |
| CORE-063 | Context Structure Enforcement | MUST | — |
| CORE-064 | Execution Context Injection | SHOULD | — |
| CORE-070 | Marking State | MUST | — |
| CORE-071 | Marking Thread Safety | MUST | — |
| CORE-072 | Initial Marking | MUST | — |
| CORE-073 | Marking Snapshot and Restore | SHOULD | CORE-010, CORE-011, CORE-072, TIME-010, TIME-011 |

### ENV — Environment Places
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| ENV-001 | Environment Place Wrapper | MUST | — |
| ENV-002 | Environment Place Registration | MUST | — |
| ENV-003 | inject() Thread Safety | MUST | — |
| ENV-004 | inject() Completion Semantics | MUST | — |
| ENV-005 | inject() Wake-Up | MUST | CONC-010 |
| ENV-006 | inject() Rejection on Closed or Draining Executor | MUST | — |
| ENV-010 | Implicit Long-Running Behavior | MUST | — |
| ENV-011 | Graceful Drain | MUST | ENV-010 |
| ENV-012 | Event-Driven Workflow Pattern | SHOULD | ENV-001, 002, 010 |
| ENV-013 | Immediate Close | MUST | ENV-010 |
| ENV-014 | Mid-Execution Marking Snapshot | SHOULD | ENV-010 |
| ENV-015 | Immediate Termination | MAY | ENV-013 |
| ENV-016 | Observable Termination | MAY | ENV-013 |

### EVT — Events & Observability
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| EVT-001 | Event Immutability | MUST | — |
| EVT-002 | ExecutionStarted Event | MUST | — |
| EVT-003 | ExecutionCompleted Event | MUST | — |
| EVT-004 | TransitionEnabled Event | MUST | — |
| EVT-005 | TransitionClockRestarted Event | MUST | TIME-012 |
| EVT-006 | TransitionStarted Event | MUST | — |
| EVT-007 | TransitionCompleted Event | MUST | — |
| EVT-008 | TransitionFailed Event | MUST | EXEC-030 |
| EVT-009 | TransitionTimedOut Event | MUST | TIME-013 |
| EVT-010 | ActionTimedOut Event | MUST | IO-013, EXEC-022 |
| EVT-011 | TokenAdded Event | MUST | — |
| EVT-012 | TokenRemoved Event | MUST | — |
| EVT-013 | LogMessage Event | SHOULD | — |
| EVT-014 | MarkingSnapshot Event | SHOULD | — |
| EVT-020 | EventStore Interface | MUST | — |
| EVT-021 | InMemoryEventStore | MUST | — |
| EVT-022 | NoopEventStore | MUST | — |
| EVT-023 | LoggingEventStore | SHOULD | — |
| EVT-024 | DebugEventStore | SHOULD | — |
| EVT-025 | Session Archive Format | SHOULD | — |
| EVT-030 | Event Filtering | SHOULD | — |
| EVT-031 | EventStore Live Subscriptions | SHOULD | EVT-020, EVT-021 |
| EVT-032 | Marking Replay Cache | SHOULD | EVT-021, CONC-025 |

### EXEC — Execution Model
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| EXEC-001 | Orchestrator Loop Steps | MUST | ENV-003 |
| EXEC-002 | Priority-Based Firing Order | MUST | — |
| EXEC-003 | Competitive Conflict Resolution | MUST | — |
| EXEC-010 | FIFO Token Consumption | MUST | CORE-013, IO-007 |
| EXEC-011 | Guarded Token Consumption | SHOULD | IO-006 |
| EXEC-012 | Read Arc Peek | MUST | CORE-032 |
| EXEC-013 | Reset Arc Execution | MUST | CORE-034 |
| EXEC-020 | Output Token Deposition | MUST | — |
| EXEC-021 | Output Spec Validation | MUST | IO-011, 012, 015 |
| EXEC-022 | Action Timeout Handling | MUST | IO-013, 014, EVT-009 |
| EXEC-030 | Action Failure | MUST | EVT-007 |
| EXEC-031 | No Rollback | MUST | — |
| EXEC-040 | Standard Quiescence | MUST | — |
| EXEC-041 | Execution Result | MUST | — |
| EXEC-050 | Timestamp-Based Stale Detection | SHOULD | CORE-032, 010 |

### EXP — Export
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| EXP-001 | Graph Export Format | MUST | — |
| EXP-002 | Visual Semantics — Places | MUST | — |
| EXP-003 | Visual Semantics — Transitions | MUST | — |
| EXP-004 | Arc Rendering | MUST | — |
| EXP-005 | XOR Branch Labels | SHOULD | — |
| EXP-006 | Cardinality Labels | SHOULD | — |
| EXP-007 | Export Configuration | SHOULD | — |
| EXP-008 | Styling | SHOULD | — |
| EXP-010 | Formal Interchange Format | MAY | — |
| EXP-011 | Compile-Time Diagram Generation | MAY | — |
| EXP-012 | XOR/AND Junction Nodes | MUST | — |
| EXP-013 | Combined reset+output Edge | MUST | — |
| EXP-014 | Junction ID Format and Layout Stability | MUST | — |
| EXP-015 | Doc Generator Parity | MUST | EXP-011, EXP-012, EXP-013 |
| EXP-016 | Subnet Instance Cluster Subgraphs | SHOULD | EXP-001, EXP-014, MOD-010, MOD-040 |
| EXP-017 | Compound Cluster Layout Hints | SHOULD | EXP-016, EXP-014 |
| EXP-018 | ν-Match Edge Decoration | SHOULD | EXP-006, NU-020 |

### IO — Input/Output Specifications
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| IO-001 | Input One | MUST | CORE-030 |
| IO-002 | Input Exactly | MUST | CORE-030 |
| IO-003 | Input All | MUST | CORE-030 |
| IO-004 | Input AtLeast | MUST | CORE-030 |
| IO-005 | Input AND-Join Semantics | MUST | — |
| ~~IO-006~~ | ~~Input Guard Predicate~~ (Removed) | — | — |
| IO-007 | requiredCount and consumptionCount Contract | MUST | — |
| IO-010 | Output Place (Leaf) | MUST | — |
| IO-011 | Output And | MUST | — |
| IO-012 | Output Xor | MUST | — |
| IO-013 | Output Timeout | MUST | EVT-009 |
| IO-014 | Output ForwardInput | MUST | — |
| IO-015 | Output Validation | MUST | EVT-007 |
| IO-016 | Branch Enumeration | SHOULD | — |
| IO-017 | allPlaces Flattening | MUST | — |

### MOD — Modular Composition
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| MOD-001 | SubnetDef Definition (open net + interface) | MUST | — |
| MOD-002 | Subnet Identity (sealed/sum-type distinction from PetriNet) | MUST | — |
| MOD-003 | Port Declaration (name + direction + place) | MUST | — |
| MOD-004 | Port Direction Semantics (advisory; arcs govern flow) | SHOULD | CORE-030–035 |
| MOD-005 | Channel Declaration (interface transitions for synchronous fusion) | MUST | — |
| MOD-006 | Subnet Validation at Build | MUST | CORE-040, CORE-041 |
| MOD-010 | Instance Creation via instantiate(prefix, params) | MUST | CORE-001, CORE-040 |
| MOD-011 | Instance Handle Map (typed port + channel handles) | MUST | MOD-003, MOD-005, MOD-010 |
| MOD-012 | Per-Instance State Isolation | MUST | MOD-010, CORE-070, TIME-010 |
| MOD-013 | Nested Instantiation (prefix concatenation associative) | MUST | MOD-010, MOD-012, MOD-020 |
| MOD-014 | SubnetDef.fromNet retrofit utility | MAY | MOD-001, MOD-006 |
| MOD-020 | Composition Operation (port mapping by structural rewrite) | MUST | MOD-010, MOD-011 |
| MOD-021 | Channel Composition (transition merge: arc union + conflict resolution) | MUST | MOD-005, CORE-021, TIME-001 |
| MOD-022 | Type Compatibility at Compose | MUST | CORE-003, MOD-011, MOD-020 |
| MOD-023 | Composition Produces Flat Net | MUST | MOD-020, MOD-021, CONC-007, EXEC-001 |
| MOD-024 | Identity-Default Port Inference (auto-compose) | SHOULD | MOD-003, MOD-005, MOD-010, MOD-020, MOD-023 |
| MOD-025 | Direct Composition (compose a subnet without instantiation) | MUST | MOD-001, MOD-020, MOD-023, CORE-040 |
| MOD-026 | Subnet-Membership Metadata for Direct Composition | SHOULD | MOD-025, MOD-023, MOD-001 |
| MOD-030 | Action Binding Per Instance (share-by-default, override via bindActions) | MUST | CORE-042, MOD-010 |
| MOD-031 | Action Place Resolution under Composition (declared → actual correspondence) | MUST | MOD-010, MOD-013, MOD-020, MOD-023, MOD-025, MOD-030, CORE-042 |
| MOD-040 | Export Grouping (subgraph cluster_* per instance prefix) | SHOULD | MOD-010, EXP-001, EXP-014 |
| MOD-041 | Debug Protocol Subnet Instances | SHOULD | MOD-010, MOD-013 |
| MOD-050 | Verification Pass-Through on Composed Flat Net | MUST | MOD-023, VER-001 |
| MOD-051 | SubnetDef.verify(harness) for local property verification | SHOULD | MOD-001, VER-001, ENV-001 |
| MOD-060 | Fusion Set Declaration (orthogonal to composition) | MUST | CORE-003, MOD-020 |
| MOD-061 | Fusion Resolution at build() | MUST | MOD-023, MOD-060, CORE-040 |

### NU — ν-nets (correlated fork/join)
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| NU-001 | Name Identity | MUST | CORE-010 |
| NU-010 | Fresh-Name Minting | MUST | CORE-050, IO-011 |
| NU-020 | Match Specification | MUST | IO-001, IO-005, CORE-022, CORE-013 |
| NU-021 | Guard / Match Composition | MUST | NU-020 |
| NU-022 | Deterministic Match Selection | MUST | NU-020, NU-001 |
| NU-030 | Freshness Scoping under Composition | MUST | MOD-010, MOD-012, MOD-020 |
| NU-040 | Bounded Budget and Decidability | SHOULD | VER-002, EXEC-040, NU-010, NU-020 |
| NU-050 | Exact Verification of Matched Transitions | MAY | VER-004, NU-020, NU-040 |
| NU-051 | EXTENDED Coloured-Consumer Fragment | MAY | NU-050, VER-012, NU-020 |
| NU-052 | Conflict-Only Priority for Route B | MAY | VER-012, NU-050, NU-020 |
| NU-053 | EXTENDED-Coloured Quiescence in Route A SMT | MAY | NU-050, NU-051, VER-004, VER-012 |
| NU-060 | Match-Arc Composition | SHOULD | MOD-021, NU-020 |

### PERF — Performance
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| PERF-001 | Linear Scaling | MUST | CONC-005 |
| PERF-002 | Enablement Check O(W) | MUST | CONC-004 |
| PERF-003 | Dirty Set O(affected) | MUST | CONC-005 |
| PERF-004 | Lock-Free Hot Path | MUST | CONC-006 |
| PERF-010 | Noop Event Store Zero-Cost | MUST | EVT-022 |
| PERF-011 | Inline Action Optimization | SHOULD | CONC-011 |
| PERF-020 | Benchmark Suite | MUST | — |
| PERF-021 | Target Performance Ranges | SHOULD | — |
| PERF-022 | Regression Detection | MUST | — |
| PERF-030 | Bitmap Memory Efficiency | MUST | — |
| PERF-031 | Token Storage Efficiency | SHOULD | — |
| PERF-040 | Flat-Array Memory Layout | SHOULD | CONC-020 |
| PERF-041 | Precompiled Executor Target Speedup | SHOULD | CONC-020, PERF-020 |
| PERF-042 | Sparse Enablement Masks | SHOULD | CONC-004, CONC-020 |

### TIME — Timing
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| TIME-001 | Timing Specification | MUST | — |
| TIME-002 | Immediate Timing | MUST | — |
| TIME-003 | Deadline Timing | MUST | EVT-008 |
| TIME-004 | Delayed Timing | MUST | — |
| TIME-005 | Window Timing | MUST | — |
| TIME-006 | Exact Timing | MUST | — |
| TIME-010 | Clock Starts on Enablement | MUST | — |
| TIME-011 | Clock Restarts on Re-enablement | MUST | — |
| TIME-012 | Clock Restart on Reset Arc | MUST | CORE-034, EVT-004 |
| TIME-013 | Deadline Enforcement | MUST | EVT-008 |
| TIME-014 | Competitive Scheduling with Timing | MUST | EXEC-003 |

### VER — Verification
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| VER-001 | SMT Verification Pipeline | SHOULD | — |
| VER-002 | Safety Properties | SHOULD | — |
| VER-003 | Verification Result | SHOULD | — |
| VER-004 | Untimed Over-Approximation | SHOULD | — |
| VER-005 | P-Invariant Computation | SHOULD | — |
| VER-006 | Environment Analysis Mode | SHOULD | — |
| VER-010 | State Class Graph Analysis | MAY | — |
| VER-011 | DBM Zone Representation | MAY | — |
| VER-012 | Name-Aware State Class Graph (ν-Partition Quotient) | MAY | VER-010, 011, NU-020, NU-050 |
| VER-020 | Siphon and Trap Analysis | MAY | — |
| VER-021 | XOR Branch Analysis | SHOULD | IO-012, 016 |

---

## Priority Distribution

| Priority | Count | Description |
|----------|-------|-------------|
| MUST     | 140   | Core contract; all implementations must conform |
| SHOULD   | 53    | Recommended; implementations should include unless technically infeasible |
| MAY      | 13    | Optional; implementations may include |

---

## Shared Semantics vs Implementation-Specific Divergences

| Aspect | Shared | Java | TypeScript | Rust |
|--------|--------|------|------------|------|
| Arc types | 5 (Input, Output, Inhibitor, Read, Reset) | ✓ | ✓ | ✓ (untyped PlaceId) |
| Input cardinality | 4 (One, Exactly, All, AtLeast) | ✓ | ✓ | ✓ |
| Output composition | 5 (And, Xor, Place, Timeout, ForwardInput) | ✓ | ✓ | ✓ |
| Timing variants | 5 (Immediate, Deadline, Delayed, Window, Exact) | ✓ | ✓ | ✓ |
| Bitmap word size | — | 64-bit (long) | 32-bit (Uint32Array) | 64-bit (u64) * |
| Concurrency model | Single-threaded orchestrator | Actions invoked inline; concurrency from the returned stage (e.g. virtual threads) | Promise microtasks | Tokio async tasks |
| Timeout abandonment | Firing abandoned; pre-timeout output discarded ([IO-013]) | ✓ (context detach) | ✓ (context detach) | ✓ (drops ctx) |
| Sync action-throw containment | Failing action fails only that firing ([EXEC-030]) | ✓ | ✓ | ✓ |
| Inject after natural termination | Rejected, not hung ([ENV-006]) | ✓ (`terminated` flag) | ✓ (draining guard) | ✓ |
| Immediate termination / observable termination | [ENV-015] / [ENV-016] (MAY) | ✓ | Pending | Pending |
| Token type safety | Typed places + typed tokens | Generics (compile-time) | Phantom type param | Generics (compile-time) |
| Guard predicates | Filter on input arcs | ✓ (on Arc.Input) | ✓ (on In variants) | Not yet |
| SMT verification | IC3/PDR via Z3 Spacer | ✓ | ✓ (WASM) | Not yet |
| State class graph | Berthomieu-Diaz | ✓ | ✓ | ✓ |
| Graph export | At least one format | DOT (Graphviz) | DOT (Graphviz) | DOT (Graphviz) |
| Log capture | Action log → events | SLF4J LogCaptureScope | ctx.log() | Not yet |
| Debug event store | Live tailing | ✓ | ✓ | ✓ |
| Action binding | Separated from structure | ✓ (bindActions) | ✓ (bindActions) | NetStructureBuilder |
| Precompiled flat-array executor | 2–4× speedup via flat arrays | ✓ (PrecompiledNetExecutor) | ✓ (PrecompiledNetExecutor) | Not yet |
| Inline sync execution | Avoid task dispatch | — | — | ✓ (try_run_inline) |
| Modular composition | Open-net subnets, instantiation, port composition, fusion | Not yet | Not yet | Not yet |
| ν-net correlated fork/join | Fresh-name minting + join by name equality | ✓ | ✓ | ✓ |

\* Rust uses 64-bit words matching Java.

**Python** (`libpetri-py`) binds the Rust crate rather than re-implementing the engine, so it
inherits the Rust column above instead of forming its own, and its session archives are
wire-compatible with Rust's. A few SHOULD capabilities currently land Rust/Python-first —
mid-execution snapshot ([ENV-014]), marking snapshot/restore ([CORE-073]), live event
subscriptions ([EVT-031]), and the marking replay cache ([EVT-032]); their per-language status is
tracked in those requirements.

**Executor-hardening divergence (Java-first).** A 2026 hardening pass landed several
robustness fixes in Java ahead of the other implementations: a synchronous action throw fails
only that firing rather than killing the loop ([EXEC-030]); output written before an `Out.Timeout`
budget expires is discarded rather than merged with the timeout branch ([IO-013] AC5); `inject()`
after natural termination is rejected rather than hanging ([ENV-006]); and the new lifecycle
surface `terminateNow()` / `awaitTermination()` / run-timeout policy ([ENV-015], [ENV-016]).
TypeScript has since matched the failure-containment ([EXEC-030]) and timeout-abandonment
([IO-013]) semantics via a context-detach port, and already satisfied inject-after-termination by
construction — its draining/closed guard makes the hang unreachable. Rust matches the same three.
The lifecycle surface ([ENV-015]/[ENV-016]) remains Java-only, tracked for a coordinated addition
to Rust/Python/TypeScript. The table above is the authoritative per-language status.

---

## Coverage Matrix

This matrix maps spec requirements to test classes/files in each implementation. "—" indicates no corresponding test exists yet.

| Requirement | Java Test | TypeScript Test | Rust Test |
|-------------|-----------|-----------------|-----------|
| CORE-001–003 | `PlaceTest` | `place.test.ts` | `place::tests` |
| CORE-010–013 | `TokenTest` | `token.test.ts` | `token::tests` |
| CORE-020–022 | `TransitionTest` | `transition.test.ts` | `transition::tests` |
| CORE-030–036 | `ArcTest` | `arc.test.ts` | `arc::tests` |
| CORE-040–042 | `PetriNetTest` | `petri-net.test.ts` | `net::tests` |
| CORE-050–054 | `TransitionActionTest` | `transition-action.test.ts` | `context::tests` |
| CORE-060–064 | `TransitionContextTest` | `transition-context.test.ts` | `context::tests` |
| CORE-070–072 | `MarkingTest` | `marking.test.ts` | `marking::tests` |
| CORE-073 | — | — | `executor_handle::tests`; Python `test_marking_snapshot.py` (Rust/Python-first) |
| IO-001–007 | `InTest` | `in.test.ts` | `input::tests` |
| IO-010–017 | `OutTest` | `out.test.ts` | `output::tests` |
| TIME-001–006 | `TimingTest` | `timing.test.ts` | `timing::tests` |
| TIME-010–014 | `NetExecutorTimingTest` | `executor-timing.test.ts` | — |
| EXEC-001–003 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| EXEC-010–013 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| EXEC-020–022 | `NetExecutorTest` | `executor-support.test.ts` | `executor::tests` |
| EXEC-030–031 | `NetExecutorFailureTest` | `executor-failure.test.ts` | — |
| EXEC-040–041 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| CONC-004–008 | `BitmapNetExecutorTest` | `compiled-net.test.ts` | `compiled_net::tests`, `bitmap::tests` |
| ENV-001–006 | `EnvironmentPlaceTest` | `environment.test.ts` | `injector::tests` |
| ENV-010–013 | `EnvironmentPlaceTest` | `environment.test.ts` | `environment::tests` |
| ENV-014 | — | — | `executor_handle::tests`; Python `test_marking_snapshot.py` (Rust/Python-first) |
| ENV-015–016 | `AbstractNetExecutorEnvironmentTest` (Java-first) | — | — |
| VER-001–006 | `SmtVerifierTest` | `smt-verifier.test.ts` | `structural_check::tests`, `p_invariant::tests` |
| VER-010–011 | `StateClassGraphTest` | `analysis/*.test.ts` | `state_class_graph::tests` |
| VER-012 | `SmtVerifierTest` (Route B) | `smt-verifier.test.ts` (Route B) | `nu_scg_verifier::tests` |
| EVT-001–014 | `NetEventTest` | `net-event.test.ts` | `net_event::tests` |
| EVT-020–024 | `EventStoreTest` | `event-store.test.ts` | `event_store::tests` |
| EVT-025 | `SessionArchiveWriterConsistencyTest`, `SessionArchiveV3Test` | `session-archive-writer-consistency.test.ts`, `session-archive-v3.test.ts` | `session_archive_reader::tests` |
| EVT-031 | — | — | Python `test_subscribe_stream.py` (Rust/Python-first) |
| EVT-032 | `MarkingCacheTest` | `marking-cache.test.ts` | `marking_cache::tests` |
| EXP-001–008 | `DotExporterTest` | `dot-exporter.test.ts` | `dot_renderer::tests`, `mapper::tests` |
| EXP-017 | `ClusterBuilderTest`, `DotRendererTest` | `cluster-builder.test.ts` | `cluster_builder::tests` |
| CONC-020–026 | `PrecompiledNetExecutorEngineTest` | `precompiled-net-executor.test.ts` | — |
| PERF-001–004 | `BitmapNetExecutorBenchmark` | — | — |
| PERF-020–022 | — | — | — |
| PERF-040–042 | `PrecompiledNetExecutorBenchmark` | `precompiled-net-executor.bench.ts` | — |
| MOD-001 | `SubnetDefTest#builder_producesSubnetDef_withName_body_iface` | `subnet-def.test.ts > builder produces SubnetDef with name, body, iface` | `subnet_def::tests::subnet_def_builder_basic` |
| MOD-002 | `SubnetDefTest#subnetDef_isSubnetOpen_andClosedWrapsPetriNet` | `subnet-def.test.ts > Subnet pattern matching on kind is exhaustive` | `subnet::tests::open_variant_carries_subnet_def` |
| MOD-003 | `InterfaceTest#port_sealedHierarchy_isExhaustivelyPatternMatched`, `SubnetDefTest#inputOutputInoutPort_appearOnInterface` | `interface.test.ts > port discriminated direction is preserved through accessors` | `interface::tests::interface_builder_basic_ports` |
| MOD-004 | `SubnetDefTest#inputOutputInoutPort_appearOnInterface` | `interface.test.ts > port discriminated direction is preserved through accessors` | `interface::tests::interface_builder_inout_port` |
| MOD-005 | `InterfaceTest#channel_syncChannel_retrievableByName`, `SubnetDefTest#channel_declared_appearsOnInterface` | `interface.test.ts > channel retrievable by name` | `interface::tests::interface_builder_channel` |
| MOD-006 | `SubnetDefTest#build_rejectsPortPlace_notInBody`, `build_rejectsChannelTransition_notInBody`, `build_rejectsDuplicatePortName_withinNamespace`, `build_rejectsDuplicateChannelName_withinNamespace` | `subnet-def.test.ts > build rejects port place not in body` (and three siblings) | `subnet_def::tests::rejects_port_referencing_non_body_place`, `rejects_duplicate_port_names`, `rejects_channel_referencing_non_body_transition`, `rejects_duplicate_channel_names` |
| MOD-010 | `InstanceTest#instantiate_returnsRenamedBody`, `instantiate_renamedArcsReferenceRenamedPlaces` | `instantiate.test.ts > returns a renamed body where every place starts with prefix + "/"` | `subnet_def::tests::instantiate_returns_renamed_body` |
| MOD-011 | `InstanceTest#instantiate_handleMap_returnsRenamedPort`, `port_typeMismatch_isRejected`, `port_unknownName_isRejected`, `channel_unknownName_isRejected` | `instantiate.test.ts > port handle returns the renamed Place<T> by ORIGINAL name`, `> channel handle returns the renamed Transition by ORIGINAL name` | `subnet_def::tests::instantiate_handle_map_returns_renamed_port`, `instantiate_handle_map_returns_renamed_channel`, `instance::tests::port_panics_on_wrong_type` |
| MOD-012 | `InstanceTest#instantiate_perInstanceStateIsolation`, `ComposeTest#compose_twoProducerInstances_perInstanceState` | `instantiate.test.ts > two instances with different prefixes have disjoint place sets`, `compose.test.ts > compose_twoProducerInstances_perInstanceState` | `subnet_def::tests::instantiate_per_instance_state_isolation`, `compose_e2e::compose_two_producer_instances_per_instance_state` |
| MOD-013 | `SubnetDotExportTest#dotExport_nestedInstance_nestedClusters` (covers nested prefix concatenation observably) | `subnet-dot-export.test.ts > dotExport_nestedInstance_nestedClusters` | `cluster_builder::tests::nested_prefixes_build_tree` |
| MOD-014 | `SubnetDefFromNetTest#fromNet_validNet_succeeds`, `fromNet_portPlaceMissing_throws`, `fromNet_channelTransitionMissing_throws`, `fromNet_outputIsInstantiable` | `subnet-def-from-net.test.ts > valid net + iface yields a well-formed SubnetDef<void>` (and siblings) | `subnet_def::tests::from_net_wraps_existing_petri_net`, `from_net_rejects_port_referencing_non_body_place`, `from_net_rejects_channel_referencing_non_body_transition`, `from_net_result_paramtype_unit` |
| MOD-020 | `ComposeTest#compose_singlePort_mergesPlace`, `compose_internalPlacesGetTheirOwnSlot`, `SubnetRewriterTest#renameNet_endToEnd_renamesEverythingAndFillsMaps` | `compose.test.ts > compose_singlePort_mergesPlace`, `> compose_internalPlacesGetTheirOwnSlot` | `compose::tests::compose_single_port_merges_place`, `compose_internal_places_get_their_own_slot` |
| MOD-021 | `ChannelCompositionTest#channelMerge_unionsArcsFromBothSides` (+ 16 sibling cases) | `channel-composition.test.ts > channelMerge_unionsArcsFromBothSides` (+ 16 sibling cases) | `rewriter::tests::channel_merge_unions_arcs_from_both_sides` (+ 14 sibling cases), `channel_composition::channel_merge_end_to_end_retry_policy` |
| MOD-022 | `ComposeTest#compose_typeMismatch_throwsIllegalArgumentException`, `compose_typedBindings_compileTimeSafe` | `compose.test.ts > compose_typeMismatch_compileTimeOnly: typed bindPort signature rejects wrong types at compile time` | `compose::tests::compose_typed_bindings_form` (compile-time enforcement; type errors validated by `cargo check`) |
| MOD-023 | `ComposeTest#compose_producerBufferConsumer_endToEnd` | `compose.test.ts > compose_producerBufferConsumer_endToEnd: tokens flow producer -> buffer -> consumer` | `compose_e2e::compose_producer_buffer_consumer_end_to_end` |
| MOD-024 | `AutoComposeTest#autoCompose_structurallyEqualToExplicitBindPort` (+ 7 sibling cases: explicit-interface match, host-no-pre-declare via arcs, no-interface body inference, channel rejection, multi-subnet e2e, inout port, empty body) | `auto-compose.test.ts > autoCompose_structurallyEqualToExplicitBindPort` (+ 7 sibling cases) | `auto_compose::auto_compose_structurally_equal_to_explicit_bind_port` (+ 7 sibling cases) |
| MOD-025 | `ComposeDirectTest#composeDirect_mergesBodyPlacesByName` (+ 12 sibling scenarios, `SCG-1/2` reachability + order-independence) | `compose-direct.test.ts > composeDirect_mergesBodyPlacesByName` (+ sibling scenarios) | `compose_direct_e2e::compose_direct_merges_body_places_by_name` (+ siblings; validation panics covered by `compose_direct_subnet_with_channel_panics` / `compose_direct_transition_name_collision_panics`) |
| MOD-026 | `ComposeDirectMembershipTest` | `compose-direct-membership.test.ts` | `petri_net::tests::direct_compose_records_membership_per_subnet` (+ siblings) |
| MOD-030 | `InstanceTest#instantiate_actionsSharedByReference`, `bindActions_overridesOnlyForThisInstance`, `bindActions_partialOverride_leavesUnnamedTransitionsAlone` | `instantiate.test.ts > two instances of the same def share each transition's action by reference`, `> rebinds the action on the named transition (MOD-030)`, `> does not mutate the original instance (MOD-030: per-instance scope)` | `subnet_def::tests::instantiate_actions_shared_by_reference`, `bind_actions_overrides_only_for_this_instance`, `instance::tests::bind_actions_replaces_action_for_named_transition` |
| MOD-031 | `ComposeTest` (action place resolution) | `compose-action-place-alias.test.ts` | `mod031_place_resolution` |
| MOD-040 | `SubnetDotExportTest#dotExport_singleInstance_oneCluster`, `dotExport_twoInstances_twoSiblingClusters`, `dotExport_nestedInstance_nestedClusters`, `dotExport_clusterIdsAreSanitized` | `subnet-dot-export.test.ts > dotExport_singleInstance_oneCluster`, `> dotExport_twoInstances_twoSiblingClusters`, `> dotExport_nestedInstance_nestedClusters`, `> dotExport_clusterIdsAreSanitized` | `cluster_builder::tests::single_prefix_groups_nodes_and_intra_edges`, `nested_prefixes_build_tree`, `subnet_diagrams::composed_with_clusters_emits_cluster_for_each_prefix` |
| MOD-041 | `DebugProtocolSubnetTest#subscribed_composedNet_populatedSubnetInstances`, `subscribed_nestedInstance_parentPrefixSet`, `placeInfo_instancePrefix_populated`, `transitionInfo_instancePrefix_populated`, `netEventConverter_emitsInstancePrefixForPrefixedEvents` | `subnet-protocol.test.ts > subscribed_composedNet_populatedSubnetInstances`, `> subscribed_nestedInstance_parentPrefixSet`, `> placeInfo_instancePrefix_populated`, `> transitionInfo_instancePrefix_populated`, `> netEventConverter_emitsInstancePrefixForPrefixedEvents` | `debug_session_registry::tests::subscribed_composed_net_populated_subnet_instances`, `subscribed_nested_instance_parent_prefix_set`, `place_info_instance_prefix_populated_for_prefixed_names`, `transition_info_instance_prefix_populated_for_prefixed_names` |
| MOD-050 | `SubnetVerifyTest#verify_returnsResultWithAllProperties`, `verify_leakyBucket_isKBounded` (verifier sees composed flat net with no special API) | `subnet-verify.test.ts > verify_returnsResultWithAllProperties — one entry per harness property`, `> verify_leakyBucket_isKBounded` | `subnet_verify::verify_leaky_bucket_is_k_bounded`, `subnet_verify::verify_synthetic_net_binds_all_ports` |
| MOD-051 | `SubnetVerifyTest#verify_missingInputGenerator_throws`, `verify_outputPortOnly_doesNotRequireGenerator`, `verify_syntheticNetBindsAllPorts`, `verify_inputGenerator_isInvokedAtConstruction`, `verify_leakyBucket_isKBounded` | `subnet-verify.test.ts > verify_missingInputGenerator_throws — names the missing port`, `> verify_outputPortOnly_doesNotRequireGenerator`, `> verify_syntheticNetBindsAllPorts`, `> verify_inputGenerator_isInvokedAtConstruction`, `> verify_leakyBucket_isKBounded` | `harness::tests::verify_missing_input_generator_panics`, `verify_output_port_only_does_not_require_generator`, `verify_synthetic_net_binds_all_ports`, `verify_input_generator_invoked_at_construction`, `verify_returns_result_with_all_properties` |
| MOD-060 | `FusionSetTest#fusionSet_firstMemberIsCanonical`, `fusionSet_typeHomogeneity_enforced`, `fusionSet_emptySet_throws`, `fusionSet_of_factoryConvenience` | `fusion-set.test.ts > firstMemberIsCanonical`, `> emptySet_throws`, `> singleMember_isValid`, `> of_factoryConvenience` | `fusion::tests::fusion_set_first_member_is_canonical`, `fusion_set_empty_panics`, `fusion_set_single_member_is_valid`, `fusion_set_of_factory` |
| MOD-061 | `FusionTest#fuse_substitutesNonCanonicalInArcs`, `fuse_chained_threeBucketsShareLimiter`, `fuse_runsAfterCompose`, `fuse_andCompose_orthogonality` | `fusion.test.ts > fuse_substitutesNonCanonicalInArcs`, `> fuse_chained_threeBucketsShareLimiter`, `> fuse_runsAfterCompose`, `> fuse_andCompose_orthogonality` | `fusion::fuse_substitutes_non_canonical_in_arcs`, `fuse_chained_three_buckets_share_limiter`, `fuse_runs_after_compose`, `fuse_and_compose_orthogonality` |
| NU-001–060 | `AbstractNetExecutorEngineTest#nuJoin_matchesByName_notFifo`, `nuJoin_blocksWithoutMatchingName`, `nuFork_mintsUniqueIds_thenJoinMerges` (all 3 executors) | `nu-net.test.ts > join matches by name, not FIFO` (+ siblings, both executors) | `backend_suite_tests::nu_join_matches_by_name_not_fifo`, `nu_join_blocks_without_matching_name`, `nu_fork_mints_unique_ids_then_join_merges` (both backends); Python `test_nu_net.py` |
| NU-052 | `NuScgPriorityTest` | `name-scg-priority.test.ts` | `nu_scg_verifier::tests` (priority); Python `test_nu_verification.py` |
| NU-053 | `SmtVerifierTest` (Route A quiescence) | `smt-verifier.test.ts` (Route A quiescence) | `name_coloured_encoder::tests`, `smt_verifier::tests` (nu053); Python `test_nu_verification.py` |

---

## Real-World Pattern Examples

These patterns are derived from a representative real-time event-driven workflow (~50 transitions, 70+ places) and are called out in the relevant spec files:

| Pattern | Spec Requirement | Example |
|---|---|---|
| Reset arcs don't require tokens | [CORE-034] | Timestamp place cleared on new operation |
| Read arcs enable multi-reader | [CORE-033] | Shared result list read by multiple downstream actions |
| Inhibitor negative precondition | [CORE-031] | Violation flag blocks downstream fork |
| XOR exactly-one routing | [IO-012] | Guard → safe/violation; Classification → branch A/branch B |
| In.all() drain semantics | [IO-003] | Buffered data drained on processing window open |
| Competitive scheduling | [EXEC-003] + [TIME-014] | Primary action P=10 vs fallback P=-10 with 3s delay |
| Implicit long-running behavior | [ENV-010] | Session awaits external events indefinitely |
| Multiple environment places | [ENV-012] | Activity signals, data streams, tool requests, state changes |
| Action timeout | [EXEC-022] | Guard actions with 2s timeout |
| Stale detection via read arc | [EXEC-050] | Commit action reads latest timestamp to detect staleness |
