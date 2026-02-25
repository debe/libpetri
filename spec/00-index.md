# TCPN Technical Requirements Specification

## Purpose

This specification defines the **observable contract** of the Timed Coloured Petri Net (TCPN) engine — what the engine guarantees, not how any particular language implements it. It exists for:

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

## Spec Philosophy

- **Language-agnostic**: Requirements describe *what*, not *how*. No Java types, Rust traits, or TypeScript interfaces appear in requirement text.
- **Verifiable**: Every requirement has acceptance criteria that can be tested.
- **Traceable**: Requirements use `[PREFIX-NNN]` cross-references.
- **Implementation notes** appear only where runtime behavior necessarily diverges (e.g., bitmap word size: 64-bit in Java, 32-bit in TypeScript/Rust).

---

## Spec Files

| File | Prefix | Scope | Req Count |
|------|--------|-------|-----------|
| [01-core-model.md](01-core-model.md) | CORE | Places, tokens, transitions, arcs, net construction, actions, context, marking | 33 |
| [02-input-output-specs.md](02-input-output-specs.md) | IO | Input cardinality, composite output routing, validation | 15 |
| [03-timing.md](03-timing.md) | TIME | Firing intervals, clock semantics, deadline enforcement | 11 |
| [04-execution-model.md](04-execution-model.md) | EXEC | Orchestrator loop, scheduling, token consumption, failure, quiescence | 15 |
| [05-concurrency.md](05-concurrency.md) | CONC | Single-threaded orchestrator, bitmap executor, async actions, wake-up | 11 |
| [06-environment-places.md](06-environment-places.md) | ENV | External event injection, long-running mode | 9 |
| [07-verification.md](07-verification.md) | VER | SMT/IC3, state class graph, structural analysis | 10 |
| [08-events-observability.md](08-events-observability.md) | EVT | Event types, event store, log capture | 20 |
| [09-export.md](09-export.md) | EXP | Graph export, formal interchange | 10 |
| [10-performance.md](10-performance.md) | PERF | Scaling, benchmarks, memory efficiency | 11 |
| **Total** | | | **145** |

---

## Alphabetical Cross-Reference Index

### CONC — Concurrency
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| CONC-001 | Orchestrator Thread Ownership | MUST | — |
| CONC-002 | Action Execution on Separate Task Pool | MUST | — |
| CONC-003 | Happens-Before Guarantee | MUST | — |
| CONC-004 | Bitmap-Based Enablement Check | MUST | — |
| CONC-005 | Dirty Set Optimization | MUST | — |
| CONC-006 | Lock-Free Completion Signaling | MUST | — |
| CONC-007 | Compiled Net Representation | MUST | — |
| CONC-008 | Multi-Phase Enablement | MUST | — |
| CONC-010 | Orchestrator Wake-Up | MUST | — |
| CONC-011 | Inline Synchronous Execution | SHOULD | — |
| CONC-012 | Concurrent Action Limit | MAY | — |

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

### ENV — Environment Places
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| ENV-001 | Environment Place Wrapper | MUST | — |
| ENV-002 | Environment Place Registration | MUST | — |
| ENV-003 | inject() Thread Safety | MUST | — |
| ENV-004 | inject() Completion Semantics | MUST | — |
| ENV-005 | inject() Wake-Up | MUST | CONC-010 |
| ENV-006 | inject() Rejection on Closed Executor | MUST | — |
| ENV-010 | Long-Running Mode | MUST | — |
| ENV-011 | Explicit Close | MUST | — |
| ENV-012 | Event-Driven Workflow Pattern | SHOULD | ENV-001, 002, 010 |

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
| EVT-030 | Event Filtering | SHOULD | — |

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

### IO — Input/Output Specifications
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| IO-001 | Input One | MUST | CORE-030 |
| IO-002 | Input Exactly | MUST | CORE-030 |
| IO-003 | Input All | MUST | CORE-030 |
| IO-004 | Input AtLeast | MUST | CORE-030 |
| IO-005 | Input AND-Join Semantics | MUST | — |
| IO-006 | Input Guard Predicate | SHOULD | — |
| IO-007 | requiredCount and consumptionCount Contract | MUST | — |
| IO-010 | Output Place (Leaf) | MUST | — |
| IO-011 | Output And | MUST | — |
| IO-012 | Output Xor | MUST | — |
| IO-013 | Output Timeout | MUST | EVT-009 |
| IO-014 | Output ForwardInput | MUST | — |
| IO-015 | Output Validation | MUST | EVT-007 |
| IO-016 | Branch Enumeration | SHOULD | — |
| IO-017 | allPlaces Flattening | MUST | — |

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
| VER-020 | Siphon and Trap Analysis | MAY | — |
| VER-021 | XOR Branch Analysis | SHOULD | IO-012, 016 |

---

## Priority Distribution

| Priority | Count | Description |
|----------|-------|-------------|
| MUST     | 110   | Core contract; all implementations must conform |
| SHOULD   | 29    | Recommended; implementations should include unless technically infeasible |
| MAY      | 6     | Optional; implementations may include |

---

## Shared Semantics vs Implementation-Specific Divergences

| Aspect | Shared | Java | TypeScript | Rust |
|--------|--------|------|------------|------|
| Arc types | 5 (Input, Output, Inhibitor, Read, Reset) | ✓ | ✓ | ✓ (untyped PlaceId) |
| Input cardinality | 4 (One, Exactly, All, AtLeast) | ✓ | ✓ | ✓ |
| Output composition | 5 (And, Xor, Place, Timeout, ForwardInput) | ✓ | ✓ | ✓ |
| Timing variants | 5 (Immediate, Deadline, Delayed, Window, Exact) | ✓ | ✓ | ✓ |
| Bitmap word size | — | 64-bit (long) | 32-bit (Uint32Array) | 64-bit (u64) * |
| Concurrency model | Single-threaded orchestrator | Virtual threads | Promise microtasks | Tokio async tasks |
| Token type safety | Typed places + typed tokens | Generics (compile-time) | Phantom type param | Generics (compile-time) |
| Guard predicates | Filter on input arcs | ✓ (on Arc.Input) | ✓ (on In variants) | Not yet |
| SMT verification | IC3/PDR via Z3 Spacer | ✓ | ✓ (WASM) | Not yet |
| State class graph | Berthomieu-Diaz | ✓ | — | — |
| Graph export | At least one format | Mermaid | Mermaid | Not yet |
| Log capture | Action log → events | SLF4J LogCaptureScope | ctx.log() | Not yet |
| Debug event store | Live tailing | ✓ | — | — |
| Action binding | Separated from structure | ✓ (bindActions) | ✓ (bindActions) | NetStructureBuilder |
| Inline sync execution | Avoid task dispatch | — | — | ✓ (try_run_inline) |

\* Rust bitmap executor not yet implemented; uses direct iteration.

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
| IO-001–007 | `InTest` | `in.test.ts` | `input::tests` |
| IO-010–017 | `OutTest` | `out.test.ts` | `output::tests` |
| TIME-001–006 | `TimingTest` | `timing.test.ts` | `timing::tests` |
| TIME-010–014 | `NetExecutorTimingTest` | `executor-timing.test.ts` | — |
| EXEC-001–003 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| EXEC-010–013 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| EXEC-020–022 | `NetExecutorTest` | `executor-support.test.ts` | `executor::tests` |
| EXEC-030–031 | `NetExecutorFailureTest` | `executor-failure.test.ts` | — |
| EXEC-040–041 | `NetExecutorTest` | `bitmap-net-executor.test.ts` | `executor::tests` |
| CONC-004–008 | `BitmapNetExecutorTest` | `compiled-net.test.ts` | — |
| ENV-001–006 | `EnvironmentPlaceTest` | `environment.test.ts` | `injector::tests` |
| ENV-010–012 | `LongRunningTest` | `long-running.test.ts` | — |
| VER-001–006 | `SmtVerifierTest` | `smt-verifier.test.ts` | — |
| VER-010–011 | `StateClassGraphTest` | — | — |
| EVT-001–014 | `NetEventTest` | `net-event.test.ts` | `net_event::tests` |
| EVT-020–024 | `EventStoreTest` | `event-store.test.ts` | `event_store::tests` |
| EXP-001–008 | `MermaidExporterTest` | `mermaid-exporter.test.ts` | — |
| PERF-001–004 | `BitmapNetExecutorBenchmark` | — | — |
| PERF-020–022 | — | — | — |

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
| Long-running mode | [ENV-010] | Session awaits external events indefinitely |
| Multiple environment places | [ENV-012] | Activity signals, data streams, tool requests, state changes |
| Action timeout | [EXEC-022] | Guard actions with 2s timeout |
| Stale detection via read arc | [EXEC-050] | Commit action reads latest timestamp to detect staleness |
