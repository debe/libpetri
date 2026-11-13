<!-- Generated from lean/Libpetri/Spec/Text/Chapter/Ch00.lean, the chapters and the requirement texts, by lean/spec-tools/Render.lean. Do not edit: edit the Lean source, then run `lake env lean spec-tools/Render.lean` from lean/. -->
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
- **Rule only**: requirement text states no runtime status. Per-language API names are in each language's own documentation; defects, unbuilt requirements and implementation-defined divergences are in the runtime ledger ([runtime-defects.md](runtime-defects.md)).
- **Status lines**: an accepted requirement carries no `Status` line. `**Status:** Proposed` marks a requirement that at least one implementation it targets has not built yet. The spec does not say which: each such implementation has an UNBUILT entry for the requirement in the runtime ledger ([runtime-defects.md](runtime-defects.md)), and the Status line is deleted when the last entry closes. `**Status:** Removed` marks a tombstone. Requirement text states the rule only; what a runtime does beyond it belongs to that runtime's own documentation, and where a runtime breaks an accepted requirement, to a defect entry in the ledger.

---

## Spec Files

| File | Prefix | Scope | Req Count |
|------|--------|-------|-----------|
| [01-core-model.md](01-core-model.md) | CORE | Places, tokens, transitions, arcs, dead-arc warning, net construction, actions, context, marking | 35 |
| [02-input-output-specs.md](02-input-output-specs.md) | IO | Input cardinality, composite output routing, validation | 14 |
| [03-timing.md](03-timing.md) | TIME | Firing intervals, clock semantics, deadline enforcement, injectable clock | 12 |
| [04-execution-model.md](04-execution-model.md) | EXEC | Orchestrator loop, scheduling, token consumption, failure, quiescence, terminal places | 14 |
| [05-concurrency.md](05-concurrency.md) | CONC | Single-threaded orchestrator, bitmap executor, precompiled flat-array executor, async actions, wake-up | 17 |
| [06-environment-places.md](06-environment-places.md) | ENV | External event injection, implicit long-running behavior, executor lifecycle | 13 |
| [07-verification.md](07-verification.md) | VER | SMT/IC3, total budget, state-equation phase, firing bound, bounded witness phase, state class graph, stubborn-set reduction, timed counterexample check, structural analysis, open-net contracts | 23 |
| [08-events-observability.md](08-events-observability.md) | EVT | Event types, event store, log capture | 23 |
| [09-export.md](09-export.md) | EXP | Graph export, formal interchange | 17 |
| [10-performance.md](10-performance.md) | PERF | Scaling, benchmarks, memory efficiency, flat-array executor performance | 14 |
| [11-modular-composition.md](11-modular-composition.md) | MOD | Open-net subnet definition, instantiation, port composition, bound-port references, channel fusion, action binding per instance, place fusion | 27 |
| [12-nu-nets.md](12-nu-nets.md) | NU | Token name identity, fresh-name minting (ν-binder/fork), join by name equality, join relay, name alignment, bounded-budget decidability ledger | 15 |
| **Total** | | | **224** |

> **CORE-064** (Execution Context Injection), **IO-006** (Input Guard Predicate), **EXEC-011** (Guarded Token Consumption), **EXEC-050** (Timestamp-Based Stale Detection) and **CONC-012** (Concurrent Action Limit) were removed (see [CORE-064], [IO-006], [EXEC-011], [EXEC-050], [CONC-012]); each is retained as a struck-through tombstone for traceability and **excluded** from the active count. Counts above are active requirements only.

The advice that [CORE-064], [CONC-012] and [EXEC-050] carried is kept in [Usage guidance (non-normative)](#usage-guidance-non-normative).

[glossary.md](glossary.md) defines the terms of the CORE and IO firing semantics. It is unnumbered, holds no requirements and is not counted above.

[runtime-defects.md](runtime-defects.md) is the runtime ledger. It records each place where a runtime breaks or broke a requirement the spec keeps (`RD-NN`, open or fixed, with the change that fixed it), each Proposed requirement a targeted runtime has not built (UNBUILT), and the implementation-defined divergences the spec allows. It is unnumbered, holds no requirements and is not counted above.

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
| ~~CONC-012~~ | ~~Concurrent Action Limit~~ (Removed) | — | — |
| CONC-020 | Precompiled Net Representation | SHOULD | CONC-007 |
| CONC-021 | Opcode-Based Consume Operations | SHOULD | — |
| CONC-022 | Flat-Array Token Storage | SHOULD | CORE-013 |
| CONC-023 | Priority-Partitioned Ready Queues | SHOULD | EXEC-002 |
| CONC-024 | Precomputed Timing Arrays | SHOULD | — |
| CONC-025 | Lazy Marking Synchronization | SHOULD | — |
| CONC-026 | Optional Output Validation Skip | MAY | IO-015, EXEC-021, NU-054 |

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
| CORE-022 | Transition Enablement | MUST | IO-001, CORE-030, CORE-031, CORE-032 |
| CORE-030 | Input Arc | MUST | — |
| CORE-031 | Inhibitor Arc | MUST | — |
| CORE-032 | Read Arc | MUST | — |
| CORE-033 | Read Arc Multi-Reader | MUST | CORE-032 |
| CORE-034 | Reset Arc | MUST | — |
| CORE-035 | Output Arc | MUST | — |
| CORE-036 | Arc Semantics Summary | MUST | — |
| CORE-037 | Dead Arc Warning | SHOULD | CORE-031, CORE-032, CORE-034, CORE-072, ENV-001, EVT-013 |
| CORE-040 | Net Builder | MUST | — |
| CORE-041 | Net Immutability | MUST | CORE-040, EXEC-042 |
| CORE-042 | Action Binding Separation | MUST | — |
| CORE-043 | Output-Declaring Transitions Must Produce | MUST | CORE-042, CORE-051, IO-015 |
| CORE-050 | Transition Action | MUST | — |
| CORE-051 | Passthrough Action | MUST | — |
| CORE-052 | Fork Action | SHOULD | — |
| CORE-053 | Transform Action | SHOULD | — |
| CORE-054 | Produce Action | SHOULD | — |
| CORE-060 | Context Input Access | MUST | CORE-050, EXEC-010 |
| CORE-061 | Context Read Access | MUST | CORE-032, EXEC-012, EXEC-013 |
| CORE-062 | Context Output Access | MUST | CORE-035, IO-013, IO-017 |
| CORE-063 | Context Structure Enforcement | MUST | CORE-060, CORE-061, CORE-062 |
| ~~CORE-064~~ | ~~Execution Context Injection~~ (Removed) | — | — |
| CORE-070 | Marking State | MUST | — |
| CORE-071 | Marking Thread Safety | MUST | — |
| CORE-072 | Initial Marking | MUST | EVT-013 |
| CORE-073 | Marking Snapshot and Restore | MUST | CORE-010, CORE-011, CORE-013, CORE-072, TIME-010, TIME-011, TIME-013, TIME-015, ENV-014, EVT-009, EVT-014, EVT-025, IO-013, MOD-024, NU-022, VER-004, VER-010, VER-013 |

### ENV — Environment Places
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| ENV-001 | Environment Place Wrapper | MUST | — |
| ENV-002 | Environment Place Registration | MUST | ENV-001 |
| ENV-003 | inject() Thread Safety | MUST | ENV-002, ENV-013, ENV-015, CONC-010, EXEC-001, EXEC-041, EXEC-042 |
| ENV-004 | inject() Completion Semantics | MUST | ENV-003, ENV-013 |
| ENV-005 | inject() Wake-Up | MUST | CONC-010, ENV-003, ENV-013, ENV-015, EXEC-001, EXEC-042, TIME-015 |
| ENV-006 | inject() Rejection on Closed or Draining Executor | MUST | ENV-002, ENV-004, ENV-011, ENV-013, ENV-015, EXEC-042 |
| ENV-010 | Implicit Long-Running Behavior | MUST | ENV-001, ENV-002, ENV-003, ENV-005, EXEC-001, EXEC-040, EXEC-041, EXEC-042, TIME-010, TIME-013 |
| ENV-011 | Graceful Drain | MUST | ENV-010, EXEC-001, EXEC-040, EXEC-042, CONC-010 |
| ENV-012 | Event-Driven Workflow Pattern | SHOULD | ENV-001, ENV-002, ENV-003, ENV-004, ENV-010, EXEC-001, CONC-002, CONC-005, TIME-010, TIME-013 |
| ENV-013 | Immediate Close | MUST | ENV-010, ENV-004, EXEC-040 |
| ENV-014 | Mid-Execution Marking Snapshot | SHOULD | ENV-003, ENV-004, ENV-010, ENV-011, ENV-013, ENV-015, EXEC-001, EXEC-031, EXEC-040, CORE-071, CORE-073, TIME-015 |
| ENV-015 | Immediate Termination | MAY | ENV-013 |
| ENV-016 | Observable Termination | MAY | ENV-013, EXEC-041 |

### EVT — Events & Observability
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| EVT-001 | Event Immutability | MUST | — |
| EVT-002 | ExecutionStarted Event | MUST | — |
| EVT-003 | ExecutionCompleted Event | MUST | — |
| EVT-004 | TransitionEnabled Event | MUST | — |
| EVT-005 | TransitionClockRestarted Event | MUST | TIME-012 |
| EVT-006 | TransitionStarted Event | MUST | — |
| EVT-007 | TransitionCompleted Event | MUST | EVT-011, EXEC-020, EXEC-021, EXEC-022 |
| EVT-008 | TransitionFailed Event | MUST | EXEC-030, EXEC-021, NU-054 |
| EVT-009 | TransitionTimedOut Event | MUST | TIME-013 |
| EVT-010 | ActionTimedOut Event | MUST | IO-013, EXEC-022, EVT-009, NU-054 |
| EVT-011 | TokenAdded Event | MUST | — |
| EVT-012 | TokenRemoved Event | MUST | — |
| EVT-013 | LogMessage Event | SHOULD | CORE-072, ENV-012, ENV-013, EXEC-041 |
| EVT-014 | MarkingSnapshot Event | SHOULD | CORE-073 |
| EVT-020 | EventStore Interface | MUST | — |
| EVT-021 | InMemoryEventStore | MUST | — |
| EVT-022 | NoopEventStore | MUST | — |
| EVT-023 | LoggingEventStore | SHOULD | — |
| EVT-024 | DebugEventStore | SHOULD | — |
| EVT-025 | Session Archive Format | SHOULD | — |
| EVT-030 | Event Filtering | SHOULD | — |
| EVT-031 | EventStore Live Subscriptions | SHOULD | EVT-020, EVT-021, EVT-030 |
| EVT-032 | Marking Replay Cache | SHOULD | EVT-021, EVT-004, EVT-006, EVT-007, EVT-008, EVT-009, EVT-010, EVT-011, EVT-012, EVT-014 |

### EXEC — Execution Model
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| EXEC-001 | Orchestrator Loop Steps | MUST | ENV-003 |
| EXEC-002 | Priority-Based Firing Order | MUST | TIME-010 |
| EXEC-003 | Competitive Conflict Resolution | MUST | EXEC-001, EXEC-002, EXEC-010, CORE-022 |
| EXEC-010 | FIFO Token Consumption | MUST | CORE-013, IO-007, NU-020 |
| ~~EXEC-011~~ | ~~Guarded Token Consumption~~ (Removed) | — | — |
| EXEC-012 | Read Arc Peek | MUST | CORE-032, CORE-030 |
| EXEC-013 | Reset Arc Execution | MUST | CORE-034, EXEC-012, CORE-032, EXEC-003 |
| EXEC-020 | Output Token Deposition | MUST | EXEC-021, EXEC-022, EXEC-042, IO-015 |
| EXEC-021 | Output Spec Validation | MUST | IO-011, IO-012, IO-015, EVT-008, EXEC-030, NU-054 |
| EXEC-022 | Action Timeout Handling | MUST | IO-013, IO-014, EVT-010, TIME-015, EXEC-021, NU-054 |
| EXEC-030 | Action Failure | MUST | EVT-008, CONC-002, NU-054 |
| EXEC-031 | No Rollback | MUST | EXEC-021, EXEC-030, NU-054 |
| EXEC-040 | Standard Quiescence | MUST | — |
| EXEC-041 | Execution Result | MUST | EXEC-040, ENV-013, ENV-015 |
| EXEC-042 | Terminal Places | SHOULD | EXEC-001, EXEC-020, EXEC-022, EXEC-040, EXEC-041, CONC-001, IO-015, ENV-004, ENV-013, ENV-014, ENV-015, EVT-013, VER-002, VER-014, VER-022, MOD-001 |
| ~~EXEC-050~~ | ~~Timestamp-Based Stale Detection~~ (Removed) | — | — |

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
| EXP-016 | Subnet Instance Cluster Subgraphs | SHOULD | EXP-001, EXP-014, MOD-010, MOD-026, MOD-040 |
| EXP-017 | Compound Cluster Layout Hints | SHOULD | EXP-012, EXP-014, EXP-016 |
| EXP-018 | ν-Match Edge Decoration | SHOULD | EXP-006, EXP-017, NU-020 |

### IO — Input & Output Specifications
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
| IO-011 | Output And | MUST | IO-015, IO-016 |
| IO-012 | Output Xor | MUST | IO-015, IO-016 |
| IO-013 | Output Timeout | MUST | EVT-009 |
| IO-014 | Output ForwardInput | MUST | IO-007, IO-013, EXEC-010, TIME-015 |
| IO-015 | Output Validation | MUST | EVT-007, CORE-051, CORE-043 |
| IO-016 | Branch Enumeration | SHOULD | — |
| IO-017 | allPlaces Flattening | MUST | — |

### MOD — Modular Composition
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| MOD-001 | SubnetDef Definition (open net + interface) | MUST | — |
| MOD-002 | Subnet Identity (sealed/sum-type distinction from PetriNet) | MUST | — |
| MOD-003 | Port Declaration (name + direction + place) | MUST | — |
| MOD-004 | Port Direction Semantics (advisory; arcs govern flow) | MUST | CORE-030, CORE-031, CORE-032, CORE-033, CORE-034, CORE-035 |
| MOD-005 | Channel Declaration (interface transitions for synchronous fusion) | MUST | — |
| MOD-006 | Subnet Validation at Build | MUST | CORE-040, CORE-041 |
| MOD-010 | Instance Creation via instantiate(prefix, params) | MUST | CORE-001, CORE-040 |
| MOD-011 | Instance Handle Map (typed port + channel handles) | MUST | MOD-003, MOD-005, MOD-010 |
| MOD-012 | Per-Instance State Isolation | MUST | MOD-010, MOD-020, MOD-021, MOD-024, MOD-025, MOD-060, CORE-070, TIME-010, TIME-011, TIME-012, TIME-013 |
| MOD-013 | Nested Instantiation (prefix concatenation associative) | MUST | MOD-010, MOD-012, MOD-014, MOD-020, MOD-021 |
| MOD-014 | SubnetDef.fromNet retrofit utility | MUST | MOD-001, MOD-006 |
| MOD-020 | Composition Operation (port mapping by structural rewrite) | MUST | MOD-003, MOD-010, MOD-011, MOD-021, MOD-022, CORE-030, IO-011, IO-012 |
| MOD-021 | Channel Composition (transition merge: arc union + conflict resolution) | MUST | MOD-005, MOD-020, MOD-031, CORE-011, CORE-021, CORE-030, TIME-001, IO-011, IO-012, EXEC-001, EXEC-012, EXEC-020, CONC-003, NU-060 |
| MOD-022 | Type Compatibility at Compose | MUST | CORE-003, MOD-011, MOD-020 |
| MOD-023 | Composition Produces Flat Net | MUST | MOD-020, MOD-021, CONC-007, EXEC-001 |
| MOD-024 | Identity-Default Port Inference (auto-compose) | SHOULD | MOD-003, MOD-005, MOD-010, MOD-020, MOD-023 |
| MOD-025 | Direct Composition (compose a subnet without instantiation) | MUST | MOD-001, MOD-020, MOD-023, CORE-040 |
| MOD-026 | Subnet-Membership Metadata for Direct Composition | SHOULD | MOD-025, MOD-023, MOD-001 |
| MOD-027 | References to Bound Ports | MUST | MOD-010, MOD-011, MOD-020, MOD-024, MOD-061, CORE-002, CORE-040 |
| MOD-030 | Action Binding Per Instance (share-by-default, override via bindActions) | MUST | CORE-042, MOD-010 |
| MOD-031 | Action Place Resolution under Composition (declared → actual correspondence) | MUST | MOD-010, MOD-013, MOD-014, MOD-020, MOD-021, MOD-023, MOD-024, MOD-025, MOD-030, MOD-061, CORE-042, EXEC-031 |
| MOD-040 | Export Grouping (subgraph cluster_* per instance prefix) | SHOULD | MOD-010, MOD-013, MOD-026, EXP-001, EXP-014, EXP-016 |
| MOD-041 | Debug Protocol Subnet Instances | SHOULD | MOD-010, MOD-013 |
| MOD-050 | Verification Pass-Through on Composed Flat Net | MUST | MOD-023, VER-001 |
| MOD-051 | SubnetDef.verify(harness) for local property verification | SHOULD | MOD-001, MOD-030, VER-001, VER-006, VER-013, VER-022, ENV-001, CORE-042, CORE-043, NU-051 |
| MOD-060 | Fusion Set Declaration (orthogonal to composition) | MUST | CORE-003, MOD-020 |
| MOD-061 | Fusion Resolution at build() | MUST | MOD-021, MOD-023, MOD-060, CORE-040 |

### NU — ν-nets: Correlated Fork / Join by Identity
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| NU-001 | Name Identity | MUST | CORE-010 |
| NU-010 | Fresh-Name Minting | MUST | CORE-050, IO-011, IO-013, IO-014, NU-040, NU-050 |
| NU-011 | Resume-Safe Fresh-Name Minting | MUST | NU-010, NU-020, CORE-073, TIME-015, VER-004 |
| NU-020 | Match Specification | MUST | IO-001, IO-002, IO-003, IO-004, IO-005, IO-007, CORE-022, CORE-013, EXEC-010, NU-001, NU-022 |
| NU-021 | Match as the Sole Per-Token Filter | MUST | NU-020, EXEC-010, IO-007 |
| NU-022 | Deterministic Match Selection | MUST | NU-020, NU-001 |
| NU-030 | Freshness Scoping under Composition | MUST | MOD-010, MOD-020, MOD-021, MOD-061, CORE-042, NU-010, NU-011, NU-054 |
| NU-040 | Bounded Budget and Decidability | SHOULD | VER-002, EXEC-040, NU-010, NU-020 |
| NU-050 | Exact Verification of Matched Transitions | MAY | VER-004, VER-006, VER-012, NU-001, NU-010, NU-020, NU-040, NU-051, NU-053, TIME-001, TIME-012, TIME-013 |
| NU-051 | EXTENDED Coloured-Consumer Fragment | MAY | NU-050, VER-012, NU-020 |
| NU-052 | Conflict-Only Priority for the Route B Name-SCG | MAY | VER-012, NU-050, NU-020, VER-004, VER-002, VER-010, IO-007, NU-055, CONC-002, EXEC-002, EXEC-003 |
| NU-053 | EXTENDED-Coloured Quiescence in the Route A SMT Encoder | MAY | NU-050, NU-051, VER-004, VER-005, VER-006, VER-012, VER-013, VER-015 |
| NU-054 | Join Relay | MAY | NU-020, NU-030, NU-051, NU-053, VER-012, IO-015, IO-016, CONC-026 |
| NU-055 | Name Alignment | MAY | VER-002, VER-003, VER-006, VER-012, NU-010, NU-050, NU-051, NU-054 |
| NU-060 | Match-Arc Composition | SHOULD | MOD-021, NU-020, NU-054 |

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
| TIME-003 | Deadline Timing | MUST | EVT-009 |
| TIME-004 | Delayed Timing | MUST | — |
| TIME-005 | Window Timing | MUST | TIME-001, TIME-003 |
| TIME-006 | Exact Timing | MUST | — |
| TIME-010 | Clock Starts on Enablement | MUST | — |
| TIME-011 | Clock Restarts on Re-enablement | MUST | TIME-010 |
| TIME-012 | Clock Restart on Intermediate Disablement | MUST | TIME-010, TIME-011, CORE-034, EXEC-003, EXEC-013, EVT-004, NU-020, NU-022 |
| TIME-013 | Deadline Enforcement | MUST | TIME-010, EVT-009 |
| TIME-014 | Competitive Scheduling with Timing | MUST | EXEC-002, EXEC-003 |
| TIME-015 | Injectable Clock | SHOULD | TIME-010, TIME-011, TIME-013, CORE-011, CORE-072, EXEC-001, EXEC-002, CONC-010, ENV-003, ENV-004, ENV-005, ENV-013, IO-013, MOD-010, PERF-010, PERF-020, PERF-021 |

### VER — Verification
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| VER-001 | SMT Verification Pipeline | SHOULD | CORE-072 |
| VER-002 | Safety Properties | SHOULD | TIME-013 |
| VER-003 | Verification Result | SHOULD | — |
| VER-004 | Untimed Over-Approximation | SHOULD | TIME-013, EXEC-001, EXEC-003, EXEC-042, CONC-002, NU-052 |
| VER-005 | P-Invariant Computation | SHOULD | — |
| VER-006 | Environment Analysis Mode | SHOULD | VER-002, VER-003, VER-004, VER-012, VER-014, VER-017, VER-022, NU-050, NU-051, NU-055 |
| VER-007 | Invariant Strengthening from P-Semiflows | SHOULD | VER-004, VER-005, VER-006, NU-050, NU-053 |
| VER-010 | State Class Graph Analysis | MAY | IO-007, EXEC-010, TIME-012, TIME-013, VER-001, VER-004, VER-011, VER-013 |
| VER-011 | DBM Zone Representation | MAY | VER-010 |
| VER-012 | Name-Aware State Class Graph (ν-Partition Quotient) | MAY | VER-010, VER-011, VER-017, NU-020, NU-050, IO-007 |
| VER-013 | Solver Transport | SHOULD | VER-001, VER-003, VER-007, VER-017, VER-022, MOD-051, IO-016 |
| VER-014 | Conditional Sink Places (Designed Terminals) | SHOULD | VER-002, VER-012, VER-013 |
| VER-015 | Linear State-Equation Bound | SHOULD | VER-001, VER-004, VER-005, VER-006, VER-013, NU-053 |
| VER-016 | State-Equation Strengthening with Firing Counters | SHOULD | VER-001, VER-004, VER-005, VER-006, VER-007, VER-013, VER-015 |
| VER-017 | Bounded State-Space Enumeration Route | SHOULD | VER-001, VER-002, VER-003, VER-004, VER-006, VER-010, VER-012, VER-013, VER-014, VER-015, VER-024, EXEC-042 |
| VER-018 | State-Equation Phase with Refinement | SHOULD | VER-001, VER-003, VER-004, VER-006, VER-013, VER-015, VER-016 |
| VER-019 | Firing-Bound Phase | SHOULD | VER-001, VER-003, VER-004, VER-013, VER-018 |
| VER-020 | Siphon and Trap Analysis | MAY | — |
| VER-021 | XOR Branch Analysis | SHOULD | IO-012, IO-016, VER-001, VER-004, VER-010 |
| VER-022 | Open-Net Verification Against a Contract | MAY | VER-002, VER-003, VER-004, VER-006, VER-010, VER-012, VER-013, VER-014, VER-017, VER-019, TIME-013, EXEC-042, CORE-043, NU-010 |
| VER-023 | Timed Counterexample Check | SHOULD | VER-002, VER-003, VER-004, VER-006, VER-010, VER-012, VER-013, VER-014, VER-017, VER-022, EXEC-003, EXEC-042, TIME-013 |
| VER-024 | Stubborn-Set Reduction of the Enumeration Route | SHOULD | VER-004, VER-017, VER-021, EXEC-042, IO-014 |
| VER-025 | Bounded Witness Phase | SHOULD | VER-001, VER-003, VER-004, VER-006, VER-013, VER-018, VER-019, VER-023, NU-050, NU-053, NU-055 |

---

## Priority Distribution

| Priority | Count | Description |
|----------|-------|-------------|
| MUST     | 146   | Core contract; all implementations must conform |
| SHOULD   | 62    | Recommended; implementations should include unless technically infeasible |
| MAY      | 16    | Optional; implementations may include |
| **Total** | **224** | Matches the active-requirement total above; tombstones (CORE-064, IO-006, EXEC-011, EXEC-050, CONC-012) excluded |

---

## Coverage Matrix

The proof and test coverage of every active requirement, per implementation, is [coverage-matrix.md](coverage-matrix.md), which `scripts/spec-coverage-matrix.py` generates from the Lean evidence and the `[ID]` citations in the tests.

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
| Stale detection via read arc | [CORE-032] + [CORE-010] (see [Usage guidance](#usage-guidance-non-normative)) | Commit action reads latest timestamp to detect staleness |

## Usage guidance (non-normative)

This section holds advice that used to be written as requirements. It binds no implementation,
has no acceptance criteria and is not counted above. Each entry names the tombstone it came
from.

### Stale detection with a read arc (from [EXEC-050])

A transition can tell whether the data it consumes is still current by comparing timestamps. It
reads a "latest request timestamp" through a read arc ([CORE-032]) and compares it with the
creation timestamp of the token it consumes ([CORE-010]). The engine provides only these
primitives: the comparison is action logic, and a stale token can be routed to a discard
branch through an XOR output ([IO-012]). To test it, read the latest timestamp, consume an
older token and check that the action takes the discard branch.

### Bounding concurrent actions with a permit place (from [CONC-012])

An executor may expose a limit on the number of actions in flight at once, to keep a net with
many enabled transitions from exhausting resources; no implementation does today. The same
bound is better written in the net: a permit place holding N tokens, an input arc from it on
every transition that starts bounded work and an output arc back to it on the transition that
finishes that work.
At most N such actions are then in flight, the rest wait until a permit returns, and the bound
is visible to verification as a place bound.

### Host objects in the transition context (from [CORE-064])

A language binding may let the host put objects such as a tracing span or configuration into
the transition context, keyed by type or by string key, so that the action can read them while
it runs and gets nothing (null or None) for a key that was never set. Not every implementation
offers this, and no requirement depends on it.
