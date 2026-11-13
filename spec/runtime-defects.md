<!-- Generated from lean/Libpetri/Spec/Text/Chapter/Ledger.lean and the ledger entries of lean/Libpetri/Spec/Ledger/, by lean/spec-tools/Render.lean. Do not edit: edit the Lean source, then run `lake env lean spec-tools/Render.lean` from lean/. -->
# Runtime Ledger

This file is not a requirement file. It holds no requirement IDs of its own and is not counted
in the 13 spec files or the active requirements of [00-index.md](00-index.md).

It holds three kinds of entry:

- **Defect** (`RD-NN`): a runtime breaks a requirement that the spec keeps. See [Defects](#defects).
- **UNBUILT** (`UB-NN`): a `**Status:** Proposed` requirement that a runtime it targets has not
  built. There is one entry per requirement and set of runtimes. An entry is removed when those
  runtimes build the requirement, and the requirement's Status line is deleted when its last entry
  goes.
- **Divergence**: an implementation-defined difference that the spec allows. It needs no fix and
  has no status.

## Unbuilt requirements

### UB-01. Immediate termination

- **Requirements:** ENV-015.
- **Runtimes:** Rust, TypeScript, Python.
- **Missing:** `terminateNow()`. Java has it on both executors.
- **Status:** open.

### UB-02. awaitTermination

- **Requirements:** ENV-016.
- **Runtimes:** TypeScript, Rust, Python.
- **Missing:** `awaitTermination(timeout)`. Java has it on both executors.
- **Status:** open.

### UB-03. Run-timeout policy

- **Requirements:** ENV-016.
- **Runtimes:** Rust, Python.
- **Missing:** a run with a caller timeout and an *abandon* or *close* policy. Java
  (`run(Duration, RunTimeoutPolicy)`) and TypeScript (`run(timeoutMs, onTimeout)`) have it on both
  executors; Rust has `run_sync` and `run_async` only.
- **Status:** open.

### UB-04. Live event-store subscriptions

- **Requirements:** EVT-031.
- **Runtimes:** Java, TypeScript, Rust.
- **Missing:** live subscriptions on the event store. The Python binding has them
  (`InMemoryEventStore.subscribe` and `subscribe_stream`, built in `rust/libpetri-py`); the Rust
  crate's own `InMemoryEventStore` (`libpetri-event`) has none.
- **Status:** open.

## Divergences

Python binds the Rust crate, so it follows the Rust column unless a cell says otherwise.

| Aspect | Spec | Java | TypeScript | Rust |
|---|---|---|---|---|
| Bitmap word size | not specified | 64-bit (`long`) | 32-bit (`Uint32Array`) | 64-bit (`u64`) |
| Concurrency model | single-threaded orchestrator | actions invoked inline; concurrency comes from the returned stage | Promise microtasks | Tokio async tasks |
| Place equality ([MOD-024]) | implementation's own | structural on name and token type; restore takes the net's places | name only | name only |
| Token type safety | typed places and tokens | generics (compile time) | phantom type parameter | generics (compile time) |
| Inject into an unregistered place ([ENV-002]) | error for a handle-taking inject | failed future | rejects; `injectNoAwait` throws | deposited into the named place; registration is the host's |
| Enablement-timestamp resolution ([EXEC-002] AC3) | sub-ms precision kept | monotonic `long` nanoseconds | float milliseconds | float milliseconds |
| Injectable clock seam ([TIME-015]) | host-supplied clock | `ExecutionEnvironment` | `Clock` | `ExecutorClock`; Python offers only the Rust-side `ManualClock` and `SteppedClock` |
| Mid-action publication ([IO-015]) | optional | none | none | `ctx.flush()`; flushed tokens survive a later validation failure |
| Inline synchronous execution | not specified | none | none | `try_run_inline` |
| Action binding | separate from structure | `bindActions` | `bindActions` | `NetStructureBuilder` |
| Log capture ([EVT-013]) | action log becomes events | SLF4J `LogCaptureScope` | `ctx.log()` | `ctx.log()` |
| Verification cancellation ([VER-013]) | shares the total budget's stop | thread interruption, flag restored | `AbortSignal` | `CancelToken` (Python `libpetri.CancelToken`) |

## Defects

A **runtime defect** is a place where a runtime breaks a requirement that the spec keeps. The
spec was not weakened to match the runtime: the requirement stays as written, the Lean block
states it, and the runtime is fixed later in a runtime change. Each entry names the requirements
it breaks, the runtimes that break them, where in the code, and the Lean evidence that shows it,
if there is any. A Lean block that calls something a recorded defect cites the entry by its
number (`RD-NN`).

An entry stays `open` until the runtime change lands. Its status is then `fixed, unreleased` until
a release carries the fix, and `fixed in <version>` after that. A fixed entry stays here as history,
with a **Fix** item that says what changed and names the regression tests in each runtime. Code
is named by its function, type or test, not by line number.

Every entry from RD-01 to RD-43 is fixed. RD-44 to RD-47 were found while those fixes were made and
are recorded here already fixed.

RD-10, RD-13 and RD-14 were withdrawn on 2026-11-12 as not defects: transition names are assumed
distinct (ruling D23), non-ASCII cluster names are implementation-defined (ruling D46 (a)), and the
collision of sanitized IDs is a known limit of EXP-016. Their numbers are not reused.

| ID | Requirements | Runtimes | Status |
|---|---|---|---|
| RD-01 | EXEC-021, EXEC-022, IO-013, CORE-036 | Java, TypeScript | fixed, unreleased |
| RD-02 | CORE-041 | TypeScript | fixed, unreleased |
| RD-03 | CORE-040, CORE-002, IO-016, IO-017 | TypeScript | fixed, unreleased |
| RD-04 | EVT-001 | TypeScript | fixed, unreleased |
| RD-05 | CORE-042 | TypeScript | fixed, unreleased |
| RD-06 | CORE-051 | Java, TypeScript | fixed, unreleased |
| RD-07 | CORE-021 | Python | fixed, unreleased |
| RD-08 | CORE-043 | Rust, Java, TypeScript, Python | fixed, unreleased |
| RD-09 | CORE-060 | Java | fixed, unreleased |
| RD-11 | MOD-020 | Rust, Java, TypeScript, Python | fixed, unreleased |
| RD-12 | EXP-016, EXP-017, MOD-040 | Rust, Java, TypeScript, Python | fixed, unreleased |
| RD-15 | EXEC-022, CONC-003 | Rust, Python | fixed, unreleased |
| RD-16 | TIME-014, TIME-010, EXEC-001, EXEC-002, TIME-003, TIME-005, TIME-013 | Java, TypeScript | fixed, unreleased |
| RD-17 | EVT-025 | Java | fixed, unreleased |
| RD-18 | EVT-025 | Python | fixed, unreleased |
| RD-19 | EVT-025 | Python | fixed, unreleased |
| RD-20 | EVT-025 | Python | fixed, unreleased |
| RD-21 | EVT-030, EVT-013 | Java | fixed, unreleased |
| RD-22 | EVT-032 | Java | fixed, unreleased |
| RD-23 | MOD-031 | Rust, Java, TypeScript, Python | fixed, unreleased |
| RD-24 | MOD-025 | Java | fixed, unreleased |
| RD-25 | MOD-061, MOD-026 | Rust, Java, TypeScript | fixed, unreleased |
| RD-26 | VER-003, NU-053 | Java | fixed, unreleased |
| RD-27 | NU-051 | Rust, Python | fixed, unreleased |
| RD-28 | VER-017 | TypeScript | fixed, unreleased |
| RD-29 | MOD-051 | TypeScript | fixed, unreleased |
| RD-30 | MOD-031 | Python | fixed, unreleased |
| RD-31 | MOD-031, IO-013, IO-014, CORE-036, EXEC-022 | Java, TypeScript | fixed, unreleased |
| RD-32 | CONC-010, TIME-010 | TypeScript | fixed, unreleased |
| RD-33 | CONC-003, EXEC-020 | Java, TypeScript | fixed, unreleased |
| RD-34 | ENV-016 | Java | fixed, unreleased |
| RD-35 | ENV-002, ENV-010 | Java | fixed, unreleased |
| RD-36 | EVT-025, EVT-014 | Java | fixed, unreleased |
| RD-37 | EXP-017 | Java, TypeScript | fixed, unreleased |
| RD-38 | NU-010 | Rust, Python | fixed, unreleased |
| RD-39 | NU-052, VER-006, NU-055 | Rust, Java, TypeScript, Python | fixed, unreleased |
| RD-40 | VER-010, VER-012 | Rust, TypeScript, Python | fixed, unreleased |
| RD-41 | MOD-030 | TypeScript | fixed, unreleased |
| RD-42 | VER-013 | Java, TypeScript | fixed, unreleased |
| RD-43 | VER-013 | Java | fixed, unreleased |
| RD-44 | EVT-025 | Python | fixed, unreleased |
| RD-45 | EVT-014, EVT-025 | Java | fixed, unreleased |
| RD-46 | EVT-032 | Java | fixed, unreleased |
| RD-47 | CORE-043 | Java | fixed, unreleased |
| RD-48 | EVT-032 | Java, TypeScript, Rust, Python | fixed, unreleased |
| RD-49 | EVT-014 | Rust, Python | fixed, unreleased |
| RD-50 | EVT-014 | Rust, Python | open |
| RD-51 | EVT-030 | Java, TypeScript, Rust | fixed, unreleased |
| RD-52 | EXEC-041 | TypeScript | fixed, unreleased |
| RD-53 | NU-020, NU-054, EXEC-041 | Java, TypeScript | fixed, unreleased |
| RD-54 | IO-012, IO-011 | Rust, TypeScript | fixed, unreleased |

### RD-01. The timeout outcome is validated against the output spec

- **Requirements:** EXEC-021, EXEC-022, IO-013 (ruling D24 (a)), CORE-036 (the ninth sentence: a
  firing that ends with the timeout outcome deposits in every place as many tokens as the timeout
  outcome puts there).
- **Runtimes:** Java, TypeScript.
- **Defect:** both validate the timeout outcome against the whole output spec, so a spec such as
  `And(A, Timeout(d, B))` fails the firing on every timeout instead of depositing `B`. Rust skips
  validation on the timeout path and still runs the join-relay check.
  `java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`
  (`processCompletedTransitions`), `typescript/src/runtime/bitmap-net-executor.ts`
  (`validateOutSpec` in `processCompletedTransitions`, on the completion path that also settles a
  timed-out firing). The production
  executors have the same check: `PrecompiledNetExecutor.processCompletedTransitions` in Java and
  the general branch of `typescript/src/runtime/precompiled-net-executor.ts`.
- **Lean evidence:** `clashExec_timeoutValidated_conflict` (ClashesExec.lean),
  `EXEC_021_forbids_validateTimeout` (EXEC_021.lean), `IO_013_forbids_validateTimeout`
  (IO_013.lean).
- **Fix:** both executors of each runtime skip the output-spec validation and the IO-016
  multiplicity warning for a firing that ended with the timeout outcome and run only the join-relay
  check (NU-054), so `And(A, Timeout(d, B))` deposits `B`. Java
  `AbstractNetExecutorEngineTest.OutputTimeoutTests.outTimeout_andSibling_depositsTheTimeoutChildUnvalidated_EXEC021`
  and `outTimeout_andSibling_forwardsEveryTokenWithoutMultiplicityWarning_EXEC021`; TypeScript
  `executor-shared-semantics.test.ts`, "the timeout outcome is not validated (EXEC-021, EXEC-022,
  IO-013)", on both executors.
- **Status:** fixed, unreleased.

### RD-02. The TypeScript builder hands its live sets to the built net

- **Requirements:** CORE-041 (ruling D66 (a)).
- **Runtimes:** TypeScript.
- **Defect:** `build()` passes the builder's own place and transition sets to the net, so a later
  builder call changes a net that was already built. `PetriNetBuilder.build`
  (`typescript/src/core/petri-net.ts`).
  A channel `compose` after `build()` even deletes the caller transition from the built net. Only
  the build without fusion shares the sets.
- **Lean evidence:** `CORE_041_forbids_alias` (CORE_041.lean), `aliasBuilder_unstable`
  (Reference/Build.lean).
- **Fix:** `build()` hands the net copies of the builder's place and transition sets. TypeScript
  `petri-net.test.ts`, "a built net keeps its places and transitions when the builder is used again
  (CORE-041)" and "a channel compose after build leaves the built net intact (CORE-041)".
- **Status:** fixed, unreleased.

### RD-03. TypeScript identifies places by object reference

- **Requirements:** CORE-040 (line 3, "no place twice"), CORE-002 (ruling D66 (a)), IO-016
  (a branch is a set of places: the `And` line's union), IO-017 (the `And` and `Xor` lines'
  union).
- **Runtimes:** TypeScript.
- **Defect:** `place(name)` returns a new object on each call and the built net keeps places by
  reference, while the compiled net keys them by name, so one place can be held twice.
  `place` (`typescript/src/core/place.ts`), the `_places` field of `PetriNetBuilder` and its
  `transition` method (`typescript/src/core/petri-net.ts`).
  The output spec's place sets do the same: `allPlaces` and `enumerateBranches`
  (`typescript/src/core/out.ts`) collect into a JS `Set` of place objects, so
  `Xor(And(A, B), And(A', C))` with `A` and `A'` two `place('A')` objects (it builds: the IO-011
  and IO-012 checks compare names) has an `allPlaces` set of four members for three places, and
  the unbuildable `And(A, A')` enumerates one branch of two members for one place. The fusion
  build and the `Transition` input, read and output place sets compare places by object as well,
  so `fork` or `transform` on `Xor(And(A, B), And(A', C))` writes `A` twice.
- **Lean evidence:** none beyond the CORE_040, CORE_002, IO_016 and IO_017 assumes; under name
  identity the TypeScript net breaks CORE_040 line 3, and the TypeScript `allPlaces` breaks the
  union of IO_017's `Xor` line.
- **Fix:** places are kept by name, and the first object seen for a name wins, in the builder, the
  fusion build, the transition place sets, `allPlaces` and `enumerateBranches`. TypeScript
  `petri-net.test.ts`, "holds one place for two place objects with one name (CORE-002, CORE-040)"
  and its fusion variant; `transition.test.ts`, "collects input, read and output places by name
  (CORE-002)"; `out.test.ts`, "collects one place per name (CORE-002, IO-017)" and "a branch holds
  one place per name (CORE-002, IO-016)".
- **Status:** fixed, unreleased.

### RD-04. A TypeScript event shares the executor's consumed array

- **Requirements:** EVT-001 (AC2: collections in events are copies; ruling D66 (a)).
- **Runtimes:** TypeScript.
- **Defect:** the `TransitionStarted` event carries the executor's own `consumed` array, which the
  executor also hands on, so the event is not a copy. `typescript/src/runtime/bitmap-net-executor.ts`
  (`fireTransition`), `TransitionStarted` (`typescript/src/event/net-event.ts`). The precompiled executor
  (`typescript/src/runtime/precompiled-net-executor.ts`) does the same.
- **Lean evidence:** none. EVT-001 has no block: a Lean event is a value, so a shared array cannot
  be stated (`netEvent_value`, GlossaryEvents.lean, cites EVT-001).
- **Fix:** both executors put a copy of the consumed tokens into the `TransitionStarted` event, made
  only when an event store is enabled. TypeScript `executor-shared-semantics.test.ts`, "carries a
  copy of the consumed tokens (EVT-001 AC2)", on both executors.
- **Status:** fixed, unreleased.

### RD-05. A TypeScript resolver that returns `undefined` binds `undefined`

- **Requirements:** CORE-042 (a resolver that returns no action defers).
- **Runtimes:** TypeScript.
- **Defect:** `bindActionsWithResolver` treats only `null` as no action, so a plain JavaScript
  resolver such as `name => obj[name]` rebinds an unknown transition to `undefined`.
  `PetriNet.bindActionsWithResolver` (`typescript/src/core/petri-net.ts`). `SubnetDef.bindActionsWithResolver`
  (`typescript/src/core/subnet-def.ts`) makes the same test.
- **Lean evidence:** none; the CORE_042 assumes cite it (the block reads a resolver's `null`/`None`
  as `none`, line 3, and the model has no `undefined`).
- **Fix:** both resolver forms treat `undefined` as `null`, and their return type is widened to
  `TransitionAction | null | undefined`. TypeScript `petri-net.test.ts`, "bindActionsWithResolver
  defers a transition when the resolver returns undefined (CORE-042)";
  `subnet-verify-options.test.ts`, "the resolver form defers a transition on undefined, as on null
  (CORE-042)".
- **Status:** fixed, unreleased.

### RD-06. Java and TypeScript accept `action(null)`

- **Requirements:** CORE-051.
- **Runtimes:** Java, TypeScript.
- **Defect:** the builder setter stores `null` (or `undefined`) as the action. The identity check
  of CORE-043 passes such a transition, and every firing of it then fails. Python raises
  `TypeError`; Rust cannot express it. `Transition.Builder.action`
  (`java/src/main/java/org/libpetri/core/Transition.java`), `TransitionBuilder.action`
  (`typescript/src/core/transition.ts`).
- **Lean evidence:** none; the CORE_051 assumes record it.
- **Fix:** the builder setter rejects a missing action: Java throws `NullPointerException` on
  `action(null)` and TypeScript a `TypeError` on `null` or `undefined`; leaving the call out still
  gives the passthrough default. Java `TransitionTest.core051_builder_rejectsNullAction`; TypeScript
  `transition.test.ts`, "rejects a null or undefined action (CORE-051)".
- **Status:** fixed, unreleased.

### RD-07. A Python transition is not equal to itself when read back

- **Requirements:** CORE-021 (AC2).
- **Runtimes:** Python.
- **Defect:** the `Transition` wrapper defines no `__eq__` or `__hash__`, and `PetriNet.transitions`
  returns a fresh wrapper on every access, so `net.transitions[0] == net.transitions[0]` is
  `False`. The fix is `__eq__` and `__hash__` on the wrapped `TransitionId`.
  `PyTransition` and the `transitions` getter of `PyPetriNet` (`rust/libpetri-py/src/model.rs`).
- **Lean evidence:** none; the CORE_021 assumes record it.
- **Fix:** the wrapper defines `__eq__` and `__hash__` over the wrapped transition's `TransitionId`.
  Python `test_smoke.py::test_core_021_ac2_transition_read_back_equals_itself`.
- **Status:** fixed, unreleased.

### RD-08. The CORE-043 check runs on the derived split net under CONFLICT

- **Requirements:** CORE-043 (line 3: a verification entry point fails exactly when compiling the
  submitted net does).
- **Runtimes:** Rust, Java, TypeScript, and Python through Rust.
- **Defect:** under `PrioritySemantics` CONFLICT the verifier splits a sink into a start half,
  which keeps the sink's name and action and gains an output place, and then runs the CORE-043
  check on that derived net. A net that compiles is refused, and the Rust error says the sink
  declares an output spec when it declares none.
  Rust: `with_in_flight` (`rust/libpetri-verification/src/smt_verifier.rs`), `halves`
  (`in_flight.rs`), `verify_name_scg` (`nu_scg_verifier.rs`), `StateClassGraph::build_core`
  (`state_class_graph.rs`).
  Java: the state-space lookup in `SmtVerifier.pipeline`
  (`java/src/main/java/org/libpetri/smt/SmtVerifier.java`), `StateClassGraph.initialStateClass`
  (`java/src/main/java/org/libpetri/analysis/StateClassGraph.java`).
  TypeScript: `SmtVerifier.verify` (`typescript/src/verification/smt-verifier.ts`, after `prepare()`).
  Rust's SMT entry already checks the submitted net; its refusals come from the graph builders it
  calls on the split net, which are CORE-043 entry points with checks of their own, so a check
  run once before any rewrite does not end the defect on its own. Java also checks a field that
  a previous call left rewritten, so a reused verifier can fail its second call (RD-47).
- **Lean evidence:** none; the CORE_043 assumes record it.
- **Fix:** the start half of a split passthrough sink gets a placeholder action instead of the
  passthrough in all three runtimes, so the split net passes CORE-043 exactly when the submitted net
  does; Java and TypeScript also run the entry check on the caller's net before `prepare()`. The
  public graph builders keep their own checks. Rust `smt_verifier.rs`
  `core043_conflict_split_of_a_passthrough_sink_is_not_refused`; Java
  `SplitDemandTest.CORE043_aConflictSplitOfAPassthroughSinkIsNotRefused`; TypeScript
  `smt-verifier-core043.test.ts`, "a conflict split of a passthrough sink is not refused
  (CORE-043)"; Python
  `test_smoke.py::test_core_043_conflict_split_of_a_passthrough_sink_is_not_refused`.
- **Status:** fixed, unreleased.

### RD-09. Java's `input` with several tokens contradicts its own javadoc

- **Requirements:** CORE-060 (the case is open in the spec; ruling D50 (a)).
- **Runtimes:** Java.
- **Defect:** with more than one token delivered from a place, `input` returns the oldest token's
  value, while its javadoc says it fails. Rust, TypeScript and Python report an error.
  `TransitionContext.input` (`java/src/main/java/org/libpetri/core/TransitionContext.java`) against
  its own javadoc.
  Java's `fork()` and `transform(Place, fn)` rely on `input` returning the oldest token (the
  documented CORE-052 divergence), so the javadoc is what is wrong.
- **Lean evidence:** `CORE_060_batch_undecided` shows the block leaves the case open; the
  defect is Java against its own documentation.
- **Fix:** the javadoc says that `input` returns the oldest value and points to `inputs(Place)` for
  the whole batch; the behaviour is unchanged. Java
  `TransitionContextTest.core060_input_withSeveralTokens_returnsOldestValue` pins it.
- **Status:** fixed, unreleased.

### RD-11. A caller transition bound to two channels is not rejected

- **Requirements:** MOD-020 (ruling D72 (ii)(b): a caller transition bound to two channels of
  one instance in one call is an error, AC6). The port half of the first entry is withdrawn:
  every runtime rejects a port re-bound in one call with `Port '<name>' is already bound`
  (ruling D72 (i)(a); `ComposeBindingsBuilder::bind_port` in `rust/libpetri-core/src/compose.rs`,
  `ComposeBindings.bindPort` in `java/src/main/java/org/libpetri/core/ComposeBindings.java` and
  `typescript/src/core/compose-bindings.ts`).
- **Runtimes:** all.
- **Defect:** no runtime rejects one caller transition bound to two channels of one instance.
  Rust stages the merges in a map keyed by the caller's name, so only the merge its hash order
  visits last survives; Java and TypeScript add both merges under one name
  (`apply_composition` in `rust/libpetri-core/src/petri_net.rs`, `applyComposition` in
  `java/src/main/java/org/libpetri/core/PetriNet.java` and `typescript/src/core/petri-net.ts`).
- **Lean evidence:** none; MOD-020 makes distinct caller-side names a caller obligation
  (`mod020_fresh`, MOD_020.lean) and states nothing about such a call.
- **Fix:** each runtime's channel binding rejects a caller transition, compared by identity, that is
  already bound to another channel of the call, with `Transition '<t>' is already bound to channel
  '<c1>'; it cannot also be bound to channel '<c2>' (MOD-020)`; Python raises it as `ValueError`.
  Rust `compose.rs` `bind_channel_rejects_one_caller_transition_on_two_channels_mod020` and
  `compose_one_caller_transition_on_two_channels_names_both_mod020`; Java
  `ChannelCompositionTest.compose_oneCallerTransitionOnTwoChannels_isRejected_MOD020_AC6`;
  TypeScript `channel-composition.test.ts`, "compose_oneCallerTransitionOnTwoChannels_isRejected
  (MOD-020 AC6)"; Python
  `test_channel_composition.py::test_one_caller_transition_bound_to_two_channels_is_rejected`.
- **Status:** fixed, unreleased.

### RD-12. An empty `/` segment in a cluster key fails the export

- **Requirements:** EXP-016, EXP-017, MOD-040 (ruling D46 (a)).
- **Runtimes:** Rust (panics), Java and TypeScript (throw), and Python through Rust.
- **Defect:** on a key such as `a//x` or `http://host/x`, `register_prefix_chain` skips the empty
  segment and never registers the key itself; the builder then fails at the node's key.
  `rust/libpetri-export/src/cluster_builder.rs` (`register_prefix_chain`). Python's
  `dot_export` and archive writer reach that exporter and raise `PanicException`. Java fails on
  fewer keys: `String.split` keeps inner empty segments, so the keys `a//x` and `http://host`
  draw, and only a key with a leading or trailing `/`, such as `/a` (the key of `/a/x`) or `a/`
  (the key of `a//x`), throws a `NullPointerException`
  (`java/src/main/java/org/libpetri/export/ClusterBuilder.java`, `registerPrefixChain`).
  TypeScript throws a `TypeError` on a key with a leading `/` and on the empty key
  (`typescript/src/export/cluster-builder.ts`).
- **Lean evidence:** `registerChain` (Reference/ExportCluster.lean); EXP-016's name assumption
  (`ExportNet.ClusterKeysWellFormed`) keeps such nets out of the block.
- **Fix:** the three exporters register the glossary key chain (every non-empty prefix that ends
  before a `/`, then the key itself, the empty key included) and take the deepest common prefix as
  the longest element of one chain that is in the other; keys without an empty segment draw as
  before. Rust `cluster_builder.rs` `exp_016_key_with_empty_segment_registers_its_key_chain` and
  `dot_exporter.rs` `exp_016_empty_segment_names_export_without_panic`; Java
  `ClusterBuilderTest.partitionRegistersTheKeyChainOfAKeyWithAnEmptySegment_EXP016` and
  `SubnetDotExportTest.dotExport_emptySegmentNames_doNotThrow_EXP016`; TypeScript
  `cluster-builder.test.ts`, "EXP-016: a key with an empty /-segment (a/, a//x, /a) draws its key
  chain and does not throw"; Python
  `test_dot_export.py::test_exp_016_empty_segment_cluster_key_exports_without_panic` and
  `::test_exp_016_empty_segment_cluster_key_archives_without_panic`.
- **Status:** fixed, unreleased.

### RD-15. A flush can publish after the action completed

- **Requirements:** EXEC-022 (line 4: no output the action had not published before the budget
  ran out is deposited or published); CONC-003 (line 2: a publication deposits only a batch the
  action flushed before it completed).
- **Runtimes:** Rust, Python.
- **Defect:** the flush closure has no completed or abandoned check and can outlive the action:
  a Rust action that moved `ctx.flush_fn()` into a spawned task, or a Python context held past
  the action, can still send a batch after the action completed, by a normal return, an error
  return or the expiry of its budget (on a timeout the executor drops the action future). Phase
  1b then deposits that batch, although the action had completed before it flushed it. The fix
  is an abandoned flag on the closure, set in the timeout arm and at completion.
  `rust/libpetri-runtime/src/executor_core/executor.rs` (the `set_flush_fn` closure in
  `fire_transition_async`), `rust/libpetri-core/src/context.rs` (`flush_fn`),
  `rust/libpetri-py/src/action.rs` (`PyActionContext::from_transition_context`).
- **Lean evidence:** `EXEC_022_forbids_lateFlush` (EXEC_022.lean); `CONC_003_forbids_flushAfterError`
  (CONC_003.lean), the case after an error return.
- **Fix:** the flush closure and its spawned task share a gate under one lock: the task marks the
  firing ended once the action completes, fails or times out, before it sends the completion, and a
  later flush returns an error naming EXEC-022 and deposits nothing (Python raises `RuntimeError`).
  Rust `backend_suite_tests.rs` `late_flush::exec_022_a_flush_after_the_firing_ended_is_refused` and
  `late_flush::exec_022_a_flush_before_the_timeout_is_deposited`; Python
  `test_ctx_flush.py::test_a_flush_after_the_timeout_is_refused_exec_022` and
  `::test_a_flush_after_the_action_returned_is_refused_exec_022`.
- **Status:** fixed, unreleased.

### RD-16. Java's firing pass and decision to wait judge at readings of their own

- **Requirements:** TIME-014 (line 3), TIME-010 (the firing pass and the decision to wait judge
  at the deadline step's reading, and no other step of the cycle takes a new reading for these
  judgements), EXEC-001 (ruling D61 (c)), EXEC-002 (the executor companion `EXEC_002_cycle`, line 1:
  a pass starts only transitions of the ready order at the deadline step's reading), TIME-003
  (line 2), TIME-005 (line 3), TIME-013 (line 2: no firing of a reapable transition whose elapsed
  time is greater than its latest bound plus the tolerance).
- **Runtimes:** Java (both executors) and TypeScript (its decision to wait; see RD-32).
- **Defect:** a Java cycle takes four readings of the firing clock: the enablement update, the
  deadline step, the firing pass and the decision to wait each read the clock (`clockNanos()`).
  The pass judges readiness at its own reading instead of the deadline step's, and the decision
  to wait judges the next timing boundary at a fourth reading (`nanosUntilNextTimedTransition`,
  called from `awaitCompletionOrEvent`, its poll loop and `awaitExternalEvent`). Rust takes one
  reading per cycle and conforms. TypeScript's deadline step and pass share one reading, which
  conforms, but its decision to wait takes another (RD-32). The pass checks only the earliest
  bound at its reading and never checks expiry again, so a `Deadline` or `Window` transition
  whose elapsed time passes its latest bound plus the tolerance between the deadline step's reading and the pass's is neither reaped nor refused:
  it fires. Example: `Deadline(100)`, tolerance 5, armed at 0; the deadline step reads 105.9 ms
  (elapsed 105, not past 105, so no reap), the pass reads 106.0 ms (elapsed 106) and fires it.
  The reading at the decision to wait is later than the deadline step's, so it only shortens the
  wait, which CONC-010 accepts; it is still a new reading that TIME-010 rules out.
  `updateDirtyTransitions`, `enforceDeadlines`, `fireReadyGeneral` and
  `nanosUntilNextTimedTransition` (used in `awaitCompletionOrEvent`, its poll loop
  `awaitCompletionPolling` and `awaitExternalEvent`), in
  `java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java` and
  `java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java`.
- **Lean evidence:** `TIME_014_forbids_passReread` (TIME_014.lean),
  `TIME_010_cycle_forbids_rereadAtBegin` and `TIME_010_cycle_forbids_rereadAtPark`
  (TIME_cycle.lean).
- **Fix:** Java takes one firing-clock reading per cycle, before the enablement update, and hands it
  to the deadline step, the firing pass and the decision to wait in both executors; the poll loop
  only counts the timer down. TypeScript's decision to wait takes the cycle reading through the
  RD-32 change. Java `AbstractInjectableClockTest`:
  `firingPassJudgesReadinessAtTheDeadlineStepsReading_TIME014_TIME010`,
  `firingPassNeverStartsAReapableTransitionPastItsLatestBound_TIME013_TIME010` and
  `decisionToWaitJudgesTheNextBoundaryAtTheCycleReading_TIME010_CONC010`; TypeScript
  `injectable-clock.test.ts`, "CONC-010 AC3 / TIME-010: a boundary that falls due during the wait
  setup still gets a timer".
- **Status:** fixed, unreleased.

### RD-17. Java's archive header order changes from one JVM to the next

- **Requirements:** EVT-025 (two archives of identical run data are identical).
- **Runtimes:** Java.
- **Defect:** the V2 and V3 header build the tags and the metadata histogram with `Map.copyOf`,
  whose iteration order is randomised per JVM, and the writer serialises maps in iteration order.
  The compact constructors of `SessionArchive.V2` and `SessionArchive.V3`
  (`java/src/main/java/org/libpetri/debug/archive/SessionArchive.java`) and of `SessionMetadata`
  (`java/src/main/java/org/libpetri/debug/archive/SessionMetadata.java`). The writer makes its own
  `Map.copyOf` of the tags before the header does (`writeV2` and `writeV3` in
  `java/src/main/java/org/libpetri/debug/archive/SessionArchiveWriter.java`), so every
  V2 and V3 header the writer writes is affected.
- **Lean evidence:** `EVT_025_mutant_seededTags` (EVT_025.lean).
- **Fix:** the header tags and the metadata histogram are unmodifiable maps in ascending code-point
  order of their keys (`CodePointOrder.sortedCopy`), and the writer hands the session's tags to the
  header without a copy of its own. Java
  `SessionArchiveV3Test.headerRendersTagsAndHistogramInAscendingKeyOrder_EVT025` and
  `readBackTagsAndHistogramIterateInAscendingKeyOrder_EVT025`.
- **Status:** fixed, unreleased.

### RD-18. Python archives at most 10,000 events

- **Requirements:** EVT-025 (one record for each event of the store's snapshot).
- **Runtimes:** Python.
- **Defect:** `write_from_store` copies the store into a debug store of the default capacity of
  10,000 events before writing, so a larger store is archived without its oldest events.
  `rust/libpetri-py/src/archive.rs` (`DebugEventStore::new` in `write_from_store`).
- **Lean evidence:** `EVT_025_forbids_copyThroughBounded` (EVT_025.lean).
- **Fix:** the copy is a debug store sized to the snapshot, so no event is evicted before the write.
  Python `test_archive.py::test_evt_025_archive_keeps_every_event_of_a_store_over_10000`.
- **Status:** fixed, unreleased.

### RD-19. Python writes archive version 3 only

- **Requirements:** EVT-025 (a writer for each of the header versions 1, 2 and 3; AC1).
- **Runtimes:** Python.
- **Defect:** the binding offers `write_from_store`, which always writes version 3, and no
  `writeV1` or `writeV2`. `rust/libpetri-py/src/archive.rs`.
- **Lean evidence:** `EVT_025_forbids_v3Only` (EVT_025.lean).
- **Fix:** `SessionArchiveWriter` offers `write_v1` and `write_v2` beside `write_from_store`, which
  writes version 3; `write_v1` takes no tags, since the version 1 header has none. Python
  `test_archive.py::test_evt_025_ac1_writes_header_versions_1_2_and_3`.
- **Status:** fixed, unreleased.

### RD-20. Python stamps an empty archive with the wall clock

- **Requirements:** EVT-025 (two archives of identical run data are identical).
- **Runtimes:** Python.
- **Defect:** for an empty store `write_from_store` takes the start and end times from
  `SystemTime::now`, so two archives of the same empty session differ.
  `rust/libpetri-py/src/archive.rs`.
- **Lean evidence:** none; the EVT_025 assumes record it.
- **Fix:** the start time is the first event's timestamp, or 0 for an empty store, and the end time
  the last event's, or none for an empty store; the wall clock is not read. Python
  `test_archive.py::test_evt_025_two_archives_of_one_empty_session_are_identical`.
- **Status:** fixed, unreleased.

### RD-21. Java's `transitionEvents` throws on an event with no transition name

- **Requirements:** EVT-030 (every helper is total; ruling D29 (a)), EVT-013 (AC4: a diagnostic
  that no transition is responsible for carries an empty or absent name, so a consumer reads it
  without failing).
- **Runtimes:** Java.
- **Defect:** `transitionEvents` calls `equals` on the transition name of every log message and
  throws on an engine diagnostic whose name is `null`, which both Java executors emit on an
  interrupted run. `java/src/main/java/org/libpetri/event/EventStore.java`.
- **Lean evidence:** `EVT_030_mutant_throwsOnNameless` (EVT_030.lean).
- **Fix:** `transitionEvents` compares names with `Objects.equals`, so an event with no transition
  name is skipped and the helper does not throw. Java
  `EventStoreTest.transitionEventsSkipsAnEventWithNoTransitionName_EVT030_AC2` and
  `AbstractTerminationReasonTest.interruptedRunEmitsAnEngineWarning_EVT013`, on both executors.
- **Status:** fixed, unreleased.

### RD-22. Java's `computeAt` does not clamp the index

- **Requirements:** EVT-032 (AC2: an index beyond the stream length is clamped; ruling D83 (a)).
- **Runtimes:** Java.
- **Defect:** `MarkingCache.computeAt` passes the index to `subList` and throws
  `IndexOutOfBoundsException` past the stream length.
  `java/src/main/java/org/libpetri/debug/MarkingCache.java`. The debug protocol handler has the
  same unclamped `subList` on its fallback path (RD-46).
- **Lean evidence:** `EVT_032_mutant_noClamp` (EVT_032.lean).
- **Fix:** `computeAt` clamps the index to the stream length after its check for an index of 0 or
  less. Java `MarkingCacheTest.computeAtBeyondStreamLengthClampsToEnd_EVT032_AC2`.
- **Status:** fixed, unreleased.

### RD-23. A channel merge drops the caller's declared places from the correspondence

- **Requirements:** MOD-031 (key-set completeness of the declared-to-actual correspondence
  through every rewrite pass; ruling D69 (a) leaves the merged case out of the block).
- **Runtimes:** Rust, Java, TypeScript, and Python through Rust.
- **Defect:** when a caller transition that carries no correspondence is merged with an instance
  transition that carries one, the merged transition keeps the instance side's correspondence
  whole, and a transition that carries a correspondence is never re-read from its arcs. The
  caller's declared places are then no keys, so a later pass that renames one of them (fusion at
  build, or instantiating the retrofitted net under MOD-014) leaves it unresolved, and the
  caller's action fails its declared-place check after its inputs were consumed (EXEC-031).
  `merge_local_name_maps` and `build_local_name_map` (`rust/libpetri-core/src/rewriter.rs`),
  `mergePlaceAlias` (`java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java` and
  `typescript/src/core/internal/subnet-rewriter.ts`). The opposite case, a caller that
  carries a correspondence merged with an instance transition that carries none, drops the
  instance side's declared places in the same functions.
- **Lean evidence:** `MOD_031_mergeThenPass_undecided` (MOD_031.lean): after the runtimes' merge
  and one pass the declared place `h` resolves to `h`, which no arc names; after the reference's
  merge it resolves to `f`.
- **Fix:** a channel merge gives a side that carries no correspondence an identity entry for every
  place its arcs and output specification name, merges the two sides with identity yielding to
  non-identity, and drops the result when it is all identity, as the Lean reference `corrMergeVia
  corrSideFull` does. Rust `mod031_place_resolution.rs`
  `channel_merge_then_fusion_keeps_caller_declared_place_mod031` and `mod031_identity_roundtrip.rs`
  `channel_merge_then_fusion_caller_action_fires_mod031`; Java
  `ChannelCompositionTest.channelMerge_callerWithoutAlias_keepsItsDeclaredPlacesAsKeys_MOD031`,
  `channelMerge_instanceWithoutAlias_keepsItsDeclaredPlacesAsKeys_MOD031` and
  `NestedPlaceAliasTest.channelMergeThenFusion_callerResolvesItsDeclaredPlace_MOD031`; TypeScript
  `compose-action-place-alias.test.ts`, "channel merge then fusion: caller action resolves its
  declared place (MOD-031 key-set completeness)", and `channel-composition.test.ts`,
  "channelMerge_callerWithoutAlias_keepsItsDeclaredPlacesAsKeys (MOD-031 key-set completeness)";
  Python `test_channel_composition.py::test_caller_declared_place_survives_a_later_renaming_pass`.
- **Status:** fixed, unreleased.

### RD-24. Java's compose token-type check reads one host place per name

- **Requirements:** MOD-025 (line 4: a body place whose name the builder holds with another token
  type is rejected).
- **Runtimes:** Java.
- **Defect:** `compose(SubnetDef)` compares each body place with one host place per name, the
  one put last into a name-keyed map. When the builder already holds two places of one name with
  different token types (Java's `Place` equality is structural on name and type) and the last one
  has the body place's type, Java accepts the call where MOD-025 rejects it.
  `java/src/main/java/org/libpetri/core/PetriNet.java` (`Builder.compose(SubnetDef)`).
- **Lean evidence:** none; line 4 of MOD-025 (MOD_025.lean) states the rejection, and no theorem
  models Java's name-keyed map.
- **Fix:** the check indexes the host places by name to a list and rejects a body place when any
  host place of that name has another token type. Java
  `ComposeDirectTest.composeDirect_placeTokenTypeConflict_withTwoSameNamedHostPlaces_throws_MOD025`.
- **Status:** fixed, unreleased.

### RD-25. A fusion set that lists its first member again drops that member

- **Requirements:** MOD-061 (step 3: the canonical member remains; lines 1 and 3) and MOD-026
  (AC5: the surviving canonical place keeps its own entry; lines 1 and 2).
- **Runtimes:** Rust, Java, TypeScript.
- **Defect:** the non-canonical members are every member after the first position, so a set
  with members `[a, b, a]` counts `a` among them. Fusion then drops the declared place `a` (it
  comes back only through an arc of a rewritten transition), runs the input merge on a transition
  whose only input arcs are on `a`, and drops `a`'s cluster entry.
  `build_with_fusion` (`rust/libpetri-core/src/petri_net.rs`), `buildWithFusion` and
  `filterFusedMembership` (`java/src/main/java/org/libpetri/core/PetriNet.java` and
  `typescript/src/core/petri-net.ts`). The input merge has no visible effect,
  since CORE-030 already rejects two input arcs on one place; what shows is the dropped standalone
  `a` and its dropped membership entry. Python was listed at first, but the binding declares no
  fusion sets (MOD-060), so it has no such call.
- **Lean evidence:** `mod061_dupCanonical_kept` (MOD_061.lean) and `mod026_dupCanonical_kept`
  (MOD_026.lean): the reference keeps `a` and its entry.
- **Fix:** the fusion build skips a non-canonical member equal to the canonical member, so `[a, b,
  a]` keeps the declared place `a` and its entry; `nonCanonical()` itself is unchanged. Rust
  `fusion.rs` `fuse_repeated_canonical_member_keeps_it_mod061` and `petri_net.rs`
  `direct_compose_then_fuse_repeated_canonical_keeps_its_entry_mod026`; Java
  `FusionTest.fuse_repeatedCanonicalMember_keepsIt_MOD061` and
  `ComposeDirectMembershipTest.directCompose_thenFuseWithRepeatedCanonical_keepsCanonicalEntry_MOD026`;
  TypeScript `fusion.test.ts`, "fuse_repeatedCanonicalMember_keepsIt (MOD-061 step 3)", and
  `compose-direct-membership.test.ts`,
  "directCompose_thenFuseWithRepeatedCanonical_keepsCanonicalEntry (MOD-026 AC5)".
- **Status:** fixed, unreleased.

### RD-26. Java reports `counterexampleConfirmed` `false` on the name-coloured encoding

- **Requirements:** VER-003 (the initial-violation sentence: the empty firing sequence, with
  `counterexampleConfirmed` not `false`; AC8: on the name-coloured encoding no replay applies and
  `counterexampleConfirmed` is absent) and NU-053 (the name-coloured fixpoint query).
- **Runtimes:** Java.
- **Defect:** the check that the initial marking violates the property is gated on a flat
  answer (`colouredPlan == null`), but the replay that follows has no such gate. On a
  name-coloured `Violated` the flat decoder finds no `Reachable` fact of the flat arity (the
  coloured `Reachable` has another shape), the empty decode makes `assessCounterexample` return
  `Unconfirmed`, and the result is `Violated` with `counterexampleConfirmed` `false`, also when
  the initial marking violates the property. Rust and TypeScript leave the field absent on this
  path. The IC3/PDR `Violated` case of `SmtVerifier.pipeline` and `SmtVerifier.assessCounterexample`
  (`java/src/main/java/org/libpetri/smt/SmtVerifier.java`); `CounterexampleDecoder.decodeStateSet`
  (`java/src/main/java/org/libpetri/smt/z3/CounterexampleDecoder.java`); Rust
  `rust/libpetri-verification/src/smt_verifier.rs` (`replay_phase` returns `None` when
  coloured). Confirmed by a run: `JoinRelayTest.fig12c(true)` with `R = 2`, budget `R`, the
  `FIG12C_CARRIERS` and `PlaceBound(R, 1)` (violated at the initial marking) returns `Violated`
  on route `SMT` with the name-coloured encoding, an empty trace and `counterexampleConfirmed`
  `false`. A coloured `Reachable` with the flat arity, which would need one colour slot per
  coloured place, does not occur on a net the encoding accepts: every ν-join consumes from two
  coloured places at once, so the encoding has at least two slots.
- **Lean evidence:** line 6 of VER-003 (VER_003.lean) asks for `counterexampleConfirmed` not
  `false` at an initial violation; a decider that answers `some false` there, the reference
  otherwise, fails the block (checked in the wave W10 mutant run, not kept as a theorem). ν-nets
  are outside `Reference.TimedNet`, so VER_003.lean has no theorem about the coloured path.
- **Fix:** on the name-coloured encoding the `Violated` answer takes the no-replay branch, reports
  `Counterexample replay: not applicable (name-coloured encoding, NU-053)` and leaves
  `counterexampleConfirmed` absent, as Rust and TypeScript do. Java
  `InitialViolationTraceTest.VER003_AC8_aNameColouredInitialViolationLeavesCounterexampleConfirmedAbsent`
  and `VER003_AC8_aNameColouredViolationLeavesCounterexampleConfirmedAbsent`.
- **Status:** fixed, unreleased.

### RD-27. Rust ignores a carrier declaration it cannot resolve, outside Route B

- **Requirements:** NU-051 (the carrier bullet: a declared carrier that is not a place of the net
  is refused, in either fragment mode and whatever the query; ruling D95 (a)).
- **Runtimes:** Rust, Python (which runs the Rust verifier).
- **Defect:** Rust checks the declared carriers only under EXTENDED and only inside Route B
  (`rust/libpetri-verification/src/nu_scg_verifier.rs`, `verify_name_scg`, which answers
  `Unknown` naming the place). An absent carrier is therefore silently ignored in three cases:
  under BASE; under EXTENDED on a call that does not reach Route B; and under EXTENDED on a
  bounded quiescence query that does reach it, because the pipeline drops the Route B `Unknown`
  there and defers to Route A (`defer_to_route_a` in `SmtVerifier::verify_net`,
  `rust/libpetri-verification/src/smt_verifier.rs`), whose `build_plan` skips a carrier it cannot
  resolve (`rust/libpetri-verification/src/name_coloured_encoder.rs`). The open-net route
  (`verify_open_net` with a `configure_smt` hook) refuses an unknown mint but ignores an unknown
  carrier as well, and the doc comments promised more than Rust checked. Java and TypeScript
  reject the declaration in both modes (`SmtVerifier.carrierPlaces`).
- **Lean evidence:** `NU_051_carrier_forbids_routeBOnly` (BASE) and
  `NU_051_carrier_forbids_routeADeferral` (EXTENDED) in `NU_051_carrier.lean`: the shape Rust
  ships answers `Proven` on the co-mint net with the mistyped carrier `7`.
- **Fix:** `SmtVerifier::verify` judges the carrier declaration on the caller's net before any
  rewrite or route and answers `Unknown` with `declared carrier place 'x' not in the net (NU-051)`
  in both modes; `encode_scripts` panics with the same reason, and `verify_open_net` refuses before
  either route. Python's `encode_smt_scripts` raises `ValueError` with it. Rust
  `mint_declarations.rs` `nu_051_an_unknown_carrier_is_refused_in_both_modes_on_every_route`,
  `nu_051_encode_scripts_panics_for_a_carrier_not_in_the_net` and
  `nu_051_verify_open_net_answers_unknown_for_a_carrier_not_in_the_net`; Python
  `test_nu_mint_contract.py::test_nu_051_an_unknown_carrier_is_refused_in_both_modes` and
  `::test_nu_051_encode_smt_scripts_rejects_a_carrier_not_in_the_net`.
- **Status:** fixed, unreleased.

### RD-28. TypeScript's state-space cache grows on every `Arrivals` query and never hits

- **Requirements:** VER-017 (the cache key: under `Arrivals` the key covers the closure, or the
  verifier does not use the cache for that query and says so in the report; AC7).
- **Runtimes:** TypeScript.
- **Defect:** the enumeration looks the graph up under the caller's net and the closed initial
  marking (`typescript/src/verification/smt-verifier.ts`, `enumerate`), and the marking
  half of the key names `Place` objects by identity
  (`typescript/src/verification/state-space-cache.ts`, `resolveStateSpace` and `markingKey`). The
  `Arrivals` closure makes new arrival-source `Place` objects on every call
  (`typescript/src/verification/smt-verifier.ts`, `applyArrivals`), so every query under
  `Arrivals` misses, builds, and adds one more entry, and the report does not say that the cache
  was not used. No verdict is wrong, since the cache never hits there. `Arrivals(0)`, and
  `Arrivals` with no environment place, do not close the net and hit the cache. Java bypasses the
  cache under `Arrivals` with a report line; Rust and Python key the fingerprint of the closed net.
- **Lean evidence:** none; `VER_017_cache` takes the key as an abstract value (its assumes
  records the `Arrivals` clause as the key's job).
- **Fix:** the enumeration does not use the cache when the `Arrivals` closure added arrival sources,
  and writes Java's report line for it; `Arrivals(0)` still uses the cache. TypeScript
  `state-space-cache.test.ts`, the two tests of "VER-017 AC7" (two `arrivals(k)` queries through one
  cache each build and carry the line; `arrivals(0)` uses the cache).
- **Status:** fixed, unreleased.

### RD-29. TypeScript hands the selected environment mode to `verify` only when there is an input port

- **Requirements:** MOD-051 (the setup of each per-property verification: the verifier is set up
  with the harness environment places and the selected environment mode, and then passed,
  together with the synthetic net, through the configure hook).
- **Runtimes:** TypeScript.
- **Defect:** `SubnetDef.verify` registers the environment places and the selected mode only when
  the harness has an environment place (`typescript/src/core/subnet-def.ts`). For a subnet
  with no input or in-out port the configure hook receives a verifier on the verifier default
  `AlwaysAvailable` (the `_environmentMode` field of `SmtVerifier`,
  `typescript/src/verification/smt-verifier.ts`), not on the selected
  mode, so a hook that registers an environment place itself runs under the wrong mode. Rust
  (`run_per_property`, `rust/libpetri-verification/src/harness.rs`) and Java
  (`SubnetDef.verify`, `java/src/main/java/org/libpetri/core/SubnetDef.java`) set the mode on every call, and
  Python rides on Rust.
- **Lean evidence:** `MOD_051_forbids_modeOnlyWithEnvs` in `MOD_051.lean`: the forwarder without
  its input port, verified under `Ignore` with a hook that registers `sut/IN`; the TypeScript
  shape (`mod051ModeOnlyWithEnvs`) proves `TerminatesAtSink` where line 4 requires `Violated`.
- **Fix:** `SubnetDef.verify` sets the harness environment places and the selected mode on every
  per-property verifier, whether or not the harness has an environment place. TypeScript
  `subnet-verify-options.test.ts`, "a hook on a subnet with no input port runs under the selected
  mode (MOD-051)".
- **Status:** fixed, unreleased.

### RD-30. The Python binding adapter resolves the given name before the correspondence

- **Requirements:** MOD-031 (an action's context operations resolve a declared place through the
  correspondence, and a binding adapter that resolves for its actions keeps the same order).
- **Runtimes:** Python.
- **Defect:** `require_output` and `resolve_lookup_key` first look the given name up in the
  allowed outputs or in the delivered input or read map, and fall back through `local_name_map`
  only when that fails (`rust/libpetri-py/src/action.rs`). When the given name is itself
  a place of the call's kind that the correspondence resolves to another place (a port `a` bound
  to the caller place `b`, and a port `b` bound to `c`), the call answers for the given place,
  not for the place the correspondence names. Java and TypeScript resolve first; the Rust native
  context hands the correspondence to native actions.
- **Lean evidence:** `MOD_031_ctx_mutant_literalFirst_killed` and `mod031ctx_collision` in
  `MOD_031.lean`: on the collision example the name-first lookup answers for the wrong place.
- **Fix:** the adapter resolves the given name through the correspondence first and looks up only
  the resolved name; its error messages still name the given name. Python
  `test_subnet_local_names.py::test_correspondence_resolves_before_the_given_name_mod031` (`[input]`
  and `[read]`) and `::test_output_resolves_before_the_given_name_mod031`.
- **Status:** fixed, unreleased.

### RD-31. Java and TypeScript resolve the timeout branch's places a second time

- **Requirements:** MOD-031 (the correspondence is applied once, to a declared place), IO-013 (the
  timeout outcome deposits the tokens of its child on the child's places), IO-014 (a forward
  deposits in `to` the tokens consumed from `from`: `forwardToHarvest` resolves `to` again, so
  with port `a` bound to `b` and port `b` bound to `c` the forward meant for `b` lands on `c`),
  CORE-036 (the ninth sentence and the outcome line: the timeout token meant for `b` is
  deposited on `c`), EXEC-022 (line 1: the timeout outcome is the token-level outcome of the
  `Timeout` child).
- **Runtimes:** Java, TypeScript.
- **Defect:** the executor deposits the timeout branch through `outputToHarvest` and
  `forwardToHarvest` with the places the rewritten output specification names, which are already
  the actual places (`java/src/main/java/org/libpetri/runtime/ExecutorSupport.java`,
  `produceTimeoutOutputRecursive`; `typescript/src/runtime/executor-support.ts`,
  `produceTimeoutOutput`). Both methods resolve the place through the correspondence again
  (`java/src/main/java/org/libpetri/core/TransitionContext.java`;
  `typescript/src/core/transition-context.ts`). On a collision (port `a` bound to the
  caller place `b`, port `b` bound to `c`) the timeout token meant for `b` lands on `c`. The
  `from` side of a `ForwardInput` is resolved twice as well (Java reads it through
  `TransitionContext.inputTokens`, TypeScript in `forwardToHarvest`), so a timeout can forward a
  token taken from the wrong input, or fail the firing when the twice-resolved place fails the
  declared-place check before `action-timed-out` is emitted. Rust deposits the timeout branch on
  the places as given.
- **Lean evidence:** `mod031ctx_timeout_resolveTwice` in `MOD_031.lean`.
- **Fix:** `outputToHarvest` and `forwardToHarvest` take the actual places of the rewritten output
  spec as given, and Java reads the `from` tokens from the raw input. Java
  `AbstractNetExecutorEngineTest.OutputTimeoutTests.outTimeout_portCollision_depositsOnTheBoundPlace_MOD031_IO013`
  and `outTimeout_forwardInput_portCollision_forwardsFromTheBoundPlace_MOD031_IO014`; TypeScript
  `compose-action-place-alias.test.ts`, "the timeout branch deposits on the bound place under a
  port-name collision" and "a timeout ForwardInput reads and deposits on the actual places under a
  collision", on both executors.
- **Status:** fixed, unreleased.

### RD-32. TypeScript blocks without a timer when a boundary falls due during the wait's setup

- **Requirements:** CONC-010 (line 4 and AC3: a block taken while an armed transition has a
  timing boundary ahead at the reading of the cycle's deadline step sets a timer no longer than
  the wait to the nearest such boundary, plus the timer resolution), TIME-010 (the decision to
  wait of a cycle judges elapsed time at the reading of its deadline step, and no other step of
  the cycle takes a new reading for these judgements).
- **Runtimes:** TypeScript (both executors).
- **Defect:** `awaitWork` computes its timer from a fresh clock reading taken inside
  `millisUntilNextTimedTransition` (`typescript/src/runtime/bitmap-net-executor.ts`,
  `precompiled-net-executor.ts`), later than the cycle reading `cycleNowMs` (taken in
  `executeLoop`) and after the
  `await Promise.resolve()` yield. When a boundary has passed by that later reading, the method
  returns 0. The wait returns early only when no action is in flight
  (`if (timerMs === 0 && promises.length === 0) return;`); with an action in
  flight it skips the timer (`if (timerMs > 0)`) and blocks in `Promise.race`
  over the in-flight completions and the wake-up only. Example: a `Delayed(10)` transition `t`
  armed at reading 0, an action `u` in flight for an hour, a cycle reading of 9.9 (so `t` is not
  Ready and nothing fires) and a wait reading of 10.05: the loop blocks with no timer and `t`
  waits for `u` to return. Rust takes its timer from `cycle_now`
  (`run_async`, `rust/libpetri-runtime/src/executor_core/executor.rs`), and Java leaves its poll as soon
  as `nanosUntilNextTimedTransition() <= 0` (`BitmapNetExecutor.java`,
  `PrecompiledNetExecutor.java`); Python rides on Rust. This is the TypeScript half of RD-16's
  decision to wait.
- **Lean evidence:** `CONC_010_forbids_untimedPark` in `CONC_010.lean`: a park with no timer while
  `nextBoundary` at the cycle reading is set breaks line 4. At the later reading `t` is Ready, so
  line 2 would forbid the block as well. `TIME_010_cycle_forbids_rereadAtPark` in
  `TIME_cycle.lean`: a decision to wait that takes a new reading breaks the TIME-010 companion's
  line 5.
- **Fix:** `awaitWork(cycleNowMs)` hands the cycle reading to `millisUntilNextTimedTransition`,
  which takes no reading of its own, in both executors; the same change fixes the TypeScript half of
  RD-16. TypeScript `injectable-clock.test.ts`, "CONC-010 AC3 / TIME-010: a boundary that falls due
  during the wait setup still gets a timer", on both executors.
- **Status:** fixed, unreleased.

### RD-33. Java and TypeScript read the output collector at admission, not at completion

- **Requirements:** CONC-003 (line 1: a commit deposits exactly the tokens the action wrote
  before it returned), EXEC-020 (the produced tokens of an admitted completion are what the
  action wrote).
- **Runtimes:** Java and TypeScript (both executors).
- **Defect:** neither runtime detaches the output collector when an action completes normally;
  only the timeout path detaches it (`detachForTimeout`,
  `java/src/main/java/org/libpetri/core/TransitionContext.java`,
  `typescript/src/core/transition-context.ts`). The output is read when the orchestrator
  later admits the completion, in `processCompletedTransitions` of
  `java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`
  (`flight.context().rawOutput()`; the completion is queued in `fireTransition`),
  `PrecompiledNetExecutor.java`, `typescript/src/runtime/bitmap-net-executor.ts` (the
  `.then` in `fireTransition` detaches nothing) and `precompiled-net-executor.ts`. So a token an
  action writes after its future or promise completed, from a thread or a timer it started, and
  before the completion is admitted, is deposited at the commit. Rust moves the outputs into the
  completion message when the action returns. Java's synchronous paths (`processSyncOutput`) read
  the output without detaching it too, and `PrecompiledNetExecutor` reused a pooled context per
  transition, so a write that arrived after admission landed in the next firing of the same
  transition. The fix is to detach the collector at completion, as the timeout path already does.
- **Lean evidence:** `CONC_003_forbids_lateWrite` (CONC_003.lean).
- **Fix:** both runtimes detach the write target when the action completes (`detachAtCompletion`)
  and keep what was written as the harvest, so a later write is dropped. Java detaches in the
  completion callback and on the synchronous path, and its precompiled executor gives every firing a
  fresh context; TypeScript detaches in the first reaction to the action's promise, also with an
  action timeout armed. Java
  `AbstractNetExecutorEngineTest.OutputAtCompletionTests.aWriteAfterCompletionIsNotDeposited_CONC003`
  and `aLateWriteDoesNotReachTheNextFiring_CONC003`; TypeScript `executor-shared-semantics.test.ts`,
  "a token written after the action's promise settled is not deposited (CONC-003)", with and without
  an action timeout, on both executors.
- **Status:** fixed, unreleased.

### RD-34. Java's awaitTermination waits out its timeout on a loop that never ran or that died at boot

- **Requirements:** ENV-016 (second block, `ENV_016_await`: line 1 and the sentence that a call
  on an executor whose loop was never started answers true at once, without waiting for the
  timeout; AC1, true once the loop has stopped; the sentence that `awaitTermination` is not
  defeated by a failure such as a throwing event store).
- **Runtimes:** Java (both executors).
- **Defect:** two paths leave `started` true and `terminatedFuture` never completed, so
  `awaitTermination` gets past `if (!started) return true`, waits out its whole timeout and
  answers false, on every later call too.
  (a) A rejected submit. `run(Duration, RunTimeoutPolicy)` sets `started = true` before
  `CompletableFuture.supplyAsync(this::executeLoop, executor)`
  (`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`,
  `PrecompiledNetExecutor.java`). When the executor rejects the task, the call throws
  `RejectedExecutionException` and the loop never runs. A `close()` before the run does this on
  an executor that owns its pool, since `close()` shuts the pool down (`BitmapNetExecutor.close`);
  a caller-supplied executor that rejects the task does it without a close.
  (b) A store that throws at boot. `executeLoop` emits `ExecutionStarted` and the first marking
  snapshot before its `try`/`finally` (`BitmapNetExecutor.java`,
  `PrecompiledNetExecutor.java`), and `emitEvent` does not catch
  (`BitmapNetExecutor.java`, `PrecompiledNetExecutor.java`). A store that
  throws on these appends makes `run()` throw before the `finally` that completes
  `terminatedFuture`; the loop is gone and `running` stays true. The termination bookkeeping of
  the `finally` already survives a throwing store; the boot does not.
  Reproduced against `java/target/classes`: after a rejected `run(Duration)`, and after a
  `run()` that threw `IllegalStateException` from a store that throws on every append, both
  executors answer `awaitTermination(300 ms)` with false after 300 ms. TypeScript, Rust and
  Python provide no `awaitTermination`.
- **Lean evidence:** none of its own. Case (a) is an answer false on a loop that never started,
  which line 1 of `ENV_016_await` forbids (`ENV_016_await_mutant_blocksUnstarted` is that
  answer). Case (b) has no image in the model, which has no step for a loop that dies before its
  run: read as a loop that stays running, it meets every line, so the defect shows only against
  AC1 and the quoted throwing-store sentence. The fix is to set `started` only once the submit
  is accepted, or to complete `terminatedFuture` when the submit fails, and to move the boot
  emissions inside the `try`.
- **Fix:** `run(Duration, policy)` restores `started` and rethrows when the submit throws, and
  `executeLoop` emits its boot events inside the `try`, so a store that throws at boot still reaches
  the `finally` that completes `terminatedFuture`, with the termination reason `STOPPED`. Java
  `AbstractNetExecutorEnvironmentTest.LifecycleTests.awaitTermination_trueAtOnceAfterARejectedRun_ENV016`
  and `awaitTermination_trueAfterABootThatThrew_ENV016_AC1`, on both executors.
- **Status:** fixed, unreleased.

### RD-35. Java's executor builders keep the caller's environment-place set

- **Requirements:** ENV-002 (first block, `ENV_002`: the sentence 'The set of registered
  environment places is fixed when the executor is built; no step of a run adds or removes one.',
  line 1 and line 3), ENV-010 (whether the run waits at quiescence).
- **Runtimes:** Java (both executors).
- **Defect:** `Builder.environmentPlaces(Set<EnvironmentPlace<?>>)` stores the caller's set
  (`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`,
  `PrecompiledNetExecutor.java`), `build()` passes it on and the constructor keeps it
  without a copy (`this.environmentPlaces = environmentPlaces;` in both constructors). `inject`
  tests that live set on every call (`environmentPlaces.contains(place)` in both), so a host that changes its own set after `build()` adds or
  removes a registration in the middle of the run. `hasEnvironmentPlaces` is read once in the
  constructor, so the quiescence decision of ENV-010 keeps the registration of
  the build while `inject` and the dead-arc report follow the changed set. The varargs overload
  copies (`Set.of(places)`) and is not affected. TypeScript copies the names into a set of its
  own; Rust and Python take the registrations by value.
  Reproduced against `java/target/classes`: an executor built with the caller's set `{A}`
  answers an injection into `B` with an error; after the caller removes `A` and adds `B`, an
  injection into `A` fails and one into `B` is accepted.
- **Lean evidence:** `ENV_002_forbids_shrinks` (ENV_002.lean): an executor whose registrations
  are removed during the run breaks line 3. A registration added during the run breaks line 1.
  The fix is `Set.copyOf(places)` in the builder or the constructor.
- **Fix:** both executor constructors keep `Set.copyOf(environmentPlaces)` and compute
  `hasEnvironmentPlaces` from that copy, so `inject`, the dead-arc report and the quiescence
  decision read one fixed set. Java
  `AbstractNetExecutorEnvironmentTest.LifecycleTests.environmentPlacesAreFixedAtBuild_ENV002`, on
  both executors.
- **Status:** fixed, unreleased.

### RD-36. Java's debug protocol renders maps and sets in a per-JVM order

- **Requirements:** EVT-025 (the reproducibility paragraph: 'an implementation MUST NOT put one
  on the path to the archive or the debug protocol', the debug protocol half), EVT-014 (AC5:
  rendering the same event stream twice onto the debug protocol yields identical output).
- **Runtimes:** Java.
- **Defect:** `NetEventConverter.toEventInfo` builds the `details` of `NetEventInfo` with
  `Map.of(...)` of two or more entries (`ExecutionStarted`, `ExecutionCompleted`,
  `TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut`), and `withInstancePrefix`
  returns `Map.copyOf(copy)`, so every event of a composed net whose details then hold two or
  more entries is affected too.
  `java/src/main/java/org/libpetri/debug/NetEventConverter.java`: those five cases of
  `toEventInfo` and the `Map.copyOf` in `withInstancePrefix`, and through `withInstancePrefix` also
  the `TransitionStarted`, `ActionTimedOut`, `TokenAdded` and `TokenRemoved` cases.
  `DebugSessionRegistry.tagsFor` hands `Map.copyOf(session.tags())` to
  `SessionSummary.tags` (`DebugSessionRegistry.java`), and the `SubnetInstanceInfo`
  constructor copies its name sets with `Set.copyOf` (`DebugResponse.java`), which drops
  the `LinkedHashSet` order `buildSubnetInstances` builds for a stable `Subscribed` response
  (recorded on its own as RD-45).
  The iteration order of these immutable collections is salted per JVM, `DebugResponse` is a
  Jackson type, and Jackson writes a map and a set in iteration order (no
  `ORDER_MAP_ENTRIES_BY_KEYS` is set, and a set is written as an array either way), so one event,
  session list or subscription renders differently from one JVM to the next. Rust builds the
  event details as a `BTreeMap` (`rust/libpetri-debug/src/net_event_converter.rs`), and
  TypeScript as object literals and insertion-ordered sets.
  Reproduced with JDK 25.0.2: `Map.of` of the three `ExecutionCompleted` keys and
  `Set.copyOf(List.of("a", "b", "c", "d"))` print in different orders in successive JVMs.
- **Lean evidence:** none; the debug protocol has no model. The EVT_025 assumes record it.
- **Fix:** the debug-protocol records normalise their collections where they are built:
  `NetEventInfo.details` and `SessionSummary.tags` are sorted by code point, as Rust's `BTreeMap`
  is, `DebugSessionRegistry.tagsFor` returns a sorted copy, and `SubnetInstanceInfo` keeps its build
  order (RD-45). Java `NetEventConverterTest.detailsRenderInKeyOrder_EVT014_AC5`,
  `DebugSessionRegistryTest.tagsForIsSortedByKey_EVT025` and
  `DebugProtocolSubnetTest.subnetInstanceNamesKeepBuildOrder_EVT014_AC5`.
- **Status:** fixed, unreleased.

### RD-37. Java and TypeScript dedup ghost edges by a NUL-joined string

- **Requirements:** EXP-017 (line 2: a ghost edge for every bridged ordered pair of cluster keys;
  'dedup by ordered pair').
- **Runtimes:** Java, TypeScript.
- **Defect:** `synthesizeGhostEdges` keys the dedup map by the string `x + "\0" + y`, not by the
  ordered pair. A cluster key may hold the NUL character (it is ASCII, inside EXP-016's name
  assumption, and no builder checks place names), so the distinct pairs (`a\0b`, `c`) and
  (`a`, `b\0c`) share the key `a\0b\0c` and the second pair gets no ghost edge.
  `java/src/main/java/org/libpetri/export/ClusterBuilder.java`,
  `typescript/src/export/cluster-builder.ts`. Rust keys the dedup map by the
  `(String, String)` pair (`rust/libpetri-export/src/cluster_builder.rs`, ghost synthesis). The
  fix is a key that cannot collide, such as a nested map or a length-prefixed key.
- **Lean evidence:** `EXP_017_forbids_nulDedup` and `exp017_nulNet_counts` (EXP_017.lean): on
  `exp017NulNet` the reference draws two ghost edges and the NUL-joined dedup draws one.
- **Fix:** Java dedups by the ordered pair `List.of(x, y)` and TypeScript by the length-prefixed key
  `${x.length}:${x}${y}`; neither can collide. Java
  `ClusterBuilderTest.ghostEdgesDedupByOrderedPair_nulInKeyDoesNotMerge_EXP017`; TypeScript
  `cluster-builder.test.ts`, "EXP-017: ghost edges dedup by ordered pair".
- **Status:** fixed, unreleased.

### RD-38. Rust verification checks the mint declaration against its own rewritten net

- **Requirements:** NU-010 (the declared-mint bullet: a declared mint that is not a transition of
  the net is refused, with the same reason naming it at every entry point; AC6).
- **Runtimes:** Rust, Python (which runs the Rust verifier).
- **Defect:** `SmtVerifier::verify` checks the declared mints
  (`name_fragment::unknown_mint_reason(self.net, ...)`,
  `rust/libpetri-verification/src/smt_verifier.rs`) inside `verify_net`, after the
  verifier's own rewrites: the `Arrivals(k)` closure (`with_arrivals`, called from `verify`), the
  inert places, the in-flight split and the terminal rewrite (`verify_terminals_split`). Those
  rewrites add transitions such as `complete:<t>` (`completion_transition`,
  `rust/libpetri-verification/src/in_flight.rs`) and `env:arrive[i]:<p>` (`close_open_net`,
  `rust/libpetri-verification/src/open_net/closure.rs`), so a
  declaration naming one of them is accepted and verification answers a verdict. Every other
  entry point checks the caller's net and refuses the same request with
  `declared mint transition 'complete:t' not in the net (NU-010)`: Rust `encode_scripts`
  (`smt_verifier.rs`, before `with_arrivals`), Python `encode_smt_scripts`
  (`py_encode_smt_scripts`, `rust/libpetri-py/src/verification.rs`), Java at declaration
  (`SmtVerifier.mintTransitions`, `java/src/main/java/org/libpetri/smt/SmtVerifier.java`)
  and TypeScript at declaration and in `encodeScripts`
  (`mintTransitions` and `encodeScripts`, `typescript/src/verification/smt-verifier.ts`, both on
  `callerNet`). Rust's own docs promise the same answer (`encode_scripts` panics "with the reason
  verify answers Unknown with"; the doc comment of `unknown_mint_reason` in `name_fragment.rs`). The fix is to run the check on the caller's net before
  `with_arrivals`, as `encode_scripts` does. Open-net verification is not affected: all three
  runtimes check its declaration on the closed net.
- **Lean evidence:** `NU_010_unknownMint_forbids_rewrittenNet` (`NU_010_ac6.lean`): an entry
  point that checks the names against the caller's transitions plus `complete:t` answers
  `Violated` on `p0 -> t -> p1` with `complete:t` declared, where the reference script encoding
  fails with the NU-010 reason (`nu010_rewritten_vs_encode`).
- **Fix:** `verify` judges the mint declaration on the caller's net before the `Arrivals` closure
  and the other rewrites, as `encode_scripts` does, so `complete:t` and `env:arrive[0]:p0` are
  refused with the NU-010 reason. Rust `mint_declarations.rs`
  `nu_010_ac6_mint_naming_a_rewrite_added_transition_is_refused`; Python
  `test_nu_mint_contract.py::test_nu_010_ac6_mint_naming_a_rewrite_added_transition_is_refused`.
- **Status:** fixed, unreleased.

### RD-39. The Route B environment decline reads the selected mode, not whether conflict priority applies

- **Requirements:** NU-052 (the second shall sentence: under `CONFLICT` the verifier verifies
  every call conflict priority does not apply to as under `NONE`), VER-006 AC8 (Route B declines
  for a shared environment input only when "conflict priority prunes on an environment input two
  transitions consume"; "Otherwise its verdict stands"), NU-055 (the third rule of step 5 of the
  refusal order: a shared environment input is refused only "where conflict priority is in effect
  ([NU-052])").
- **Runtimes:** Rust, Java, TypeScript, and Python through Rust.
- **Defect:** the verifier switches the mode it hands on to `NONE` only when the in-flight split
  refuses a pruner (Rust `with_in_flight`, Java `applyInFlight` through `conflictOff`, TypeScript
  `applyInFlight` through `_effectivePriority`). When conflict priority does not apply because a
  transition of the net is read as reapable, the selected `CONFLICT` reaches the Route B
  environment check, which declines whenever an environment place under `AlwaysAvailable` or
  `Bounded(k)` has two or more consumers ("is a consumed input shared under conflict priority"),
  although Route B itself turns the pruning off on that net (`verify_via_name_scg_reaping`,
  `NuScgVerifier.verifyReaping`, `verifyViaNameScgReaping`). So on a net with a ν-join, no declared
  budget, one `Deadline` or `Window` transition (`assumeNoReaping` not set) and an uncoloured
  environment place two transitions consume, `Unreachable` or `PlaceBound` on a non-environment
  place answers `Unknown` ("Declined under environment injection") under `CONFLICT` and the Route B
  verdict under `NONE`. The same check refuses a name-alignment call: under `CONFLICT`, on a net
  with a reapable transition, a `NameAligned(S)` or `QuiescentNameAligned(S)` call under
  `AlwaysAvailable` whose uncoloured environment place outside `S` two transitions consume, and
  that steps 1 to 4 and the first two rules of step 5 let through, answers `Unknown` ("is a
  consumed input shared under conflict priority") where the refusal order of NU-055 reaches its
  later rules or builds the graph.
  Rust: `SmtVerifier::verify_net` (passes `self.priority_semantics` to
  `route_b_env_observation`) and `route_b_env_observation` (the decline), in
  `rust/libpetri-verification/src/smt_verifier.rs`.
  Java: `SmtVerifier.pipeline` (passes `effectivePriority()`, still `CONFLICT` unless
  `conflictOff`) and `routeBEnvObservation` (the decline), in
  `java/src/main/java/org/libpetri/smt/SmtVerifier.java`.
  TypeScript: `SmtVerifier.runPipeline` (passes `_effectivePriority`) and `routeBEnvObservation`
  (the decline), in `typescript/src/verification/smt-verifier.ts`.
  The fix is to hand the environment check `CONFLICT` only when conflict priority applies
  (`conflict_pruning_applies` and the pruning not turned off by the split), `NONE` otherwise.
- **Lean evidence:** none; the setup model `NuSetupFn` of `NU_052_split` does not model the
  environment decline. The `NU_052_split` assumes record it, and the `NU_055_refusal` assumes
  in `NU_055_steps.lean` (the paragraph on step 5 of the refusal order) record that the gate's conflict fact is "conflict priority is in
  effect" as NU-052 states it, not the runtimes' reading.
- **Fix:** the Route B environment check gets `CONFLICT` only where conflict pruning applies and
  `NONE` otherwise, in all three runtimes; where pruning applies the decline still stands. Rust
  `smt_verifier.rs` `nu_052_env_decline_only_where_conflict_priority_applies`; Java
  `SmtVerifierTest.envDeclineReadsWhetherConflictPriorityApplies_NU052_VER006_AC8`; TypeScript
  `smt-verifier.test.ts`, "NU-052 / VER-006 AC8: the env decline applies only where conflict
  priority is in effect"; Python
  `test_nu_verification.py::test_nu_052_env_decline_only_where_conflict_priority_applies`.
- **Status:** fixed, unreleased.

### RD-40. Rust and TypeScript dedup state classes by a marking string that does not escape place names

- **Requirements:** VER-010 (the key sentence, `VER_010_key` line 2: two classes of the graph
  share a key exactly when they have the same marking and zone; and through it the run coverage
  of `VER_010` line 1 on a graph reported complete), VER-012 (`VER_012` line 8: the Route B graph
  identifies two classes exactly when they have the same base class and name key; and through it
  AC3's completeness of a closed graph).
- **Runtimes:** Rust, TypeScript, and Python through Rust's verifier.
- **Defect:** both runtimes dedup state classes by a rendered string in which place names are not
  escaped. Rust renders the marking as `name:count` entries joined by `,`
  (`MarkingState::canonical_key`, `rust/libpetri-verification/src/marking_state.rs`), the
  class key appends `|` and `Dbm::zone_key` (`StateClass::canonical_key` in `state_class.rs`;
  `dbm.rs`, clock names joined by `,`), and `StateClassGraph::build` dedups by that string
  (in `build_core`, `state_class_graph.rs`). TypeScript renders the marking as `{name:count, ...}`
  (`MarkingState.toString`, `typescript/src/verification/marking-state.ts`) and dedups by
  `classKey` = marking string, `|`, zone key (`analysis/state-class-graph.ts`, used in
  `StateClassGraph.build`). Route B interns the base class by the same strings: Rust `intern_base`
  (`name_state_class_graph.rs`, `canonical_key` then `#` and the `ready_earliest` bits),
  TypeScript `internBase` over `baseKeyOf` (`analysis/name-state-class.ts`,
  `analysis/name-state-class-graph.ts`). Place names are arbitrary strings (`Place::new`
  checks nothing), so the markings {`a`:1, `b`:1} and {`a:1,b`:1} (TypeScript: {`a:1, b`:1}) get
  one key. On the net `t1: x -> a, b`, `t2: x -> 'a:1,b'` from {`x`:1}, both successors of the
  initial class have no clocks, so their class keys are equal: the Rust build reports
  `complete=true` with 2 classes where the correct graph has 3, the edge (`t2`, 0) points to the
  class with marking {`a`:1, `b`:1}, and `is_reachable` of {`a:1,b`:1} answers `false`. The
  TypeScript build also stores 2 classes. A marking that a timed run reaches is then missing from
  a graph reported closed, which can give an unsound `Proven`; in Route B the first arrival's base
  class is kept and the second marking is lost the same way. Java keys by structure
  (`StateClass.equals` over `MarkingState` and the DBM, and the record `BaseKey` in
  `NameStateClassGraph.java`), so it does not collide. Rust's `reachable_markings` dedups by
  the same string, and `zone_key` leaves clock names unescaped; TypeScript's counterexample
  decoder dedups markings by `toString()` too. The fix is a key that cannot collide:
  key the maps by the structured marking and zone, as Java does, or escape or length-prefix every
  name in the rendering.
- **Lean evidence:** `VER_010_key_forbids_markingBlind` (`VER_010.lean`): an identity that gives
  two classes with different markings and one zone one key breaks `VER_010_key` line 2. The model
  indexes places by number and has no place names, so the string rendering itself is not modelled.
- **Fix:** Rust escapes `\`, `,`, `:`, `|` and `#` in place and clock names in `canonical_key` and
  `zone_key`, so the class key, `reachable_markings` and `intern_base` are injective. TypeScript
  keys classes, Route B base classes, `StateClass.equals`, `isReachable` and the counterexample
  decoder by `MarkingState.key()`, the JSON of the sorted entries; the public
  `StateClassGraph.reachableMarkings()` still returns display strings. Rust `state_class_graph.rs`
  `ver_010_class_key_does_not_merge_markings_through_place_names`, `marking_state.rs`
  `ver_010_canonical_key_escapes_separators` and `dbm.rs` `ver_010_zone_key_escapes_clock_names`;
  TypeScript `state-class-graph.test.ts`, "VER-010: a place named "a:1, b" does not share a class
  key with {a:1, b:1}" and "VER-012: Route B keeps the marking that renders like the first
  arrival's". Python runs the Rust verifier and has no test of its own.
- **Status:** fixed, unreleased.

### RD-41. TypeScript gives an unnamed transition of an instance the action of the first transition of its name

- **Requirements:** MOD-030 (`MOD_030` line 4: a transition the mapping does not name keeps the
  action it carried in the receiver).
- **Runtimes:** TypeScript.
- **Defect:** `Instance.bindActions` binds the renamed body through a resolver that, for a name
  the mapping does not give, returns the action of the first transition of the renamed body with
  that name (`typescript/src/core/instance.ts`), and
  `PetriNet.bindActionsWithResolver` rebuilds a transition whenever the resolver's action differs
  from its own (`typescript/src/core/petri-net.ts`). No builder and no instantiation checks
  transition names (ruling D23 assumes them distinct; `renameNet` adds every body transition,
  `typescript/src/core/internal/subnet-rewriter.ts`), so an instance can hold two
  transitions of one name. Instantiate a body with `x` (action A1), `x` (action A2) and `y` as
  `p` and call `bindActions({y: B})`: the second `p/x` ends up with A1 instead of A2. With
  distinct names the first transition of a name is the transition itself and nothing changes.
  Rust and Python (the resolver returns `None`, so the transition is cloned,
  `bind_actions_with_resolver` in `rust/libpetri-core/src/petri_net.rs`) and Java (the resolver
  returns `null`, so the action is kept, `Instance.bindActions` in
  `java/src/main/java/org/libpetri/core/Instance.java`) keep the
  transition's own action. The fix is a resolver that returns `null` for a name the mapping does not give, as Java does.
- **Lean evidence:** `MOD_030_forbids_firstOfName` (`MOD_030.lean`): the binding that gives an
  unnamed transition the action of the first transition of its name breaks `MOD_030` line 4 on
  an instance with two transitions named `p/x`.
- **Fix:** the resolver returns `null` for a name the mapping does not give, so every such
  transition keeps its own action. TypeScript `instantiate.test.ts`, "MOD-030: a transition the
  mapping does not name keeps its own action, even with a same-named sibling".
- **Status:** fixed, unreleased.

### RD-42. Java and TypeScript treat the last millisecond of the total budget differently from the clamp

- **Requirements:** VER-013 (the total budget sentence, `VER_013_args` line 6: with no whole
  millisecond remaining no process starts, and AC9 'no z3 process starts once the budget is
  spent'; the stop sentences, `VER_013_stop` line 4: a solver call is refused only by a poll
  that finds the stop, and line 6: the `Unknown` then gets the reason `total verification budget
  of <N> ms exhausted during <phase>`).
- **Runtimes:** Java, TypeScript.
- **Defect:** both runtimes poll the deadline on a finer clock than the clamp reads it, so when
  less than one millisecond of the total budget is left the two disagree. Java:
  `Z3Solver.run` (`java/src/main/java/org/libpetri/smt/z3/Z3Solver.java`) calls
  `deadline.check()`, which throws only once the nanosecond deadline has passed
  (`VerificationDeadline.expired`, `java/src/main/java/org/libpetri/core/internal/VerificationDeadline.java`),
  and then sets `left = Math.max(1, deadline.remainingMs())` with `remainingMs` the remaining
  nanoseconds divided down to whole milliseconds. With 0 < remaining < 1 ms the whole
  milliseconds left are 0, yet Java starts a `z3` process with `-t:1`, `-T:2` and a 2001 ms
  watchdog. TypeScript: `runZ3Text` (`typescript/src/verification/z3/z3-process.ts`)
  refuses when `Math.floor(deadline.remainingMs()) <= 0` but records no stop, while every poll
  (`Deadline.check` through `passed()`, `remainingMs() <= 0`,
  `typescript/src/verification/total-budget.ts`; `enter`, and the `unknown` case of the IC3/PDR
  query and the certificate check in `runPipeline`, `smt-verifier.ts`) still sees
  time left. In that window the IC3/PDR query is refused, `runZ3Spacer` turns the rejection into
  `unknown` with the reason `total verification budget of <N> ms exhausted; z3 not started`
  (`z3/spacer-runner.ts`), the `check()` of the `unknown` case does not throw, and
  `verify()` returns that reason without `during IC3/PDR query`. A step that steps aside after a
  refused call (the state-equation phase, for example) is followed by `enter()` of the next
  step, which passes, so a step is entered after the refusal. Rust and Python use one
  whole-millisecond `remaining()` for the entry poll, the polls inside a step and the clamp
  (`total_budget.rs` `expired_now`, `step`, `cut`, `clamp`), so the clamp refuses exactly when a
  poll records `Stop::Budget`. The fix is one clock for both:
  Java should start no process when `remainingMs()` is 0 and record the budget stop there (or
  poll and clamp on whole milliseconds, as Rust does); TypeScript should record the stop when
  the clamp refuses, or poll on `Math.floor(remainingMs()) <= 0`.
- **Lean evidence:** `VER_013_args_forbids_javaSubMs` (`VER_013.lean`): the clamp that raises a
  remainder of 0 whole milliseconds to 1 ms breaks `VER_013_args` line 6 while lines 4 and 5
  hold for it. `VER_013_stop_forbids_refuseUnrecorded` (`VER_013.lean`): a runner whose refused
  call records no stop breaks `VER_013_stop` line 4, and its `Unknown` keeps the refusal's own
  reason. The two clocks themselves are not modelled; the model has one stop per poll.
- **Fix:** both runtimes poll on the whole-millisecond clock the clamp reads: Java's `expired()` is
  `remainingMs() <= 0` and `Z3Solver.run` starts no process with no whole millisecond left, and
  TypeScript's `passed()` tests `Math.floor(remainingMs()) <= 0`. Java
  `TotalBudgetTest.subMillisecondRemainderStopsAsTheClampDoes_VER013_AC9` and
  `StubZ3Test.totalBudget_noProcessStartsWithoutAWholeMillisecondLeft_VER013_AC9`; TypeScript
  `total-budget.test.ts`, "VER-013 AC9: with less than one whole millisecond left the poll stops as
  the clamp refuses".
- **Status:** fixed, unreleased.

### RD-43. Java does not poll the total budget after an unclamped z3 call

- **Requirements:** VER-013 (the stop sentences, `VER_013_stop` line 4: a solver call that
  starts its process polls again after the reply, and a stop that poll is the first to find is
  charged to the running step; and through it line 6 and AC9's reason: an `Unknown` reached after
  the deadline passed gets `total verification budget of <N> ms exhausted during <phase>`).
- **Runtimes:** Java.
- **Defect:** after the process, `Z3Solver.run`
  (`java/src/main/java/org/libpetri/smt/z3/Z3Solver.java`) checks only
  `VerificationDeadline.cancelled()` and `clamped && deadline.expired() && !answered(reply)`. A
  total budget that runs out during a call whose own timeout was not clamped is therefore not
  recorded. Concrete run: total budget 10 000 ms, per-call timeout 5 000 ms, and the IC3/PDR
  query starts with exactly 5 000 ms left, so `left < timeoutMs` is false and the call is not
  clamped; `z3` overruns `-t` and is stopped by the `-T` backstop at about 6 s. `SpacerRunner.run`
  returns `Unknown` with the hard-timeout reason, the HORN `Unknown` case of `SmtVerifier.pipeline`
  (`java/src/main/java/org/libpetri/smt/SmtVerifier.java`) does not poll, and no later
  `enter()` follows, so `verify()` returns the solver's reason where Rust and TypeScript give
  `total verification budget of 10000 ms exhausted during IC3/PDR query`. Rust and Python poll
  after every call (`Z3Solver::run` calls `total_budget::note_if_expired`, which is `cut`), and
  TypeScript's `unknown` case of the IC3/PDR query polls with `run.deadline?.check()`
  (in `runPipeline`, `typescript/src/verification/smt-verifier.ts`). The fix is a deadline
  poll after every call, clamped or not (`deadline.check()` once the reply is in, before it is
  returned unanswered), as Rust's `note_if_expired` does.
- **Lean evidence:** `VER_013_stop_forbids_noPostPoll` (`VER_013.lean`): the runner whose solver
  calls make no poll after the reply breaks `VER_013_stop` line 4 on the IC3/PDR query under a
  100 ms budget spent from poll 2 and a solver that answers `unknown`; its finished `Unknown`
  keeps `the solver answered unknown` where the reference gives the budget reason.
- **Fix:** `Z3Solver.run` polls after every reply, clamped or not, and charges a stop to the running
  step when the reply is not an answer; an answer that arrives after the deadline is returned and
  the next `enter()` stops the call, as Rust's `note_if_expired` does. Java
  `StubZ3Test.totalBudget_spentDuringAnUnclampedCallIsChargedToThatStep_VER013`.
- **Status:** fixed, unreleased.

### RD-44. Python archive headers carry an empty structure

- **Requirements:** EVT-025 (the writer line: the header carries the session's own header fields).
- **Runtimes:** Python.
- **Defect:** `write_from_store` built the archived debug session with `places: None`
  (`rust/libpetri-py/src/archive.rs`), so `build_net_structure` returned no places and no
  transitions (`rust/libpetri-debug/src/debug_session_registry.rs`) and the header's
  `structure` listed neither, although the writer has the net. The Rust registry fills it (`places:
  Some(PlaceAnalysis::from_net(net))`, `register_with_tags` in `debug_session_registry.rs`).
- **Lean evidence:** none; the EVT_025 model keeps the session's header fields, the net structure
  among them, opaque.
- **Fix:** the archived session carries `places: Some(PlaceAnalysis::from_net(net))`, so the
  header's `structure` lists the net's places and transitions. Python
  `test_archive.py::test_evt_025_archive_header_structure_lists_the_nets_places_and_transitions`.
- **Status:** fixed, unreleased.

### RD-45. Java's `SubnetInstanceInfo` loses the build order of its name sets

- **Requirements:** EVT-014 (AC5: rendering the same event stream twice onto the debug protocol
  yields identical output), EVT-025 (the reproducibility paragraph, the debug protocol half).
- **Runtimes:** Java.
- **Defect:** the `SubnetInstanceInfo` constructor copied its place and transition name sets with
  `Set.copyOf` (`java/src/main/java/org/libpetri/debug/DebugResponse.java`), which drops the
  `LinkedHashSet` order `buildSubnetInstances` builds, so a `Subscribed` response listed the names
  of a subnet instance in an order salted per JVM. It was found with RD-36, whose text names the
  same constructor.
- **Lean evidence:** none; the debug protocol has no model.
- **Fix:** the constructor copies each set into an unmodifiable `LinkedHashSet`, which keeps the
  build order and still rejects `null`. Java
  `DebugProtocolSubnetTest.subnetInstanceNamesKeepBuildOrder_EVT014_AC5`.
- **Status:** fixed, unreleased.

### RD-46. Java's debug protocol handler does not clamp a replay index

- **Requirements:** EVT-032 (AC2: an index beyond the stream length is clamped).
- **Runtimes:** Java.
- **Defect:** `DebugProtocolHandler.ClientState.computeStateAt` passes the index to `subList` on its
  fallback without a subscription
  (`java/src/main/java/org/libpetri/debug/DebugProtocolHandler.java`), the same unclamped
  call as RD-22. It was latent: the protocol commands reach that fallback only with an index within
  the stream.
- **Lean evidence:** `EVT_032_mutant_noClamp` (EVT_032.lean).
- **Fix:** the call clamps the index with `Math.clamp(targetIndex, 0, events.size())`. It has no
  test of its own: `ClientState` is private and no protocol command reaches the fallback with an
  index past the end; `MarkingCacheTest.computeAtBeyondStreamLengthClampsToEnd_EVT032_AC2` covers
  the clamp of RD-22.
- **Status:** fixed, unreleased.

### RD-47. A reused Java `SmtVerifier` checks the net its previous call rewrote

- **Requirements:** CORE-043 (line 3: a verification entry point fails exactly when compiling the
  submitted net does).
- **Runtimes:** Java.
- **Defect:** the CORE-043 check before `prepare()` read the mutable `net` field (`pipeline` and
  `encodeScripts` in `java/src/main/java/org/libpetri/smt/SmtVerifier.java`), which the previous
  call left rewritten. A second call therefore threw when the first call's rewrite had made a
  CORE-043 violation, the case of RD-08 (a passthrough sink split under `CONFLICT`), for example on
  `encodeScripts()` called twice. The read outside the synchronized `prepare()` was also a data race
  when threads share a verifier.
- **Lean evidence:** none; the CORE_043 assumes record it, as for RD-08.
- **Fix:** `pipeline()` and `encodeScripts()` run the check on the caller's net (`callerNet`), with
  the RD-08 change. Java `SplitDemandTest.CORE043_aReusedVerifierChecksTheCallersNet`.
- **Status:** fixed, unreleased.

### RD-48. No debug protocol handler invalidates its replay cache after an eviction

- **Requirements:** EVT-032 (AC3: a cache whose event list changed other than by growing at its end
  needs `invalidate()` before the next call).
- **Runtimes:** Java, TypeScript, Rust, Python.
- **Defect:** the debug protocol handler kept one marking replay cache per session and reused it
  after the session's debug event store evicted events. A seek or a step backward after an eviction
  replayed from a snapshot of events the store no longer held, so it returned a state that is not
  the replay of the retained events.
- **Lean evidence:** none; EVT_032 and EVT_032_B state the cache contract and assume a coherent
  caller.
- **Fix:** the handler invalidates the cache before it computes a state whenever the store's
  evicted count changed since the cache was last used (Java also compares the first retained
  event). Java `DebugProtocolHandler.SubscriptionState.computeStateAt`, TypeScript
  `SubscriptionState.computeStateAt` in `debug-protocol-handler.ts`, Rust `compute_state_at` in
  `debug_protocol_handler.rs`; Python uses the Rust handler. Tests: Java
  `DebugProtocolHandlerTest.SeekAndStepFlow.seekAfterEvictionReplaysTheRetainedEvents_EVT032_AC3`
  and the step-backward twin, the TypeScript and Rust handler tests citing EVT-032.
- **Status:** fixed, unreleased.

### RD-49. Rust never emits the MarkingSnapshot event

- **Requirements:** EVT-014 (AC1: emitted at least at execution start and before execution
  completion).
- **Runtimes:** Rust, Python.
- **Defect:** Rust declared `NetEvent::MarkingSnapshot` and its consumers read it (debug converter,
  marking cache, archive metadata), but no executor emitted it.
- **Lean evidence:** the Rust and Python emission `polRust` (`lean/Libpetri/Reference/Events.lean`)
  emits both snapshots; the Rust stream then meets EVT-032's run companion (`EVT_032_B_rust`),
  which reads only the counts.
- **Fix:** the shared executor core emits `MarkingSnapshot` right after `ExecutionStarted` and right
  before `ExecutionCompleted`, on both backends and in `run_sync` and `run_async`, so Python gets it
  too. The session archive reader now reads an archived snapshot back instead of turning it into a
  `TransitionEnabled` for an unknown transition. A store that records several runs now holds each
  run's start snapshot, so a replay resets to that run's marking.
- **Status:** fixed, unreleased.

### RD-50. The Rust MarkingSnapshot event carries token counts, not tokens

- **Requirements:** EVT-014 (the snapshot is a map from place name to the place's tokens in FIFO
  order).
- **Runtimes:** Rust, Python.
- **Defect:** `NetEvent::MarkingSnapshot` holds `BTreeMap<Arc<str>, usize>`, a count per place,
  so the event cannot carry the tokens.
- **Lean evidence:** `EVT_014_forbids_countsOnly`: a snapshot that keeps each place's count and
  loses its tokens breaks EVT-014, and keeps its order and place-set lines
  (`evt014_countsOnly_lines34`). No theorem states EVT-014 of the Rust emission `polRust`.
- **Fix:** none yet. Carrying tokens changes the shape of a public enum variant, a breaking change
  that needs a coordinated major release of the Rust crate and the Python binding.
- **Status:** open.

### RD-51. The event stores lack the EVT-030 query helpers

- **Requirements:** EVT-030 (AC3: filter by place name and page with offset and limit; AC5: an
  event-type histogram).
- **Runtimes:** Java, TypeScript, Rust.
- **Defect:** only the Python binding offered a place filter, offset and limit, and `counters()`;
  the Rust store also had no filter by event type.
- **Lean evidence:** none.
- **Fix:** each store gains the helpers with the Python binding's semantics, without an API break.
  Java: default methods `EventStore.placeEvents`, `filter(predicate, offset, limit)` and
  `counters()`. TypeScript: free functions `queryEvents` (with `EventQuery`), `placeEvents`,
  `countEvents`, `counters` and `eventPlaceName`. Rust: `InMemoryEventStore::events_of_type`,
  `place_events`, `query(&EventQuery)`, `count_of_types` and `counters`, and
  `NetEvent::event_type`. Tests cite EVT-030 in each language.
- **Status:** fixed, unreleased.

### RD-52. TypeScript keeps reporting `stopped` after the loop an expired run budget left running finishes

- **Requirements:** EXEC-041 (a finish makes its own termination reason available to the caller;
  `stopped` only after an immediate termination, another caller-requested stop, a host fault or a
  run-ending failure of the run's event store; a run budget that expires ends the caller's wait, not
  the loop).
- **Runtimes:** TypeScript.
- **Defect:** after `run(timeoutMs)` expired, both executors set the reason to `stopped` and set it at
  the loop's finish only while it still read `running` (`executeLoop` in
  `typescript/src/runtime/bitmap-net-executor.ts` and `precompiled-net-executor.ts`). The loop that
  the abandon or close policy left running then finished quiescent, terminal or closed, and
  `terminationReason()` still answered `stopped`, so the cause of that finish was never reported.
  Java sets the reason only at the loop's finish.
- **Lean evidence:** none.
- **Fix:** `executeLoop` sets the reason from the terminal flag, the close flag and quiescence at
  every finish. The reason reads `stopped` from the expiry until the loop finishes; the caller of the
  expired run still gets the truncation through the rejected promise. Tests citing EXEC-041 in
  `typescript/tests/runtime/terminal-places.test.ts` check both policies on both executors.
- **Status:** fixed, unreleased.

### RD-53. A match key that throws ends the run in Java and TypeScript

- **Requirements:** NU-020 (a token whose key yields no name has no name on that input), NU-054 (a
  projection that fails yields no name), EXEC-041 (`stopped` only after an immediate termination,
  another caller-requested stop, a host-runtime fault or a run-ending failure of the run's event
  store).
- **Runtimes:** Java, TypeScript.
- **Defect:** a match-key projection that threw while the loop decided enablement or consumed the
  matched tokens escaped the executor. Java caught only `ClassCastException`
  (`MatchSpec.MatchKey.extract`, and the consume predicate of `fireTransition` in
  `BitmapNetExecutor.java` and `PrecompiledNetExecutor.java`), so any other `RuntimeException` ended
  the run with `STOPPED` and `run()` raised it, or the executor's constructor raised it when it
  seeded the match cache. TypeScript caught nothing (`buildNameIndex`, `cacheAddToken` and
  `fireTransition`), so `run()` rejected with the projection's error. Python already read a raise as
  no name (`make_py_projection` in `rust/libpetri-py/src/model.rs`); a Rust projection cannot fail by
  type.
- **Lean evidence:** none.
- **Fix:** a projection that throws yields no name: Java's `MatchKey.extract` and the consume
  predicates catch any `RuntimeException`, and every TypeScript key call goes through `projectName`
  in `typescript/src/runtime/match-engine.ts`. The token correlates with nothing and the run goes
  on. Tests citing NU-054 and EXEC-041 (`nuJoin_throwingKeyIsNoName_*` in
  `AbstractNetExecutorEngineTest.java`, 'a throwing key is no name' in
  `typescript/tests/runtime/nu-net.test.ts`) check both executors, on the match cache and on the
  rebuild path: the join fires on the name it can match and the run ends quiescent.
- **Status:** fixed, unreleased.

### RD-54. Rust and TypeScript build an Xor of fewer than two children or an empty And written without its constructor

- **Requirements:** IO-012 (line 1, an `Xor` node has two or more children; AC1), IO-011 (AC1, an `And`
  node has at least one child).
- **Runtimes:** Rust, TypeScript.
- **Defect:** the arity checks lived only in the `xor()` and `and()` factories
  (`rust/libpetri-core/src/output.rs`, `typescript/src/core/out.ts`). Rust's `Out::Xor` and `Out::And`
  variants are public and a TypeScript output spec can be written as an object literal, and neither
  `TransitionBuilder::build` (`rust/libpetri-core/src/transition.rs`) nor `TransitionBuilder.build`
  (`typescript/src/core/transition.ts`) ran the checks again, although both re-run the IO-002/IO-004
  count and TIME-001 timing factory checks for these paths. `Out::Xor(vec![])` built a transition that
  consumes on every firing and then fails output validation; a one-child Xor built as its child, and
  an empty And as a spec that claims no place. Java checks in the `Arc.Out.Xor` and `Arc.Out.And`
  record constructors; Python goes through `xor()` and `and()`.
- **Lean evidence:** none beyond the IO_012 AC1 assume.
- **Fix:** the transition builders of Rust and TypeScript reject an `Xor` node with fewer than two
  children or an `And` node without one, at any depth, the first such node in pre-order reporting
  with the factory's message, after the timing check and before the output-spec checks
  (`arity_violation` in `output.rs`, `arityViolation` in `out.ts`). Python's `xor_outputs` and
  `and_outputs` now raise the factory's message as a `ValueError`. Tests citing IO-012 AC1 and
  IO-011 AC1: `io_012_ac1_xor_and_io_011_ac1_and_arity_is_checked_at_build` in `transition.rs`,
  'IO-012 AC1, IO-011 AC1: an object literal does not skip the arity check' in
  `typescript/tests/core/out-build-checks.test.ts`, and
  `test_io_012_ac1_and_io_011_ac1_arity_is_the_factory_check` in
  `python/tests/test_output_spec_build_checks.py`.
- **Status:** fixed, unreleased.
