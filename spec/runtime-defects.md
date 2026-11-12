# Runtime Defect Ledger

This file is not a requirement file. It holds no requirement IDs of its own and is not counted
in the 13 spec files or the active requirements of [00-index.md](00-index.md).

A **runtime defect** is a place where a runtime breaks a requirement that the spec keeps. The
spec was not weakened to match the runtime: the requirement stays as written, the Lean block
states it, and the runtime is fixed later in a runtime change. Each entry names the requirements
it breaks, the runtimes that break them, where in the code, and the Lean evidence that shows it,
if there is any. A Lean block that calls something a recorded defect cites the entry by its
number (`RD-NN`).

An entry stays `open` until the runtime change lands. Then its status becomes `fixed in <version>`
and the entry stays here as history. Line numbers are hints taken when the entry was written; the
named function is the reference.

| ID | Requirements | Runtimes | Status |
|---|---|---|---|
| RD-01 | EXEC-021, EXEC-022, IO-013 | Java, TypeScript | open |
| RD-02 | CORE-041 | TypeScript | open |
| RD-03 | CORE-040, CORE-002 | TypeScript | open |
| RD-04 | EVT-001 | TypeScript | open |
| RD-05 | CORE-042 | TypeScript | open |
| RD-06 | CORE-051 | Java, TypeScript | open |
| RD-07 | CORE-021 | Python | open |
| RD-08 | CORE-043 | Rust, Java, TypeScript, Python | open |
| RD-09 | CORE-060 | Java | open |
| RD-10 | CORE-020, MOD-020 | Rust, Java, TypeScript, Python | open |
| RD-11 | MOD-020 | Rust, Java, TypeScript, Python | open |
| RD-12 | EXP-016, EXP-017, MOD-040 | Rust, Java | open |
| RD-13 | EXP-016 | Rust | open |
| RD-14 | EXP-016 | Rust, Java, TypeScript | open |
| RD-15 | EXEC-022 | Rust, Python | open |
| RD-16 | TIME-014, TIME-010, EXEC-001 | Java | open |
| RD-17 | EVT-025 | Java | open |
| RD-18 | EVT-025 | Python | open |
| RD-19 | EVT-025 | Python | open |
| RD-20 | EVT-025 | Python | open |
| RD-21 | EVT-030, EVT-013 | Java | open |
| RD-22 | EVT-032 | Java | open |
| RD-23 | MOD-031 | Rust, Java, TypeScript, Python | open |
| RD-24 | MOD-025 | Java | open |
| RD-25 | MOD-061, MOD-026 | Rust, Java, TypeScript, Python | open |
| RD-26 | VER-003, NU-053 | Java | open |
| RD-27 | NU-051 | Rust, Python | open |
| RD-28 | VER-017 | TypeScript | open |
| RD-29 | MOD-051 | TypeScript | open |
| RD-30 | MOD-031 | Python | open |
| RD-31 | MOD-031, IO-013 | Java, TypeScript | open |

### RD-01. The timeout outcome is validated against the output spec

- **Requirements:** EXEC-021, EXEC-022, IO-013 (ruling D24 (a)).
- **Runtimes:** Java, TypeScript.
- **Defect:** both validate the timeout outcome against the whole output spec, so a spec such as
  `And(A, Timeout(d, B))` fails the firing on every timeout instead of depositing `B`. Rust skips
  validation on the timeout path and still runs the join-relay check.
  `java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java:1897-1898`
  (`processCompletedTransitions`), `typescript/src/runtime/bitmap-net-executor.ts:1253`
  (`validateOutSpec` on the completion path that also settles a timed-out firing).
- **Lean evidence:** `clashExec_timeoutValidated_conflict` (ClashesExec.lean),
  `EXEC_021_forbids_validateTimeout` (EXEC_021.lean).
- **Status:** open.

### RD-02. The TypeScript builder hands its live sets to the built net

- **Requirements:** CORE-041 (ruling D66 (a)).
- **Runtimes:** TypeScript.
- **Defect:** `build()` passes the builder's own place and transition sets to the net, so a later
  builder call changes a net that was already built. `typescript/src/core/petri-net.ts:740-741`.
- **Lean evidence:** `CORE_041_forbids_alias` (CORE_041.lean), `aliasBuilder_unstable`
  (Reference/Build.lean).
- **Status:** open.

### RD-03. TypeScript identifies places by object reference

- **Requirements:** CORE-040 (line 3, "no place twice"), CORE-002 (ruling D66 (a)).
- **Runtimes:** TypeScript.
- **Defect:** `place(name)` returns a new object on each call and the built net keeps places by
  reference, while the compiled net keys them by name, so one place can be held twice.
  `typescript/src/core/place.ts:25-27`, `typescript/src/core/petri-net.ts:158`, `:212-227`.
- **Lean evidence:** none beyond the CORE_040 and CORE_002 assumes; under name identity the
  TypeScript net breaks CORE_040 line 3.
- **Status:** open.

### RD-04. A TypeScript event shares the executor's consumed array

- **Requirements:** EVT-001 (AC2: collections in events are copies; ruling D66 (a)).
- **Runtimes:** TypeScript.
- **Defect:** the `TransitionStarted` event carries the executor's own `consumed` array, which the
  executor also hands on, so the event is not a copy. `typescript/src/runtime/bitmap-net-executor.ts`
  (`fireTransition`), `typescript/src/event/net-event.ts:59-64`.
- **Lean evidence:** none. EVT-001 has no block: a Lean event is a value, so a shared array cannot
  be stated (`netEvent_value`, GlossaryEvents.lean, cites EVT-001).
- **Status:** open.

### RD-05. A TypeScript resolver that returns `undefined` binds `undefined`

- **Requirements:** CORE-042 (a resolver that returns no action defers).
- **Runtimes:** TypeScript.
- **Defect:** `bindActionsWithResolver` treats only `null` as no action, so a plain JavaScript
  resolver such as `name => obj[name]` rebinds an unknown transition to `undefined`.
  `typescript/src/core/petri-net.ts:95-97`.
- **Lean evidence:** none; the CORE_042 block reads `none` as the resolver's `null`.
- **Status:** open.

### RD-06. Java and TypeScript accept `action(null)`

- **Requirements:** CORE-051.
- **Runtimes:** Java, TypeScript.
- **Defect:** the builder setter stores `null` (or `undefined`) as the action. The identity check
  of CORE-043 passes such a transition, and every firing of it then fails. Python raises
  `TypeError`; Rust cannot express it. `java/src/main/java/org/libpetri/core/Transition.java:367-370`,
  `typescript/src/core/transition.ts:222-225`.
- **Lean evidence:** none; the CORE_051 assumes record it.
- **Status:** open.

### RD-07. A Python transition is not equal to itself when read back

- **Requirements:** CORE-021 (AC2).
- **Runtimes:** Python.
- **Defect:** the `Transition` wrapper defines no `__eq__` or `__hash__`, and `PetriNet.transitions`
  returns a fresh wrapper on every access, so `net.transitions[0] == net.transitions[0]` is
  `False`. The fix is `__eq__` and `__hash__` on the wrapped `TransitionId`.
  `rust/libpetri-py/src/model.rs:198-225`, `:492-496`.
- **Lean evidence:** none; the CORE_021 assumes record it.
- **Status:** open.

### RD-08. The CORE-043 check runs on the derived split net under CONFLICT

- **Requirements:** CORE-043 (line 3: a verification entry point fails exactly when compiling the
  submitted net does).
- **Runtimes:** Rust, Java, TypeScript, and Python through Rust.
- **Defect:** under `PrioritySemantics` CONFLICT the verifier splits a sink into a start half,
  which keeps the sink's name and action and gains an output place, and then runs the CORE-043
  check on that derived net. A net that compiles is refused, and the Rust error says the sink
  declares an output spec when it declares none.
  Rust: `rust/libpetri-verification/src/smt_verifier.rs:872-879`, `in_flight.rs:390-403`,
  `nu_scg_verifier.rs:277` (`verify_name_scg`), `state_class_graph.rs:160`
  (`StateClassGraph::build_core`).
  Java: `java/src/main/java/org/libpetri/smt/SmtVerifier.java:1885-1888`,
  `java/src/main/java/org/libpetri/analysis/StateClassGraph.java:630`.
  TypeScript: `typescript/src/verification/smt-verifier.ts:1215-1216` (after `prepare()`).
  The fix is to run the check once, on the submitted net, before any rewrite.
- **Lean evidence:** none; the CORE_043 assumes record it.
- **Status:** open.

### RD-09. Java's `input` with several tokens contradicts its own javadoc

- **Requirements:** CORE-060 (the case is open in the spec; ruling D50 (a)).
- **Runtimes:** Java.
- **Defect:** with more than one token delivered from a place, `input` returns the oldest token's
  value, while its javadoc says it fails. Rust, TypeScript and Python report an error.
  `java/src/main/java/org/libpetri/core/TransitionContext.java:164-168` against the javadoc at `:162`.
- **Lean evidence:** `CORE_060_batch_undecided` shows the block leaves the case open; the
  defect is Java against its own documentation.
- **Status:** open.

### RD-10. No builder or compose checks transition names

- **Requirements:** CORE-020 and every name-keyed requirement under the unique-names assumption
  (rulings D10, D23); MOD-020 (composition).
- **Runtimes:** all.
- **Defect:** no net builder and no instance compose rejects two transitions of one name, so a
  composed net can hold a duplicate name, which the name-keyed requirements assume away.
  `rust/libpetri-core/src/petri_net.rs:319-339`, `:1216-1220`,
  `java/src/main/java/org/libpetri/core/PetriNet.java:902-904`.
- **Lean evidence:** none; the shared unique-names assumption (`NamesDistinct`, `Cfg.WF.names`)
  keeps such nets out of the blocks.
- **Status:** open.

### RD-11. A caller transition bound to two channels is not rejected

- **Requirements:** MOD-020 (ruling D72 (ii)(b): a caller transition bound to two channels of
  one instance in one call is an error, AC6). The port half of the first entry is withdrawn:
  every runtime rejects a port re-bound in one call with `Port '<name>' is already bound`
  (ruling D72 (i)(a); `rust/libpetri-core/src/compose.rs:103-105`,
  `java/src/main/java/org/libpetri/core/ComposeBindings.java:69-72`,
  `typescript/src/core/compose-bindings.ts:74-76`).
- **Runtimes:** all.
- **Defect:** no runtime rejects one caller transition bound to two channels of one instance.
  Rust stages the merges in a map keyed by the caller's name, so only the merge its hash order
  visits last survives; Java and TypeScript add both merges under one name
  (`apply_composition` in `rust/libpetri-core/src/petri_net.rs`, `applyComposition` in
  `java/src/main/java/org/libpetri/core/PetriNet.java` and `typescript/src/core/petri-net.ts`).
- **Lean evidence:** none; MOD-020 makes distinct caller-side names a caller obligation
  (`mod020_fresh`, MOD_020.lean) and states nothing about such a call.
- **Status:** open.

### RD-12. An empty `/` segment in a cluster key fails the export

- **Requirements:** EXP-016, EXP-017, MOD-040 (ruling D46 (a)).
- **Runtimes:** Rust (panics), Java (throws). TypeScript draws the clusters the model draws.
- **Defect:** on a key such as `a//x` or `http://host/x`, `register_prefix_chain` skips the empty
  segment and never registers the key itself; the builder then fails at the node's key.
  `rust/libpetri-export/src/cluster_builder.rs:270` (`register_prefix_chain`),
  `java/src/main/java/org/libpetri/export/ClusterBuilder.java`.
- **Lean evidence:** `registerChain` (Reference/ExportCluster.lean); EXP-016's name assumption
  (`ExportNet.ClusterKeysWellFormed`) keeps such nets out of the block.
- **Status:** open.

### RD-13. Rust keeps Unicode letters in a cluster ID

- **Requirements:** EXP-016 (ruling D46 (a) leaves non-ASCII names implementation-defined).
- **Runtimes:** Rust.
- **Defect:** Rust's sanitize keeps Unicode letters, so for a key `Größe` Rust draws
  `cluster_Größe` where Java and TypeScript draw `cluster_Gr__e`. Listed so that a later change
  can align the runtimes; under D46 (a) it breaks no line.
  `rust/libpetri-export/src/mapper.rs:41-51`.
- **Lean evidence:** `exp016_nonAsciiKey_outside` (EXP_016.lean).
- **Status:** open.

### RD-14. Cluster keys are looked up by DOT ID

- **Requirements:** EXP-016 (ruling D46 (a)).
- **Runtimes:** Rust, Java, TypeScript.
- **Defect:** all three look a node's cluster key up by its DOT ID (`node_id_to_prefix`,
  `nodeIdToPrefix`), so two names that sanitise to one ID, such as `b1/x` and `b1_x`, become one
  node in one cluster. EXP-014's name assumption keeps such nets out of the block.
  `rust/libpetri-export/src/cluster_builder.rs`, `java/src/main/java/org/libpetri/export/PetriNetGraphMapper.java`,
  `typescript/src/export/petri-net-mapper.ts`.
- **Lean evidence:** `exp016_collide_outside` (EXP_016.lean).
- **Status:** open.

### RD-15. A flush can publish after the action's budget ran out

- **Requirements:** EXEC-022 (line 4: no output the action had not published before the budget
  ran out is deposited or published).
- **Runtimes:** Rust, Python.
- **Defect:** on a timeout the executor drops the action future, but the flush closure has no
  abandoned check and can outlive it: a Rust action that moved `ctx.flush_fn()` into a spawned
  task, or a Python context held past the dropped future, can still send a batch, which Phase 1b
  then deposits after the firing ended with its timeout outcome. The fix is an abandoned flag on
  the closure, set in the timeout arm and at completion.
  `rust/libpetri-runtime/src/executor_core/executor.rs:1653-1673` (`set_flush_fn` closure),
  `rust/libpetri-core/src/context.rs:176` (`flush_fn`), `rust/libpetri-py/src/action.rs:389`.
- **Lean evidence:** `EXEC_022_forbids_lateFlush` (EXEC_022.lean).
- **Status:** open.

### RD-16. Java's firing pass judges readiness at a reading of its own

- **Requirements:** TIME-014 (line 3), TIME-010 (the firing pass judges at the deadline step's
  reading), EXEC-001 (ruling D61 (c)).
- **Runtimes:** Java (both executors).
- **Defect:** a Java cycle takes three readings of the firing clock: the enablement update, the
  deadline step and the firing pass each read the clock (`clockNanos()`), and the pass judges
  readiness at its own reading instead of the deadline step's. Rust takes one reading per cycle
  and TypeScript two (the update's, and one that the deadline step and the pass share), which
  both conform.
  `java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java:1292`, `:1451`, `:1528`
  (`updateDirtyTransitions`, `enforceDeadlines`, `fireReadyGeneral`);
  `java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:2009`, `:2110`, `:2202`.
- **Lean evidence:** `TIME_014_forbids_passReread` (TIME_014.lean),
  `TIME_010_cycle_forbids_rereadAtBegin` (TIME_cycle.lean).
- **Status:** open.

### RD-17. Java's archive header order changes from one JVM to the next

- **Requirements:** EVT-025 (two archives of identical run data are identical).
- **Runtimes:** Java.
- **Defect:** the V2 and V3 header build the tags and the metadata histogram with `Map.copyOf`,
  whose iteration order is randomised per JVM, and the writer serialises maps in iteration order.
  `java/src/main/java/org/libpetri/debug/archive/SessionArchive.java:148`, `:181`,
  `java/src/main/java/org/libpetri/debug/archive/SessionMetadata.java:48`.
- **Lean evidence:** `EVT_025_mutant_seededTags` (EVT_025.lean).
- **Status:** open.

### RD-18. Python archives at most 10,000 events

- **Requirements:** EVT-025 (one record for each event of the store's snapshot).
- **Runtimes:** Python.
- **Defect:** `write_from_store` copies the store into a debug store of the default capacity of
  10,000 events before writing, so a larger store is archived without its oldest events.
  `rust/libpetri-py/src/archive.rs:87` (`DebugEventStore::new`).
- **Lean evidence:** `EVT_025_forbids_copyThroughBounded` (EVT_025.lean).
- **Status:** open.

### RD-19. Python writes archive version 3 only

- **Requirements:** EVT-025 (a writer for each of the header versions 1, 2 and 3; AC1).
- **Runtimes:** Python.
- **Defect:** the binding offers `write_from_store`, which always writes version 3, and no
  `writeV1` or `writeV2`. `rust/libpetri-py/src/archive.rs`.
- **Lean evidence:** `EVT_025_forbids_v3Only` (EVT_025.lean).
- **Status:** open.

### RD-20. Python stamps an empty archive with the wall clock

- **Requirements:** EVT-025 (two archives of identical run data are identical).
- **Runtimes:** Python.
- **Defect:** for an empty store `write_from_store` takes the start and end times from
  `SystemTime::now`, so two archives of the same empty session differ.
  `rust/libpetri-py/src/archive.rs:73-81`.
- **Lean evidence:** none; the EVT_025 assumes record it.
- **Status:** open.

### RD-21. Java's `transitionEvents` throws on an event with no transition name

- **Requirements:** EVT-030 (every helper is total; ruling D29 (a)), EVT-013 (AC4: a diagnostic
  that no transition is responsible for carries an empty or absent name, so a consumer reads it
  without failing).
- **Runtimes:** Java.
- **Defect:** `transitionEvents` calls `equals` on the transition name of every log message and
  throws on an engine diagnostic whose name is `null`, which both Java executors emit on an
  interrupted run. `java/src/main/java/org/libpetri/event/EventStore.java:138`.
- **Lean evidence:** `EVT_030_mutant_throwsOnNameless` (EVT_030.lean).
- **Status:** open.

### RD-22. Java's `computeAt` does not clamp the index

- **Requirements:** EVT-032 (AC2: an index beyond the stream length is clamped; ruling D83 (a)).
- **Runtimes:** Java.
- **Defect:** `MarkingCache.computeAt` passes the index to `subList` and throws
  `IndexOutOfBoundsException` past the stream length.
  `java/src/main/java/org/libpetri/debug/MarkingCache.java:40`.
- **Lean evidence:** `EVT_032_mutant_noClamp` (EVT_032.lean).
- **Status:** open.

### RD-23. A channel merge drops the caller's declared places from the correspondence

- **Requirements:** MOD-031 (key-set completeness of the declared-to-actual correspondence
  through every rewrite pass; ruling D69 (a) leaves the merged case out of the block).
- **Runtimes:** Rust, Java, TypeScript (Python rides on Rust).
- **Defect:** when a caller transition that carries no correspondence is merged with an instance
  transition that carries one, the merged transition keeps the instance side's correspondence
  whole, and a transition that carries a correspondence is never re-read from its arcs. The
  caller's declared places are then no keys, so a later pass that renames one of them (fusion at
  build, or instantiating the retrofitted net under MOD-014) leaves it unresolved, and the
  caller's action fails its declared-place check after its inputs were consumed (EXEC-031).
  `rust/libpetri-core/src/rewriter.rs:746`, `:309-318`,
  `java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java:654-655`,
  `typescript/src/core/internal/subnet-rewriter.ts:603-604`.
- **Lean evidence:** `MOD_031_mergeThenPass_undecided` (MOD_031.lean): after the runtimes' merge
  and one pass the declared place `h` resolves to `h`, which no arc names; after the reference's
  merge it resolves to `f`.
- **Status:** open.

### RD-24. Java's compose token-type check reads one host place per name

- **Requirements:** MOD-025 (line 4: a body place whose name the builder holds with another token
  type is rejected).
- **Runtimes:** Java.
- **Defect:** `compose(SubnetDef)` compares each body place with one host place per name, the
  one put last into a name-keyed map. When the builder already holds two places of one name with
  different token types (Java's `Place` equality is structural on name and type) and the last one
  has the body place's type, Java accepts the call where MOD-025 rejects it.
  `java/src/main/java/org/libpetri/core/PetriNet.java:611-615`.
- **Lean evidence:** none; line 4 of MOD-025 (MOD_025.lean) states the rejection, and no theorem
  models Java's name-keyed map.
- **Status:** open.

### RD-25. A fusion set that lists its first member again drops that member

- **Requirements:** MOD-061 (step 3: the canonical member remains; lines 1 and 3) and MOD-026
  (AC5: the surviving canonical place keeps its own entry; lines 1 and 2).
- **Runtimes:** Rust, Java, TypeScript (Python rides on Rust).
- **Defect:** the non-canonical members are every member after the first position, so a set
  with members `[a, b, a]` counts `a` among them. Fusion then drops the declared place `a` (it
  comes back only through an arc of a rewritten transition), runs the input merge on a transition
  whose only input arcs are on `a`, and drops `a`'s cluster entry.
  `rust/libpetri-core/src/petri_net.rs:939-943`, `:962-974`,
  `java/src/main/java/org/libpetri/core/PetriNet.java:1163-1169`, `:1093-1107`,
  `typescript/src/core/petri-net.ts:844-848`, `:771-783`.
- **Lean evidence:** `mod061_dupCanonical_kept` (MOD_061.lean) and `mod026_dupCanonical_kept`
  (MOD_026.lean): the reference keeps `a` and its entry.
- **Status:** open.

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
  path. `java/src/main/java/org/libpetri/smt/SmtVerifier.java:2421`, `:2455`, `:2488`,
  `:3698`; `java/src/main/java/org/libpetri/smt/z3/CounterexampleDecoder.java:69`; Rust
  `rust/libpetri-verification/src/smt_verifier.rs:3164` (`replay_phase` returns `None` when
  coloured). Confirmed by a run: `JoinRelayTest.fig12c(true)` with `R = 2`, budget `R`, the
  `FIG12C_CARRIERS` and `PlaceBound(R, 1)` (violated at the initial marking) returns `Violated`
  on route `SMT` with the name-coloured encoding, an empty trace and `counterexampleConfirmed`
  `false`.
- **Lean evidence:** line 6 of VER-003 (VER_003.lean) asks for `counterexampleConfirmed` not
  `false` at an initial violation; a decider that answers `some false` there, the reference
  otherwise, fails the block (checked in the wave W10 mutant run, not kept as a theorem). ν-nets
  are outside `Reference.TimedNet`, so VER_003.lean has no theorem about the coloured path.
- **Status:** open.

### RD-27. Rust ignores a carrier declaration it cannot resolve, outside Route B

- **Requirements:** NU-051 (the carrier bullet: a declared carrier that is not a place of the net
  is refused, in either fragment mode and whatever the query; ruling D95 (a)).
- **Runtimes:** Rust, Python (which runs the Rust verifier).
- **Defect:** Rust checks the declared carriers only under EXTENDED and only inside Route B
  (`rust/libpetri-verification/src/nu_scg_verifier.rs:279-290`, `verify_name_scg`, which answers
  `Unknown` naming the place). An absent carrier is therefore silently ignored in three cases:
  under BASE; under EXTENDED on a call that does not reach Route B; and under EXTENDED on a
  bounded quiescence query that does reach it, because the pipeline drops the Route B `Unknown`
  there and defers to Route A (`rust/libpetri-verification/src/smt_verifier.rs:1374-1379`,
  `defer_to_route_a`), whose `build_plan` skips a carrier it cannot resolve
  (`rust/libpetri-verification/src/name_coloured_encoder.rs:196-201`). Java and TypeScript
  reject the declaration in both modes (`SmtVerifier.carrierPlaces`).
- **Lean evidence:** `NU_051_carrier_forbids_routeBOnly` (BASE) and
  `NU_051_carrier_forbids_routeADeferral` (EXTENDED) in `NU_051_carrier.lean`: the shape Rust
  ships answers `Proven` on the co-mint net with the mistyped carrier `7`.
- **Status:** open.

### RD-28. TypeScript's state-space cache grows on every `Arrivals` query and never hits

- **Requirements:** VER-017 (the cache key: under `Arrivals` the key covers the closure, or the
  verifier does not use the cache for that query and says so in the report; AC7).
- **Runtimes:** TypeScript.
- **Defect:** the enumeration looks the graph up under the caller's net and the closed initial
  marking (`typescript/src/verification/smt-verifier.ts:2251-2254`, `enumerate`), and the marking
  half of the key names `Place` objects by identity
  (`typescript/src/verification/state-space-cache.ts:139`, `:163-171`, `markingKey`). The
  `Arrivals` closure makes new arrival-source `Place` objects on every call
  (`typescript/src/verification/smt-verifier.ts:338-345`, `applyArrivals`), so every query under
  `Arrivals` misses, builds, and adds one more entry, and the report does not say that the cache
  was not used. No verdict is wrong, since the cache never hits there. Java bypasses the cache
  under `Arrivals` with a report line; Rust and Python key the fingerprint of the closed net.
- **Lean evidence:** none; `VER_017_cache` takes the key as an abstract value (its assumes
  records the `Arrivals` clause as the key's job).
- **Status:** open.

### RD-29. TypeScript hands the selected environment mode to `verify` only when there is an input port

- **Requirements:** MOD-051 (the setup of each per-property verification: the verifier is set up
  with the harness environment places and the selected environment mode, and then passed,
  together with the synthetic net, through the configure hook).
- **Runtimes:** TypeScript.
- **Defect:** `SubnetDef.verify` registers the environment places and the selected mode only when
  the harness has an environment place (`typescript/src/core/subnet-def.ts:359-362`). For a subnet
  with no input or in-out port the configure hook receives a verifier on the verifier default
  `AlwaysAvailable` (`typescript/src/verification/smt-verifier.ts:149`), not on the selected
  mode, so a hook that registers an environment place itself runs under the wrong mode. Rust
  (`rust/libpetri-verification/src/harness.rs:465-468`) and Java
  (`java/src/main/java/org/libpetri/core/SubnetDef.java:369-371`) set the mode on every call, and
  Python rides on Rust.
- **Lean evidence:** `MOD_051_forbids_modeOnlyWithEnvs` in `MOD_051.lean`: the forwarder without
  its input port, verified under `Ignore` with a hook that registers `sut/IN`; the TypeScript
  shape (`mod051ModeOnlyWithEnvs`) proves `TerminatesAtSink` where line 4 requires `Violated`.
- **Status:** open.

### RD-30. The Python binding adapter resolves the given name before the correspondence

- **Requirements:** MOD-031 (an action's context operations resolve a declared place through the
  correspondence, and a binding adapter that resolves for its actions keeps the same order).
- **Runtimes:** Python.
- **Defect:** `require_output` and `resolve_lookup_key` first look the given name up in the
  allowed outputs or in the delivered input or read map, and fall back through `local_name_map`
  only when that fails (`rust/libpetri-py/src/action.rs:307-345`). When the given name is itself
  a place of the call's kind that the correspondence resolves to another place (a port `a` bound
  to the caller place `b`, and a port `b` bound to `c`), the call answers for the given place,
  not for the place the correspondence names. Java and TypeScript resolve first; the Rust native
  context hands the correspondence to native actions.
- **Lean evidence:** `MOD_031_ctx_mutant_literalFirst_killed` and `mod031ctx_collision` in
  `MOD_031.lean`: on the collision example the name-first lookup answers for the wrong place.
- **Status:** open.

### RD-31. Java and TypeScript resolve the timeout branch's places a second time

- **Requirements:** MOD-031 (the correspondence is applied once, to a declared place), IO-013 (the
  timeout outcome deposits the tokens of its child on the child's places).
- **Runtimes:** Java, TypeScript.
- **Defect:** the executor deposits the timeout branch through `outputToHarvest` and
  `forwardToHarvest` with the places the rewritten output specification names, which are already
  the actual places (`java/src/main/java/org/libpetri/runtime/ExecutorSupport.java:505`, `:514`,
  `produceTimeoutOutputRecursive`; `typescript/src/runtime/executor-support.ts:320`, `:328`,
  `produceTimeoutOutput`). Both methods resolve the place through the correspondence again
  (`java/src/main/java/org/libpetri/core/TransitionContext.java:404-428`;
  `typescript/src/core/transition-context.ts:262-283`). On a collision (port `a` bound to the
  caller place `b`, port `b` bound to `c`) the timeout token meant for `b` lands on `c`. Rust
  deposits the timeout branch on the places as given.
- **Lean evidence:** `mod031ctx_timeout_resolveTwice` in `MOD_031.lean`.
- **Status:** open.
