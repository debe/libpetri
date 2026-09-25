# libpetri for Java

[![Maven Central](https://img.shields.io/maven-central/v/org.libpetri/libpetri)](https://central.sonatype.com/artifact/org.libpetri/libpetri)
[![Java](https://img.shields.io/badge/Java-25-orange)](pom.xml)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](../LICENSE)

The Java 25 implementation of libpetri: typed Coloured Time Petri Nets, asynchronous transition actions, modular composition, observability, DOT export, and formal verification.

For the motivation and a workflow using every arc type, concurrency, and timeout routing, start with the [project README](../README.md#why-a-petri-net).

## Install

```xml
<dependency>
  <groupId>org.libpetri</groupId>
  <artifactId>libpetri</artifactId>
  <version>7.0.0</version>
</dependency>
```

Java 25 is required. The repository includes a Maven wrapper, so a system Maven installation is optional for source builds.

## Quick start

```java
import org.libpetri.core.*;
import org.libpetri.runtime.BitmapNetExecutor;
import java.util.*;
import java.util.concurrent.CompletableFuture;

var input = Place.of("input", String.class);
var output = Place.of("output", String.class);

var uppercase = Transition.builder("uppercase")
    .inputs(Arc.In.one(input))
    .outputs(Arc.Out.place(output))
    .action(ctx -> {
        ctx.output(output, ctx.input(input).toUpperCase());
        return CompletableFuture.completedFuture(null);
    })
    .build();

var net = PetriNet.builder("example").transitions(uppercase).build();

try (var executor = BitmapNetExecutor.builder(
        net, Map.of(input, List.of(Token.of("hello")))).build()) {
    var result = executor.run();
    System.out.println(result.peekFirst(output).value()); // HELLO
}
```

Places are typed, transitions are immutable, and output declarations are checked against what the action produces.

## Execution and concurrency

`BitmapNetExecutor` is the readable reference backend. `PrecompiledNetExecutor` is the production hot path; it compiles the same net into flat arrays, opcode streams, ring buffers, and priority queues.

Java actions are invoked **inline on the orchestrator thread**. libpetri does not dispatch them to an executor. Concurrency begins when an action promptly returns a `CompletionStage` driven elsewhere; blocking inside the action blocks the whole net. The executor passed to `run(Duration)` hosts the orchestrator loop, not transition work.

One orchestrator owns the marking. Completed stages, external events, and timers wake it so token movement remains deterministic even when actions overlap.

## Terminal places

```java
var net = PetriNet.builder("workflow")
    .transitions(/* ... */)
    .terminal(result)          // the run is over once `result` holds a token
    .build();

var marking = executor.run();
executor.terminationReason(); // TERMINAL — a completed reason, like QUIESCENT
```

A net that never quiesces, such as one with environment places, can say "done" in the model. The executor checks the initial marking and every token it deposits. Once a terminal place is marked, no transition fires afterwards, not even one already enabled later in the same pass. Actions still in flight are abandoned and their results discarded, and queued external events are refused. A terminal place must not be an input or read by any transition, and a subnet body may not declare one. The verifiers apply the declaration themselves: you do not restate it as sink places.

## Checkpoint and resume

```java
var snap = executor.snapshot();                 // does not stop the net
if (snap.isRestorePoint()) save(snap.marking()); // Map<String, List<Token<?>>>

var resumed = BitmapNetExecutor.builder(net, Map.of()).restore(saved).build();
```

A snapshot maps place names to tokens, in a canonical order, and carries `createdAt` through untouched. Persist one only when `isRestorePoint()` is true: `actionInFlight` is set while an action is running or an injected event has not reached its place yet, and either way a token is in no place. While the orchestrator is parked in its wait, built-in or a host's, a `marking()` or `snapshot()` from another thread is answered at once from the current state, without waking it. A `snapshot()` from another thread that the orchestrator cannot serve within two seconds — it is stuck in a blocking inline action — comes back flagged in flight, never as a restore point. Timing clocks restart on resume, so a `deadline` gets a fresh full budget. Minted ν-names are `<transition>#<scope>:<n>` with a random scope per executor; pin `executionScope(...)` on the builder when a replay must reproduce them, fresh per run segment.

Because `Place` equality is structural, `Marking.fromSnapshot(snapshot, net.places())` takes the net's places, and a net declaring two places with one name cannot be snapshotted or restored.

## SMT verification needs a `z3` executable

The verifier (`org.libpetri.smt.SmtVerifier`) does not bundle a solver. It runs the `z3` executable found on `PATH` (or named by `LIBPETRI_Z3`), version 4.8.0 or newer, one process per query; `SmtVerifier.z3Available()` tells you whether one resolves, and without it every verification returns `Unknown` with a reason naming the command. Set `LIBPETRI_SMT_DUMP` to a directory to keep every SMT-LIB2 script and solver reply. The timeout is per solver invocation.

Not every query reaches the solver. On an untimed net with no ν-joins and no environment places, `SmtVerifier` first enumerates the state-class graph up to `enumerationMaxClasses(int)` (default 50 000, `0` disables) and reads the verdict off it — exact, and far cheaper than a fixpoint search on a long pipeline ([VER-017]). A reachability-safety property is then tried against the linear state-equation bound (`linearBound(boolean)`, on by default, [VER-015]) before IC3/PDR runs.

To ask many questions of one net, pass the same `StateSpaceCache` to each verifier with `stateSpaceCache(cache)`. The enumeration graph is then built once per net instance and initial marking, and a known truncation skips the attempt. Verdicts, witnesses and routes do not change.

Options that change what the encoders see:

| Method | Default | What it does |
|---|---|---|
| `sinkPlaces(Place…)` | none | Places where a token may always rest, for `deadlockFree()` / `terminatesAtSink()` |
| `sinkPlacesWhen(marker, Place…)` | none | Places where a token may rest **while `marker` is marked** — a halt or pause terminal ([VER-014]) |
| `linearBound(boolean)` | `true` | The structural `y·M ≤ y·M0` pre-proof for reachability-safety properties ([VER-015]) |
| `stateEquation(boolean)` | `false` | Carries the marking equation over firing counters into the flat encoding ([VER-016]) |
| `semiflowInvariants(boolean)` / `semiflowInvariants(SemiflowMode)` | `OFF` | Unions the gate-validated P-semiflows into the encoders' invariant list; `AUTO` does it exactly when the null-space basis lost a law to the H1 guard ([VER-007]) |
| `enumerationMaxClasses(int)` | `50_000` | Class budget for the enumeration route; `0` sends every query to the SMT pipeline ([VER-017]) |

`SmtVerificationResult.route()` names which route decided the verdict. Read it before concluding anything from an **empty** `invariants()`: off the `SMT` route that means "not computed", never "the net has none" ([VER-003]).

> **Breaking:** `route` is a new *record component* of `SmtVerificationResult`, inserted after `verdict`. Reading the result is unaffected — every existing accessor keeps its name and type — but the canonical constructor gained a parameter, so downstream code that calls `new SmtVerificationResult(…)` (a hand-built test double, say) or deconstructs the record in a pattern (`case SmtVerificationResult(var verdict, var report, …)`) must be updated. A Java record has no way to add a component without this; the field is on the result rather than only in the report because a consumer reading fields cannot otherwise tell an empty `invariants()` apart from a net with none.

## Main packages

| Package | Purpose |
|---|---|
| `org.libpetri.core` | Places, tokens, transitions, timing, arcs, and subnet composition |
| `org.libpetri.runtime` | Bitmap and precompiled executors, markings, and external events |
| `org.libpetri.event` | Execution events and event stores |
| `org.libpetri.analysis` / `org.libpetri.smt` | Structural, timed, and SMT verification |
| `org.libpetri.export` | DOT/Graphviz export |
| `org.libpetri.debug` | Debug protocol, sessions, and archives |

The generated Javadocs include `@PetriNet` and `@Subnet` diagrams through the bundled doclet.

## Build and test

```bash
./mvnw verify
./mvnw test
./mvnw javadoc:javadoc
./mvnw test-compile exec:exec -Pjmh
```

## Project links

- [Language-agnostic specification](../spec/00-index.md)
- [Lean soundness and backend-refinement proofs](../lean/README.md)
- [Changelog](../CHANGELOG.md)
- [Apache License 2.0](../LICENSE)
