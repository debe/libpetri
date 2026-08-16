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
  <version>2.14.0</version>
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
