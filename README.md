# libpetri

A high-performance **Timed Coloured Petri Net** (TCPN) engine with formal verification, available in multiple languages.

## What is a Timed Coloured Petri Net?

A Petri net extended with **typed tokens** (data flows through the workflow), **colored places** (type-safe containers), and **firing intervals** (transitions must fire within time bounds). This combination enables both executable workflow orchestration and formal timing analysis.

## Implementations

| Language | Directory | Runtime | Status |
|----------|-----------|---------|--------|
| Java 25 | [`java/`](java/) | Virtual threads | Production |
| TypeScript | [`typescript/`](typescript/) | Promises / event loop | Production |
| Rust | _planned_ | Tokio async | v0.1.0 |

## Features

- **5 arc types** — Input, Output, Inhibitor, Read, Reset
- **5 timing variants** — Immediate, Deadline, Delayed, Window, Exact
- **Bitmap-based O(W) enablement checking** — constant-time per word
- **Priority-based scheduling** with conflict resolution
- **SMT formal verification** via Z3 (IC3/PDR)
- **State class graph analysis** (Berthomieu-Diaz algorithm)
- **Mermaid diagram export** for visualization
- **Live debug UI** with event replay and checkpoint navigation

## Specification

The [`spec/`](spec/) directory contains **145 language-agnostic requirements** covering the complete engine contract. All implementations conform to the same spec.

See [spec/00-index.md](spec/00-index.md) for the full index and coverage matrix.

## Quick Start

### Java

```java
var request = Place.of("Request", String.class);
var response = Place.of("Response", String.class);

var process = Transition.builder("Process")
    .input(request)
    .output(response)
    .deadline(5000)
    .action((in, out) -> {
        String req = in.value(request);
        out.add(response, "Processed: " + req);
        return CompletableFuture.completedFuture(null);
    })
    .build();

var net = PetriNet.builder("Example")
    .transitions(process)
    .build();

try (var executor = NetExecutor.create(net, Map.of(
        request, List.of(Token.of("hello"))))) {
    Marking result = executor.run();
    System.out.println(result.peekFirst(response).value());
}
```

```bash
cd java
gradle wrapper
./gradlew test
```

### TypeScript

```typescript
import { Place, Transition, PetriNet, BitmapNetExecutor, Token } from 'libpetri';

const request = Place.of<string>('Request');
const response = Place.of<string>('Response');

const process = Transition.builder('Process')
  .input(request)
  .output(response)
  .deadline(5000)
  .action(async (ctx) => {
    const req = ctx.input(request);
    ctx.output(response, `Processed: ${req}`);
  })
  .build();

const net = PetriNet.builder('Example')
  .transitions(process)
  .build();

const executor = new BitmapNetExecutor(net, new Map([
  [request, [Token.of('hello')]]
]));
const result = await executor.run();
```

```bash
cd typescript
npm install
npm test
```

## License

[Apache License 2.0](LICENSE)

## Website

[libpetri.org](https://libpetri.org)
