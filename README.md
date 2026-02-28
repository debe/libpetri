# libpetri

**Executable Coloured Time Petri Nets with formal verification** — model concurrent workflows with typed data, real-time constraints, and mathematically proven safety properties.

| Implementation | Language | Runtime | Status |
|---|---|---|---|
| [**libpetri-java**](java/) | Java 25 | Virtual threads | Production |
| [**libpetri-ts**](typescript/) | TypeScript 5.7 | Promises / event loop | In development |

> Rust implementation planned — see [`spec/`](spec/) for the language-agnostic contract all implementations follow.

[Specification](spec/00-index.md)

---

## Why libpetri

- **Executable formal models** — Petri nets that actually run: typed tokens flow through places, transitions fire with real-time deadlines, and async actions execute concurrently. Not a simulator — a production workflow engine.
- **Two implementations, one spec** — Java and TypeScript share [145 language-agnostic requirements](spec/00-index.md) covering every arc type, timing variant, and execution phase. Same behavior, verified independently.
- **Research-backed** — Grounded in the theory of *Coloured Time Petri Nets* applied to agentic systems. The Order Processing Pipeline below demonstrates every arc type, timing mode, and place type in one deadlock-free net.

---

## Core Capabilities

| Capability | Details |
|---|---|
| **Arc types** | Input, Output, Inhibitor, Read (non-consuming), Reset (clear all) |
| **Input cardinality** | `one`, `exactly(n)`, `all` (drain), `atLeast(n)` — with optional guard predicates |
| **Output routing** | `place` (single), `and` (fork), `xor` (choice), `timeout`, `forwardInput` |
| **Timing** | Immediate, Deadline, Delayed, Window, Exact — with urgent deadline enforcement |
| **Executor** | Bitmap-based O(W) enablement, dirty-set optimization, priority + FIFO scheduling |
| **Concurrency** | Single-threaded orchestrator, concurrent async actions (virtual threads / promises) |
| **Environment places** | External event injection for long-running, event-driven workflows |
| **Events** | 13 event types, pluggable stores (in-memory, noop, logging, debug) |
| **Formal verification** | SMT/IC3 via Z3 — deadlock freedom, mutual exclusion, place bounds, unreachability |
| **Structural analysis** | P-invariants (Farkas), siphon/trap pre-checks, XOR branch analysis |
| **State class graph** | Berthomieu-Diaz algorithm for timed reachability (Java) |
| **Export** | DOT/Graphviz (primary), Mermaid (deprecated) |

---

## Quick Start

### Java

```java
import org.libpetri.core.*;
import org.libpetri.runtime.NetExecutor;
import java.time.Duration;
import java.util.*;
import java.util.concurrent.CompletableFuture;

var request  = Place.of("Request", String.class);
var response = Place.of("Response", String.class);

var process = Transition.builder("Process")
    .inputs(In.one(request))
    .outputs(Out.place(response))
    .timing(Timing.deadline(Duration.ofSeconds(5)))
    .action(ctx -> {
        String req = ctx.input(request);
        ctx.output(response, "Processed: " + req);
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
    // → "Processed: hello"
}
```

```bash
cd java && ./mvnw verify
```

### TypeScript

```typescript
import {
  place, tokenOf, one, outPlace, deadline,
  Transition, PetriNet, BitmapNetExecutor
} from 'libpetri';

const request  = place<string>('Request');
const response = place<string>('Response');

const process = Transition.builder('Process')
  .inputs(one(request))
  .outputs(outPlace(response))
  .timing(deadline(5000))
  .action(async (ctx) => {
    const req = ctx.input(request);
    ctx.output(response, `Processed: ${req}`);
  })
  .build();

const net = PetriNet.builder('Example')
  .transitions(process)
  .build();

const executor = new BitmapNetExecutor(net, new Map([
  [request, [tokenOf('hello')]],
]));
const result = await executor.run();
console.log(result.peekFirst(response)?.value);
// → "Processed: hello"
```

```bash
cd typescript && npm install && npm test
```

---

## Showcase: Order Processing Pipeline

An order fulfillment workflow (8 transitions, 12 places) that demonstrates **every** arc type, place type, and timing mode — with no deadlocks. Rendered using libpetri's DOT exporter.

<p align="center">
  <img src="docs/showcase-order-pipeline.svg" alt="Order Processing Pipeline — Showcase Petri Net" width="600">
</p>

**Patterns at work:**

| Pattern | Where | How |
|---|---|---|
| **AND-fork** | Receive | Splits Order into Validating + InStock + Active in one firing |
| **AND-join** | Approve | Waits for both PaymentOk and InStock before proceeding |
| **XOR routing** | Authorize, RetryPayment | Produces to exactly one of PaymentOk / PaymentFailed |
| **Inhibitor arc** | RetryPayment, Ship, Cancel, Monitor | Blocks when a place has tokens (e.g., no retry after Overdue) |
| **Read arc** | Ship, Monitor | Tests Active without consuming — persists across the workflow |
| **Reset arc** | Reject, Cancel | Clears all tokens from places (e.g., Cancel resets 5 places) |
| **Environment place** | CancelRequest | External cancellation signal injected at runtime |
| **Priority** | Receive (prio=10) | Fires before other enabled transitions |
| **All 5 timing modes** | See below | Immediate, Window, Delayed, Deadline, Exact |

**Timing modes demonstrated:**

| Transition | Timing | Meaning |
|---|---|---|
| Receive, Ship, Reject, Cancel | `immediate()` | Fire as soon as enabled |
| Authorize | `window(200ms, 5s)` | Fire between 200ms and 5s |
| RetryPayment | `delayed(1s)` | Wait at least 1s before retry |
| Approve | `deadline(2s)` | Must fire within 2s |
| Monitor | `exact(10s)` | Fires at precisely 10s (urgency) |

<details>
<summary><strong>Java code (from PaperNetworks.java)</strong></summary>

```java
var order         = Place.of("Order", String.class);
var active        = Place.of("Active", String.class);
var validating    = Place.of("Validating", String.class);
var inStock       = Place.of("InStock", String.class);
var paymentOk     = Place.of("PaymentOk", String.class);
var paymentFailed = Place.of("PaymentFailed", String.class);
var ready         = Place.of("Ready", String.class);
var shipped       = Place.of("Shipped", String.class);
var rejected      = Place.of("Rejected", String.class);
var cancelled     = Place.of("Cancelled", String.class);
var overdue       = Place.of("Overdue", String.class);
var cancelRequest = Place.of("CancelRequest", String.class); // EnvironmentPlace at runtime

var receive = Transition.builder("Receive")
    .inputs(In.one(order))
    .outputs(Out.and(validating, inStock, active))    // AND-fork
    .timing(Timing.immediate())
    .priority(10)
    .build();

var authorize = Transition.builder("Authorize")
    .inputs(In.one(validating))
    .outputs(Out.xor(paymentOk, paymentFailed))       // XOR choice
    .timing(Timing.window(Duration.ofMillis(200), Duration.ofSeconds(5)))
    .build();

var retryPayment = Transition.builder("RetryPayment")
    .inputs(In.one(paymentFailed))
    .inhibitor(overdue)                                // blocked after timeout
    .outputs(Out.xor(paymentOk, paymentFailed))
    .timing(Timing.delayed(Duration.ofSeconds(1)))
    .build();

var approve = Transition.builder("Approve")
    .inputs(In.one(paymentOk), In.one(inStock))       // AND-join
    .outputs(Out.place(ready))
    .timing(Timing.deadline(Duration.ofSeconds(2)))
    .build();

var ship = Transition.builder("Ship")
    .inputs(In.one(ready))
    .read(active)                                      // read arc
    .inhibitor(cancelled)
    .outputs(Out.place(shipped))
    .timing(Timing.immediate())
    .build();

var reject = Transition.builder("Reject")
    .inputs(In.one(paymentFailed), In.one(overdue))
    .reset(inStock)                                    // reset arc
    .outputs(Out.place(rejected))
    .timing(Timing.immediate())
    .build();

var cancel = Transition.builder("Cancel")
    .inputs(In.one(cancelRequest))                     // environment place
    .inhibitors(shipped, rejected)
    .resets(validating, paymentFailed, inStock, paymentOk, ready)  // multiple resets
    .outputs(Out.place(cancelled))
    .timing(Timing.immediate())
    .build();

var monitor = Transition.builder("Monitor")
    .read(active)
    .inhibitors(shipped, rejected, cancelled, overdue)
    .outputs(Out.place(overdue))
    .timing(Timing.exact(Duration.ofSeconds(10)))      // exact timing (urgency)
    .build();

return PetriNet.builder("OrderProcessingPipeline")
    .transitions(receive, authorize, retryPayment, approve, ship, reject, cancel, monitor)
    .build();
```

</details>

---

## API at a Glance

<details>
<summary><strong>Arc types</strong></summary>

| Arc | Semantics | Java | TypeScript |
|---|---|---|---|
| **Input** | Consume token(s) from place | `In.one(p)` | `one(p)` |
| **Output** | Deposit token into place | `Out.place(p)` | `outPlace(p)` |
| **Inhibitor** | Block when place has tokens | `.inhibitor(p)` | `.inhibitor(p)` |
| **Read** | Test without consuming | `.read(p)` | `.read(p)` |
| **Reset** | Clear all tokens from place | `.reset(p)` | `.reset(p)` |

</details>

<details>
<summary><strong>Input cardinality</strong></summary>

| Cardinality | Semantics | Java | TypeScript |
|---|---|---|---|
| **One** | Consume exactly 1 token | `In.one(p)` | `one(p)` |
| **Exactly(n)** | Consume exactly n tokens | `In.exactly(n, p)` | `exactly(n, p)` |
| **All** | Drain all tokens (at least 1) | `In.all(p)` | `all(p)` |
| **AtLeast(n)** | Consume all, require >= n | `In.atLeast(n, p)` | `atLeast(n, p)` |

All input specs support optional guard predicates to filter tokens.

</details>

<details>
<summary><strong>Output routing</strong></summary>

| Routing | Semantics | Java | TypeScript |
|---|---|---|---|
| **Place** | Deposit to a single place | `Out.place(p)` | `outPlace(p)` |
| **And** | Fork to all children | `Out.and(p1, p2)` | `and(outPlace(p1), outPlace(p2))` |
| **Xor** | Route to exactly one child | `Out.xor(p1, p2)` | `xor(outPlace(p1), outPlace(p2))` |
| **Timeout** | Fallback output after delay | `Out.timeout(Duration, p)` | `timeout(ms, outPlace(p))` |
| **ForwardInput** | Pass consumed token through | `Out.forwardInput(from, to)` | `forwardInput(from, to)` |

</details>

<details>
<summary><strong>Timing variants</strong></summary>

| Variant | Interval | Behavior | Java | TypeScript |
|---|---|---|---|---|
| **Immediate** | [0, inf) | Fire as soon as enabled, no deadline | `Timing.immediate()` | `immediate()` |
| **Deadline** | [0, d] | Fire anytime before deadline | `Timing.deadline(Duration)` | `deadline(ms)` |
| **Delayed** | [d, +inf) | Wait at least d, then fire | `Timing.delayed(Duration)` | `delayed(ms)` |
| **Window** | [a, b] | Fire between a and b | `Timing.window(Duration, Duration)` | `window(a, b)` |
| **Exact** | [t, t] | Fire at precisely t | `Timing.exact(Duration)` | `exact(ms)` |

Transitions are force-disabled past their deadline (urgent semantics).

</details>

---

## Formal Verification

Both implementations include SMT-based verification via Z3 using the IC3/PDR algorithm, with structural pre-checks for fast results.

| Property | Description |
|---|---|
| **Deadlock freedom** | No reachable state where all transitions are disabled |
| **Mutual exclusion** | Two places never hold tokens simultaneously |
| **Place bound** | A place never exceeds *k* tokens |
| **Unreachability** | A set of places never all hold tokens simultaneously |

**Pipeline:** structural siphon/trap analysis → P-invariant computation (Farkas) → XOR branch analysis → SMT encoding → IC3/PDR solving

### Java

```java
import org.libpetri.smt.*;

var result = SmtVerifier.forNet(net)
    .initialMarking(m -> m.tokens(pending, 1))
    .property(SmtProperty.deadlockFree())
    .timeout(Duration.ofSeconds(60))
    .verify();

System.out.println(result.verdict());  // Proven, Violated, or Unknown
```

### TypeScript

```typescript
import { SmtVerifier, deadlockFree } from 'libpetri/verification';

const result = await SmtVerifier.forNet(net)
  .initialMarking(m => m.tokens(pending, 1))
  .property(deadlockFree())
  .timeout(30_000)
  .verify();

console.log(result.verdict.type);  // 'proven' | 'violated' | 'unknown'
```

---

## Architecture

### Execution Loop

The executor runs a single-threaded orchestration loop with five phases per cycle:

1. **Process completions** — collect outputs from finished async actions
2. **Process events** — inject tokens from environment places
3. **Update enablement** — re-evaluate only dirty transitions via bitmap masks
4. **Fire transitions** — select by priority, then FIFO by enablement time
5. **Await work** — sleep until an action completes, a timer fires, or an event arrives

### Module Structure

| Module | Java | TypeScript |
|---|---|---|
| Core model | `org.libpetri.core` | `libpetri` (core exports) |
| Runtime | `org.libpetri.runtime` | `libpetri` (runtime exports) |
| Events | `org.libpetri.event` | `libpetri` (event exports) |
| Verification | `org.libpetri.smt` | `libpetri/verification` |
| Export | `org.libpetri.export` | `libpetri/export` |

Both share the same architecture: immutable net definitions, builder-pattern construction, bitmap-based enablement with dirty-set optimization, and a single-threaded orchestrator dispatching async actions to a separate task pool.

---

## Specification

The [`spec/`](spec/) directory defines the complete engine contract — **145 requirements** across 10 files.

| File | Prefix | Scope | Count |
|---|---|---|---|
| [01-core-model.md](spec/01-core-model.md) | CORE | Places, tokens, transitions, arcs, net construction | 33 |
| [02-input-output-specs.md](spec/02-input-output-specs.md) | IO | Input cardinality, output routing, validation | 15 |
| [03-timing.md](spec/03-timing.md) | TIME | Firing intervals, clock semantics, deadlines | 11 |
| [04-execution-model.md](spec/04-execution-model.md) | EXEC | Orchestrator loop, scheduling, quiescence | 15 |
| [05-concurrency.md](spec/05-concurrency.md) | CONC | Bitmap executor, async actions, wake-up | 11 |
| [06-environment-places.md](spec/06-environment-places.md) | ENV | External event injection, long-running mode | 9 |
| [07-verification.md](spec/07-verification.md) | VER | SMT/IC3, state class graph, structural analysis | 10 |
| [08-events-observability.md](spec/08-events-observability.md) | EVT | Event types, event store, log capture | 20 |
| [09-export.md](spec/09-export.md) | EXP | Graph export, formal interchange | 10 |
| [10-performance.md](spec/10-performance.md) | PERF | Scaling, benchmarks, memory efficiency | 11 |
| **Total** | | | **145** |

**Priority:** 110 MUST · 29 SHOULD · 6 MAY

See [spec/00-index.md](spec/00-index.md) for the full cross-reference index and coverage matrix.

---

## Build & Test

### Java

```bash
cd java
./mvnw verify                                          # Full build + tests
./mvnw test                                            # Run all tests
./mvnw test -Dtest="org.libpetri.core.PetriNetTest"    # Single test class
./mvnw test -Dtest="*BitmapNetExecutor*"               # Wildcard match
./mvnw test-compile exec:exec -Pjmh                    # Run JMH benchmarks
./mvnw javadoc:javadoc                                 # Generate Javadocs
```

Java 25 with preview features enabled. Uses Maven 3.9.x via wrapper.

### TypeScript

```bash
cd typescript
npm install              # Install dependencies
npm run build            # Build with tsup
npm run check            # Type-check (tsc --noEmit)
npm test                 # Run vitest
npm run test:watch       # Watch mode
npm test -- core         # Run tests matching "core"
```

TypeScript 5.7, ESM-only, strict mode. Built with tsup, tested with vitest.

---

## License

[Apache License 2.0](LICENSE)

---

[Specification](spec/00-index.md)
