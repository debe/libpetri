# libpetri

TypeScript implementation of a **Timed Coloured Petri Net** (TCPN) engine with bitmap-based execution, formal verification via Z3, and Mermaid visualization.

## Architecture

```
src/
├── core/          # Net definition: places, transitions, arcs, timing, output specs
├── runtime/       # Async bitmap-based executor, marking, compiled net
├── event/         # Event store and net event types (discriminated union)
├── export/        # Mermaid flowchart exporter
└── verification/  # SMT-based property verification (Z3)
```

### Core (`src/core/`)

Immutable net definitions with typed, colored tokens.

| Type | Description |
|------|-------------|
| `Place<T>` | Typed token container (phantom type for compile-time safety) |
| `EnvironmentPlace<T>` | External event injection point |
| `Transition` | Arc specs, timing, priority, guards, action binding |
| `PetriNet` | Immutable net definition; `bindActions()` separates structure from runtime behavior |
| `Out` | Discriminated union for output specs: `and`, `xor`, `place`, `timeout`, `forward-input` |
| `In` | Input arc specs with cardinality: `one`, `exactly`, `all`, `at-least` |
| `Timing` | TPN firing intervals: `immediate`, `deadline`, `delayed`, `window`, `exact` |
| `TransitionAction` | `(ctx: TransitionContext) => Promise<void>` — async action bound to a transition |

### Runtime (`src/runtime/`)

Async single-threaded executor using bitmap-based enablement tracking.

| Type | Description |
|------|-------------|
| `BitmapNetExecutor` | Main executor — dirty-set tracking, priority scheduling, deadline enforcement |
| `CompiledNet` | Precomputed bitmap masks and reverse indices for O(W) enablement checks |
| `Marking` | Mutable FIFO token state per place |

Key performance features:
- `Uint32Array` bitmaps for place marking and transition dirty sets
- Kernighan's bit-trick for dirty set iteration
- Pre-allocated buffers to reduce GC pressure
- Precomputed reverse index (place → affected transitions)

### Event (`src/event/`)

Observable execution events as a discriminated union (`NetEvent`).

Event types: `execution-started`, `execution-completed`, `transition-enabled`, `transition-started`, `transition-completed`, `transition-failed`, `transition-timed-out`, `action-timed-out`, `token-added`, `token-removed`, `log-message`, `marking-snapshot`.

`InMemoryEventStore` captures events; `noopEventStore()` is a zero-cost singleton for production.

### Export (`src/export/`)

`mermaidExport(net, config)` generates Mermaid flowchart syntax with ELK layout, including arc types (inhibitor, read, reset), timing annotations, and priority labels.

### Verification (`src/verification/`)

SMT-based formal verification using Z3. Encodes the Petri net as an integer linear program and checks reachability properties.

Supported properties:
- **Deadlock freedom** — no reachable state where all transitions are disabled
- **Mutual exclusion** — two places never both hold tokens simultaneously
- **Place bounds** — token count in a place never exceeds a limit
- **Unreachability** — a marking is never reachable

Also computes **P-invariants** (Farkas variant) and supports IC3/PDR-style incremental verification.

## Quick Start

```typescript
import { place, PetriNet, Transition, one, outPlace, tokenOf, BitmapNetExecutor } from 'libpetri';

// Define places
const input = place<string>('input');
const output = place<string>('output');

// Define transition
const process = Transition.builder('process')
  .inputs(one(input))
  .outputs(outPlace(output))
  .action(async (ctx) => {
    const value = ctx.input(input);
    ctx.output(output, value.toUpperCase());
  })
  .build();

// Build net
const net = PetriNet.builder('Example').transition(process).build();

// Execute
const executor = new BitmapNetExecutor(
  net,
  new Map([[input, [tokenOf('hello')]]]),
);
const marking = await executor.run();
console.log(marking.peekTokens(output)); // [Token { value: 'HELLO' }]
```

## Verification Example

```typescript
import { SmtVerifier, deadlockFree } from 'libpetri/verification';

const result = await SmtVerifier.forNet(net)
  .initialMarking(m => m.tokens(input, 1))
  .property(deadlockFree())
  .verify();

console.log(result.verdict); // { type: 'proven', method: 'structural' }
```

## Build & Test

```bash
npm run build    # Build with tsup
npm run check    # Type-check with tsc --noEmit
npm test         # Run tests with vitest
```
