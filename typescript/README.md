# libpetri for TypeScript

[![npm](https://img.shields.io/npm/v/libpetri)](https://www.npmjs.com/package/libpetri)
[![TypeScript](https://img.shields.io/badge/TypeScript-6-blue)](https://www.typescriptlang.org/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](https://github.com/debe/libpetri/blob/main/LICENSE)

The TypeScript 6 implementation of libpetri: typed Coloured Time Petri Nets for Promise-based applications, with modular composition, two execution backends, observability, DOT export, and formal verification.

See the [project README](https://github.com/debe/libpetri#why-a-petri-net) for the motivation and an order workflow using every arc type, concurrent actions, and timeout routing.

## Install

```bash
npm install libpetri
```

libpetri is ESM-only. The core runtime has no browser-only assumption; optional viewer and documentation entry points declare their own peer dependencies.

## Quick start

```typescript
import {
  BitmapNetExecutor, PetriNet, Transition,
  one, outPlace, place, tokenOf,
} from 'libpetri';

const input = place<string>('input');
const output = place<string>('output');

const uppercase = Transition.builder('uppercase')
  .inputs(one(input))
  .outputs(outPlace(output))
  .action(async (ctx) => {
    ctx.output(output, ctx.input(input).toUpperCase());
  })
  .build();

const net = PetriNet.builder('example').transition(uppercase).build();
const executor = new BitmapNetExecutor(
  net,
  new Map([[input, [tokenOf('hello')]]]),
);

const result = await executor.run();
console.log(result.peekFirst(output)?.value); // HELLO
```

## Execution and concurrency

`BitmapNetExecutor` is the reference implementation. `PrecompiledNetExecutor` compiles the same net into flat arrays, opcode streams, and priority-partitioned ready queues for production hot paths.

The orchestrator owns the marking and invokes ready actions without awaiting earlier actions first. Promise continuations therefore overlap naturally, while marking updates remain serialized. CPU-heavy synchronous code still blocks the JavaScript event loop; move it to a worker or external service.

Use places and transitions for coordination rather than hiding concurrency inside `Promise.all`: the net can then visualize, trace, replay, and verify the fan-out and join.

## Package entry points

| Import | Purpose |
|---|---|
| `libpetri` | Core model, runtime, events, and composition |
| `libpetri/export` | DOT mapping and rendering |
| `libpetri/verification` | Structural analysis, state classes, and Z3-backed SMT verification |
| `libpetri/debug` | Debug protocol and session archives |
| `libpetri/viewer` | Interactive DOT/SVG viewer |
| `libpetri/doclet` | TypeDoc integration |

The model supports input, output, read, inhibitor, and reset arcs; immediate, deadline, delayed, window, and exact timing; AND/XOR/timeout routing; environment places; reusable subnets; place fusion; and ν-net identity correlation.

## Build and test

```bash
npm install
npm run build
npm run check
npm test
```

## Project links

- [Language-agnostic specification](https://github.com/debe/libpetri/blob/main/spec/00-index.md)
- [Lean soundness and backend-refinement proofs](https://github.com/debe/libpetri/blob/main/lean/README.md)
- [Changelog](https://github.com/debe/libpetri/blob/main/CHANGELOG.md)
- [Apache License 2.0](https://github.com/debe/libpetri/blob/main/LICENSE)
