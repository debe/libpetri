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
| `libpetri/viewer` | Interactive DOT/SVG viewer, the canonical renderer |
| `libpetri/render-dom` | Thin compatibility wrapper over `libpetri/viewer` |
| `libpetri/doclet` | TypeDoc integration |

The model supports input, output, read, inhibitor, and reset arcs; immediate, deadline, delayed, window, and exact timing; AND/XOR/timeout routing; environment places; reusable subnets; place fusion; and ν-net identity correlation.

## Visualization

`libpetri/viewer` is the canonical renderer. It lays nodes out with ELK, routes edges orthogonally, and draws the result through Graphviz `nop2`, then adds pan/zoom, cluster collapse, subnet toggling, and filtering. Every first-party surface uses it: the debug UI, the TypeDoc plugin here, the Java javadoc taglet, and the Rust docgen all embed the same bundle, so a net looks the same whichever port documented it.

```typescript
import { dotExport } from 'libpetri/export';
import { mount } from 'libpetri/viewer';

const handle = await mount(dotExport(net), document.getElementById('diagram')!, {
  chrome: true,
});
handle.fit();
```

The viewer is browser-only and declares `@viz-js/viz`, `panzoom`, and `elkjs` as optional peer dependencies, so a headless runtime install does not pull in a rendering stack. Install all three wherever you mount it:

```bash
npm install @viz-js/viz panzoom elkjs
```

Without `elkjs` the default layout throws and names the missing peer; `mount(dot, el, { layout: 'graphviz' })` falls back to stock Graphviz layout, which is the one supported way to render without it.

Not every path through the package produces the same picture:

| Path | Layout | Edges |
|---|---|---|
| `mount()` from `libpetri/viewer` | ELK placement, ELK routes via `nop2` | orthogonal |
| `renderDotToContainer()` from `libpetri/render-dom` | delegates to `mount()` | orthogonal |
| the TypeDoc plugin | embeds the viewer, mounts client-side | orthogonal |
| `dotToSvg()` from `libpetri/doclet` | stock Graphviz `dot` | diagonal splines |
| `dotExport()` piped to your own `dot -Tsvg` | stock Graphviz `dot` | diagonal splines |

If a diagram renders with diagonal edges where you expected right angles, it went through one of the bottom two rows, or through a viewer bundle older than 2.10.5. Generated doc pages record which one drew them in `data-libpetri-viewer` on the diagram container.

### TypeDoc plugin

Register the plugin and declare the block tag it reads:

```json
{
  "plugin": ["libpetri/doclet"],
  "blockTags": ["@petrinet"]
}
```

An `@petrinet` tag on a symbol that builds or exposes a net renders that net as a diagram in the generated page, with the DOT source in a collapsible block underneath. The viewer bundle is inlined into the HTML, so the output is self-contained and works offline with no `dot` binary and no network access.

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
