# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

libpetri is a multi-language **Coloured Time Petri Net** (CTPN) engine with formal verification. Four implementations conform to one language-agnostic specification (`spec/`, **208 active requirements across 13 files** — `spec/00-index.md` is the canonical count):

| Implementation | Language | Runtime | Status |
|---|---|---|---|
| `java/` | Java 25 | `CompletionStage` (actions invoked inline; see note) | Production |
| `typescript/` | TypeScript 6.0 | Promises / event loop | Production |
| `rust/` | Rust 2024 | Tokio async tasks | Production |
| `python/` | Python ≥3.11 | Tokio async via PyO3 | Beta |

Java, TypeScript, and Rust are verified independently against the spec; **Python is PyO3 bindings on the Rust runtime** (it rides on Rust, not a separate implementation).

## Build & Test Commands

### Java (`java/`)

```bash
cd java
./mvnw verify                                  # Full build + tests
./mvnw test                                    # Run all tests
./mvnw test -Dtest="org.libpetri.core.PetriNetTest"       # Single test class
./mvnw test -Dtest="*BitmapNetExecutor*"                   # Wildcard match
./mvnw test-compile exec:exec -Pjmh           # Run JMH benchmarks
./mvnw javadoc:javadoc                         # Generate documentation (uses custom PetriNetTaglet)
```

Java 25 (no preview features — all used features are finalized). Uses Maven 3.9.x via wrapper.

### TypeScript (`typescript/`)

```bash
cd typescript
npm install                    # Install dependencies
npm run build                  # Build with tsup
npm run check                  # Type-check (tsc --noEmit)
npm test                       # Run vitest
npm run test:watch             # Watch mode
npm test -- core               # Run tests matching "core"
```

TypeScript 6.0, ESM-only, strict mode. Built with tsup (multi-entry: `index`, `export`, `verification`, `debug`, `doclet`), tested with vitest. JaCoCo code coverage auto-generated in Java (`target/site/jacoco/`).

### Rust (`rust/`)

```bash
cd rust
cargo build --workspace --exclude libpetri-py --all-features   # build (libpetri-py needs Python-extension linkage)
cargo test  --workspace --exclude libpetri-py --all-features   # THE real CI gate
cargo test -p libpetri-runtime                                  # single crate
cargo test -p libpetri-runtime precompiled                      # filter tests by name
cargo bench                                                     # Criterion benchmarks
```

Rust 2024 edition, rustc ≥1.88. Cargo workspace of 10 crates (`libpetri-core`, `-event`, `-runtime`, `-export`, `-verification`, `-debug`, `-docgen`, `libpetri` umbrella, `libpetri-py`, `benches`). **NOT fmt/clippy-gated** — match the existing hand-style; CI runs neither. Verification shells out to the **`z3` binary** via SMT-LIB2 text (the `z3` cargo feature is an empty compile-gate, *not* the z3/z3-sys crate).

### Python (`python/`)

```bash
cd python
pip install -e '.[dev]'        # maturin, pytest, pytest-asyncio, pytest-benchmark
maturin develop                # build the Rust extension (libpetri._libpetri) into the venv
maturin develop --release      # optimized (LTO) build — slower compile
pytest                         # run tests (asyncio_mode=auto)
pytest tests/test_executor.py  # single file
pytest -k precompiled          # filter by name
```

Python ≥3.11. The wheel is built by maturin from `rust/libpetri-py` (PyO3); version is decoupled from the Rust workspace version. Actions run on Tokio threads with **no running asyncio loop** — use async-first entry points (`start_async`/`ainvoke`/`astream`); `asyncio.gather`/`create_task` raise at construction. Subscriptions are batched/filtered Rust-side (no per-event Python callbacks).

## Architecture

All four implementations share the same architecture, mirrored across languages (Python via the Rust runtime).

### Core Model (`src/core/`)

- **Place\<T\>** — Typed, named token container. Identity by name. `EnvironmentPlace<T>` is a subtype for external event injection.
- **Token\<T\>** — Immutable value + timestamp.
- **Transition** — Consumes/produces tokens via arcs. Has optional timing constraints and priority. Actions are async (`CompletableFuture<Void>` in Java, `Promise<void>` in TypeScript).
- **Arc types** — Input (consume), Output (produce), Inhibitor (block when present), Read (test without consuming), Reset (clear all).
- **Timing** — `immediate`, `deadline(ms)`, `delayed(ms)`, `window(early, late)`, `exact(ms)`. Urgent semantics: transitions forced-disabled past deadline.
- **PetriNet** — Immutable net definition built via builder pattern. Transitions implicitly declare places through their arcs.

### Runtime (`src/runtime/`)

- **BitmapNetExecutor** — The **reference executor**: clear, canonical firing semantics. Single-threaded orchestrator with concurrent async actions.
  - Bitmap-based enablement: O(W) checks where W = ceil(places/wordsize)
  - Dirty-set optimization: only re-evaluates transitions whose input places changed
  - Priority scheduling, then FIFO by enablement time
- **PrecompiledNetExecutor** — The **production executor** (1.5–4× faster on sync chains). Flat-array/opcode representation, ring-buffer token storage, priority-partitioned ready queues. Must stay behaviorally identical to the Bitmap reference. In Rust it borrows `&PrecompiledNet`; `OwnedPrecompiledNet` caches the program. In Java the analogue is `PrecompiledNet` + `PrecompiledNetExecutor` (renamed from NetProgram/CompiledNetExecutor — not a VM).
- **CompiledNet** — Precomputed bitmap masks and reverse indexes (place → affected transitions)
- **Marking** — Current token distribution across places

**Java action dispatch (easy to get wrong):** `t.action().execute(ctx)` is called **inline on the
orchestrator thread**. No executor dispatches actions. The `ExecutorService` passed to
`Builder.executor(...)` hosts exactly one task — the orchestrator loop — and only under
`run(Duration)`. Concurrency comes from whatever drives the `CompletionStage` the action returns,
which libpetri does not own; a blocking action blocks the whole net. Consequently
`CompletableFuture.cancel(true)` on `Out.Timeout` cannot interrupt anything.

### Execution loop phases (per cycle):

1. Process completed transitions → collect outputs
2. Process external events → inject tokens from environment places
3. Update dirty transitions → re-evaluate enablement via bitmap
4. Fire ready transitions → sorted by priority, then FIFO
5. Await work → sleep until action completes, timer fires, or event arrives

### Event System (`src/event/`)

13 event types as a discriminated union (e.g., `transition-started`, `token-added`, `marking-snapshot`). `InMemoryEventStore` for debugging/testing; `noopEventStore()` for production.

### Verification (`src/verification/` in TS, `src/smt/` in Java)

Z3-based SMT verification using IC3/PDR. Supports: deadlock freedom, mutual exclusion, place bounds, unreachability. Uses Farkas method for P-invariants and structural siphon/trap pre-checks. State-class graph (Berthomieu-Diaz) for timed reachability.

**Z3 transport differs per language**: Java uses `com.microsoft.z3` JNI (in-process), TypeScript uses `z3-solver` WASM (in-process), Rust shells out to the **`z3` binary** via SMT-LIB2 text. Implications: verification is sound but incomplete for the Turing-complete fragment (inhibitor arcs) — proofs target the decidable safety properties above on bounded nets.

### Export (`src/export/`)

4-layer pipeline: `spec/petri-net-styles.json` (shared style definitions) → typed graph model (`export/graph`) → Petri net mapper (`PetriNetGraphMapper`) → DOT renderer (`DotRenderer`). Convenience functions (`dotExport()` / `DotExporter.export()`) chain mapper+renderer. ID conventions: `p_` prefix for places, `t_` prefix for transitions.

### Debug Infrastructure (`src/debug/`)

WebSocket-based debug protocol for live net inspection. `DebugSessionRegistry` manages sessions. Protocol provides `Subscribed` (with DOT diagram + net structure including `graphId` mappings), `PlaceInfo`, `TransitionInfo`. The debug-ui (`debug-ui/`) is a standalone Vite + Tailwind app using `@viz-js/viz` (Graphviz WASM) for client-side DOT→SVG rendering.

```bash
# Build debug-ui and copy to Java resources + TypeScript dist
scripts/build-debug-ui.sh
# Or manually:
cd debug-ui && npm ci && npm run build
```

The debug-ui has a Playwright layout-regression suite in `debug-ui/e2e/` (a
real browser is needed because the vitest `happy-dom` env does not compute CSS
layout). It is a local dev tool — not run in CI:

```bash
cd debug-ui
npx playwright install chromium   # one-time
npm run test:e2e
```

### Viewer (`typescript/src/viewer/`)

Canonical Petri-net diagram viewer — **one source of truth** for DOT→SVG
rendering plus the cluster overlay (collapse/expand, isolate filter,
deterministic per-prefix HSL palette, legend, filter chips). Used by:

- `debug-ui` (live debug sessions)
- `dev-preview` (Vite iteration loop)
- Java javadoc taglet (`DiagramRenderer.java`)
- Rust docgen (`libpetri-docgen`)
- TypeScript doclet plugin

Two build outputs feed those consumers:

- **ESM**: `typescript/dist/viewer/index.{js,d.ts}` — imported as `libpetri/viewer`
  by bundled consumers (debug-ui, dev-preview, TS doclet at build time).
- **IIFE**: `typescript/dist/viewer/viewer.iife.js` — self-contained, inlines
  `@viz-js/viz` (Graphviz WASM is shipped as a base64 blob inside viz.js, so
  no sidecar `.wasm` file is needed) + `panzoom`. Exposes
  `window.LibpetriViewer = { mount, discoverClusters, colorForPrefix, … }`.
  This is what Java javadoc and Rust docgen embed for offline doc pages.
- **CSS**: `typescript/dist/viewer/viewer.css` — single canonical stylesheet
  using `--lpv-*` CSS custom properties for theming.

```bash
# Build the viewer + distribute to all three doc-generator resource dirs.
# Replaces petrinet-diagrams.{js,css} in each. Diff-verified byte-identical.
scripts/build-viewer.sh
```

**Hard rule**: edits to viewer behaviour **must** happen in
`typescript/src/viewer/`. The three resource directories below are
**build outputs** and must not be hand-edited; the build script overwrites
them:

- `java/src/main/resources/javadoc/petrinet-diagrams.{js,css}`
- `rust/libpetri-docgen/resources/petrinet-diagrams.{js,css}`
- `typescript/src/doclet/resources/petrinet-diagrams.{js,css}`

Each consumer loads the file as before (no path change) — only the file
contents change, and they're identical across the three destinations.

## Specification

`spec/` contains 13 spec files (`00-index.md` … `12-nu-nets.md`), **208 active requirements**. Prefixes: CORE, IO, TIME, EXEC, CONC, ENV, VER, EVT, EXP, PERF, plus **MOD** (modular composition, `11-`) and **NU** (ν-nets / correlated fork-join by ID, `12-`). Requirements use MUST/SHOULD/MAY priority with testable acceptance criteria; cross-references use `[PREFIX-NNN]`. `spec/00-index.md` is the canonical registry — it tracks active vs removed/tombstoned IDs (e.g. IO-006), so trust the index count over any prose figure elsewhere.

## Release

Each language has its own release script and versioning. Tags are prefixed by language (e.g. `rust/v1.3.2`, `java/v1.3.1`).

- **Homepage**: https://libpetri.org (redirects to GitHub via GitHub Pages from `docs/`)
- **Maven Central**: `org.libpetri:libpetri` — `scripts/release-java.sh <version>` (GPG key, `~/.m2/settings.xml`)
- **npm**: `libpetri` — `scripts/release-typescript.sh <version>` (npm auth)
- **crates.io**: `libpetri` — `scripts/release-rust.sh <version>` (cargo login)
- All scripts support `--dry-run` to verify without publishing
- Prerequisites per script: `gh` CLI, plus language-specific auth (see script `--help`)

### Cross-language Place equality — divergence note (MOD-024)

- **Java** `Place` is a `record (name, tokenType)` — equality is **structural on both fields**.
- **TypeScript** `Place<T>` is an `interface { name }` with a phantom `_phantom?: T` — equality is **name-based at runtime** (no `tokenType` field exists).
- **Rust** `Place<T>` derives a name-only `PartialEq`/`Hash` impl (the `PhantomData<T>` does not participate).

`compose(instance)` / `compose_auto` (per `spec/11-modular-composition.md` MOD-024) uses
the implementation's existing `Place` equality:

- Java: dedupes by `(name, tokenType)` — two same-named different-typed places do NOT merge.
- TS / Rust: dedupes by name only — two same-named different-typed places WOULD merge.

This divergence is documented in MOD-024 (last paragraph of the body, the
SHOULD note on "implementations whose Place equality is name-only"). A future
breaking change that adds `tokenType` to TS Place and `TypeId` to Rust Place
would close this gap and warrant a coordinated TS/Rust 3.0 release. All three
languages are on 2.3.x with the additive MOD-024 overload.

## Key Conventions

- Immutable data everywhere — Place, Token, PetriNet, and CompiledNet are all immutable after construction.
- Builder pattern for Transition and PetriNet construction.
- Both implementations use the same test structure: `core/`, `runtime/`, `event/`, `export/`, and verification tests.
- Java uses records extensively (sealed interfaces, pattern matching, unnamed patterns, ScopedValue — all finalized in Java 25, no `--enable-preview` needed).
- TypeScript uses readonly properties and discriminated unions.
- `PaperNetworks` fixture class provides canonical reference nets used across test suites.
