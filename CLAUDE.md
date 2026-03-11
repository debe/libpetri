# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

libpetri is a multi-language **Coloured Time Petri Net** (CTPN) engine with formal verification. Two production implementations exist (Java 25 and TypeScript), both conforming to a shared specification of 145 requirements in `spec/`.

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

TypeScript 5.7, ESM-only, strict mode. Built with tsup (multi-entry: `index`, `export`, `verification`, `debug`, `doclet`), tested with vitest. JaCoCo code coverage auto-generated in Java (`target/site/jacoco/`).

## Architecture

Both implementations share the same architecture, mirrored across languages.

### Core Model (`src/core/`)

- **Place\<T\>** — Typed, named token container. Identity by name. `EnvironmentPlace<T>` is a subtype for external event injection.
- **Token\<T\>** — Immutable value + timestamp.
- **Transition** — Consumes/produces tokens via arcs. Has optional timing constraints and priority. Actions are async (`CompletableFuture<Void>` in Java, `Promise<void>` in TypeScript).
- **Arc types** — Input (consume), Output (produce), Inhibitor (block when present), Read (test without consuming), Reset (clear all).
- **Timing** — `immediate`, `deadline(ms)`, `delayed(ms)`, `window(early, late)`, `exact(ms)`. Urgent semantics: transitions forced-disabled past deadline.
- **PetriNet** — Immutable net definition built via builder pattern. Transitions implicitly declare places through their arcs.

### Runtime (`src/runtime/`)

- **BitmapNetExecutor** — The primary executor. Single-threaded orchestrator with concurrent async actions.
  - Bitmap-based enablement: O(W) checks where W = ceil(places/wordsize)
  - Dirty-set optimization: only re-evaluates transitions whose input places changed
  - Priority scheduling, then FIFO by enablement time
- **CompiledNet** — Precomputed bitmap masks and reverse indexes (place → affected transitions)
- **Marking** — Current token distribution across places

### Execution loop phases (per cycle):

1. Process completed transitions → collect outputs
2. Process external events → inject tokens from environment places
3. Update dirty transitions → re-evaluate enablement via bitmap
4. Fire ready transitions → sorted by priority, then FIFO
5. Await work → sleep until action completes, timer fires, or event arrives

### Event System (`src/event/`)

13 event types as a discriminated union (e.g., `transition-started`, `token-added`, `marking-snapshot`). `InMemoryEventStore` for debugging/testing; `noopEventStore()` for production.

### Verification (`src/verification/` in TS, `src/smt/` in Java)

Z3-based SMT verification using IC3/PDR. Supports: deadlock freedom, mutual exclusion, place bounds, unreachability. Uses Farkas method for P-invariants and structural siphon/trap pre-checks.

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

## Specification

`spec/` contains 10 spec files with requirement prefixes: CORE, IO, TIME, EXEC, CONC, ENV, VER, EVT, EXP, PERF. Requirements use MUST/SHOULD/MAY priority and have testable acceptance criteria. Cross-references use `[PREFIX-NNN]` format.

## Release

Each language has its own release script and versioning. Tags are prefixed by language (e.g. `rust/v1.3.2`, `java/v1.3.1`).

- **Homepage**: https://libpetri.org (redirects to GitHub via GitHub Pages from `docs/`)
- **Maven Central**: `org.libpetri:libpetri` — `scripts/release-java.sh <version>` (GPG key, `~/.m2/settings.xml`)
- **npm**: `libpetri` — `scripts/release-typescript.sh <version>` (npm auth)
- **crates.io**: `libpetri` — `scripts/release-rust.sh <version>` (cargo login)
- All scripts support `--dry-run` to verify without publishing
- Prerequisites per script: `gh` CLI, plus language-specific auth (see script `--help`)

## Key Conventions

- Immutable data everywhere — Place, Token, PetriNet, and CompiledNet are all immutable after construction.
- Builder pattern for Transition and PetriNet construction.
- Both implementations use the same test structure: `core/`, `runtime/`, `event/`, `export/`, and verification tests.
- Java uses records extensively (sealed interfaces, pattern matching, unnamed patterns, ScopedValue — all finalized in Java 25, no `--enable-preview` needed).
- TypeScript uses readonly properties and discriminated unions.
- `PaperNetworks` fixture class provides canonical reference nets used across test suites.
