# Changelog

## 2.8.0 (Python) — 2026-06-01

Six additive binding improvements; no API removed.

- **Subnet local-name remap.** `ctx.input("LOCAL")` / `ctx.output("LOCAL", v)`
  inside a subnet action resolve against author-local names after
  `compose(...)` rewrites the arcs to host places. Lookups try the
  literal name first, then fall back through the new
  `Transition::local_name_map` (populated by the rewriter; chained
  compose keeps only author-original keys, no intermediate-pass leak).
- **Async-action helpers.** `lp.action_gather(*coros)` and
  `lp.action_to_thread(fn, *args, **kw)` schedule on the asyncio loop
  captured at `run_async` / `start_async`, giving real `asyncio.gather`
  parallelism from inside an action on a tokio worker thread (three
  concurrent 300 ms sleeps finish in ~300 ms). `lp.captured_event_loop()`
  exposes the captured loop; the coroutine driver uses `coro.throw(exc)`
  for awaited-future errors; `await asyncio.sleep(0)` yields
  cooperatively to the executor. Concurrent `run_async` on two
  different asyncio loops in one process is detected and rejected
  with `RuntimeError` instead of silently routing helpers to the
  wrong loop.
- **`ctx.flush()` for mid-action streaming.** Buffered outputs publish
  immediately through a per-firing flush channel; downstream
  transitions can fire on the deposited tokens while the upstream
  action is still running. Already-flushed tokens stay even if the
  action later raises. Raises `RuntimeError` under sync execution.
- **Streaming subscribe.** `store.subscribe_stream(...)` yields a single
  `NetEvent` per `__anext__` (no `PyList[1]` wrapper). Unary delivery
  ~30 k events/sec; `subscribe(batch_size=256)` reaches ~950 k
  events/sec. See [`python/docs/perf-subscribe.md`](python/docs/perf-subscribe.md).
- **Batched env-place injection.** `handle.inject_many(place, iterable)`
  crosses the FFI once for any number of tokens via a new
  `ExecutorSignal::EventBatch` variant; the executor processes one
  batch atomically. ~8–9% end-to-end throughput improvement at
  N ≥ 1000.
- **Output-spec validation pinned.** The runtime enforces only the
  declared-place rule today; cardinality, AND-completeness,
  XOR-exclusivity, and `skip_output_validation` are documentation-only.
  See [`python/docs/output-spec.md`](python/docs/output-spec.md) and
  `python/tests/test_output_validation.py`.

**Known limitations (planned for 2.9.0 / next Rust major).**

- `ctx.flush()` deposits emit `TokenAdded` events identical to those
  from action completion; subscribers cannot currently distinguish
  flushed tokens from completion-deposited ones. A dedicated
  `ActionFlushed` event variant is planned for the next Rust major
  (adding it now requires `#[non_exhaustive]` on `NetEvent`, itself a
  breaking change).
- Cancelling the asyncio task that awaits `run_async` aborts the
  surrounding future but does not currently throw `CancelledError`
  into in-flight Python coroutines, so `try/except CancelledError:
  cleanup()` inside an action will not run. The proper fix (Drop guard
  that synchronously injects `CancelledError`) lands in 2.9.0.

## 3.0.0 (Rust) / 2.7.0 (Python) — 2026-06-01

**Executor backend seam (Rust).** The two Rust executors now share one
6-phase CTPN loop. `BitmapNetExecutor` and `PrecompiledNetExecutor` are type
aliases over a single generic `Executor<S, E>` that drives an internal
`ExecutorBackend` trait (bitmap vs. precompiled storage). Fully monomorphised —
the precompiled hot path stays within ±2% of the pre-refactor benchmarks (most
`precompiled_*` cases improved 1–9%); firing order, event semantics, and net
structure are unchanged.

- **Breaking (Rust)**: `marking()` returns `Cow<'_, Marking>` on both executors
  (was `&Marking` / owned `Marking`); `run_sync` / `run_async` likewise. Use
  `.into_owned()` for an owned copy.
- **`Out::Timeout` in the async path**: an async action that exceeds its budget
  now produces the timeout branch's outputs, emits an `ActionTimedOut` event, and
  forwards consumed inputs under a `ForwardInput` child — full `IO-013`/`EXEC-022`
  conformance matching Java/TS, closing two previously-ignored tests.
- Sync executor tests unified behind a `for_each_backend!` suite, so every CTPN
  semantic runs against both backends from a single source.

**Python bindings: cross-language parity.** Closes four gaps versus
Java/TypeScript/Rust — implementations stay on the Rust side per the
`feedback_pyo3_gil_cold` rule (no per-event Python callbacks; filtered,
batched GIL crossings via the existing `action.rs` coroutine pattern).

- **Marking snapshot/restore preserves `Token.created_at`.** `MarkingView.snapshot()` /
  `MarkingView.from_snapshot()` round-trips per-token timestamps; passing a
  view as `initial=` to `run_sync` / `run_async` resumes a timed net without
  clock loss. Mid-execution snapshot via `ExecutorHandle.snapshot()` (powered
  by a new `ExecutorSignal::Snapshot` upstream); `Marking` now derives `Clone`.
- **EventStore + NetEvent surface (Tier A/B/C, Rust-side).** `InMemoryEventStore`
  handle attaches via `event_store=` on `run_sync` / `start_async`. Tier A:
  filtered `store.events(types=..., transitions=..., places=..., limit=..., offset=...)`.
  Tier B: `async for batch in store.subscribe(...)` — bounded `tokio::mpsc`
  channel, Rust-evaluable filters, configurable batching with a `batch_size=1,
  batch_timeout_ms=0` unary mode for low-latency streaming. Tier C: `counters()`,
  `failures()` Rust aggregates. `NetEvent` is a frozen pyclass with lazy
  attribute getters.
- **Session Archive v3 (EVT-025).** `SessionArchiveWriter.write_from_store(...)` /
  `SessionArchiveReader.read(...)` — gzip-compressed, wire-compatible with the
  TypeScript / Rust readers. Writer consumes the `EventStore` handle directly;
  events never round-trip through Python. New `archive` Cargo feature flag and
  `HAS_ARCHIVE` runtime constant.
- **MarkingCache.** `MarkingCache(...).compute_at(store, event_index)` returns
  a `ComputedState` (marking, enabled transitions, in-flight transitions) by
  replaying from the nearest cached snapshot — backs debug-protocol seek/step
  from Python. No Python public API removed; the bindings changes are additive.

## 2.6.0

**Python bindings.** New `libpetri` PyPI package via PyO3 + maturin. Full surface
parity with Java/TS/Rust (runtime, verification, composition, debug, export),
ships with `.pyi` stubs + `py.typed` and 45 tests covering the same arc /
timing / cardinality / output semantics as the Java and Rust suites. Tokens are
untyped `Py<PyAny>` across the FFI — net structure is type-checked, runtime
token types are not (intentional cross-language divergence; validate at your
boundary if needed).

- `OwnedPrecompiledNet`: owned, `'static`-safe entry to the precompiled runtime;
  borrowed `PrecompiledNetExecutor<'p>` path preserved with no hot-path regression.
- `TransitionContext::{input_tokens_raw, read_tokens_raw}` accessors for FFI bridges.
- Built-in `lp.fork` / `lp.passthrough` actions for callback-free pass-throughs.
- `python` CI job + `scripts/release-python.sh` (mirrors the Rust release flow,
  including the documented Cargo.lock-resync gotcha).
- Async-callback perf: manual coroutine driver; `bench_chain_async_callback[100]`
  3536 µs → 750 µs (−78.8%). Sync chain −12% (LTO, `pyo3_disable_reference_pool`,
  `Arc<str>` keys).

## 2.5.0

**Subnet clustering for direct composition.** `compose(SubnetDef)` now records
which subnet each place/transition came from, and the DOT exporter renders
`subgraph cluster_<subnetName>` blocks from that metadata — so a directly-composed
net (no `prefix/` names) still groups each subnet visually. Strictly additive: a
net not built via direct composition exports byte-identically to before.

- **API**: `PetriNet.subnetMembership()` — `node-name → subnet-name` map
  (`subnet_membership()` in Rust). New `ExportConfig.ClusterSource`
  (`AUTO` | `METADATA` | `PREFIX` | `NONE`); `AUTO` (default) uses metadata when
  present and falls back to instance-prefix detection.
- **Viewer**: cluster discovery recovers membership by geometric containment, so
  directly-composed clusters report correct member counts in javadoc, rustdoc and
  the debug UI.
- New requirement **MOD-026** (SHOULD); **MOD-040** / **EXP-016** amended. No API removed.

## 2.4.0

**Direct subnet composition.** A new mode composes a `SubnetDef` into a host
net *without* instantiation/prefix-renaming — body places and transitions keep
their original names and merge by name. Unlike the auto-compose body-inference
fallback (MOD-024) it is order-independent. `instantiate(prefix)` + instance
composition is unchanged, and remains the path for independent copies.

- **API**: `compose(SubnetDef)` overload (Java/TS); `compose_direct(&SubnetDef)`
  in Rust (no overloading).
- A body transition name that collides with the host, or a subnet declaring a
  channel, is rejected at compose time.
- New requirement **MOD-025** (MUST). Strictly additive — no API removed, no
  core type changed.

## 2.3.2

*Released 2026-05-20*

**Configurable ELK layout for the canonical viewer, with side-effect-leaf
packing on by default.** The viewer's ELK placement stage gains an
`ElkLayoutConfig` — a per-subnet algorithm (`clusterLayout`) and side-effect-leaf
packing (`leafPacking`). A subnet dominated by "side-effect leaf" places (places
whose only intra-cluster arcs are reset/read) now packs those leaves into a
compact grid sub-block instead of stringing them into one wide row, so a
transition with many reset arcs lays out far more readably. Packing is enabled
by default, so every doc-generated diagram — Java javadoc, Rust `libpetri-docgen`,
and the TypeScript doclet — inherits the improvement through the regenerated
`petrinet-diagrams.js` bundle. Cross-generator parity is unchanged: all three
embed the same bundle and mount it with the same defaults.

### Added

- **TypeScript viewer**: `ElkLayoutConfig` (`clusterLayout: 'layered' |
  'rectpacking'`, `leafPacking: boolean | LeafPackingOptions`), surfaced through
  `MountOptions` and the `renderDotToSvgWithElkLayout` render entry. The render
  cache key now incorporates the layout config.
- **debug-ui**: the "Flat View" control is wired to the viewer's subnet
  visibility toggle; a Playwright layout-regression suite (`debug-ui/e2e/`) is
  added as a local dev tool — it is not run in CI.

### Compatibility

`build-viewer.sh` still installs byte-identical `petrinet-diagrams.{js,css}` to
all three doc-generator resource dirs. The Java jar's bundled debug-ui is
refreshed. No API is removed; `ElkLayoutConfig` is additive and every field is
optional.

## 2.3.1

*Released 2026-05-19*

**Doc generators consolidate on the client-side viewer.** The Java taglet, the
Rust `libpetri-docgen` crate, and the TypeScript doclet plugin all stop trying
to render DOT → SVG at build time and instead embed the DOT source in a
`data-dot` attribute. The bundled `LibpetriViewer` IIFE (Graphviz WASM baked
in) renders client-side on first view. Doc-generation hosts no longer need
`dot` or Node installed, and the per-tag subprocess overhead is gone.

### Removed

- **Java taglet**: subprocess machinery (`tryDotRender`, `tryC0Prerender`,
  `runSubprocessRenderer`, the per-DOT SVG caches, the `dotAvailable`
  cache-poison flag, and the `LIBPETRI_PRERENDER_SCRIPT` /
  `-Dlibpetri.prerender.script` env-var integration). `DiagramRenderer`
  loses its `renderSvg` / `renderSubnetSvg` paths and the `Body` switching
  record.
- **Rust `libpetri-docgen`**: the `dot` CLI fallback (`dot_to_svg`,
  `try_dot_command`, `find_attr`) and the `strip_dimensions` builder option.
- **TypeScript viewer**: `viewer-static.iife.js` (the slim ~26 KB bundle that
  stubbed Graphviz WASM), `index-static.ts`, and `render-stub.ts`. The
  remaining `mount(dotSource, …)` signature drops its `null` overload — the
  static-adopt branch is gone.
- **Build artifacts**: `scripts/prerender-c0.mjs` (Node prerender CLI) and the
  slim-bundle copy step in `scripts/build-viewer.sh`.

### Breaking — TypeScript `libpetri` npm package

- The `libpetri/viewer/layout` subpath export is **removed**. It existed only
  to serve the prerender CLI and the Java taglet's hybrid path, both of which
  are gone. The underlying `preprocess` / `elk-place` modules are still
  available internally and via direct dist imports if needed.

### Spec

- `spec/09-export.md` EXP-011 and EXP-015 reworded: implementation notes now
  describe DOT-in-`data-dot` embedding for all three generators; EXP-015
  acceptance criteria assert DOT content (extracted from `data-dot`) instead
  of rendered SVG shape.

### Compatibility

`build-viewer.sh` still installs byte-identical `petrinet-diagrams.{js,css}`
to all three doc-generator resource dirs; the invariant is unchanged. The
viewer's ESM entry (`libpetri/viewer`) and IIFE entry (`libpetri/viewer/iife`)
keep their public shape. Only consumers reaching into `libpetri/viewer/layout`
need to migrate.

## 2.3.0

*Released 2026-05-19*

**libpetri 2.3 adds identity-default auto-composition (MOD-024) to the
modular-composition layer across all three languages.** A single-argument
`compose(instance)` overload auto-binds every declared interface port to
the host place carried on its declaration, eliminating the boilerplate of
`compose(instance, b -> b.bindPort("name", host))` when the subnet's
interface already states the host wiring.

Released across Java, Rust, and TypeScript at 2.3.0. Rust and TypeScript
skip the 2.2.0 number — that section's content (the viewer subnet-visibility
toggle) shipped only in Java 2.2.0 to Maven Central; the same toggle code
is present in this Rust/TypeScript 2.3.0 release alongside MOD-024.

### `PetriNet.Builder.compose(Instance)` — auto-compose (MOD-024)

```java
// Before — explicit per-port wiring repeated at every call site:
host.compose(producer.instantiate("p1"),
             b -> b.bindPort("output", sharedQueue));

// After — port.place() carries the host wiring; auto-compose trusts it:
host.compose(producer.instantiate("p1"));
```

- Every declared port auto-binds to its own `port.place()` (the `Place` the
  `SubnetDef` builder declared via `.inputPort(name, hostPlace)` /
  `outputPort` / `inoutPort`).
- When the subnet declares **no** interface ports, body places are matched
  against the host builder's place set by `Place` record equality
  (`(name, tokenType)` in Java); matches merge, the rest stay private under
  their prefixed names per MOD-010 / MOD-012.
- Channels are **not** auto-bound. A subnet that declares any channel makes
  `compose(instance)` throw `IllegalStateException` naming the channels and
  pointing at the `compose(Instance, Consumer)` overload — transition
  identity is too delicate for inference.
- The auto-compose path shares the rewrite pipeline (`applyComposition`)
  with the explicit overloads, so the resulting flat net is structurally
  identical to a hand-written `compose(instance, bindings)` call per
  MOD-023.

### Spec

- New requirement **MOD-024** (`spec/11-modular-composition.md`) —
  Identity-Default Port Inference (auto-compose), SHOULD-level.
- `spec/00-index.md` summary updated: SHOULD count 43 → 44.

### Cross-language `Place` equality — divergence note

`compose(instance)` uses the implementation's existing `Place` equality:

- **Java** (this release): `Place` is a record `(name, tokenType)` — dedupes
  by both fields. Two same-named different-typed places do **not** merge.
- **TypeScript / Rust** (unreleased; equivalent overload present): `Place`
  equality is **name-only**, so same-named different-typed places would
  merge. This is the spec's "permissive matching" carve-out (MOD-024 last
  paragraph).

A future TS/Rust 3.0 release will close this gap by adding a token-type tag
to `Place` and tightening equality.

### Compatibility

`libpetri 2.3.0` is a strict additive extension of the prior published
versions (Java 2.2.0, Rust 2.1.0, TypeScript 2.1.0). No public API was
removed; behaviour for callers that don't invoke the new overload is
unchanged. The new method is one overload on `PetriNet.Builder` /
`PetriNetBuilder`; pre-existing overloads keep their signatures.

For TypeScript and Rust, this release also brings to npm/crates.io the
**viewer subnet-visibility toggle** documented in the `## 2.2.0` section
below (already in `main` since 2026-05-19 but never published to those
registries). Java had that release on its own; this release reunifies the
three languages on the same version number.

## 2.2.0

*Released 2026-05-19*

**libpetri 2.2 adds a runtime subnet-visibility toggle to the canonical viewer.**
Every diagram surface — debug-ui, dev-preview, Javadoc, Rustdoc, TypeDoc — now
exposes a chrome button that flips between the clustered (post-2.1) view and
the flat pre-subnets view without leaving the page.

### Viewer — clustered ↔ flat toggle

The viewer's chrome strip grows a **Flat view / Subnets view** button next to
**Reset** and **Fullscreen**. Clicking it re-mounts the diagram with the
alternate variant: in flat mode the `subgraph cluster_*` wrappers and their
`ltail`/`lhead` cross-cluster references are stripped, so Graphviz lays the
graph out without visual groupings. Same nodes, same edges, no clusters.

New on the public viewer API (`typescript/src/viewer/`):

- `MountOptions.subnets?: 'show' | 'hide'` — initial mode. Defaults to
  `'show'`; inherits from `previousHandle` when omitted so live re-renders
  preserve the user's choice.
- `ViewerHandle.subnets` — current mode (read-only).
- `ViewerHandle.setSubnets(mode)` / `toggleSubnets()` — programmatic switch.
  Returns the new handle (the toggle triggers an internal re-mount because
  Graphviz lays out cluster boundaries during layout).
- `libpetri-viewer:remount` CustomEvent dispatched on the host container
  whenever an internal re-mount happens. Consumers that cache the handle
  (e.g. debug-ui) can listen and update their reference.
- `flattenClusters(dot)` exported from `libpetri/viewer` — pure function
  for callers who want to derive flat DOT directly.

### Distribution

The new viewer bundle is synced byte-identically to all three doclet
destinations (`java/src/main/resources/javadoc/`, `rust/libpetri-docgen/resources/`,
`typescript/src/doclet/resources/`). No changes to `DotExporter` / export
APIs in any language — the toggle is purely a viewer-layer concern.

### Compatibility

`libpetri 2.2.0` is a strict superset of `2.1.0`: no public API was removed,
no behaviour changed for callers that don't opt into the new options.
Diagrams mount in clustered mode by default. The toggle button is rendered
but disabled on the pre-rendered-SVG mount path (`mount(null, …)`) because
no DOT is available for the alternate render.

## 2.1.0

*Released 2026-05-19*

**libpetri 2.1 is about visual coherence at scale.** Composed nets with many
subnets now lay out cleanly in DOT/Graphviz, and the canonical viewer gains a
production-grade C0 layout pipeline shared across debug-ui, the Javadoc taglet,
Rustdoc, and TypeDoc.

### Spec — EXP-017: compound cluster layout hints

The DOT export sets `compound="true"` unconditionally on the digraph and emits
*invisible ghost edges* connecting clusters bridged by single-hop orphan paths.
Graphviz uses the `ltail`/`lhead` hints on those ghost edges to keep
cluster-to-cluster flow direction stable while the visible edges still pass
through the real orphan transitions.

The synthesis is deterministic across Java, Rust, and TypeScript exporters:
ghost-edge anchors are the first-witness `(a → o, o → b)` pair encountered in
input iteration order, ordered cluster pairs `(X, Y)` collapse to one ghost edge
each, and `X == X` or single-neighbour orphans produce nothing. Eight
acceptance criteria are codified in `spec/09-export.md` and mirrored in
`ClusterBuilderTest` in all three languages.

### Viewer — canonical C0 layout pipeline

`typescript/src/viewer/layout/` is now the single source of truth for the
multi-cluster layout flow used by every documentation surface:

1. `parseLibpetriDot(dot)` — typed graph model from libpetri-exported DOT
2. `foldOrphans(graph, 0.7)` — adopt orphan nodes into their dominant cluster
   when ≥70 % of their edges point there
3. `replicateShared(graph)` — clone shared places into every foreign cluster
   they touch, redirect edges to local copies (`p_${id}__rep__${cluster}`
   naming is load-bearing — downstream overlays key off it)
4. `elkLayout(graph)` — ELK placement; orphans are wrapped in a synthetic
   `cluster_orchestrator` so they pack alongside real subnets
5. `writeBack(graph, layout)` — re-emit DOT with `pos="x,y!"` pins and
   cluster `bb="…"` so Graphviz `neato -n` produces the final SVG

Around the rendered SVG the viewer ships four idempotent overlays:

- **`c0-annotations.ts`** — `data-id` / `data-src` / `data-dst` / `data-instance`
  injection plus `intra-cluster` / `cross-cluster` edge classes
- **`replica-tagging.ts`** — `.petri-replica` + `data-replica-of` on every clone
  of a shared place, plus the ⇄ glyph for visual identification
- **`highlight.ts`** — click-to-highlight that walks through junctions and
  surfaces every real neighbour; highlighting a shared place highlights every
  copy together
- **`visibility.ts`** — directed-reachability orphan visibility that hides
  unrelated orphan chains when only a subset of clusters is shown

The new `chrome/sidebar.ts` replaces the legacy legend + filter strip with a
cluster-chip sidebar: plain-click toggles, shift-click isolates, ctrl/cmd-click
multi-selects, plus show-all / hide-all and a highlight-mode toggle.

`mount()` returns two new C0-only methods: `handle.highlight(nodeId)` and
`handle.setVisibility(state)`. Both are gated on `layout: 'elk'` (the new
default); pass `layout: 'graphviz'` for the plain pre-2.1 rendering.

A 16-entry LRU cache in `render.ts` (keyed on FNV-1a of the DOT source) makes
re-mounts on identical DOT skip the entire pipeline.

### Doclet — opt-in Node-CLI pre-render for Javadoc

`PetriNetTaglet` now tries a Node-CLI pre-render path before falling back to
`dot -Tsvg`. Set `LIBPETRI_PRERENDER_SCRIPT` (or `-Dlibpetri.prerender.script=…`
to survive the Gradle daemon's env capture) to the path of
`typescript/scripts/prerender-c0.mjs` and the taglet pipes DOT to Node, runs the
full C0 pipeline, and embeds the resulting SVG inline. ~1 second per 14-subnet
diagram; cached per-DOT-source for the lifetime of the doc build.

Both render paths share a single `runSubprocessRenderer` driver with a typed
`SubprocessRendererConfig` record — concurrent stdout/stderr drain to avoid the
OS pipe-fill deadlock, per-renderer timeout, cache-poison hook on missing or
wedged binaries. ~120 LOC of duplication is gone.

### Distribution

The canonical viewer bundle (`viewer.iife.js`, `viewer.css`) is built once from
`typescript/src/viewer/` and synced byte-identically to all three doclet
destinations (`java/src/main/resources/javadoc/`, `rust/libpetri-docgen/resources/`,
`typescript/src/doclet/resources/`). The viewer's public ESM surface gains
`libpetri/viewer/layout` so the Node prerender script and any external tooling
can drive the C0 pipeline directly.

### Performance

- Cluster building is O(N + E + O·I·G) with no hidden O(n²); ghost-edge dedup
  is O(1) per ordered pair.
- The C0 overlays batch DOM mutations after computing target state — no
  interleaved getBBox / setAttribute, no layout thrash.
- ELK runs once per unique DOT input; downstream overlays are O(N + E) walks
  with map-backed lookups.

### Compatibility

`libpetri 2.1.0` is a strict superset of `2.0.0`: no public API was removed,
no behaviour changed for nets that don't compose subnets. Consumers that
explicitly want the pre-2.1 viewer behaviour can pass `layout: 'graphviz'`
to `mount()`. The Javadoc taglet's legacy `dot -Tsvg` path still runs when
the C0 env var / sysprop is unset.

## 2.0.0

*Released 2026-05-18*

**libpetri 2.0 is about modular composition.** You can now build large
Petri nets the way you build large programs — by writing small reusable
pieces and snapping them together. Producer, buffer, consumer, rate
limiter: each becomes a self-contained subnet with a typed interface,
and the composition machinery wires them up.

Everything from 1.x still works. The 2.0 surface is additive — your
existing builders, runtime, events, exports, and verification code
compile unchanged.

### Subnets and instances

Define a reusable fragment as a `SubnetDef`. It looks like a normal net,
but its boundary is declared as an `Interface` with two kinds of names:

- **Ports** — boundary places that a host net can wire into its own
  places. Typed by token type.
- **Channels** — boundary transitions that fuse with host transitions
  when composed, giving you synchronous coupling between subnets.

A `SubnetDef` is a template. Call `def.instantiate("p1", params)` to get
an `Instance`, which is the same net with everything renamed to
`p1/<originalName>`. Instantiate it twice and you get two independent
copies that won't collide. Instances also inherit shared default
actions from the def, and you can override per-instance with
`bindActions(...)` — the rest of the instance keeps the shared
reference, so changing the def's action propagates to every instance
that didn't override it.

You can retrofit an existing 1.x `PetriNet` as a subnet via
`SubnetDef.fromNet(net, iface)` without rewriting it.

### Composing with the builder

The new `PetriNet.builder().compose(instance, bindings)` method weaves
an instance into the enclosing net:

```java
var producer = SubnetDef.<Void>builder("Producer")…build();
var buffer   = SubnetDef.<Integer>builder("Buffer")…build();

var system = PetriNet.builder("Pipeline")
    .compose(producer.instantiate("p"), b ->
        b.bindPort("output", hostInput))
    .compose(buffer.instantiate("b", 4), b ->
        b.bindPort("in", hostInput).bindChannel("backpressure", limiter))
    .build();
```

What this does:

- **Port bindings** rewrite every arc on the instance so the port place
  becomes the host place. After `build()` the two places are the same
  place.
- **Channel bindings** merge the instance's boundary transition with a
  host transition: arc union, timing intersection, caller-wins
  priority, sequential action composition.

`build()` returns a flat `PetriNet`. The executor, exporter, verifier,
and event store see no difference from a hand-written net.

### FusionSet — shared places across instances

When two instances need to share state — a single rate limiter across
three workers, one bounded buffer feeding two consumers — declare a
`FusionSet` of equivalent places:

```java
.fuse(FusionSet.of("limiter",
    workerA.port("slots", Integer.class),
    workerB.port("slots", Integer.class),
    workerC.port("slots", Integer.class)))
```

At `build()`, the non-canonical members are substituted away. Fusion is
orthogonal to composition: declare it before or after your `compose(...)`
calls — same result.

### Better visualization for composed nets

DOT exports now emit one `subgraph cluster_*` per instance prefix, with
nested instances producing nested clusters. Output is byte-identical to
1.x for any net that doesn't use composition. The Java doclet picks up
the same data: a new `@SubnetStructure` annotation and the
`{@subnet Name}` inline tag let you point at subnet defs from doc
comments, and `SubnetDotExport` renders compact interface-only diagrams
(ports and channels, no internals) for API reference pages.

### Debug protocol speaks subnets

The debug-ui has a new subnet panel. The wire protocol's `Subscribed`,
`PlaceInfo`, and `TransitionInfo` responses now carry instance
descriptors so the UI can walk composed nets by prefix and let you
drill in.

### Verifying a subnet on its own

You can now prove properties about a subnet in isolation, before you
compose it into anything:

```java
var result = bufferDef.verify(
    VerificationHarness.<Integer>builder(4)
        .input("in", () -> Token.of(...))
        .property(new PlaceBound("items", 4))
        .build());
```

The harness wraps the subnet in a synthetic enclosing net, feeds the
declared input ports from environment generators, and runs the standard
Z3/SMT verifier. You get back a `VerificationResult` with per-property
outcomes plus `allHold()` / `firstFailure()` shortcuts. Verifying an
already-composed flat net works exactly like 1.x — no API change there.

### Faster doc pages: pre-rendered SVG

The Java javadoc taglet now pre-renders each diagram at doc-generation
time when `dot` is on `PATH`, embedding the resulting SVG directly and
shipping a slim `viewer-static.iife.js` bundle (~26KB) that drops the
inlined Graphviz WASM. Page-load latency drops dramatically on doc
pages with many `{@petrinet ...}` references. When `dot` isn't
available the taglet transparently falls back to client-side rendering
with the full bundle — no configuration needed.

The viewer's `mount()` now accepts `null` as the DOT source (adopts an
existing `<svg>` child), and gains a `fit()` method plus built-in
Reset and Fullscreen chrome buttons when `chrome:true`.

### Migration from 1.x

No code changes needed. Update your dependency to `2.0.0` and existing
code keeps working. The new modular-composition APIs are available
under:

- **Java** — `org.libpetri.core.{SubnetDef, Instance, Interface, FusionSet, ComposeBindings, Subnet}` plus `org.libpetri.verification.VerificationHarness`.
- **TypeScript** — re-exported from `libpetri`: `SubnetDef`, `Instance`, `Interface`, `FusionSet`, `ComposeBindings`, `VerificationHarness`.
- **Rust** — new modules in `libpetri-core` (`subnet`, `compose`, `fusion`, `interface`, `instance`); `libpetri-verification` gains the harness; `libpetri-export` gains cluster output.

For a complete worked example see the **Modular Composition** section
in the top-level README. The full formal contract lives in
`spec/11-modular-composition.md` (22 new requirements, MOD-001..061);
spec totals are now 183 across 11 documents.

## 1.8.5

### Fix: doc-viewer zoom cap raised from 5x to 1000x

`petrinet-diagrams.js` (the small pan/zoom/fullscreen helper inlined into
Javadoc and TypeDoc HTML) clamped wheel zoom to `Math.min(5, ...)`, hitting
a hard ceiling at 500%. Bumped to `Math.min(1000, ...)` and floor lowered
from `0.1` to `0.02`, matching the bounds the live debug-ui and dev-preview
viewers already use via `libpetri/render-dom` (panzoom defaults). Java and
TypeScript ship parallel copies of this asset; both are updated and now
carry a sync-reminder comment to keep them byte-identical.

No Rust change — `libpetri-docgen` does not ship this JS asset.

## 1.8.4

### Feat: XOR/AND junction nodes + combined reset+output edges

New visualization rules in `spec/09-export.md` (EXP-012, EXP-013, EXP-014,
EXP-015), implemented identically in Java/TypeScript/Rust mappers:

- **EXP-012** — Every `Out.Xor` / `Out.And` group with two or more children
  now becomes a synthetic *diamond junction node* between the transition and
  its children. The discriminator is an inline heavy glyph: `✕` (U+2715) for
  XOR, `✚` (U+271A) for AND. Single-child groups still collapse to a direct
  edge — no orphan junctions. New style categories `xor-junction` and
  `and-junction` (shape `diamond`, fill `#FFFFFF`, stroke `#333333`,
  width/height `0.3`, fontsize `14`, `fixedsize="true"`).
- **EXP-013** — When a transition outputs to place `P` and resets `P`, the
  separate output and reset edges collapse into one edge labelled `"reset+out"`,
  styled as the new `reset-output` category (color `#fd7e14`, style `bold`,
  penwidth `2.0`). The rule applies whether the output leaf is direct from the
  transition or nested under a junction.
- **EXP-014** — Junction IDs follow `j_<sanitizedTransition>__<kind>_<idx>`,
  where `<idx>` is a flat depth-first pre-order counter starting at 0. Same
  numbering scheme in all three languages, so DOT output is byte-identical
  across implementations for the same input net. New round-trip stability
  tests in each language assert that two consecutive exports produce
  byte-equal DOT.
- **EXP-015** — Compile-time doc generators (Javadoc taglet, `cargo doc`
  build script, TypeDoc plugin) all delegate to their language's mapper, so
  the new junction nodes and combined edges show up in generated SVGs without
  any doc-generator-specific code.

### Refactor: `EmitCtx` threaded through Out-tree emission

Java `JunctionCtx`, Rust `EmitCtx<'_>`, and TypeScript `EmitCtx` bundle the
mutable per-transition state (counter, reset-place set, combined accumulator,
node + edge sinks) into a single value passed by the recursive emitter. The
public mapper API is unchanged; internal helpers drop from nine arguments
each to four (`out`, `parentId`, `branchLabel`, `ctx`). On the Java side this
also retires the `int[] counter = { 0 }` mutable-array idiom; on the Rust
side it lets `#[allow(clippy::too_many_arguments)]` go away.

### New: `libpetri/render-dom` browser package entry

A new TypeScript package entry exports `renderDotToContainer(dot, container,
opts)` — a small wrapper around `@viz-js/viz` (Graphviz WASM) and `panzoom`
that pins the `dot` engine for layout stability and disposes prior panzoom
instances on re-render. The debug-ui (`debug-ui/src/net/actions/diagram.ts`)
now imports this entry instead of bootstrapping viz.js + panzoom inline,
deleting ~140 lines of duplicated setup. A new Vite-based `dev-preview/`
sandbox uses the same module against the new `sample.dot` golden file for
local visual iteration. The script `npm run regenerate-sample` reproduces
that file deterministically from the TS mapper; it exercises every rule above.

## 1.8.3

### Fix: archive header `eventCount` matches body length

The session archive writer (Java/TS/Rust) populated header `eventCount` from
`DebugEventStore.eventCount()` — the **lifetime cumulative append counter** that
never decrements on eviction — while iterating the body from the live event queue.
After any eviction, the header overstated the body by exactly the eviction count,
breaking the `archive.eventCount() == archive.events().size()` round-trip
invariant.

A second, Java-only failure mode: header `eventCount`,
`SessionMetadata.computeFrom(...)`, and the body loop were three separate reads of
the concurrent `ConcurrentLinkedQueue`. A producer thread appending between any
two reads desynchronised them.

Fix: every writer entry-point now takes a single immutable snapshot of the event
store and derives header `eventCount`, V2/V3 metadata, and the body iteration from
that one list. Identical pattern across all three languages. Wire format is
unchanged — old archives remain readable, new archives remain readable by older
1.8.x readers (the field is canonical content, not wire layout).

Codified as new acceptance criterion **EVT-025 #8**. Regression tests added in
all three implementations: eviction round-trip in Java/TS/Rust, plus a virtual-thread
concurrent-producer stress test on Java where `ConcurrentLinkedQueue` makes the race
observable.

## 1.8.2

### Revert `splines=curved`

`splines=curved` from 1.8.1 produced overly wavy edge routing on dense nets — in
practice noticeably worse than Graphviz's default B-spline routing. Removed.

`outputorder=edgesfirst` is kept — that one is still the right fix for the
label-under-edge overlap problem from 1.8.0.

## 1.8.1

### Debug-UI diagram readability

Two graph attributes added to the DOT output produced by `PetriNetGraphMapper`
(all three languages) so the rendered debug-ui diagram is easier to read on dense
nets:

- **`outputorder=edgesfirst`** — Graphviz draws edges first and nodes (including
  `xlabel` place names) on top. Edge lines no longer slice through place labels.
- **`splines=curved`** — softer curved edge routing instead of the default
  spline style. Noticeably cleaner on graphs with many crossings.

The spec file `spec/petri-net-styles.json` is the single source of truth; the
Java/TS/Rust style constants are regenerated by `scripts/generate-styles.sh`.

The debug-ui (`debug-ui/src/net/actions/diagram.ts`) now pins the viz.js layout
engine to `dot` explicitly. libpetri servers emit byte-stable DOT (Java uses
`LinkedHashMap` in `PlaceAnalysis`; TS/Rust iterate ordered collections), and the
`dot` engine produces identical layout for identical input — so diagrams are
deterministic across debug-ui reloads. Pinning guards against future viz.js
default changes to force-directed engines.

## 1.8.0

### Archive format v3 (all three languages)

`SessionArchive` gains a third variant (`V3`). The v3 header is structurally identical to
v2 — same `endTime`, `tags`, pre-computed `metadata` — but the version bump signals that
the event body format now carries **structured token payloads** alongside the legacy
display string. See [EVT-025](spec/08-events-observability.md) for the full contract.

Default writer output is now v3:

- **Java**: `SessionArchiveWriter.write` emits v3. Tokens serialize as
  `{valueType: <FQN>, v: <structured JSON>, createdAt}` with `{valueType, text}` fallback
  for values Jackson cannot structure and `{valueType: "void"}` for unit tokens. The
  reader resolves `valueType` via `Class.forName` — classes on the current classpath
  hydrate with their original type; missing classes degrade to `Token<JsonNode>`
  preserving the payload tree.
- **TypeScript**: `SessionArchiveWriter.write` emits v3. `TokenInfo.structured` carries
  the JSON projection (`JSON.parse(JSON.stringify(v))` with empty-object / symbol /
  function filtering). `Token<T>` gains an optional `structured?` field that
  `SessionArchiveReader.readFull` populates on replay — live tokens leave it undefined
  and the runtime ignores it.
- **Rust**: `SessionArchiveWriter::write_with_registry` emits v3 via a user-supplied
  [`TokenProjectorRegistry`](rust/libpetri-debug/src/token_projector_registry.rs).
  Replay hydrates each `TokenAdded` / `TokenRemoved` event with a `ReplayedTokenPayload
  { type_name_str, value_json }` implementing the same `TokenPayload` trait as live
  `ErasedToken`, so consumers treat live and replayed tokens uniformly. Executors only
  attach the payload when `EventStore::CAPTURES_TOKENS = true`, so `NoopEventStore`
  builds monomorphize the capture branch to dead code — zero overhead in production.

### Backward compatibility

- Readers in all three languages still accept v1 and v2 archives. Unknown versions are
  rejected with an error naming the observed version and the supported range.
- `writeV1` / `writeV2` (`write_v1` / `write_v2` in Rust) still exist, but note: the
  writer no longer produces byte-for-byte 1.7.x event bodies — it always emits v3 token
  shapes regardless of the header version. Consumers pinned to a 1.7.x reader may choke
  on the extra `structured` field; either upgrade the reader or consume archives
  produced by a 1.7.x writer.

### Breaking changes

- **Rust**: `NetEvent::TokenAdded` and `NetEvent::TokenRemoved` gain a third struct field
  (`token: Option<Arc<dyn TokenPayload>>`). Both variants are now `#[non_exhaustive]`;
  downstream pattern matches must use `{ place_name, timestamp, .. }` or explicitly
  destructure `token`. Use the new `NetEvent::token_added(...)` /
  `token_added_with(...)` constructors to build events (they keep the variant fields
  private-by-convention and survive future field additions).
- **Rust**: `libpetri-core` now depends on `libpetri-event` so that `ErasedToken` can
  implement `TokenPayload`. This is a workspace-internal change; downstream crates pick
  it up automatically via `libpetri` umbrella.
- **TypeScript**: `Token<T>` gains an optional `structured?: unknown` field. Additive —
  existing `{ value, createdAt }` literals remain valid. Consumers destructuring via
  `{ value, createdAt, ...rest }` will pick up the extra field.
- **Java**: No source-breaking changes. The serialized `NetEvent` JSON now emits tokens
  in the new v3 shape — any hand-rolled Jackson deserializer for `Token` must understand
  the v3 format (or use `NetEventSerializer` which does).

### Security

Archive deserialization is a trust boundary in all three languages — Java because
`Class.forName` on an archive-supplied FQN triggers static initializers, TypeScript
because a hostile `toJSON()` override could return misleading data, Rust because a
hostile `type_name` string could misattribute a payload. Do not deserialize archives
from untrusted network sources without a guard. See EVT-025 security note.

## 1.7.0

### Archive format v2 (all three languages)

`SessionArchive` is now a sealed hierarchy (`V1` / `V2`) — Java sealed interface + records,
TypeScript discriminated union keyed on `version: 1 | 2`, Rust enum. The v2 header adds:

- `endTime` — the `complete()` timestamp, preserving session duration across archival.
- `tags` — the user-defined tag snapshot at write time.
- `metadata` (new `SessionMetadata`) — single-pass aggregates: event-type histogram
  (PascalCase keys, alphabetical, identical wire format across languages), first/last event
  times, and `hasErrors` (true for any `TransitionFailed`, `TransitionTimedOut`,
  `ActionTimedOut`, or `LogMessage` at level `ERROR`, case-insensitive).

v2 lets listing/sampling tools answer "which sessions had errors" or "how many events of
type X" without decompressing the body. Per-event wire format is identical to v1.

### Backward compatibility

- Readers peek `version` via a probe DTO and deserialize into the matching variant. v1
  archives from libpetri ≤ 1.6.1 remain fully readable; mixed v1/v2 buckets coexist.
- v2-only accessors (`tags()`, `endTime()`, `metadata()`) return safe defaults on v1 archives.
- `writeV1()` / `write_v1()` escape hatch for producing archives consumable by older readers.
  Default `write()` emits v2.
- Shared metadata helpers usable on live sessions or v1 reads:
  Java `SessionMetadata.fromEvents`, TypeScript `computeMetadata`, Rust `compute_metadata`.
- Rust adds `NetEvent::has_error_signal()` — superset of `is_failure()` that also catches
  `LogMessage` at `ERROR`. `is_failure()` is unchanged.

### Performance

- v2 overhead vs v1: **+0.8%** on a 1000-event session (20,872 vs 20,703 bytes LZ4).
  LZ4/gzip frame dedup absorbs the repeated header strings; v2's value is at read time, not
  on disk.

### Compatibility

- **Java** binary-incompatible for code pattern-matching on the old `SessionArchive` record —
  recompile against 1.7.0.
- **Rust** `imported.metadata.session_id` (field) → `session_id()` (method). No in-workspace
  consumers affected.
- **TypeScript** source-compatible; the discriminated union narrows existing
  `version === CURRENT_VERSION` checks.
- Archive envelopes still differ by language (Java LZ4, TS/Rust gzip; Java/TS ISO-8601,
  Rust u64-ms). Cross-language read is future work.
- No spec changes for the archive format — it is implementation-defined.

### Bulk token output on `TransitionContext` (all three languages)

Transition actions can now push multiple tokens to the same output place in one call,
avoiding the `for v in values { ctx.output(...) }` loop that previously incurred per-element
place-declaration validation:

- **Java**: `@SafeVarargs public final <T> TransitionContext output(Place<T>, T...)` and
  `<T> TransitionContext output(Place<T>, Iterable<? extends T>)`. Strict-match overload
  resolution (JLS §15.12.2.5) keeps the existing single-value `output(Place<T>, T)` call
  path unchanged.
- **TypeScript**: `ctx.output<T>(place, ...values: T[])` and
  `ctx.outputToken<T>(place, ...tokens)` now accept rest parameters. Single-arg call sites
  continue to type-check.
- **Rust**: new `ctx.output_many<T>(place_name, impl IntoIterator<Item = T>)`. Accepts
  arrays, `Vec`, slice iterators, and iterator adaptors. The existing single-value
  `output()` is untouched.

All three implementations validate the output place **once** before iterating, share a
single timestamp across the produced tokens (matching "fired at time T" semantics), and
fail fast on undeclared places without leaving partial output. See [CORE-062].

### Spec Changes

- **CORE-062 updated.** Extended the acceptance criteria to cover the bulk-form API, the
  validate-once-fail-fast contract, and the empty-bulk-is-a-no-op degenerate case.

## 1.6.1

### Session tags (all three languages)

`DebugSessionRegistry` sessions now carry arbitrary `Map<String,String>` tags
(e.g. `{channel: "voice", env: "staging"}`). Storage lives on the `DebugSession` itself —
no shadow map, no cleanup coordination. Java uses `ConcurrentHashMap` for lock-free updates;
TS/Rust mutate in place. New APIs across languages: `register(id, net, tags)`,
`tag(id, key, value)`, `tagsFor(id)`, and an optional `tagFilter` on `listSessions` /
`listActiveSessions`.

### Session endTime

`complete(sessionId)` stamps an `endTime` once (first-completion semantics). `duration()`
returns `Optional<Duration>` / `undefined | number` / `Option<u64>` ms.

### Wire protocol

- `DebugResponse.SessionSummary` adds optional `tags`, `endTime`, `durationMs`. Older clients
  tolerate the new fields.
- `registerImported` overload accepts `endTime` + `tags` for archive round-trips.

### Breaking changes (Rust internal wire format)

- `DebugCommand` / `DebugResponse` inline enum-variant fields now serialize in **camelCase**
  to match Java/TypeScript (`sessionId`, `activeOnly`, `tagFilter`, `netName`, `dotDiagram`,
  `eventCount`, `startIndex`, `hasMore`, `currentMarking`, `enabledTransitions`,
  `inFlightTransitions`, `currentIndex`, `breakpointId`, `eventIndex`, `fromIndex`, `fileName`,
  `storageAvailable`). Previously snake_case, which prevented the TypeScript debug-ui from
  connecting to a Rust backend. Inner struct types were already correct. Update any Rust-only
  client code that hardcoded JSON keys.

### Compatibility

Otherwise additive and source-compatible. Archive v1 format untouched; v2 with tags +
histograms ships in 1.7.0. No spec changes.

## 1.5.3

### Dependency Updates

- **lz4-java**: changed groupId from `org.lz4` to `at.yawk.lz4` (upstream artifact relocation).

## 1.5.2

### Bug Fixes

- **Fixed CPU spin in `drain()` with enabled timed transitions (Java, Rust).** Calling `drain()`
  on an executor with environment places while timed transitions were enabled but not yet ready
  (nothing in-flight) caused the orchestrator to spin at 100% CPU. In Java, `awaitWork()` fell
  through without blocking because `hasEnvironmentPlaces && !draining.get()` was false and no
  other branch applied. In Rust, the same condition caused premature termination (dropping
  enabled timed transitions). With 20 concurrent nets on 4 cores, total CPU burned was ~5,600ms
  for a 400ms wall-clock window. Affects `BitmapNetExecutor` and `NetExecutor` (Java),
  `BitmapNetExecutor` and `PrecompiledNetExecutor` (Rust async). Java `PrecompiledNetExecutor`
  and TypeScript were already correct. Regression introduced in 1.5.0.

## 1.5.1

### Bug Fixes

- **Fixed CPU spin in `close()` with in-flight async actions (Java).** Calling `close()` while
  async transition actions were running caused the orchestrator thread to spin at 100% CPU until
  those actions completed. The `awaitCompletionOrEvent()` poll loop now blocks with 50ms polling
  intervals instead of exiting immediately when `closed` is set. Affects all three Java executors:
  `BitmapNetExecutor`, `NetExecutor`, `PrecompiledNetExecutor`. TypeScript and Rust were not
  affected (event-driven architectures). Regression introduced in 1.5.0.

## 1.5.0

### Breaking Changes

- **Removed `longRunning` flag.** Long-running behavior is now implicit when environment places
  are registered — no explicit flag needed. Remove `.longRunning(true)` / `long_running: true`
  from all executor builders/options.

- **`close()` is now immediate shutdown (ENV-013).** Queued events are discarded; in-flight
  actions complete; executor terminates. Use the new `drain()` for graceful behavior.

- **Rust: channel type `ExternalEvent` → `ExecutorSignal`.** The async channel now carries
  lifecycle signals (`Drain`, `Close`) alongside events. Wrap events:
  `tx.send(ExecutorSignal::Event(event))`.

### New Features

- **`drain()` — graceful shutdown (ENV-011).** Rejects new `inject()` calls, processes
  queued events, completes in-flight actions, terminates at quiescence.

- **`close()` — immediate shutdown (ENV-013).** Discards queued events, completes in-flight,
  terminates. `close()` after `drain()` escalates from graceful to immediate.

- **Rust: `ExecutorHandle`** — RAII lifecycle wrapper with typed `inject()`/`drain()`/`close()`
  and auto-drain on drop. Re-exported from umbrella crate under `tokio` feature.

### Spec Changes

| Requirement | Change |
|---|---|
| ENV-006 | Reject `inject()` on closed **or draining** executor |
| ENV-010 | Rewritten: implicit long-running from environment places |
| ENV-011 | Rewritten: graceful `drain()` (was "explicit close") |
| ENV-013 | **New**: immediate `close()` |
| Total | 155 → 156 requirements |
