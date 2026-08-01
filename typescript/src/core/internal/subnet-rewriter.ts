/**
 * @internal
 *
 * Package-internal utility encapsulating the structural rewrite primitive used
 * by {@link SubnetDef.instantiate} and (later) `PetriNetBuilder.compose(...)`
 * per **MOD-020**.
 *
 * The rewrite is purely structural: every place reference in every arc is
 * replaced according to a supplied `Map<string, Place<unknown>>` keyed by
 * **original place name** (TypeScript Place identity is name-based per
 * `runtime/compiled-net.ts`'s `Map<string, number>`). Every transition is
 * rebuilt with rewritten arcs, preserving timing, priority, and action by
 * reference per **MOD-030**.
 *
 * ## Design — one engine, multiple callers
 *
 * The {@link renameNet} entry point is specialised to the rename pass: it
 * allocates fresh prefixed places via the `place(name)` factory, records the
 * old-to-new mapping in caller-supplied `Map`s (so callers can build
 * port/channel handle maps), and emits a renamed `PetriNet`. The arc-rewrite
 * helpers ({@link rewriteIn}, {@link rewriteOut}, etc.) are factored out so
 * the future `compose(...)` caller can substitute port-place mappings against
 * an arbitrary remap without renaming everything.
 *
 * ## Performance — V8 hidden-class stability
 *
 * - Places are constructed exclusively via the existing `place<T>(name)`
 *   factory (from `core/place.ts`) so V8 can settle a single hidden class for
 *   all `Place` allocations. We never synthesize `{name: ...}` literals
 *   inline.
 * - Arcs are constructed via the existing `inputArc`, `inhibitorArc`,
 *   `readArc`, `resetArc`, `outPlace`, `forwardInput`, `timeout` factories;
 *   `In` shapes go through `one`, `exactly`, `all`, `atLeast`.
 * - The recursive `Out.And` / `Out.Xor` reconstruction uses pre-sized
 *   `Array<Out>` plus a `for` loop (parallel to the Java perf reasoning about
 *   `Stream` overhead — see `SubnetRewriter.rewriteOut`). `Array.prototype.map`
 *   is avoided on this hot path.
 * - The `inputs(...)` rest-parameter into `TransitionBuilder.inputs` does
 *   create a shallow array copy internally; this matches Java's
 *   `Arc.In[t.inputSpecs().size()]` allocation and is the minimum allocation
 *   needed to land arcs in the builder's defensive copy.
 *
 * Specified by `spec/11-modular-composition.md` MOD-010, MOD-011, MOD-012,
 * MOD-013, MOD-020, MOD-030.
 */

import type { Place } from '../place.js';
import { place } from '../place.js';
import type { ArcInhibitor, ArcRead, ArcReset } from '../arc.js';
import type { In } from '../in.js';
import { one, exactly, all, atLeast } from '../in.js';
import type { Out } from '../out.js';
import { and, outPlace, forwardInput, timeout, allPlaces } from '../out.js';
import { PetriNet } from '../petri-net.js';
import { Transition } from '../transition.js';
import type { MatchSpec } from '../match-spec.js';
import type { Timing } from '../timing.js';
import type { TransitionAction } from '../transition-action.js';
import { isPassthrough } from '../transition-action.js';

// ============================================================
//  Public entry points
// ============================================================

/**
 * Returns a renamed copy of `orig`: same generic token type at the type
 * level, with `prefix + "/" + orig.name` as the new name. Goes through the
 * `place<T>(name)` factory for V8 hidden-class stability.
 */
export function renamePlace<T>(orig: Place<T>, prefix: string): Place<T> {
  return place<T>(prefix + '/' + orig.name);
}

/**
 * Renames every place and transition of `body`, prefixing each name with
 * `prefix + "/"`.
 *
 * **Side effects**: fills the two supplied maps so the caller can resolve
 * original-place / original-transition references against the rewritten
 * equivalents:
 *
 * - `placeRemap` — original place **name** → renamed place
 * - `transitionRemap` — original transition **name** → renamed transition
 *
 * Both maps are cleared on entry, then populated in iteration order.
 *
 * Note: the maps are keyed by name strings (not Place / Transition object
 * identity) because TypeScript Place identity is name-based per
 * `runtime/compiled-net.ts` (`Map<string, number>`). This matches how the
 * compiled net dedupes places.
 *
 * @param body            the subnet body to rewrite
 * @param prefix          the rename prefix
 * @param placeRemap      caller-allocated map filled with old-name → new place
 * @param transitionRemap caller-allocated map filled with old-name → new transition
 * @returns a fresh `PetriNet` whose name is `prefix + "/" + body.name` and
 *          whose places/transitions are renamed copies
 */
export function renameNet(
  body: PetriNet,
  prefix: string,
  placeRemap: Map<string, Place<unknown>>,
  transitionRemap: Map<string, Transition>,
): PetriNet {
  placeRemap.clear();
  transitionRemap.clear();

  // Pass 1: rename every place. We must do this before transitions so arc
  // rewriting can resolve every place reference unambiguously.
  for (const orig of body.places) {
    placeRemap.set(orig.name, renamePlace(orig as Place<unknown>, prefix));
  }

  // Pass 2: rebuild every transition with arcs rewritten via placeRemap.
  const builder = PetriNet.builder(prefix + '/' + body.name);

  // Add places explicitly: some may not be referenced by any transition arc,
  // but were declared on the body — preserve that membership.
  for (const renamedPlace of placeRemap.values()) {
    builder.place(renamedPlace);
  }

  for (const t of body.transitions) {
    const renamed = rewriteTransition(t, prefix, placeRemap);
    transitionRemap.set(t.name, renamed);
    builder.transition(renamed);
  }

  return builder.build();
}

/**
 * Rebuilds `t` with name `prefix + "/" + t.name` and every arc rewritten
 * through `placeRemap`. Timing, priority, and action are carried through by
 * reference (action sharing per **MOD-030**).
 *
 * If a place referenced by an arc is not present in `placeRemap` (keyed by
 * original name), the arc retains the original place — partial remaps are
 * valid (used by the future `compose(...)` caller).
 */
export function rewriteTransition(
  t: Transition,
  prefix: string,
  placeRemap: Map<string, Place<unknown>>,
): Transition {
  return rebuildWithName(t, prefix + '/' + t.name, placeRemap);
}

/**
 * Rebuilds `t` with the **same** name, substituting every arc place reference
 * through `remap`. Timing, priority, and action are carried through by
 * reference (action sharing per **MOD-030**).
 *
 * This is the rewrite primitive used by `PetriNetBuilder.compose(...)` (task
 * #12) when merging an instance's renamed body into an enclosing net: the
 * transition's prefixed name is already unique within the host (per
 * [MOD-010]), so no further renaming is needed — only port-place references
 * are substituted with the caller's places.
 *
 * If a place referenced by an arc is not present in `remap`, the arc retains
 * the original place — partial remaps are valid.
 */
export function substitutePlaces(
  t: Transition,
  remap: Map<string, Place<unknown>>,
): Transition {
  return rebuildWithName(t, t.name, remap);
}

// ============================================================
//  Shared transition-rebuild implementation
// ============================================================

/**
 * Shared implementation: rebuilds `t` with the supplied `name` and arc places
 * rewritten through `remap`. Used by both {@link rewriteTransition} (which
 * prefixes the name) and {@link substitutePlaces} (which keeps the name
 * unchanged).
 */
function rebuildWithName(
  t: Transition,
  name: string,
  remap: Map<string, Place<unknown>>,
): Transition {
  const builder = Transition.builder(name)
    .timing(t.timing)
    .priority(t.priority)
    .action(t.action);

  // Build the declared→actual place correspondence (MOD-031) from the same
  // `remap` the arcs are rewritten through, chaining any pre-existing alias so
  // nested instantiation ([MOD-013]) resolves declared → final composed place.
  const alias = buildPlaceAlias(t, remap);
  if (alias.size > 0) {
    builder.placeAlias(alias);
  }

  if (t.inputSpecs.length > 0) {
    // Pre-size for V8 hidden-class stability; for-loop over Stream.map.
    const rewrittenInputs = new Array<In>(t.inputSpecs.length);
    for (let i = 0; i < t.inputSpecs.length; i++) {
      rewrittenInputs[i] = rewriteIn(t.inputSpecs[i]!, remap);
    }
    builder.inputs(...rewrittenInputs);
  }

  if (t.outputSpec !== null) {
    builder.outputs(rewriteOut(t.outputSpec, remap));
  }

  for (let i = 0; i < t.inhibitors.length; i++) {
    builder.inhibitor(rewriteInhibitor(t.inhibitors[i]!, remap).place);
  }
  for (let i = 0; i < t.reads.length; i++) {
    builder.read(rewriteRead(t.reads[i]!, remap).place);
  }
  for (let i = 0; i < t.resets.length; i++) {
    builder.reset(rewriteReset(t.resets[i]!, remap).place);
  }

  // Carry the ν-net join correlation forward, following place renames so a
  // composed join still correlates the right (renamed) inputs (NU-020/-030).
  if (t.matchSpec !== null) {
    builder.match({
      keys: t.matchSpec.keys.map(k => ({
        place: remap.get(k.place.name) ?? k.place,
        key: k.key,
      })),
    });
  }

  return builder.build();
}

// ============================================================
//  Declared→actual place correspondence (MOD-031)
// ============================================================

/**
 * Builds the per-transition **declared → actual** place correspondence (per
 * **MOD-031**) for a transition being rewritten through `remap`, keyed by the
 * author-original declared place **name** → actual composed place. Mirrors the
 * Rust `build_local_name_map` / Java `buildPlaceAlias` algorithm so all three
 * implementations agree.
 *
 * **Chained path** — when `t` already carries a non-empty alias (from an
 * earlier rewrite pass: nested instantiation [MOD-013], or
 * instantiate-then-compose), each `declaredName → prev` entry is carried
 * forward as `declaredName → (remap.get(prev.name) ?? prev)`; identity results
 * are dropped. The arcs are deliberately **not** walked in this case — their
 * places are intermediate-pass names, not author-original, so recording them
 * would leak intermediate keys the user never declared.
 *
 * **First-pass path** — when `t` carries no alias, every arc place maps to its
 * remapped place keyed by the author-original name; identity entries are
 * skipped. The ForwardInput `from` is captured via the input walk and its `to`
 * via {@link allPlaces}.
 */
function buildPlaceAlias(
  t: Transition,
  remap: Map<string, Place<unknown>>,
): ReadonlyMap<string, Place<unknown>> {
  const prev = t.placeAlias;
  if (remap.size === 0 && prev.size === 0) {
    return EMPTY_ALIAS;
  }

  const alias = new Map<string, Place<unknown>>();

  if (prev.size > 0) {
    for (const [declaredName, prevActual] of prev) {
      const replaced = remap.get(prevActual.name);
      const finalActual = replaced !== undefined ? replaced : prevActual;
      if (finalActual.name !== declaredName) {
        alias.set(declaredName, finalActual);
      }
    }
    return alias;
  }

  const record = (p: Place<unknown>): void => {
    if (alias.has(p.name)) return;
    const replaced = remap.get(p.name);
    if (replaced !== undefined && replaced.name !== p.name) {
      alias.set(p.name, replaced);
    }
  };
  for (const spec of t.inputSpecs) record(spec.place as Place<unknown>);
  for (const rd of t.reads) record(rd.place as Place<unknown>);
  for (const inh of t.inhibitors) record(inh.place as Place<unknown>);
  for (const rs of t.resets) record(rs.place as Place<unknown>);
  if (t.outputSpec !== null) {
    for (const p of allPlaces(t.outputSpec)) record(p as Place<unknown>);
  }
  return alias;
}

/** @internal Shared empty correspondence for the no-op rewrite case. */
const EMPTY_ALIAS: ReadonlyMap<string, Place<unknown>> = new Map();

// ============================================================
//  Arc rewrite helpers (exhaustive switches — no default)
// ============================================================

/**
 * Rewrites an {@link In} via the place remap. Exhaustive `switch` over the
 * discriminated union variants `one`, `exactly`, `all`, `at-least`. Guards are
 * carried through by reference.
 */
export function rewriteIn(spec: In, remap: Map<string, Place<unknown>>): In {
  switch (spec.type) {
    case 'one':
      return one(resolve(spec.place, remap), spec.guard);
    case 'exactly':
      return exactly(spec.count, resolve(spec.place, remap), spec.guard);
    case 'all':
      return all(resolve(spec.place, remap), spec.guard);
    case 'at-least':
      return atLeast(spec.minimum, resolve(spec.place, remap), spec.guard);
  }
}

/**
 * Rewrites an {@link Out} via the place remap. Exhaustive recursive `switch`
 * over the discriminated union variants `place`, `forward-input`, `and`, `xor`,
 * `timeout`.
 *
 * `and` / `xor` traversal uses explicit pre-sized `Array<Out>` + indexed
 * `for` (no `Array.prototype.map`) per the perf notes on this module.
 */
export function rewriteOut(out: Out, remap: Map<string, Place<unknown>>): Out {
  switch (out.type) {
    case 'place':
      return outPlace(resolve(out.place, remap));

    case 'forward-input':
      return forwardInput(resolve(out.from, remap), resolve(out.to, remap));

    case 'and': {
      const children = out.children;
      const rewritten = new Array<Out>(children.length);
      for (let i = 0; i < children.length; i++) {
        rewritten[i] = rewriteOut(children[i]!, remap);
      }
      // Reconstruct via the same shape the `and(...)` factory produces. We
      // skip the factory's variadic spread on this hot path; the resulting
      // shape is identical.
      return { type: 'and', children: rewritten };
    }

    case 'xor': {
      const children = out.children;
      const rewritten = new Array<Out>(children.length);
      for (let i = 0; i < children.length; i++) {
        rewritten[i] = rewriteOut(children[i]!, remap);
      }
      return { type: 'xor', children: rewritten };
    }

    case 'timeout':
      return timeout(out.afterMs, rewriteOut(out.child, remap));
  }
}

/** Rewrites an {@link ArcInhibitor} via the place remap. */
export function rewriteInhibitor(
  inh: ArcInhibitor,
  remap: Map<string, Place<unknown>>,
): ArcInhibitor {
  return { type: 'inhibitor', place: resolve(inh.place, remap) };
}

/** Rewrites an {@link ArcRead} via the place remap. */
export function rewriteRead(
  rd: ArcRead,
  remap: Map<string, Place<unknown>>,
): ArcRead {
  return { type: 'read', place: resolve(rd.place, remap) };
}

/** Rewrites an {@link ArcReset} via the place remap. */
export function rewriteReset(
  rs: ArcReset,
  remap: Map<string, Place<unknown>>,
): ArcReset {
  return { type: 'reset', place: resolve(rs.place, remap) };
}

// ============================================================
//  Resolution helper
// ============================================================

/**
 * Looks up `p` in `remap` by `p.name`; returns the original if absent
 * (partial-remap semantics for the future `compose` caller).
 *
 * The unchecked cast is safe at runtime: TypeScript erases generics, and the
 * remap is populated by {@link renamePlace}, which preserves the token type
 * by construction (the renamed Place carries the same `T` at the type level
 * via the `place<T>(name)` factory). Future callers that put non-rename
 * mappings in must preserve the same invariant.
 */
function resolve<T>(p: Place<T>, remap: Map<string, Place<unknown>>): Place<T> {
  const replaced = remap.get(p.name);
  return replaced !== undefined ? (replaced as Place<T>) : p;
}

// ============================================================
//  Channel composition: transition merge (MOD-021)
// ============================================================

/**
 * Merges a caller-side transition with an instance-side (renamed) channel
 * transition into a single {@link Transition} per **MOD-021**.
 *
 * ## Merge semantics
 *
 * - **Identity / name** — caller-wins. The merged transition's name is
 *   `mergedName` (typically `caller.name`), so the merged transition remains
 *   discoverable from caller-side code paths.
 * - **Arcs** — input/inhibitor/read/reset arcs are unioned: caller-side first,
 *   then instance-side. Duplicates (by structural key — same arc kind +
 *   place name) are deduped so identical arcs to a shared place collapse.
 * - **Output spec** — if both sides carry an output spec, they are wrapped
 *   under a single new outer `OutAnd(caller, instance)` so both sides' outputs
 *   fire on a successful merged firing. If only one side has an output spec,
 *   that one wins. If neither side has one, the merged transition has none.
 *   `OutAnd` permits heterogeneous children (recursive trees), so wrapping a
 *   possibly-`OutAnd` child under a new outer `OutAnd` is structurally legal.
 * - **Timing** — see {@link mergeTimings}. Caller wins when one side is
 *   `Immediate`; equal non-`Immediate` timings collapse; conflicting
 *   non-`Immediate` timings throw.
 * - **Priority** — see {@link pickPriority}. Caller-side wins (policy, not a
 *   bug).
 * - **Action** — see {@link composeActions}. Sequential composition: caller-
 *   side action runs first, then on its completion the instance-side action
 *   runs against the same {@link import('../transition-context.js').TransitionContext}.
 *   The runtime sees one transition firing per [CORE-021] / [EXEC-001].
 *
 * @throws when timings conflict (per [MOD-021]) — the message names the
 *         channel and both timings so users can resolve it explicitly.
 */
export function mergeTransitions(
  caller: Transition,
  instance: Transition,
  mergedName: string,
): Transition {
  if (mergedName === undefined || mergedName === null || mergedName.length === 0) {
    throw new Error('mergeTransitions: mergedName must be a non-empty string');
  }

  // Resolve timing / match / alias first so any conflict short-circuits before
  // building. The ν-net match and MOD-031 alias are carried as-is: both sides
  // already reference final host places at merge time (upstream substitutePlaces
  // remapped them, match included), so no further remap here.
  const mergedTiming = mergeTimings(caller.timing, instance.timing, mergedName);
  const mergedPriority = pickPriority(caller.priority, instance.priority);
  const mergedAction = composeActions(caller.action, instance.action);
  const mergedMatch = mergeMatchSpecs(caller.matchSpec, instance.matchSpec, mergedName);
  const mergedAlias = mergePlaceAlias(caller.placeAlias, instance.placeAlias, mergedName);

  const builder = Transition.builder(mergedName)
    .timing(mergedTiming)
    .priority(mergedPriority);
  if (mergedAction !== undefined) {
    builder.action(mergedAction);
  }

  // Inputs: union caller-first, then instance, dedup by (kind, place name,
  // count/minimum where applicable). Guard predicates are reference-compared
  // — two equal-shaped arcs with different guard closures are treated as
  // distinct (the safest default, matching Java's record-equality dedupe
  // when guards are absent and conservatively avoiding silent guard merges).
  const unionedInputs = unionArcs<In>(caller.inputSpecs, instance.inputSpecs, keyOfIn);
  if (unionedInputs.length > 0) {
    builder.inputs(...unionedInputs);
  }

  // Outputs: wrap both sides under OutAnd; one-sided wins; none -> none.
  const mergedOutput = mergeOutputs(caller.outputSpec, instance.outputSpec);
  if (mergedOutput !== null) {
    builder.outputs(mergedOutput);
  }

  // Inhibitors / reads / resets: arc-record union (caller first, then instance).
  for (const inh of unionArcs<ArcInhibitor>(
    caller.inhibitors,
    instance.inhibitors,
    keyOfInhibitor,
  )) {
    builder.inhibitor(inh.place);
  }
  for (const rd of unionArcs<ArcRead>(caller.reads, instance.reads, keyOfRead)) {
    builder.read(rd.place);
  }
  for (const rs of unionArcs<ArcReset>(caller.resets, instance.resets, keyOfReset)) {
    builder.reset(rs.place);
  }

  // Apply the ν-net match (NU-060) and the MOD-031 declared→actual place map
  // (both resolved above, before any building, so a conflict on either
  // short-circuits with no wasted arc-union work).
  if (mergedMatch !== null) {
    builder.match(mergedMatch);
  }
  if (mergedAlias.size > 0) {
    builder.placeAlias(mergedAlias);
  }

  return builder.build();
}

/**
 * Carries the ν-net join correlation ({@link MatchSpec}) through a channel merge
 * per **NU-060**. One-sided → that side's match survives; both-null → none; both
 * non-null → the merge is rejected, because two independent name correlations
 * cannot be silently fused into one transition and NU-060 forbids dropping a
 * match. The surviving match is returned as-is: both transitions already
 * reference final host places at merge time, so no place remap is applied here
 * (unlike {@link rebuildWithName}).
 */
function mergeMatchSpecs(
  caller: MatchSpec | null,
  instance: MatchSpec | null,
  channelName: string,
): MatchSpec | null {
  if (caller === null) return instance;
  if (instance === null) return caller;
  throw new Error(
    `Channel composition '${channelName}': both the caller-side and instance-side ` +
      `transition carry a ν-net match — refusing to fuse two independent correlations ` +
      `into one transition (NU-060). Resolve explicitly by keeping the match on a single side.`,
  );
}

/**
 * Unions the two sides' MOD-031 declared→actual place correspondences for a
 * channel merge. Both actions run within the single merged firing, so each
 * side's declared-place resolution must survive. Disjoint keys union; an entry
 * present on both sides with the same actual collapses; a genuine conflict (same
 * declared place bound to two different actual places, compared by place name)
 * is rejected naming the declared place.
 */
function mergePlaceAlias(
  caller: ReadonlyMap<string, Place<any>>,
  instance: ReadonlyMap<string, Place<any>>,
  channelName: string,
): ReadonlyMap<string, Place<any>> {
  if (caller.size === 0) return instance;
  if (instance.size === 0) return caller;
  const merged = new Map<string, Place<any>>(caller);
  for (const [declared, actual] of instance) {
    const existing = merged.get(declared);
    if (existing !== undefined && existing.name !== actual.name) {
      throw new Error(
        `Channel composition '${channelName}': conflicting declared→actual place alias ` +
          `for declared place '${declared}' — caller-side maps to '${existing.name}', ` +
          `instance-side to '${actual.name}' (MOD-031). Resolve explicitly.`,
      );
    }
    merged.set(declared, actual);
  }
  return merged;
}

/**
 * Merges two timings per **MOD-021**:
 *
 * - Both `Immediate` -> `Immediate`.
 * - One `Immediate` -> the other side wins.
 * - Both non-`Immediate` and equal (by structural inspection of the timing
 *   variant fields) -> that value collapses.
 * - Otherwise the conflict is rejected with an `Error` naming the channel
 *   and both timings — the user must resolve it explicitly.
 */
export function mergeTimings(caller: Timing, instance: Timing, channelName: string): Timing {
  if (caller.type === 'immediate' && instance.type === 'immediate') {
    return { type: 'immediate' };
  }
  if (caller.type === 'immediate') return instance;
  if (instance.type === 'immediate') return caller;
  if (timingsEqual(caller, instance)) return caller;
  throw new Error(
    `Channel composition '${channelName}': conflicting non-Immediate timings — ` +
      `caller-side ${describeTiming(caller)} vs instance-side ${describeTiming(instance)}. ` +
      `Resolve explicitly by aligning the timings on either side (MOD-021).`,
  );
}

/**
 * Caller-side priority wins per **MOD-021**. Documented as policy: the
 * instance-side priority is ignored, not blended.
 */
export function pickPriority(callerPriority: number, _instancePriority: number): number {
  return callerPriority;
}

/**
 * Composes two transition actions sequentially: the caller-side action runs
 * first, then on its resolution the instance-side action runs against the same
 * {@link import('../transition-context.js').TransitionContext}. The combined
 * action surfaces a single `Promise<void>` so the executor sees one
 * transition firing per [CORE-021] / [EXEC-001].
 *
 * Null / passthrough handling:
 * - If both sides are `undefined` or both are `passthrough`, returns
 *   `undefined` so {@link mergeTransitions} leaves the builder's default
 *   passthrough action in place.
 * - If exactly one side is `undefined` / passthrough, the other side is
 *   returned by reference (no extra wrapping).
 * - Otherwise returns a fresh sequential composition.
 *
 * Note: the production {@link Transition.builder} defaults action to
 * {@link import('../transition-action.js').passthrough}, so the `undefined`
 * branches are defensive — they exist so this helper is robust if upstream
 * surfaces a literal `undefined` action.
 */
export function composeActions(
  caller: TransitionAction | undefined,
  instance: TransitionAction | undefined,
): TransitionAction | undefined {
  const callerIsPassthrough = caller === undefined || isPassthrough(caller);
  const instanceIsPassthrough = instance === undefined || isPassthrough(instance);

  if (callerIsPassthrough && instanceIsPassthrough) return undefined;
  if (callerIsPassthrough) return instance;
  if (instanceIsPassthrough) return caller;
  return async (ctx) => {
    await caller!(ctx);
    await instance!(ctx);
  };
}

/**
 * Combines two output specs per the merge contract: if both are present,
 * wrap them under a single {@link import('../out.js').OutAnd}; otherwise
 * return the non-null side (or `null` if both are missing).
 *
 * Exported (via the surrounding module's re-export surface) for unit testing
 * and for parity with the Java internal helper.
 */
export function mergeOutputs(caller: Out | null, instance: Out | null): Out | null {
  if (caller === null && instance === null) return null;
  if (caller === null) return instance;
  if (instance === null) return caller;
  return and(caller, instance);
}

/**
 * Returns the union of two arc lists, caller-first then instance, with
 * duplicates removed by structural key. Order is preserved within each
 * source list. Used for input, inhibitor, read, and reset arcs.
 *
 * Implementation: `Map<string, A>` preserves insertion order and dedupes by
 * the supplied key function. TypeScript arc records are POJOs — there is no
 * built-in structural equality, so callers must supply a key derived from
 * the discriminating fields (kind + place name + cardinality where
 * applicable).
 */
export function unionArcs<A>(
  caller: readonly A[],
  instance: readonly A[],
  keyOf: (arc: A) => string,
): A[] {
  if (caller.length === 0 && instance.length === 0) return [];
  // Pre-size for V8 hidden-class stability; Map preserves insertion order
  // and dedupes by string key, mirroring Java's LinkedHashSet semantics.
  const seen = new Map<string, A>();
  for (let i = 0; i < caller.length; i++) {
    const arc = caller[i]!;
    const key = keyOf(arc);
    if (!seen.has(key)) seen.set(key, arc);
  }
  for (let i = 0; i < instance.length; i++) {
    const arc = instance[i]!;
    const key = keyOf(arc);
    if (!seen.has(key)) seen.set(key, arc);
  }
  const result = new Array<A>(seen.size);
  let i = 0;
  for (const arc of seen.values()) result[i++] = arc;
  return result;
}

// ============================================================
//  Internal helpers (timings, arc keys, action introspection)
// ============================================================

/**
 * Structural equality for two non-`Immediate` timings. Used by
 * {@link mergeTimings} to collapse equal timings into a single value
 * (mirrors Java's `record.equals`).
 */
function timingsEqual(a: Timing, b: Timing): boolean {
  if (a.type !== b.type) return false;
  switch (a.type) {
    case 'immediate':
      return true;
    case 'deadline':
      return a.byMs === (b as typeof a).byMs;
    case 'delayed':
      return a.afterMs === (b as typeof a).afterMs;
    case 'window': {
      const w = b as typeof a;
      return a.earliestMs === w.earliestMs && a.latestMs === w.latestMs;
    }
    case 'exact':
      return a.atMs === (b as typeof a).atMs;
  }
}

/** Human-readable timing description for the conflict-diagnostic message. */
function describeTiming(t: Timing): string {
  switch (t.type) {
    case 'immediate':
      return 'Immediate';
    case 'deadline':
      return `Deadline(byMs=${t.byMs})`;
    case 'delayed':
      return `Delayed(afterMs=${t.afterMs})`;
    case 'window':
      return `Window(earliestMs=${t.earliestMs}, latestMs=${t.latestMs})`;
    case 'exact':
      return `Exact(atMs=${t.atMs})`;
  }
}

/**
 * Structural key for an {@link In} arc. Encodes the discriminant + place
 * name + cardinality (where applicable). Guard predicates are NOT folded
 * into the key — two arcs of the same shape with different guard closures
 * are treated as distinct (the safe default).
 */
function keyOfIn(arc: In): string {
  switch (arc.type) {
    case 'one':
      return arc.guard === undefined
        ? `one|${arc.place.name}`
        : `one|${arc.place.name}|g:${guardKey(arc.guard)}`;
    case 'exactly':
      return arc.guard === undefined
        ? `exactly|${arc.place.name}|${arc.count}`
        : `exactly|${arc.place.name}|${arc.count}|g:${guardKey(arc.guard)}`;
    case 'all':
      return arc.guard === undefined
        ? `all|${arc.place.name}`
        : `all|${arc.place.name}|g:${guardKey(arc.guard)}`;
    case 'at-least':
      return arc.guard === undefined
        ? `atLeast|${arc.place.name}|${arc.minimum}`
        : `atLeast|${arc.place.name}|${arc.minimum}|g:${guardKey(arc.guard)}`;
  }
}

function keyOfInhibitor(arc: ArcInhibitor): string {
  return `inh|${arc.place.name}`;
}
function keyOfRead(arc: ArcRead): string {
  return `read|${arc.place.name}`;
}
function keyOfReset(arc: ArcReset): string {
  return `reset|${arc.place.name}`;
}

/**
 * Identity-only key for guard closures. Two distinct closure references
 * yield distinct keys; reusing the same closure across arcs collapses them.
 * We use a WeakMap so guard closures don't hold extra retention, and the
 * counter assigned per closure is stable across calls within one process.
 */
const GUARD_KEYS = new WeakMap<object, string>();
let guardKeyCounter = 0;
function guardKey(g: object): string {
  let k = GUARD_KEYS.get(g);
  if (k === undefined) {
    k = String(++guardKeyCounter);
    GUARD_KEYS.set(g, k);
  }
  return k;
}

// ============================================================
//  Fusion: bulk place substitution across a transition set (MOD-061)
// ============================================================

/**
 * Applies a fusion remap to every transition in `transitions`, substituting
 * non-canonical → canonical place references in each transition's arcs.
 * Returns a fresh insertion-ordered `Set<Transition>`; the input collection
 * is not mutated.
 *
 * This is the loop wrapper around {@link substitutePlaces}; it exists so
 * callers — notably `PetriNetBuilder.build()` during fusion resolution per
 * **MOD-061** — do not duplicate the per-transition dispatch. Transitions
 * whose arcs do not reference any key of `fusionMap` pass through unchanged
 * in shape but are still rebuilt by {@link substitutePlaces} (a fresh
 * `Transition` instance); callers that care about identity preservation for
 * un-affected transitions should instead skip the rewrite entirely when
 * `fusionMap.size === 0`.
 *
 * The remap is keyed by **non-canonical place name** → **canonical place**
 * (matching the `Map<string, Place<unknown>>` key convention used throughout
 * this module — TypeScript Place identity is name-based per
 * `runtime/compiled-net.ts`).
 *
 * @param transitions the transitions to rewrite (non-null, may be empty)
 * @param fusionMap   non-canonical name → canonical place remap (non-null)
 * @returns a fresh, insertion-ordered set of rewritten transitions
 */
export function applyFusion(
  transitions: Iterable<Transition>,
  fusionMap: Map<string, Place<unknown>>,
): Set<Transition> {
  const rewritten = new Set<Transition>();
  for (const t of transitions) {
    rewritten.add(substitutePlaces(t, fusionMap));
  }
  return rewritten;
}
