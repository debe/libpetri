/**
 * @module abstract-replayer
 *
 * Pure TS-side replayer for Spacer counterexamples over the ABSTRACT
 * (untimed, value-blind) count-vector semantics — the exact semantics the CHC
 * encoder emits and the Lean development verifies:
 *
 * - {@link enabledA} mirrors `lean/Libpetri/Basic.lean` `enabledA` and the
 *   encoder's `encodeEnabled` arm (smt-encoder.ts): every input place holds at
 *   least `pre[p]` tokens, every inhibited place is empty, every read place is
 *   non-empty.
 * - {@link fireA} mirrors `Basic.lean` `fireA` and the encoder's `encodeFire`
 *   arm: a reset or consume-all (`All`/`AtLeast`) place jumps to `post[p]`;
 *   every other place moves by `M[p] - pre[p] + post[p]`.
 * - {@link successors} mirrors one disjunct of `encodeStepRelation`: a firing
 *   is a successor only when its `M'` also respects `environmentBounds` (the
 *   `envBounds(M')` conjunct every transition disjunct carries), and one
 *   injection per modeled environment place whose guard admits it.
 * - {@link injectA} mirrors `encodeInjectionFire`/`encodeInjectionGuard`
 *   (VER-006): one environment injection adds one token to the env place,
 *   gated by `M[p] < k` for `Bounded(k)` and unguarded for `AlwaysAvailable`.
 * - {@link satisfiesBad} mirrors `encodePropertyViolation` — including the
 *   relax-env deadlock enablement and the declared-sink exemption — as a
 *   direct TS evaluator, so confirming a counterexample never needs a Z3 call.
 *
 * Because the abstraction over-approximates the concrete timed/valued net
 * (VER-004), a decoded counterexample can be spurious. This module therefore
 * only ever REPORTS an outcome ({@link ReplayOutcome}) — nothing here is
 * allowed to certify by crashing, and only the `no-chain` outcome (a fully
 * explored search that found no chain) is strong enough to withdraw a verdict.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { SmtProperty } from '../smt-property.js';
import type { Place } from '../../core/place.js';
import { MarkingState } from '../marking-state.js';
import { flatNetIndexOf } from '../encoding/flat-net.js';

/** An abstract marking: token count per flat place index. */
export type AbstractState = readonly number[];

/** One abstract step in a replayed chain. */
export type ReplayStep =
  | { readonly kind: 'fire'; readonly transition: string }
  | { readonly kind: 'inject'; readonly place: string };

/** Display name for a step: the flat transition name, or `inject(<place>)`. */
export function stepName(step: ReplayStep): string {
  return step.kind === 'fire' ? step.transition : `inject(${step.place})`;
}

/** Canonical key for an abstract state (place counts joined by comma). */
export function stateKey(state: AbstractState): string {
  return state.join(',');
}

/** Projects a MarkingState onto the flat place indexing as a count vector. */
export function vectorize(marking: MarkingState, flatNet: FlatNet): number[] {
  return flatNet.places.map(p => marking.tokens(p));
}

/** Rebuilds a MarkingState from a count vector (inverse of {@link vectorize}). */
export function toMarkingState(state: AbstractState, flatNet: FlatNet): MarkingState {
  const builder = MarkingState.builder();
  for (let i = 0; i < flatNet.places.length; i++) {
    if (state[i]! > 0) builder.tokens(flatNet.places[i]!, state[i]!);
  }
  return builder.build();
}

/**
 * Abstract enablement (`Basic.lean` `enabledA`; encoder `encodeEnabled` with
 * `relaxEnv = false`): `M[p] >= pre[p]` per input, `M[p] = 0` per inhibitor,
 * `M[p] >= 1` per read. The encoder's non-negativity conjunct is invariant
 * here (states start in ℕ^P and every step preserves it), so it is not
 * re-checked.
 */
export function enabledA(state: AbstractState, ft: FlatTransition): boolean {
  const P = state.length;
  for (let p = 0; p < P; p++) {
    if (ft.preVector[p]! > 0 && state[p]! < ft.preVector[p]!) return false;
  }
  for (const p of ft.readPlaces) {
    if (state[p]! < 1) return false;
  }
  for (const p of ft.inhibitorPlaces) {
    if (state[p]! !== 0) return false;
  }
  return true;
}

/**
 * The abstract fire relation (`Basic.lean` `fireA`; encoder `encodeFire`):
 *
 * - reset place        → `M'[p] = post[p]`
 * - consume-all place  → `M'[p] = post[p]` (All/AtLeast drain the place)
 * - otherwise          → `M'[p] = M[p] - pre[p] + post[p]`
 */
export function fireA(state: AbstractState, ft: FlatTransition): number[] {
  return fireIndexed(state, ft, new Set(ft.resetPlaces));
}

/** {@link fireA} with the transition's reset places already indexed. */
function fireIndexed(
  state: AbstractState,
  ft: FlatTransition,
  resets: ReadonlySet<number>,
): number[] {
  const P = state.length;
  const next = new Array<number>(P);
  for (let p = 0; p < P; p++) {
    if (resets.has(p) || ft.consumeAll[p]) {
      next[p] = ft.postVector[p]!;
    } else {
      next[p] = state[p]! - ft.preVector[p]! + ft.postVector[p]!;
    }
  }
  return next;
}

/**
 * One environment injection (encoder `encodeInjectionFire`): adds one token at
 * `idx`, all other places unchanged. Callers gate on the bound (VER-006).
 */
export function injectA(state: AbstractState, idx: number): number[] {
  const next = [...state];
  next[idx] = next[idx]! + 1;
  return next;
}

/** A successor state together with the step that produced it. */
export interface Successor {
  readonly state: number[];
  readonly step: ReplayStep;
}

/**
 * Per-replay indexes over a flat net, built once and reused by every expansion:
 * reset places per transition, the injection map, and the environment post-caps
 * every transition disjunct of the step relation carries.
 */
interface ReplayIndex {
  readonly flatNet: FlatNet;
  /** `resetSets[t]` — reset place indices of `flatNet.transitions[t]`. */
  readonly resetSets: readonly ReadonlySet<number>[];
  /** Injected env place index -> injection bound (`null` = unbounded). */
  readonly envInj: ReadonlyMap<number, number | null>;
  /** `environmentBounds` as `[place index, cap]` pairs: `M'[idx] <= cap`. */
  readonly envCaps: readonly (readonly [number, number])[];
}

function buildIndex(flatNet: FlatNet): ReplayIndex {
  const resetSets = flatNet.transitions.map(ft => new Set(ft.resetPlaces));
  const envInj = new Map<number, number | null>();
  for (const [name, bound] of flatNet.environmentInjection) {
    const idx = flatNet.placeIndex.get(name);
    if (idx != null) envInj.set(idx, bound);
  }
  const envCaps: [number, number][] = [];
  for (const [name, cap] of flatNet.environmentBounds) {
    const idx = flatNet.placeIndex.get(name);
    if (idx != null) envCaps.push([idx, cap]);
  }
  return { flatNet, resetSets, envInj, envCaps };
}

/** The `envBounds(M')` conjunct of every transition disjunct (smt-encoder.ts). */
function withinEnvBounds(index: ReplayIndex, state: AbstractState): boolean {
  for (const [idx, cap] of index.envCaps) {
    if (state[idx]! > cap) return false;
  }
  return true;
}

/**
 * All abstract successors of a state under the UNSTRENGTHENED step relation:
 * every enabled flat transition whose successor also respects the environment
 * post-caps, plus one injection per modeled environment place whose guard
 * admits it (`M[p] < k` for `Bounded(k)`, always for `AlwaysAvailable`).
 */
export function successors(state: AbstractState, flatNet: FlatNet): Successor[] {
  return successorsIndexed(buildIndex(flatNet), state);
}

function successorsIndexed(index: ReplayIndex, state: AbstractState): Successor[] {
  const out: Successor[] = [];
  const transitions = index.flatNet.transitions;
  for (let t = 0; t < transitions.length; t++) {
    const ft = transitions[t]!;
    if (!enabledA(state, ft)) continue;
    const next = fireIndexed(state, ft, index.resetSets[t]!);
    // The encoder conjoins envBounds(M') into every transition disjunct: a
    // firing that would push an environment place over its cap is NOT a step of
    // the encoded system, and chaining through one would confirm a trace the
    // CHC system cannot produce.
    if (!withinEnvBounds(index, next)) continue;
    out.push({ state: next, step: { kind: 'fire', transition: ft.name } });
  }
  for (const [name, bound] of index.flatNet.environmentInjection) {
    const idx = index.flatNet.placeIndex.get(name);
    if (idx == null) continue;
    if (bound === null || state[idx]! < bound) {
      out.push({ state: injectA(state, idx), step: { kind: 'inject', place: name } });
    }
  }
  return out;
}

/**
 * Relax-env enablement (encoder `encodeEnabled` with `relaxEnv = true`), used
 * only inside the deadlock predicate: input/read requirements on injectable
 * environment places are satisfiable by external injection — `AlwaysAvailable`
 * always, `Bounded(k)` iff the required cardinality is ≤ k.
 */
function enabledRelaxEnv(
  state: AbstractState,
  ft: FlatTransition,
  envInj: ReadonlyMap<number, number | null>,
): boolean {
  const P = state.length;
  for (let p = 0; p < P; p++) {
    const pre = ft.preVector[p]!;
    if (pre <= 0) continue;
    if (envInj.has(p)) {
      const bound = envInj.get(p)!;
      if (bound !== null && pre > bound) return false; // never enableable
      continue; // satisfiable by injection
    }
    if (state[p]! < pre) return false;
  }
  for (const p of ft.readPlaces) {
    if (envInj.has(p)) {
      const bound = envInj.get(p)!;
      if (bound !== null && bound < 1) return false;
      continue;
    }
    if (state[p]! < 1) return false;
  }
  for (const p of ft.inhibitorPlaces) {
    if (state[p]! !== 0) return false;
  }
  return true;
}

/**
 * Deadlock predicate (encoder `encodeDeadlock`): no flat transition is enabled
 * under relax-env semantics — a marking an external injection could re-enable
 * is NOT a deadlock (VER-006).
 */
function isDeadlockA(index: ReplayIndex, state: AbstractState): boolean {
  for (const ft of index.flatNet.transitions) {
    if (enabledRelaxEnv(state, ft, index.envInj)) return false;
  }
  return true;
}

/**
 * TS evaluator of the property-violation predicate `Bad(M)` — the direct
 * mirror of the encoder's `encodePropertyViolation`, including the declared
 * sink exemption for deadlock-freedom and the "unresolved place" edge cases
 * (unknown pending → never violated; unresolved unreachable places are
 * skipped, exactly as the encoder skips them).
 */
export function satisfiesBad(
  state: AbstractState,
  flatNet: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
): boolean {
  return satisfiesBadIndexed(buildIndex(flatNet), state, property, sinkPlaces);
}

function satisfiesBadIndexed(
  index: ReplayIndex,
  state: AbstractState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
): boolean {
  const flatNet = index.flatNet;
  switch (property.type) {
    case 'deadlock-free': {
      if (!isDeadlockA(index, state)) return false;
      for (const sink of sinkPlaces) {
        const idx = flatNetIndexOf(flatNet, sink);
        if (idx >= 0 && state[idx]! > 0) return false; // quiescent at a declared sink
      }
      return true;
    }
    case 'mutual-exclusion': {
      const idx1 = flatNetIndexOf(flatNet, property.p1);
      const idx2 = flatNetIndexOf(flatNet, property.p2);
      if (idx1 < 0 || idx2 < 0) return false; // encoder would have thrown before replay
      return state[idx1]! >= 1 && state[idx2]! >= 1;
    }
    case 'place-bound':
    case 'branch-place-bound': {
      const idx = flatNetIndexOf(flatNet, property.place);
      if (idx < 0) return false; // encoder would have thrown before replay
      return state[idx]! > property.bound;
    }
    case 'joined-or-dead-lettered': {
      const idx = flatNetIndexOf(flatNet, property.pending);
      if (idx < 0) return false; // mirror: unknown pending place is never a violation
      return isDeadlockA(index, state) && state[idx]! >= 1;
    }
    case 'unreachable': {
      let resolved = 0;
      for (const p of property.places) {
        const idx = flatNetIndexOf(flatNet, p);
        if (idx < 0) continue; // unresolved places skipped (encoder parity)
        resolved++;
        if (state[idx]! < 1) return false;
      }
      // With nothing resolved the conjunction would be vacuously true and EVERY
      // marking would violate — replay would then "confirm" at M0.
      return resolved > 0;
    }
  }
}

/** Options for {@link replayCounterexample}. */
export interface ReplayOptions {
  /** Max abstract steps searched between decoded anchors (default 3). */
  readonly segmentBudget?: number;
  /**
   * Max search nodes ADMITTED to the whole search (default 10_000).
   *
   * A node is admitted when it survives the segment budget and the domination
   * check; dominated successors are never admitted and never counted. The root
   * (`M₀`) counts as the first admitted node, and the search stops as soon as
   * `nodeBudget` nodes have been admitted and another one is due — the same
   * `>=`-before-admission rule the Rust and Java replayers apply, so the same
   * nominal budget means the same effective search depth in all of them.
   */
  readonly nodeBudget?: number;
}

/**
 * Outcome of an abstract replay attempt.
 *
 * `confirmed` — a genuine abstract chain `M₀ → … → Bad` was found.
 * `no-chain` — the search ran to completion without truncation and no chain
 * exists: the counterexample is spurious or the decoder mis-read the
 * derivation, and ONLY this outcome may withdraw a `violated` verdict.
 * `exhausted` — the search was cut short (node or segment budget, or `M₀` was
 * not among the decoded states), so nothing was proved either way.
 */
export type ReplayOutcome =
  | {
      readonly kind: 'confirmed';
      /** The replayed chain in FIRING order, `M₀ … M_bad` inclusive. */
      readonly states: readonly AbstractState[];
      /** One step per consecutive pair of {@link states}. */
      readonly steps: readonly ReplayStep[];
      readonly nodesExplored: number;
    }
  | { readonly kind: 'no-chain'; readonly nodesExplored: number }
  | { readonly kind: 'exhausted'; readonly reason: string; readonly nodesExplored: number };

/** One BFS node; the chain is recovered by walking `parent` back to the root. */
interface SearchNode {
  readonly state: AbstractState;
  /** The step that produced {@link state}; null at the root (`M₀`). */
  readonly step: ReplayStep | null;
  /** Index of the predecessor node, or -1 at the root. */
  readonly parent: number;
  /** Steps taken since the last decoded anchor (0 at an anchor). */
  readonly segment: number;
}

/**
 * Attempts to re-execute a decoded (order-free) counterexample state set in
 * the abstract semantics.
 *
 * The decoder collects Spacer's `Reachable` applications in derivation
 * TRAVERSAL order, which is not firing order; this search recovers a firing
 * order or reports that none exists. It is a single global breadth-first
 * search from `initial` over {@link successors}, where each node carries the
 * number of steps taken since the last decoded state (`segment`, reset to 0
 * whenever a decoded state is reached) and a node is expanded only while that
 * counter is below `segmentBudget`. A state is re-entered only when reached
 * with a strictly smaller segment counter (domination by `(state, segment)`),
 * and the whole search shares one `nodeBudget` counting nodes ADMITTED to the
 * search — non-dominated states only, the root included (see
 * {@link ReplayOptions.nodeBudget}).
 */
export function replayCounterexample(
  flatNet: FlatNet,
  initial: AbstractState,
  decodedStates: readonly AbstractState[],
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  options: ReplayOptions = {},
): ReplayOutcome {
  const segmentBudget = options.segmentBudget ?? 3;
  const nodeBudget = options.nodeBudget ?? 10_000;

  const anchors = new Set<string>();
  for (const s of decodedStates) anchors.add(stateKey(s));

  if (anchors.size === 0) {
    return { kind: 'exhausted', reason: 'no decoded states to replay', nodesExplored: 0 };
  }

  const initKey = stateKey(initial);
  if (!anchors.has(initKey)) {
    // Not evidence against the counterexample — the decoder simply did not
    // recover the init fact, so there is no anchored search to run.
    return {
      kind: 'exhausted',
      reason: 'the initial marking is not among the decoded states',
      nodesExplored: 0,
    };
  }

  const index = buildIndex(flatNet);
  if (satisfiesBadIndexed(index, initial, property, sinkPlaces)) {
    return { kind: 'confirmed', states: [initial], steps: [], nodesExplored: 1 };
  }

  const nodes: SearchNode[] = [{ state: initial, step: null, parent: -1, segment: 0 }];
  const bestSegment = new Map<string, number>([[initKey, 0]]);
  const queue: number[] = [0];
  let truncated = false;

  for (let head = 0; head < queue.length; head++) {
    const idx = queue[head]!;
    const node = nodes[idx]!;
    if (node.segment >= segmentBudget) {
      truncated = true; // the segment budget, not the state space, stopped us here
      continue;
    }
    for (const succ of successorsIndexed(index, node.state)) {
      const key = stateKey(succ.state);
      const segment = anchors.has(key) ? 0 : node.segment + 1;
      const prior = bestSegment.get(key);
      if (prior !== undefined && prior <= segment) continue; // dominated
      bestSegment.set(key, segment);

      // Checked BEFORE admission and with `>=`, so at most `nodeBudget` nodes
      // ever enter the search (the root among them) — same rule, same effective
      // depth, as the Rust and Java replayers.
      if (nodes.length >= nodeBudget) {
        return {
          kind: 'exhausted',
          reason: `search budget exhausted (${nodeBudget} nodes) before reaching a violating state`,
          nodesExplored: nodes.length,
        };
      }
      nodes.push({ state: succ.state, step: succ.step, parent: idx, segment });
      const childIdx = nodes.length - 1;
      if (satisfiesBadIndexed(index, succ.state, property, sinkPlaces)) {
        const chain = reconstruct(nodes, childIdx);
        return { kind: 'confirmed', ...chain, nodesExplored: nodes.length };
      }
      queue.push(childIdx);
    }
  }

  if (truncated) {
    return {
      kind: 'exhausted',
      reason:
        `no violating state within ${segmentBudget} abstract step(s) of a decoded state ` +
        `(${bestSegment.size} state(s) explored)`,
      nodesExplored: nodes.length,
    };
  }
  return { kind: 'no-chain', nodesExplored: nodes.length };
}

/** Walks `parent` links back to the root, yielding the chain in firing order. */
function reconstruct(
  nodes: readonly SearchNode[],
  last: number,
): { states: readonly AbstractState[]; steps: readonly ReplayStep[] } {
  const states: AbstractState[] = [];
  const steps: ReplayStep[] = [];
  for (let i = last; i >= 0; i = nodes[i]!.parent) {
    const node = nodes[i]!;
    states.push(node.state);
    if (node.step != null) steps.push(node.step);
  }
  states.reverse();
  steps.reverse();
  return { states, steps };
}
