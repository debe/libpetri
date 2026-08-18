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
 * - {@link injectA} mirrors `encodeInjectionFire`/`encodeInjectionGuard`
 *   (VER-006): one environment injection adds one token to the env place,
 *   gated by `M[p] < k` for `Bounded(k)` and unguarded for `AlwaysAvailable`.
 * - {@link satisfiesBad} mirrors `encodePropertyViolation` — including the
 *   relax-env deadlock enablement and the declared-sink exemption — as a
 *   direct TS evaluator, so confirming a counterexample never needs a Z3 call.
 *
 * Because the abstraction over-approximates the concrete timed/valued net
 * (VER-004), a decoded counterexample can be spurious. This module therefore
 * only ever REPORTS an outcome: {@link replayCounterexample} returns
 * `confirmed` or `unchainable`, and callers downgrade on failure — nothing
 * here is allowed to certify by crashing.
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

/** Display name for a step: the flat transition name, or `env:<place>` for injection. */
export function stepName(step: ReplayStep): string {
  return step.kind === 'fire' ? step.transition : `env:${step.place}`;
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
  const P = state.length;
  const next = new Array<number>(P);
  for (let p = 0; p < P; p++) {
    if (ft.resetPlaces.includes(p) || ft.consumeAll[p]) {
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
 * All abstract successors of a state: every enabled flat transition firing,
 * plus one injection per modeled environment place whose guard admits it
 * (`M[p] < k` for `Bounded(k)`, always for `AlwaysAvailable`).
 */
export function successors(state: AbstractState, flatNet: FlatNet): Successor[] {
  const out: Successor[] = [];
  for (const ft of flatNet.transitions) {
    if (enabledA(state, ft)) {
      out.push({ state: fireA(state, ft), step: { kind: 'fire', transition: ft.name } });
    }
  }
  for (const [name, bound] of flatNet.environmentInjection) {
    const idx = flatNet.placeIndex.get(name);
    if (idx == null) continue;
    if (bound === null || state[idx]! < bound) {
      out.push({ state: injectA(state, idx), step: { kind: 'inject', place: name } });
    }
  }
  return out;
}

/** Injected environment-place index -> bound (mirrors the encoder's map). */
function injectedEnvIndices(flatNet: FlatNet): Map<number, number | null> {
  const out = new Map<number, number | null>();
  for (const [name, bound] of flatNet.environmentInjection) {
    const idx = flatNet.placeIndex.get(name);
    if (idx != null) out.set(idx, bound);
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
  envInj: Map<number, number | null>,
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
function isDeadlockA(state: AbstractState, flatNet: FlatNet): boolean {
  const envInj = injectedEnvIndices(flatNet);
  for (const ft of flatNet.transitions) {
    if (enabledRelaxEnv(state, ft, envInj)) return false;
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
  switch (property.type) {
    case 'deadlock-free': {
      if (!isDeadlockA(state, flatNet)) return false;
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
      return isDeadlockA(state, flatNet) && state[idx]! >= 1;
    }
    case 'unreachable': {
      for (const p of property.places) {
        const idx = flatNetIndexOf(flatNet, p);
        if (idx >= 0 && state[idx]! < 1) return false; // unresolved places skipped (encoder parity)
      }
      return true;
    }
  }
}

/** Options for {@link replayCounterexample}. */
export interface ReplayOptions {
  /** Max abstract steps searched between consecutive decoded states (default 3). */
  readonly maxGap?: number;
  /** Total successor-expansion budget across the whole search (default 10_000). */
  readonly nodeBudget?: number;
}

/** Outcome of an abstract replay attempt. */
export type ReplayOutcome =
  | {
      readonly kind: 'confirmed';
      /** The replayed chain in FIRING order, `M₀ … M_bad` inclusive. */
      readonly states: readonly AbstractState[];
      /** One step per consecutive pair of {@link states}. */
      readonly steps: readonly ReplayStep[];
      readonly nodesExplored: number;
    }
  | {
      readonly kind: 'unchainable';
      readonly reason: string;
      readonly nodesExplored: number;
    };

interface WaypointPath {
  readonly states: AbstractState[];
  readonly steps: ReplayStep[];
}

/**
 * Attempts to re-execute a decoded (order-free) counterexample state set in
 * the abstract semantics.
 *
 * The decoder collects Spacer's `Reachable` applications in derivation
 * TRAVERSAL order, which is not firing order; this search recovers a firing
 * order or reports that none exists. Starting from `initial` (which must be in
 * the decoded set — Spacer derivations begin at the init fact), a BFS expands
 * at most `maxGap` abstract steps around each reached decoded state, treating
 * decoded states as waypoints; any explored state satisfying `Bad` completes
 * the chain. The whole search shares one `nodeBudget`.
 *
 * `confirmed` — a genuine abstract chain `M₀ → … → Bad` was found (the trace
 * to display, in firing order). `unchainable` — the states exist but no chain
 * reached a violating state within the gap/budget: the counterexample is
 * spurious or the decoder mis-read the derivation, and the caller must
 * downgrade the verdict.
 */
export function replayCounterexample(
  flatNet: FlatNet,
  initial: AbstractState,
  decodedStates: readonly AbstractState[],
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  options: ReplayOptions = {},
): ReplayOutcome {
  const maxGap = options.maxGap ?? 3;
  const nodeBudget = options.nodeBudget ?? 10_000;

  const waypoints = new Map<string, AbstractState>();
  for (const s of decodedStates) waypoints.set(stateKey(s), s);

  if (waypoints.size === 0) {
    return { kind: 'unchainable', reason: 'no decoded states to replay', nodesExplored: 0 };
  }

  const initKey = stateKey(initial);
  if (!waypoints.has(initKey)) {
    return {
      kind: 'unchainable',
      reason: 'the initial marking is not among the decoded states',
      nodesExplored: 0,
    };
  }

  if (satisfiesBad(initial, flatNet, property, sinkPlaces)) {
    return { kind: 'confirmed', states: [initial], steps: [], nodesExplored: 0 };
  }

  let nodes = 0;
  const reached = new Map<string, WaypointPath>();
  reached.set(initKey, { states: [initial], steps: [] });
  const queue: string[] = [initKey];

  while (queue.length > 0) {
    const wKey = queue.shift()!;
    const base = reached.get(wKey)!;
    const origin = base.states[base.states.length - 1]!;

    // Bounded BFS around this waypoint: segment paths relative to `origin`.
    const seen = new Set<string>([wKey]);
    let frontier: { state: AbstractState; states: AbstractState[]; steps: ReplayStep[] }[] = [
      { state: origin, states: [], steps: [] },
    ];

    for (let depth = 1; depth <= maxGap && frontier.length > 0; depth++) {
      const next: typeof frontier = [];
      for (const node of frontier) {
        for (const succ of successors(node.state, flatNet)) {
          nodes++;
          if (nodes > nodeBudget) {
            return {
              kind: 'unchainable',
              reason: `search budget exhausted (${nodeBudget} nodes) before reaching a violating state`,
              nodesExplored: nodes,
            };
          }
          const key = stateKey(succ.state);
          if (seen.has(key)) continue;
          seen.add(key);
          const segStates = [...node.states, succ.state];
          const segSteps = [...node.steps, succ.step];
          if (satisfiesBad(succ.state, flatNet, property, sinkPlaces)) {
            return {
              kind: 'confirmed',
              states: [...base.states, ...segStates],
              steps: [...base.steps, ...segSteps],
              nodesExplored: nodes,
            };
          }
          if (waypoints.has(key) && !reached.has(key)) {
            reached.set(key, {
              states: [...base.states, ...segStates],
              steps: [...base.steps, ...segSteps],
            });
            queue.push(key);
          }
          next.push({ state: succ.state, states: segStates, steps: segSteps });
        }
      }
      frontier = next;
    }
  }

  const unreachedCount = waypoints.size - reached.size;
  return {
    kind: 'unchainable',
    reason:
      `no abstract chain from the initial marking reaches a property-violating state ` +
      `(${reached.size}/${waypoints.size} decoded state(s) chained, ` +
      `${unreachedCount} unreachable within ${maxGap} step(s) of a chained state)`,
    nodesExplored: nodes,
  };
}
