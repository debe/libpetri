import type { Place } from '../core/place.js';
import { countAcross } from './count-clause.js';

/**
 * Safety properties that can be verified via IC3/PDR.
 *
 * Each property is encoded as an error condition: if a reachable state
 * violates the property, Spacer finds a counterexample. If no violation
 * is reachable, the property is proven.
 */
export type SmtProperty =
  | DeadlockFree
  | TerminatesAtSink
  | MutualExclusion
  | PlaceBound
  | Unreachable
  | BranchPlaceBound
  | JoinedOrDeadLettered
  | QuiescentCount;

/**
 * Deadlock-freedom: no reachable quiescent marking strands a token (VER-002).
 *
 * Violated when a reachable marking is quiescent (every transition disabled) and
 * holds a token in a place that is not a declared sink. The empty marking strands
 * nothing and never violates. This is workflow-net proper completion; for the
 * weaker "did the net reach a terminal at all", see {@link TerminatesAtSink},
 * which inverts on the empty marking.
 */
export interface DeadlockFree {
  readonly type: 'deadlock-free';
}

/**
 * Termination at a declared sink: every reachable quiescent marking has at least
 * one declared sink marked (VER-002).
 *
 * Violated when a reachable marking is quiescent and no declared sink holds a
 * token. Says nothing about tokens left elsewhere. Meaningful only with at least
 * one sink declared; with none, every quiescent marking violates vacuously.
 */
export interface TerminatesAtSink {
  readonly type: 'terminates-at-sink';
}

/** Mutual exclusion: two places never have tokens simultaneously. */
export interface MutualExclusion {
  readonly type: 'mutual-exclusion';
  readonly p1: Place<any>;
  readonly p2: Place<any>;
}

/** Place bound: a place never exceeds a given token count. */
export interface PlaceBound {
  readonly type: 'place-bound';
  readonly place: Place<any>;
  readonly bound: number;
}

/** Unreachability: the given places never all have tokens simultaneously. */
export interface Unreachable {
  readonly type: 'unreachable';
  readonly places: ReadonlySet<Place<any>>;
}

/**
 * Branch / budget place bound: a ν-net budget or fork-branch place never
 * exceeds `bound` tokens — the bounded-budget decidability lever (NU-040).
 *
 * Encodes identically to {@link PlaceBound} (a linear-integer count bound), but
 * names the ν-net intent: the live correlation pool is bounded, keeping the
 * well-structured transition system finite. The matched-transition
 * over-approximation is sound for this safety bound — a `proven` verdict holds
 * for the real net, which fires strictly fewer joins than the over-approximation.
 */
export interface BranchPlaceBound {
  readonly type: 'branch-place-bound';
  readonly place: Place<any>;
  readonly bound: number;
}

/**
 * Joined-or-dead-lettered: every forked name is eventually joined or
 * dead-lettered, so no reachable *quiescent* (deadlocked) marking still holds a
 * token in `pending` (NU-040). Violated when a reachable marking is both
 * quiescent and has `pending >= 1` — a stranded correlation group.
 */
export interface JoinedOrDeadLettered {
  readonly type: 'joined-or-dead-lettered';
  readonly pending: Place<any>;
}

/**
 * A token count at quiescence (VER-002): every reachable quiescent marking holds between
 * `min` and `max` tokens across `places` (`max` may be `Infinity`). The lower bound is
 * waived while any `waivedBy` place is marked, the upper never: a halted run ([VER-014])
 * need not refund its budget, but never holds more than there is.
 */
export interface QuiescentCount {
  readonly type: 'quiescent-count';
  readonly places: readonly Place<any>[];
  readonly min: number;
  readonly max: number;
  readonly waivedBy: readonly Place<any>[];
}

// Factory functions

export function deadlockFree(): DeadlockFree {
  return { type: 'deadlock-free' };
}

/** Quiescence reaches a declared sink (VER-002). See {@link TerminatesAtSink}. */
export function terminatesAtSink(): TerminatesAtSink {
  return { type: 'terminates-at-sink' };
}

export function mutualExclusion(p1: Place<any>, p2: Place<any>): MutualExclusion {
  return { type: 'mutual-exclusion', p1, p2 };
}

export function placeBound(place: Place<any>, bound: number): PlaceBound {
  return { type: 'place-bound', place, bound };
}

export function unreachable(places: ReadonlySet<Place<any>>): Unreachable {
  return { type: 'unreachable', places: new Set(places) };
}

/** Branch / budget place bound (NU-040). See {@link BranchPlaceBound}. */
export function branchPlaceBound(place: Place<any>, bound: number): BranchPlaceBound {
  return { type: 'branch-place-bound', place, bound };
}

/** Joined-or-dead-lettered at quiescence (NU-040). See {@link JoinedOrDeadLettered}. */
export function joinedOrDeadLettered(pending: Place<any>): JoinedOrDeadLettered {
  return { type: 'joined-or-dead-lettered', pending };
}

/**
 * A token count at quiescence (VER-002). See {@link QuiescentCount}.
 *
 * ```ts
 * quiescentCount([budget], k, k, [halt])   // the budget is back at k whenever the net comes to rest, unless it halted
 * ```
 */
export function quiescentCount(
  places: Iterable<Place<any>>,
  min: number,
  max: number,
  waivedBy: Iterable<Place<any>> = [],
): QuiescentCount {
  if (!Number.isInteger(min) || min < 0 || !(max === Infinity || Number.isInteger(max)) || max < min) {
    throw new Error(`quiescentCount needs whole bounds with 0 <= min <= max, got ${min}..${max}`);
  }
  return { type: 'quiescent-count', places: [...places], min, max, waivedBy: [...waivedBy] };
}

/** Human-readable description of a property. */
export function propertyDescription(prop: SmtProperty): string {
  switch (prop.type) {
    case 'deadlock-free':
      return 'Deadlock-freedom';
    case 'terminates-at-sink':
      return 'Terminates at a declared sink';
    case 'mutual-exclusion':
      return `Mutual exclusion of ${prop.p1.name} and ${prop.p2.name}`;
    case 'place-bound':
      return `Place ${prop.place.name} bounded by ${prop.bound}`;
    case 'unreachable':
      return `Unreachability of marking with tokens in {${[...prop.places].map(p => p.name).join(', ')}}`;
    case 'branch-place-bound':
      return `Branch place bound (ν-budget): ${prop.place.name} <= ${prop.bound}`;
    case 'joined-or-dead-lettered':
      return `Joined-or-dead-lettered: ${prop.pending.name} = 0 at quiescence`;
    case 'quiescent-count': {
      const count = `Quiescent count: ${countAcross(prop.min, prop.max, prop.places)}`;
      return prop.waivedBy.length === 0
        ? count
        : `${count}; lower bound waived while {${prop.waivedBy.map(p => p.name).join(', ')}} is marked`;
    }
  }
}
