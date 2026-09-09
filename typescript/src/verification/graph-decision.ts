/**
 * @module graph-decision
 *
 * The property predicate both state-class-graph routes decide, in one place.
 *
 * Two routes enumerate a finite graph of classes and read a verdict off it: the
 * ν name-partition quotient of [VER-012] (`nu-scg-verifier`) and the plain
 * bounded enumeration of [VER-017] (`scg-verifier`). They explore different
 * graphs, but the question they ask of a class is identical, and [VER-002] AC7
 * requires every route to decide the *same* predicate. Stating it once is what
 * keeps that true: when the sink clause last lived in two copies, one of them
 * drifted (NU-040 AC4).
 */
import type { Place } from '../core/place.js';
import type { MarkingState } from './marking-state.js';
import type { SmtProperty } from './smt-property.js';
import { strandsToken, type ConditionalSinks } from './rest-set.js';

/** A finite graph of classes, indexed `0 .. count - 1`, class 0 the initial one. */
export interface ClassView {
  readonly count: number;
  /** The marking of class `i`. */
  markingOf(i: number): MarkingState;
  /** Whether class `i` has no successor — the graph's quiescence. */
  isQuiescent(i: number): boolean;
}

/**
 * The index of the first class witnessing a violation, or `-1` when the property
 * holds across the whole graph.
 *
 * Quiescence-based properties read `isQuiescent`; reachability-safety properties
 * read the marking alone. `DeadlockFree` uses the shared rest set of [VER-014],
 * so a conditional sink excuses a token exactly as it does in the encoders.
 */
export function decideOverClasses(
  view: ClassView,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[] = [],
): number {
  const firstWhere = (pred: (i: number) => boolean): number => {
    for (let i = 0; i < view.count; i++) {
      if (pred(i)) return i;
    }
    return -1;
  };

  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
      return firstWhere(i => view.markingOf(i).tokens(property.place) > property.bound);
    case 'unreachable':
      return firstWhere(i => {
        const m = view.markingOf(i);
        for (const p of property.places) {
          if (!m.hasTokens(p)) return false;
        }
        return true;
      });
    case 'mutual-exclusion':
      return firstWhere(i => {
        const m = view.markingOf(i);
        return m.hasTokens(property.p1) && m.hasTokens(property.p2);
      });
    // DeadlockFree (VER-002): a quiescent class that strands a token — some marked
    // place is not where resting is permitted, the conditional sinks of VER-014
    // included. The empty marking strands nothing (AC4).
    case 'deadlock-free':
      return firstWhere(i => view.isQuiescent(i) && strandsToken(view.markingOf(i), sinkPlaces, conditionalSinks));
    // TerminatesAtSink (VER-002): a quiescent class that marks NO declared sink.
    // Inverts with DeadlockFree on the empty marking, by design.
    case 'terminates-at-sink':
      return firstWhere(i => view.isQuiescent(i) && !anySinkMarked(view.markingOf(i), sinkPlaces));
    // JoinedOrDeadLettered (NU-040 AC4): a quiescent class still holding a pending
    // token. No sink clause.
    case 'joined-or-dead-lettered':
      return firstWhere(i => view.isQuiescent(i) && view.markingOf(i).hasTokens(property.pending));
  }
}

/** Whether any declared sink place holds a token in `m` ([VER-002]). */
function anySinkMarked(m: MarkingState, sinks: ReadonlySet<Place<any>>): boolean {
  const sinkNames = new Set<string>();
  for (const s of sinks) sinkNames.add(s.name);
  for (const p of m.placesWithTokens()) {
    if (sinkNames.has(p.name)) return true;
  }
  return false;
}
