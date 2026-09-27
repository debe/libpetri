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
import { countViolation } from './count-clause.js';
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

  const violates = safetyViolation(property);
  if (violates !== null) return firstWhere(i => violates(view.markingOf(i)));

  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
    case 'unreachable':
    case 'mutual-exclusion':
      return -1; // unreachable: decided by `safetyViolation` above
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
    // QuiescentCount (VER-002): a quiescent class whose count across the places is below
    // the lower bound with no waiver marked, or above the upper bound.
    case 'quiescent-count':
      return firstWhere(i => view.isQuiescent(i)
        && countViolation(view.markingOf(i), property.places, property.min, property.max, property.waivedBy) !== null);
  }
}

/**
 * The class predicate of a reachability-safety property — whether a class with marking `m`
 * violates it — or `null` for a quiescence property, whose predicate also needs to know
 * whether the class has successors. It reads the marking alone, so a graph build can apply
 * it to each class as the class is discovered and stop at the first violation ([VER-012]);
 * {@link decideOverClasses} decides these properties through this same function.
 */
export function safetyViolation(property: SmtProperty): ((m: MarkingState) => boolean) | null {
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
      return m => m.tokens(property.place) > property.bound;
    case 'unreachable':
      return m => {
        for (const p of property.places) {
          if (!m.hasTokens(p)) return false;
        }
        return true;
      };
    case 'mutual-exclusion':
      return m => m.hasTokens(property.p1) && m.hasTokens(property.p2);
    default:
      return null;
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

/**
 * The report note of a violation found in the explored prefix of a graph that did not close
 * ([VER-012], [VER-017], [VER-023]).
 */
export function prefixNote(graph: string, maxClasses: number): string {
  return `\nNote: the ${graph} was truncated at ${maxClasses} classes; the violation was found in ` +
    'the explored prefix. Every explored class is reachable, so the counterexample is a real firing ' +
    'sequence, the shortest within the explored graph. A truncated graph never proves a property.\n';
}
