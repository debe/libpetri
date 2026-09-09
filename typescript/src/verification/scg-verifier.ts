/**
 * @module scg-verifier
 *
 * Bounded state-space enumeration ([VER-017]): decide a property by building the
 * state-class graph and reading the verdict off it, when the graph closes within
 * a class budget.
 *
 * IC3/PDR is built for state spaces that are wide and shallow. A workflow net is
 * the opposite — narrow and deep: a forty-node pipeline has under two thousand
 * reachable classes, but its diameter is the length of the pipeline, so the
 * fixpoint engine needs a frame per stage and its cost climbs with the cube of
 * the length. Enumerating the same net is linear in the state space and finishes
 * in milliseconds. Measured on a forty-node chain (370 places): 410 s on the
 * fixpoint path, 0.11 s here.
 *
 * The route is exact when the graph closes — sound *and* complete, so a
 * `violated` is a real firing sequence rather than a possibly-spurious
 * over-approximation, and a `proven` is never the `unknown` a fixpoint search
 * runs out of time for.
 *
 * It applies only to an **untimed** net — every transition `immediate` — and that
 * restriction is what makes the verdict interchangeable with the encoders'. The
 * state-class graph carries firing domains, so on a timed net it would explore
 * only the runs the timing admits and its `proven` would be the weaker timed
 * claim; [VER-004] is explicit that the untimed proof is the stronger one, and a
 * route must not quietly hand back a weaker claim than the one it replaced. On an
 * untimed net no domain excludes anything, the graph explores exactly the untimed
 * reachable set, and the two routes decide the same predicate over the same
 * abstraction — enumeration simply decides it where the search may not.
 *
 * When the graph does not close within the budget the route declines and the
 * caller runs the SMT pipeline unchanged: enumeration never turns a verdict into
 * `unknown` that the solver could have decided.
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import type { MarkingState } from './marking-state.js';
import type { SmtProperty } from './smt-property.js';
import type { Verdict } from './smt-verification-result.js';
import type { ConditionalSinks } from './rest-set.js';
import { decideOverClasses } from './graph-decision.js';
import { StateClassGraph } from './analysis/state-class-graph.js';
import type { StateClass } from './analysis/state-class.js';

/**
 * Whether every transition is `immediate`, so the state-class graph explores the
 * untimed reachable set exactly and its verdict is the encoders' claim rather
 * than the weaker timed one. See this module's header.
 */
export function isUntimed(net: PetriNet): boolean {
  for (const t of net.transitions) {
    if (t.timing.type !== 'immediate') return false;
  }
  return true;
}

/** The note a decided verdict carries into the report. */
export const NOTE_ENUMERATED =
  '\nNote: decided by bounded state-space enumeration — the state-class graph closed, so the ' +
  'verdict is sound AND complete: a `violated` is a real firing sequence, not a possibly-' +
  'spurious over-approximation. The net is untimed, so this is the same claim the encoders ' +
  'make (VER-017).\n';

/** Outcome of the enumeration route. */
export type ScgOutcome =
  /** The graph closed and decided the property. */
  | {
      readonly kind: 'decided';
      readonly verdict: Verdict;
      readonly trace: MarkingState[];
      readonly transitions: string[];
      readonly classCount: number;
    }
  /** The graph hit the class budget; the caller falls through to the SMT pipeline. */
  | { readonly kind: 'truncated'; readonly classCount: number };

/**
 * Decides `property` by enumeration, or reports truncation.
 *
 * @param maxClasses the class budget; `<= 0` disables the route (the caller then
 *   never calls this).
 */
export function verifyViaStateClassGraph(
  net: PetriNet,
  initial: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  maxClasses: number,
  conditionalSinks: readonly ConditionalSinks[] = [],
): ScgOutcome {
  const graph = StateClassGraph.build(net, initial, maxClasses);
  const classes = graph.stateClasses();
  if (!graph.isComplete()) return { kind: 'truncated', classCount: classes.length };

  const violating = decideOverClasses(
    {
      count: classes.length,
      markingOf: i => classes[i]!.marking,
      isQuiescent: i => graph.successors(classes[i]!).size === 0,
    },
    property,
    sinkPlaces,
    conditionalSinks,
  );

  if (violating >= 0) {
    const [trace, transitions] = counterexamplePath(graph, classes[violating]!);
    return { kind: 'decided', verdict: { type: 'violated' }, trace, transitions, classCount: classes.length };
  }
  return {
    kind: 'decided',
    verdict: { type: 'proven', method: 'state-space enumeration (VER-017)', inductiveInvariant: null },
    trace: [],
    transitions: [],
    classCount: classes.length,
  };
}

/** Shortest firing sequence from the initial class to `target`, as markings and transition names. */
function counterexamplePath(graph: StateClassGraph, target: StateClass): [MarkingState[], string[]] {
  const parent = new Map<StateClass, StateClass>();
  const via = new Map<StateClass, string>();
  const seen = new Set<StateClass>([graph.initialClass]);
  const queue: StateClass[] = [graph.initialClass];
  while (queue.length > 0) {
    const current = queue.shift()!;
    if (current === target) break;
    for (const [transition, edges] of graph.outgoingBranchEdges(current)) {
      for (const edge of edges) {
        if (seen.has(edge.target)) continue;
        seen.add(edge.target);
        parent.set(edge.target, current);
        via.set(edge.target, transition.name);
        queue.push(edge.target);
      }
    }
  }
  const chain: StateClass[] = [];
  for (let cur: StateClass | undefined = target; cur != null; cur = parent.get(cur)) {
    chain.push(cur);
  }
  chain.reverse();
  return [chain.map(sc => sc.marking), chain.slice(1).map(sc => via.get(sc)!)];
}
