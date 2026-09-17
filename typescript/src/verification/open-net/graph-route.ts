/**
 * @module open-net/graph-route
 *
 * The contract decided on the closed net's state-class graph ([VER-022]), built **untimed**
 * ([VER-004]): every clock gets `immediate()`, so the graph holds the markings the untimed
 * encoders reason about. Priority- and value-blind, like every graph route.
 *
 * A closed graph decides exactly: every quiescent class is judged, and any cycle is a run
 * that never rests. A truncated graph's findings are still real, since a class with nothing
 * enabled is quiescent whether or not it was expanded and an explored cycle is a real cycle;
 * only the absence of findings needs the graph to close.
 */
import type { Place } from '../../core/place.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';
import { StateClassGraph } from '../analysis/state-class-graph.js';
import type { StateClass } from '../analysis/state-class.js';
import type { ClosedNet } from './closure.js';
import type { OpenNetContract } from './contract.js';
import { describeFinding, quiescenceFindings, restDeclarationOf, subjectOf, type Finding } from './predicate.js';
import { contractViolation, type ContractViolation } from './result.js';

/** What the graph route found. */
export interface GraphRouteOutcome {
  readonly complete: boolean;
  readonly classCount: number;
  /** Real violations: the shallowest witness per subject, then termination. */
  readonly violations: readonly ContractViolation[];
}

/** Builds the closed net's untimed graph and judges it against `contract`. */
export function decideOnGraph(
  closed: ClosedNet,
  contract: OpenNetContract,
  maxClasses: number,
  tracedPlaces: readonly Place<any>[],
): GraphRouteOutcome {
  const graph = StateClassGraph.build(
    closed.net, closed.initialMarking, maxClasses, undefined, undefined, { untimed: true },
  );
  const classes = graph.stateClasses();
  const rest = restDeclarationOf(contract, closed);
  const tree = bfsTree(graph);

  // Classes come in BFS order, so the first class showing a subject is a shallowest one.
  const first = new Map<string, { finding: Finding; target: StateClass }>();
  for (const sc of classes) {
    // Untimed, every enabled transition can fire: nothing enabled is quiescence, expanded or not.
    if (sc.enabledTransitions.length > 0) continue;
    for (const finding of quiescenceFindings(sc.marking, contract, rest)) {
      const key = `${finding.kind}:${subjectOf(finding)}`;
      if (!first.has(key)) first.set(key, { finding, target: sc });
    }
  }

  // Clauses in contract order, then stranded places in code-point order ([VER-013]).
  const clauseOrder = new Map(contract.clauses.map((c, i) => [c.name, i]));
  const rank = (f: Finding): number =>
    f.kind === 'clause' ? clauseOrder.get(f.clause.name)! : contract.clauses.length;
  const ordered = [...first.values()].sort((a, b) => rank(a.finding) - rank(b.finding)
    || compareCodePoints(subjectOf(a.finding), subjectOf(b.finding)));

  const violations: ContractViolation[] = ordered.map(({ finding, target }) => {
    const path = pathTo(tree, target);
    return contractViolation(closed, tracedPlaces, {
      kind: finding.kind,
      subject: subjectOf(finding),
      detail: describeFinding(finding),
      transitions: path.transitions,
      markings: path.classes.map(c => c.marking),
      cycleStart: null,
      confirmed: true,
    });
  });

  if (contract.requiresTermination) {
    const cycle = findCycle(graph, tree);
    if (cycle !== null) violations.push(contractViolation(closed, tracedPlaces, cycle));
  }
  return { complete: graph.isComplete(), classCount: classes.length, violations };
}

interface TreeEdge {
  readonly parent: StateClass;
  readonly via: string;
}

/** Each explored class's BFS parent and the transition that first reached it. */
function bfsTree(graph: StateClassGraph): Map<StateClass, TreeEdge> {
  const tree = new Map<StateClass, TreeEdge>();
  const seen = new Set<StateClass>([graph.initialClass]);
  const queue: StateClass[] = [graph.initialClass];
  for (let head = 0; head < queue.length; head++) {
    const current = queue[head]!;
    for (const [transition, edges] of graph.outgoingBranchEdges(current)) {
      for (const edge of edges) {
        if (seen.has(edge.target)) continue;
        seen.add(edge.target);
        tree.set(edge.target, { parent: current, via: transition.name });
        queue.push(edge.target);
      }
    }
  }
  return tree;
}

/** The shortest firing sequence from the initial class to `target`. */
function pathTo(tree: Map<StateClass, TreeEdge>, target: StateClass): { classes: StateClass[]; transitions: string[] } {
  const classes: StateClass[] = [];
  const transitions: string[] = [];
  for (let cur: StateClass | undefined = target; cur !== undefined;) {
    classes.push(cur);
    const edge = tree.get(cur);
    if (edge === undefined) break;
    transitions.push(edge.via);
    cur = edge.parent;
  }
  return { classes: classes.reverse(), transitions: transitions.reverse() };
}

interface Frame {
  readonly node: StateClass;
  readonly edges: readonly (readonly [string, StateClass])[];
  next: number;
  /** The transition that entered this frame's class from the one below it. */
  readonly via: string | null;
}

/**
 * A reachable cycle as a lasso (the shortest stem to its entry class, then the loop), or
 * `null`. Iterative depth-first search, so a deep graph cannot overflow the stack.
 */
function findCycle(
  graph: StateClassGraph,
  tree: Map<StateClass, TreeEdge>,
): Omit<ContractViolation, 'portTrace'> | null {
  const edgesOf = (sc: StateClass): (readonly [string, StateClass])[] => {
    const out: (readonly [string, StateClass])[] = [];
    for (const [t, edges] of graph.outgoingBranchEdges(sc)) for (const e of edges) out.push([t.name, e.target]);
    return out;
  };
  // A class's position on the stack while it is open, -1 once it is finished.
  const position = new Map<StateClass, number>([[graph.initialClass, 0]]);
  const stack: Frame[] = [{ node: graph.initialClass, edges: edgesOf(graph.initialClass), next: 0, via: null }];
  while (stack.length > 0) {
    const top = stack[stack.length - 1]!;
    if (top.next >= top.edges.length) {
      position.set(top.node, -1);
      stack.pop();
      continue;
    }
    const [via, target] = top.edges[top.next++]!;
    const at = position.get(target);
    if (at === undefined) {
      position.set(target, stack.length);
      stack.push({ node: target, edges: edgesOf(target), next: 0, via });
    } else if (at >= 0) {
      // A back edge: the stack from `target` up to `top`, closed by `via`, is a cycle.
      const loop = stack.slice(at);
      const stem = pathTo(tree, target);
      const cycle = [...loop.slice(1).map(f => f.via!), via];
      return {
        kind: 'termination',
        subject: 'termination',
        detail: `a run can repeat ${cycle.join(' → ')} forever without coming to rest`,
        transitions: [...stem.transitions, ...cycle],
        markings: [...stem.classes.map(c => c.marking), ...loop.slice(1).map(f => f.node.marking), target.marking],
        cycleStart: stem.transitions.length,
        confirmed: true,
      };
    }
  }
  return null;
}
