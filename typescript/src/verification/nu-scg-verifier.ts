/**
 * ν-net exact verification via the name-aware state-class-graph name-partition
 * quotient (NU-050, Route B). Bridges {@link NameStateClassGraph} to the
 * {@link SmtVerificationResult} verdict types.
 *
 * {@link verifyViaNameScg} returns `null` when the net is outside the supported
 * mint→matched-join fragment (the caller falls back to the SMT / Route A path);
 * otherwise an exact verdict when the symbolic graph closes. When it truncates (the live
 * correlation pool is unbounded) a violation among the explored classes still stands; with
 * none the verdict is `unknown` — a truncated graph never proves.
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import type { ConditionalSinks } from './rest-set.js';
import { decideOverClasses, prefixNote, safetyViolation } from './graph-decision.js';
import type { EnvironmentPlace } from '../core/place.js';
import type { MarkingState } from './marking-state.js';
import type { EnvironmentAnalysisMode } from './analysis/environment-analysis-mode.js';
import { classify, type FragmentMode } from './analysis/name-fragment.js';
import type { PrioritySemantics } from './analysis/priority-semantics.js';
import { NameStateClassGraph } from './analysis/name-state-class-graph.js';
import type { SmtProperty } from './smt-property.js';
import type { Verdict } from './smt-verification-result.js';
import type { Deadline } from './total-budget.js';

const NOTE_EXACT =
  '\nNote: ν-join correlation decided exactly via the state-class-graph name-partition ' +
  'quotient — the symbolic graph closed, so the verdict is sound AND complete (no spurious ' +
  'different-name counterexample; quiescence is name-aware), beyond the bounded-budget ' +
  'fragment (NU-050, Route B).\n';

export interface NuScgOutcome {
  readonly verdict: Verdict;
  readonly trace: MarkingState[];
  readonly transitions: string[];
  readonly note: string;
  readonly classCount: number;
}

export function verifyViaNameScg(
  net: PetriNet,
  initial: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  environmentPlaces: Set<EnvironmentPlace<any>>,
  environmentMode: EnvironmentAnalysisMode,
  maxClasses: number,
  fragmentMode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  prioritySemantics: PrioritySemantics,
  conditionalSinks: readonly ConditionalSinks[] = [],
  deadline: Deadline | null = null,
): NuScgOutcome | null {
  const fragment = classify(net, fragmentMode, carrierPlaces);
  if (fragment === null) return null;
  // We model no initial colour assignment, so coloured places must start empty.
  for (const p of initial.placesWithTokens()) {
    if (fragment.isColoured(p.name)) return null;
  }

  // A reachability-safety property stops the build at its first violating class ([VER-012]):
  // same predicate, same witness, same shortest path as deciding over the finished graph.
  // Quiescence properties need expanded classes, so they build in full.
  const scg = NameStateClassGraph.build(
    net, initial, fragment, maxClasses, environmentPlaces, environmentMode, prioritySemantics, deadline,
    safetyViolation(property),
  );
  const complete = scg.isComplete();

  // On truncation the same predicate runs over the explored prefix ([VER-012] AC3): every
  // stored class is a real reachable class, and only an expanded class counts as quiescent.
  const violating = decide(scg, property, sinkPlaces, conditionalSinks);
  if (violating >= 0) {
    const [trace, transitions] = counterexamplePath(scg, violating);
    return {
      verdict: { type: 'violated' },
      trace,
      transitions,
      note: scg.stoppedEarly()
        ? earlyStopNote(scg.classCount())
        : complete ? NOTE_EXACT : prefixNote('ν name-aware state-class graph', maxClasses),
      classCount: scg.classCount(),
    };
  }

  if (!complete) {
    return {
      verdict: {
        type: 'unknown',
        reason:
          `ν name-aware state-class graph truncated at ${maxClasses} classes — the live ` +
          'correlation pool is not structurally bounded; reachability over unbounded fresh ' +
          'names is undecidable (NU-050, Route B). Declare a budget place to bound the live ' +
          'pool, or raise nuMaxClasses.',
      },
      trace: [],
      transitions: [],
      note: '',
      classCount: scg.classCount(),
    };
  }
  return {
    verdict: { type: 'proven', method: 'ν name-partition SCG (NU-050, Route B)', inductiveInvariant: null },
    trace: [],
    transitions: [],
    note: NOTE_EXACT,
    classCount: scg.classCount(),
  };
}

/**
 * The report note of a violation found by stopping the build at the first violating class
 * ([VER-012]). The graph was never finished, so it says nothing about closure.
 */
function earlyStopNote(classCount: number): string {
  return `\nNote: Route B stopped at the first violating class after ${classCount} classes (VER-012). ` +
    'Every explored class is reachable and classes are discovered breadth-first, so the ' +
    'counterexample is a real firing sequence and a shortest one to any violation.\n';
}

/**
 * @internal A witnessing class index for a violation, or -1 if the property holds.
 *
 * The predicate itself lives in {@link decideOverClasses}, shared with the plain
 * enumeration route of [VER-017] so the two cannot drift ([VER-002] AC7).
 */
export function decide(
  scg: NameStateClassGraph,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
): number {
  return decideOverClasses(
    {
      count: scg.classCount(),
      markingOf: i => scg.markingOf(i),
      // A frontier class of a truncated graph was never expanded: no successors recorded, but
      // not dead.
      isQuiescent: i => i < scg.expandedCount() && scg.successorsOf(i).length === 0,
    },
    property,
    sinkPlaces,
    conditionalSinks,
  );
}

/**
 * @internal Shortest firing sequence from the initial class (0) to `target`: BFS over each class's
 * labelled successor list, O(V + E).
 */
export function counterexamplePath(scg: NameStateClassGraph, target: number): [MarkingState[], string[]] {
  const n = scg.classCount();
  const parent = new Int32Array(n).fill(-1);
  const via = new Array<string>(n).fill('');
  const visited = new Uint8Array(n);
  visited[0] = 1;
  const queue: number[] = [0];
  for (let head = 0; head < queue.length; head++) {
    const u = queue[head]!;
    if (u === target) break;
    const succ = scg.successorsOf(u);
    const labels = scg.successorLabelsOf(u);
    for (let k = 0; k < succ.length; k++) {
      const v = succ[k]!;
      if (visited[v]) continue;
      visited[v] = 1;
      parent[v] = u;
      via[v] = labels[k]!;
      queue.push(v);
    }
  }
  const chain: number[] = [];
  for (let cur = target; cur !== -1; cur = parent[cur]!) {
    chain.push(cur);
  }
  chain.reverse();
  const markings = chain.map(i => scg.markingOf(i));
  const transitions = chain.slice(1).map(i => via[i]!);
  return [markings, transitions];
}
