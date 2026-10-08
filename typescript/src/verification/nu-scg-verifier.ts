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
import { classify, type FragmentMode, type NameFragment } from './analysis/name-fragment.js';
import type { PrioritySemantics } from './analysis/priority-semantics.js';
import { NameStateClassGraph } from './analysis/name-state-class-graph.js';
import type { NameAligned, QuiescentNameAligned, SmtProperty } from './smt-property.js';
import { isNameAlignment } from './name-alignment.js';
import type { Verdict } from './smt-verification-result.js';
import type { Deadline } from './total-budget.js';
import { hasLatestBound, relaxLate } from './reaping.js';
import { compareCodePoints } from '../core/internal/code-point-order.js';

const NOTE_EXACT =
  '\nNote: ν-join correlation decided exactly via the state-class-graph name-partition ' +
  'quotient — the symbolic graph closed, so the verdict is sound AND complete (no spurious ' +
  'different-name counterexample; quiescence is name-aware), beyond the bounded-budget ' +
  'fragment (NU-050, Route B).\n';

/**
 * {@link NOTE_EXACT} for a graph built on a net in which a transition keeps its latest bound (the
 * on-time executor of `assumeNoReaping`, or a direct call of {@link verifyViaNameScg} on a timed
 * net). The strong-semantics graph fires every transition by its latest bound and reads each
 * firing as one instant step, so its verdict is exact for that executor alone ([VER-004],
 * [TIME-013]).
 */
const NOTE_ON_TIME =
  '\nNote: ν-join correlation decided via the state-class-graph name-partition quotient: the ' +
  'symbolic graph closed, and a transition keeps its latest bound in it, so the verdict is exact ' +
  'only for an on-time executor whose actions take no time (quiescence is name-aware; NU-050, ' +
  'Route B).\n';

/** The note of a closed graph built on `net` ({@link NOTE_EXACT} or {@link NOTE_ON_TIME}). */
function closedNote(net: PetriNet): string {
  return [...net.transitions].some(t => hasLatestBound(t.timing)) ? NOTE_ON_TIME : NOTE_EXACT;
}

export interface NuScgOutcome {
  readonly verdict: Verdict;
  readonly trace: MarkingState[];
  readonly transitions: string[];
  readonly note: string;
  readonly classCount: number;
}

/**
 * Decides `property` on the name-aware graph, or `null` outside the fragment, for a late
 * executor ([VER-002], [VER-004], [TIME-006], [TIME-013]):
 * - the graph is built on `relaxLate`'s net, in which no transition named in `late` has a
 *   latest bound, for **every** property: a late executor reaps a deadline / window transition
 *   or fires an exact one after its bound, and fires the others meanwhile, and a
 *   strong-semantics `proven` of any property could miss those runs (Lean:
 *   `TimedScg/Retrodict.reaping_escapes_timed_graph`);
 * - an expanded class rests when every firing out of it is of a transition in `reapable`;
 *   only a quiescence property reads it;
 * - `'conflict'` priority semantics falls back to `'none'` when a transition in `reapable`
 *   exists: a reapable transition that pre-empts a conflicting one on time is reaped by a
 *   late executor, which then fires the other.
 * Both empty (the default, the on-time executor of `assumeNoReaping`, or a net timed only
 * with `immediate` and `delayed`), nothing changes.
 *
 * A name-alignment property ([NU-055]) is classified on a net without a matched transition too,
 * and an uncoloured property place or a coloured place the initial marking marks is an
 * `unknown` outcome naming the place, not `null`: no other route decides it.
 *
 * `mintTransitions` names the transitions declared to mint ([NU-010]; the verifier passes
 * `declaredMints`). A transition that writes a coloured place without consuming one and is not
 * named there puts the net outside the fragment.
 *
 * Applies no in-flight split ([VER-004]): it decides `net` as given, every firing atomic, and
 * reads reaping only through `reapable` and `late`. `SmtVerifier.verify` splits the net first, and
 * under `'conflict'` also splits every pruner and its feeders or turns the pruning off. On a graph
 * that closes with a latest bound kept the note says the verdict is exact only for an on-time
 * executor whose actions take no time.
 */
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
  mintTransitions: ReadonlySet<string>,
  prioritySemantics: PrioritySemantics,
  conditionalSinks: readonly ConditionalSinks[] = [],
  deadline: Deadline | null = null,
  reapable: ReadonlySet<string> = new Set(),
  late: ReadonlySet<string> = new Set(),
): NuScgOutcome | null {
  const reapableInNet = new Set([...net.transitions].map(t => t.name).filter(n => reapable.has(n)));
  const lifted = new Set(
    [...net.transitions].filter(t => late.has(t.name) && hasLatestBound(t.timing)).map(t => t.name),
  );
  if (reapableInNet.size === 0 && lifted.size === 0) {
    return verifyNameScg(
      net, initial, property, sinkPlaces, environmentPlaces, environmentMode, maxClasses, fragmentMode,
      carrierPlaces, mintTransitions, prioritySemantics, conditionalSinks, deadline, new Set(),
    );
  }
  const pruningOff = reapableInNet.size > 0 && prioritySemantics === 'conflict';
  const semantics: PrioritySemantics = reapableInNet.size > 0 ? 'none' : prioritySemantics;
  // The marking properties read no rest ([VER-004]).
  const restsOn = safetyViolation(property) !== null ? new Set<string>() : reapableInNet;
  const outcome = verifyNameScg(
    relaxLate(net, lifted), initial, property, sinkPlaces, environmentPlaces, environmentMode,
    maxClasses, fragmentMode, carrierPlaces, mintTransitions, semantics, conditionalSinks, deadline, restsOn,
  );
  if (outcome === null || outcome.note === '' || lifted.size === 0) return outcome;
  return { ...outcome, note: outcome.note + latenessNote(lifted, pruningOff) };
}

/** The note Route B adds when it lifted latest bounds. */
function latenessNote(lifted: ReadonlySet<string>, pruningOff: boolean): string {
  const names = [...lifted].sort(compareCodePoints).join(', ');
  return `Note: the latest bound of ${names} was lifted${pruningOff ? ' and priority pruning is off' : ''}, `
    + 'so the graph holds the runs of a late executor, which reaps a deadline or window transition '
    + 'and fires an exact one after its bound (TIME-006, TIME-013).\n';
}

function verifyNameScg(
  net: PetriNet,
  initial: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  environmentPlaces: Set<EnvironmentPlace<any>>,
  environmentMode: EnvironmentAnalysisMode,
  maxClasses: number,
  fragmentMode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  mintTransitions: ReadonlySet<string>,
  prioritySemantics: PrioritySemantics,
  conditionalSinks: readonly ConditionalSinks[],
  deadline: Deadline | null,
  reapable: ReadonlySet<string>,
): NuScgOutcome | null {
  const nameAlignment = isNameAlignment(property);
  const fragment = classify(net, fragmentMode, carrierPlaces, mintTransitions, nameAlignment);
  if (fragment === null) return null;
  // NU-055: nothing but this graph decides a name-alignment property, so where it cannot, the
  // verdict is unknown naming the place rather than a decline the caller would route elsewhere.
  if (nameAlignment) {
    const refusal = nameAlignmentRefusal(property, fragment, fragmentMode, initial);
    if (refusal !== null) {
      return { verdict: { type: 'unknown', reason: refusal }, trace: [], transitions: [], note: '', classCount: 0 };
    }
  }
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
  const violating = decide(scg, property, sinkPlaces, conditionalSinks, reapable);
  if (violating >= 0) {
    const [trace, transitions] = counterexamplePath(scg, violating);
    return {
      verdict: { type: 'violated' },
      trace,
      transitions,
      note: scg.stoppedEarly()
        ? earlyStopNote(scg.classCount())
        : complete ? closedNote(net) : prefixNote('ν name-aware state-class graph', maxClasses),
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
    note: closedNote(net),
    classCount: scg.classCount(),
  };
}

/**
 * Why Route B cannot decide the name-alignment `property` on `fragment` (NU-055), or `null`:
 * a property place that is not coloured, whose predicate would hold vacuously (AC2, AC3), or a
 * coloured place the initial marking marks (AC6), since the graph models no initial names.
 * Checked in that order, the last two steps of the NU-055 refusal order: the first uncoloured
 * place of `S` in the order of `S`, then the first marked coloured place in code-point order.
 */
function nameAlignmentRefusal(
  property: NameAligned | QuiescentNameAligned,
  fragment: NameFragment,
  fragmentMode: FragmentMode,
  initial: MarkingState,
): string | null {
  for (const { name: place } of property.places) {
    if (fragment.isColoured(place)) continue;
    const base = fragmentMode === 'base'
      ? "; under BASE only the match keys are coloured, carrier places and relay targets only " +
        "under the EXTENDED fragment (fragmentMode('extended'), NU-051, NU-054)"
      : '';
    return `place '${place}' is not a coloured place of the ν fragment (a match key, declared ` +
      `carrier or relay target), so it carries no name and name alignment on it would hold ` +
      `vacuously (NU-055)${base}`;
  }
  const marked = initial.placesWithTokens().map(p => p.name).filter(n => fragment.isColoured(n))
    .sort(compareCodePoints);
  if (marked.length > 0) {
    return `coloured place '${marked[0]}' holds a token in the initial marking; the name-partition ` +
      'graph models no initial names, so the coloured places must start empty (NU-055)';
  }
  return null;
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
  reapable: ReadonlySet<string> = new Set(),
): number {
  return decideOverClasses(
    {
      count: scg.classCount(),
      markingOf: i => scg.markingOf(i),
      // A frontier class of a truncated graph was never expanded: no successors recorded, but
      // not dead. An expanded class rests when nothing fires out of it, or only reapable
      // transitions do ([VER-002] reap-quiescence, [TIME-013]).
      isQuiescent: i => i < scg.expandedCount()
        && scg.successorLabelsOf(i).every(label => reapable.has(label)),
      namesOf: i => scg.namesOf(i),
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
