import type { Place } from '../../core/place.js';
import type { EnvironmentPlace } from '../../core/place.js';
import type { In } from '../../core/in.js';
import { consumptionCount } from '../../core/in.js';
import type { Transition } from '../../core/transition.js';
import type { PetriNet } from '../../core/petri-net.js';
import { earliest, latest } from '../../core/timing.js';
import { enumerateBranches } from '../../core/out.js';
import { MarkingState } from '../marking-state.js';
import { DBM } from './dbm.js';
import { StateClass } from './state-class.js';
import type { EnvironmentAnalysisMode } from './environment-analysis-mode.js';
import { ignore } from './environment-analysis-mode.js';
import { requireOutputProducingActions } from '../../core/internal/output-action-check.js';

/** Edge that tracks which XOR branch was taken. */
export interface BranchEdge {
  readonly branchIndex: number;
  readonly target: StateClass;
}

export interface VirtualTransition {
  readonly transition: Transition;
  readonly branchIndex: number;
  readonly outputPlaces: ReadonlySet<Place<any>>;
}

/**
 * State Class Graph for Time Petri Net analysis.
 *
 * Implements the Berthomieu-Diaz (1991) algorithm for computing the state class
 * graph of a bounded Time Petri Net.
 */
export class StateClassGraph {
  readonly net: PetriNet;
  readonly initialClass: StateClass;
  private readonly _stateClasses: StateClass[];
  private readonly _transitions: Map<StateClass, Map<Transition, BranchEdge[]>>;
  private readonly _successors: Map<StateClass, Set<StateClass>>;
  private readonly _predecessors: Map<StateClass, Set<StateClass>>;
  private readonly _complete: boolean;

  private constructor(
    net: PetriNet,
    initialClass: StateClass,
    stateClasses: StateClass[],
    transitions: Map<StateClass, Map<Transition, BranchEdge[]>>,
    complete: boolean,
  ) {
    this.net = net;
    this.initialClass = initialClass;
    this._stateClasses = stateClasses;
    this._transitions = transitions;
    this._complete = complete;

    // Build successor/predecessor maps
    this._successors = new Map();
    this._predecessors = new Map();
    for (const sc of stateClasses) {
      this._successors.set(sc, new Set());
      this._predecessors.set(sc, new Set());
    }
    for (const [from, tMap] of transitions) {
      for (const edges of tMap.values()) {
        for (const edge of edges) {
          this._successors.get(from)!.add(edge.target);
          this._predecessors.get(edge.target)!.add(from);
        }
      }
    }
  }

  /**
   * Builds the state class graph for a Time Petri Net.
   *
   * @throws Error if the net violates CORE-043 — analysis rejects the same nets execution rejects.
   */
  static build(
    net: PetriNet,
    initialMarking: MarkingState,
    maxClasses: number,
    environmentPlaces?: Set<EnvironmentPlace<any>>,
    environmentMode?: EnvironmentAnalysisMode,
  ): StateClassGraph {
    requireOutputProducingActions(net);

    const envMode = environmentMode ?? ignore();
    const envPlaces = new Set<Place<any>>();
    if (environmentPlaces) {
      for (const ep of environmentPlaces) {
        envPlaces.add(ep.place);
      }
    }

    const initialClass = initialStateClass(net, initialMarking, envPlaces, envMode);

    // BFS exploration
    const stateClasses: StateClass[] = [initialClass];
    const stateClassSet = new Set<string>([classKey(initialClass)]);
    const classMap = new Map<string, StateClass>([[classKey(initialClass), initialClass]]);
    const transitionMap = new Map<StateClass, Map<Transition, BranchEdge[]>>();
    transitionMap.set(initialClass, new Map());
    const queue: StateClass[] = [initialClass];
    let complete = true;

    while (queue.length > 0) {
      if (stateClasses.length >= maxClasses) {
        complete = false;
        break;
      }

      const current = queue.shift()!;

      for (const transition of current.enabledTransitions) {
        const virtualTransitions = expandTransition(transition);

        for (const vt of virtualTransitions) {
          const successor = computeSuccessor(net, current, vt, envPlaces, envMode);
          if (successor === null || successor.isEmpty()) continue;

          // Add edge with branch index
          const tEdges = transitionMap.get(current)!;
          if (!tEdges.has(transition)) tEdges.set(transition, []);
          tEdges.get(transition)!.push({ branchIndex: vt.branchIndex, target: successor });

          // Dedup state classes by key
          const key = classKey(successor);
          if (!stateClassSet.has(key)) {
            stateClassSet.add(key);
            classMap.set(key, successor);
            stateClasses.push(successor);
            transitionMap.set(successor, new Map());
            queue.push(successor);
          } else {
            // Rewrite edge target to existing canonical instance
            const canonical = classMap.get(key)!;
            if (canonical !== successor) {
              const edges = tEdges.get(transition)!;
              edges[edges.length - 1] = { branchIndex: vt.branchIndex, target: canonical };
            }
          }
        }
      }
    }

    return new StateClassGraph(net, initialClass, stateClasses, transitionMap, complete);
  }

  stateClasses(): readonly StateClass[] {
    return this._stateClasses;
  }

  size(): number {
    return this._stateClasses.length;
  }

  isComplete(): boolean {
    return this._complete;
  }

  successors(sc: StateClass): Set<StateClass> {
    return this._successors.get(sc) ?? new Set();
  }

  predecessors(sc: StateClass): Set<StateClass> {
    return this._predecessors.get(sc) ?? new Set();
  }

  /** Returns all outgoing transitions with their branch edges. */
  outgoingBranchEdges(sc: StateClass): Map<Transition, BranchEdge[]> {
    return this._transitions.get(sc) ?? new Map();
  }

  /** Returns the branch edges for a specific transition from a state class. */
  branchEdges(sc: StateClass, transition: Transition): BranchEdge[] {
    const map = this._transitions.get(sc);
    if (!map) return [];
    return map.get(transition) ?? [];
  }

  /** Returns all transitions that are enabled from a state class. */
  enabledTransitions(sc: StateClass): Set<Transition> {
    const map = this._transitions.get(sc);
    if (!map) return new Set();
    return new Set(map.keys());
  }

  /** Finds all state classes with a given marking. */
  classesWithMarking(marking: MarkingState): StateClass[] {
    const key = marking.toString();
    return this._stateClasses.filter(sc => sc.marking.toString() === key);
  }

  /** Checks if a marking is reachable. */
  isReachable(marking: MarkingState): boolean {
    const key = marking.toString();
    return this._stateClasses.some(sc => sc.marking.toString() === key);
  }

  /** Gets all reachable markings. */
  reachableMarkings(): Set<string> {
    const markings = new Set<string>();
    for (const sc of this._stateClasses) {
      markings.add(sc.marking.toString());
    }
    return markings;
  }

  /** Counts edges in the graph (each branch edge counts separately). */
  edgeCount(): number {
    let count = 0;
    for (const map of this._transitions.values()) {
      for (const edges of map.values()) {
        count += edges.length;
      }
    }
    return count;
  }

  toString(): string {
    return `StateClassGraph[classes=${this.size()}, edges=${this.edgeCount()}, complete=${this._complete}]`;
  }
}

function classKey(sc: StateClass): string {
  return `${sc.marking.toString()}|${sc.firingDomain.toString()}`;
}

/**
 * Builds the initial state class (enabled set + firing-domain DBM after letting
 * time pass). Shared by the plain SCG and the name-aware ν-partition SCG
 * (NU-050, Route B).
 */
export function initialStateClass(
  net: PetriNet,
  initialMarking: MarkingState,
  envPlaces: Set<Place<any>>,
  envMode: EnvironmentAnalysisMode,
): StateClass {
  const enabledTransitions = findEnabledTransitions(net, initialMarking, envPlaces, envMode);
  const clockNames = enabledTransitions.map(t => t.name);
  const lowerBounds = enabledTransitions.map(t => earliest(t.timing) / 1000);
  const upperBounds = enabledTransitions.map(t => latest(t.timing) / 1000);
  const baseDBM = DBM.create(clockNames, lowerBounds, upperBounds);
  // Class-relative earliest-ready time of each enabled clock, captured BEFORE
  // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
  const readyEarliest = enabledTransitions.map((_, k) => baseDBM.getLowerBound(k));
  const initialDBM = baseDBM.letTimePass();
  return new StateClass(initialMarking, initialDBM, enabledTransitions, readyEarliest);
}

export function expandTransition(t: Transition): VirtualTransition[] {
  let branches: ReadonlyArray<ReadonlySet<Place<any>>>;

  if (t.outputSpec !== null) {
    branches = enumerateBranches(t.outputSpec);
  } else {
    branches = [new Set()];
  }

  return branches.map((outputPlaces, i) => ({
    transition: t,
    branchIndex: i,
    outputPlaces: outputPlaces as ReadonlySet<Place<any>>,
  }));
}

export function computeSuccessor(
  net: PetriNet,
  current: StateClass,
  fired: VirtualTransition,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): StateClass | null {
  const transition = fired.transition;

  // 1. Compute new marking
  const newMarking = fireTransition(current.marking, transition, fired.outputPlaces, environmentPlaces, environmentMode);

  // 2. Determine persistent and newly enabled transitions
  const newEnabledAll = findEnabledTransitions(net, newMarking, environmentPlaces, environmentMode);

  const persistent: Transition[] = [];
  const persistentIndices: number[] = [];
  for (let i = 0; i < current.enabledTransitions.length; i++) {
    const t = current.enabledTransitions[i]!;
    if (t !== transition && newEnabledAll.includes(t)) {
      persistent.push(t);
      persistentIndices.push(i);
    }
  }

  const newlyEnabled: Transition[] = [];
  for (const t of newEnabledAll) {
    if (!persistent.includes(t)) {
      newlyEnabled.push(t);
    }
  }

  // 3. Compute successor DBM
  const firedIdx = current.transitionIndex(transition);
  const newClockNames = newlyEnabled.map(t => t.name);
  const newLowerBounds = newlyEnabled.map(t => earliest(t.timing) / 1000);
  const newUpperBounds = newlyEnabled.map(t => latest(t.timing) / 1000);

  const firedDBM = current.firingDomain.fireTransition(
    firedIdx,
    newClockNames,
    newLowerBounds,
    newUpperBounds,
    persistentIndices,
  );

  // allEnabled order matches firedDBM's clock order (persistent-then-newly-enabled).
  // Capture the class-relative earliest-ready time of each clock BEFORE
  // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
  const allEnabled = [...persistent, ...newlyEnabled];
  const readyEarliest = allEnabled.map((_, k) => firedDBM.getLowerBound(k));

  const newDBM = firedDBM.letTimePass();

  return new StateClass(newMarking, newDBM, allEnabled, readyEarliest);
}

function findEnabledTransitions(
  net: PetriNet,
  marking: MarkingState,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): Transition[] {
  const enabled: Transition[] = [];
  for (const transition of net.transitions) {
    if (isEnabled(transition, marking, environmentPlaces, environmentMode)) {
      enabled.push(transition);
    }
  }
  return enabled;
}

function isEnabled(
  transition: Transition,
  marking: MarkingState,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): boolean {
  for (const spec of transition.inputSpecs) {
    const required = inputRequiredCount(spec);
    if (!checkPlaceEnabled(spec.place, required, marking, environmentPlaces, environmentMode)) {
      return false;
    }
  }

  for (const arc of transition.reads) {
    if (!checkPlaceEnabled(arc.place, 1, marking, environmentPlaces, environmentMode)) {
      return false;
    }
  }

  for (const arc of transition.inhibitors) {
    if (marking.hasTokens(arc.place)) {
      return false;
    }
  }

  return true;
}

function inputRequiredCount(spec: In): number {
  switch (spec.type) {
    case 'one': return 1;
    case 'exactly': return spec.count;
    case 'all': return 1;
    case 'at-least': return spec.minimum;
  }
}

/**
 * Number of tokens this transition removes from `spec.place` when it fires,
 * given the `available` count currently in that place.
 *
 * Delegates to {@link consumptionCount} — the canonical IO-007 definition in
 * `core/in.ts`. The executors do not call it: `BitmapNetExecutor` fuses the
 * same rule into its consume loop (`bitmap-net-executor.ts:745`) and
 * `PrecompiledNetExecutor` compiles it to a CONSUME_ALL / CONSUME_ATLEAST
 * opcode resolved at run time (`precompiled-net.ts:423`). Three encodings of
 * one rule, which must stay in agreement.
 *
 * The analysis MUST NOT add a fourth: a divergent local definition here is
 * exactly what produced a verifier soundness bug (`all` was modelled as
 * consuming 1).
 *
 * `all` and `at-least` are **draining** arcs. The executor removes *every*
 * available token, not merely the minimum needed to enable. Do not
 * "simplify" this back to a constant. Modelling a minimum leaves residual
 * tokens the real net never holds; those phantom tokens keep inhibitor arcs
 * on the drained place unsatisfied, so successor state classes are never
 * generated and a genuinely reachable marking is reported unreachable. Since
 * `nu-scg-verifier` derives a `proven` verdict from this graph, that is a
 * false `Proven` — an unsound result, not merely an imprecise one.
 *
 * Note the deliberate asymmetry with {@link inputRequiredCount}
 * (`all` => 1, `at-least` => minimum): *enablement* tests the minimum,
 * *consumption* takes everything. Both are correct, for different questions.
 */
function inputConsumeCount(spec: In, available: number): number {
  return consumptionCount(spec, available);
}

function checkPlaceEnabled(
  place: Place<any>,
  required: number,
  marking: MarkingState,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): boolean {
  if (!environmentPlaces.has(place)) {
    return marking.tokens(place) >= required;
  }

  switch (environmentMode.type) {
    case 'always-available': return true;
    case 'bounded': return required <= environmentMode.maxTokens;
    case 'ignore': return marking.tokens(place) >= required;
  }
}

function fireTransition(
  marking: MarkingState,
  transition: Transition,
  outputPlaces: ReadonlySet<Place<any>>,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): MarkingState {
  const builder = MarkingState.builder().copyFrom(marking);

  // Consume from inputs. `all`/`at-least` drain the place, so the consumed
  // amount depends on what is actually there — read the current marking.
  for (const spec of transition.inputSpecs) {
    const available = marking.tokens(spec.place);
    if (available < inputRequiredCount(spec)) {
      // Only reachable for environment places under the always-available /
      // bounded modes, where enablement deliberately ignores the concrete
      // marking. consumeFromPlace is a no-op for those, so nothing to remove.
      continue;
    }
    const toConsume = inputConsumeCount(spec, available);
    consumeFromPlace(builder, spec.place, toConsume, environmentPlaces, environmentMode);
  }

  // Reset places
  for (const arc of transition.resets) {
    const current = marking.tokens(arc.place);
    if (current > 0) {
      builder.removeTokens(arc.place, current);
    }
  }

  // Produce to outputs
  for (const place of outputPlaces) {
    builder.addTokens(place, 1);
  }

  return builder.build();
}

function consumeFromPlace(
  builder: ReturnType<typeof MarkingState.builder>,
  place: Place<any>,
  count: number,
  environmentPlaces: Set<Place<any>>,
  environmentMode: EnvironmentAnalysisMode,
): void {
  if (!environmentPlaces.has(place)) {
    builder.removeTokens(place, count);
    return;
  }
  if (environmentMode.type === 'ignore') {
    builder.removeTokens(place, count);
  }
}
