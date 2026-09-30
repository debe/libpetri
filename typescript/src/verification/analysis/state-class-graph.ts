import type { Place } from '../../core/place.js';
import type { EnvironmentPlace } from '../../core/place.js';
import type { In } from '../../core/in.js';
import { consumptionCount, requiredCount } from '../../core/in.js';
import type { Transition } from '../../core/transition.js';
import type { PetriNet } from '../../core/petri-net.js';
import { earliest, immediate, latest, type Timing } from '../../core/timing.js';
import { type Outcome, depositCount, outcomes } from './branch-outcomes.js';
import { MarkingState } from '../marking-state.js';
import { DBM } from './dbm.js';
import { StateClass } from './state-class.js';
import type { EnvironmentAnalysisMode } from './environment-analysis-mode.js';
import { arrivalsNotModelled, ignore } from './environment-analysis-mode.js';
import { requireOutputProducingActions } from '../../core/internal/output-action-check.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';
import { environmentPlaceNames } from '../../core/internal/place-names.js';
import { Deadline } from '../total-budget.js';
import type { TotalBudgetExhausted } from '../total-budget.js';

/** Edge that tracks which XOR branch was taken. */
export interface BranchEdge {
  readonly branchIndex: number;
  readonly target: StateClass;
}

export interface VirtualTransition {
  readonly transition: Transition;
  readonly branchIndex: number;
  /** The places this outcome deposits into (the ν name layer reads places, not counts). */
  readonly outputPlaces: ReadonlySet<Place<any>>;
  /**
   * How many tokens each of those places receives: one per place an action writes, one per
   * consumed token for a timeout forward ([IO-014]).
   */
  readonly outcome: Outcome;
}

/** Options for {@link StateClassGraph.build}. */
export interface StateClassGraphOptions {
  /**
   * Explore the **untimed** reachable set ([VER-004]): every clock gets `immediate()`'s
   * `[0, ∞)`, so any enabled transition may fire next and the graph holds exactly the
   * markings the untimed encoders reason about. No effect on an all-immediate net.
   */
  readonly untimed?: boolean;
  /**
   * The total verification budget's deadline ([VER-013]): the build polls it and throws
   * {@link TotalBudgetExhausted} once it has passed. A build cut off this way returns no graph,
   * so nothing can mistake it for a class-budget truncation.
   */
  readonly deadline?: Deadline | null;
}

const IMMEDIATE: Timing = immediate();

/** The timing a clock is given: the transition's own, or `immediate()` when exploring untimed. */
function clockTiming(t: Transition, untimed: boolean): Timing {
  return untimed ? IMMEDIATE : t.timing;
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
  private readonly _expanded: number;

  private constructor(
    net: PetriNet,
    initialClass: StateClass,
    stateClasses: StateClass[],
    transitions: Map<StateClass, Map<Transition, BranchEdge[]>>,
    complete: boolean,
    expanded: number,
  ) {
    this.net = net;
    this.initialClass = initialClass;
    this._stateClasses = stateClasses;
    this._transitions = transitions;
    this._complete = complete;
    this._expanded = expanded;

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
   * The graph is built for the net as given, and every firing is one atomic step. The executor
   * consumes at the start of an action and deposits at its completion, and other transitions can
   * fire in between ([VER-004], [VER-010] AC4). To get that two-step firing, call
   * {@link splitInFlight} first and build the graph of its `net`; its `refused` case means no graph
   * of this kind is faithful to the executor. `SmtVerifier` does this itself.
   *
   * @throws Error if the net violates CORE-043 — analysis rejects the same nets execution rejects.
   */
  static build(
    net: PetriNet,
    initialMarking: MarkingState,
    maxClasses: number,
    environmentPlaces?: Set<EnvironmentPlace<any>>,
    environmentMode?: EnvironmentAnalysisMode,
    options: StateClassGraphOptions = {},
  ): StateClassGraph {
    requireOutputProducingActions(net);

    const envMode = environmentMode ?? ignore();
    // By name: an arc may name another object of an environment place (TypeScript places are
    // identified by name), and it is still the environment place.
    const envPlaces = environmentPlaceNames(environmentPlaces ?? []);
    if (envMode.type === 'arrivals' && envPlaces.size > 0) throw arrivalsNotModelled('StateClassGraph.build');
    const untimed = options.untimed === true;

    const initialClass = initialStateClass(net, initialMarking, envPlaces, envMode, untimed);

    // BFS exploration
    const stateClasses: StateClass[] = [initialClass];
    const stateClassSet = new Set<string>([classKey(initialClass)]);
    const classMap = new Map<string, StateClass>([[classKey(initialClass), initialClass]]);
    const transitionMap = new Map<StateClass, Map<Transition, BranchEdge[]>>();
    transitionMap.set(initialClass, new Map());
    // BFS in index order: every class is queued once, when it is appended, so the queue is
    // `stateClasses[expanded ..]` and needs no array of its own.
    let expanded = 0;
    let complete = true;
    const poll = Deadline.poller(options.deadline, 16);

    while (expanded < stateClasses.length) {
      if (stateClasses.length >= maxClasses) {
        complete = false;
        break;
      }
      poll();

      const current = stateClasses[expanded++]!;

      for (const transition of current.enabledTransitions) {
        const virtualTransitions = expandTransition(transition);

        for (const vt of virtualTransitions) {
          const successor = computeSuccessor(net, current, vt, envPlaces, envMode, untimed);
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

    return new StateClassGraph(net, initialClass, stateClasses, transitionMap, complete, expanded);
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

  /**
   * How many classes had their successors computed. BFS expands in index order, so
   * `stateClasses()[i]` is expanded iff `i < expandedCount()`; on a complete graph that is every
   * class. A truncated graph's unexpanded frontier has no successors recorded, which says
   * nothing about whether it is quiescent ([VER-017]).
   */
  expandedCount(): number {
    return this._expanded;
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

/**
 * The dedup key of a class: its marking and the full zone ({@link DBM.zoneKey}).
 *
 * Clocks are in canonical order by construction ({@link canonicalOrder}), so the
 * sequence in which transitions became enabled is not part of a class's identity —
 * it used to be, and on a workflow-shaped untimed net (every zone `[0, ∞)`) that
 * counted one marking once per interleaving of its enabling path: a measured
 * 1.5× class inflation, one marking held by fourteen classes.
 */
function classKey(sc: StateClass): string {
  return `${sc.marking.toString()}|${sc.firingDomain.zoneKey()}`;
}

/**
 * The canonical clock order of an enabled set: ascending by transition name in code-point
 * order ([VER-013]), ties keeping their incoming order. Returns the permutation as indices
 * into `transitions`, or `null`, without allocating, when already in order.
 *
 * Observable: successors are explored in this order, which picks the shallowest witness a
 * report prints.
 */
export function canonicalOrder(transitions: readonly Transition[]): number[] | null {
  let sorted = true;
  for (let i = 1; i < transitions.length; i++) {
    if (compareCodePoints(transitions[i]!.name, transitions[i - 1]!.name) < 0) {
      sorted = false;
      break;
    }
  }
  if (sorted) return null;
  const order: number[] = new Array<number>(transitions.length);
  for (let i = 0; i < order.length; i++) order[i] = i;
  order.sort((a, b) => compareCodePoints(transitions[a]!.name, transitions[b]!.name) || a - b);
  return order;
}

function permute<T>(items: readonly T[], order: readonly number[]): T[] {
  const out: T[] = new Array<T>(items.length);
  for (let i = 0; i < order.length; i++) out[i] = items[order[i]!]!;
  return out;
}

/**
 * Builds the initial state class (enabled set + firing-domain DBM after letting
 * time pass). Shared by the plain SCG and the name-aware ν-partition SCG
 * (NU-050, Route B).
 */
export function initialStateClass(
  net: PetriNet,
  initialMarking: MarkingState,
  envPlaces: ReadonlySet<string>,
  envMode: EnvironmentAnalysisMode,
  untimed = false,
): StateClass {
  const found = findEnabledTransitions(net, initialMarking, envPlaces, envMode);
  const order = canonicalOrder(found);
  const enabledTransitions = order === null ? found : permute(found, order);
  const clockNames = enabledTransitions.map(t => t.name);
  const lowerBounds = enabledTransitions.map(t => earliest(clockTiming(t, untimed)) / 1000);
  const upperBounds = enabledTransitions.map(t => latest(clockTiming(t, untimed)) / 1000);
  const baseDBM = DBM.create(clockNames, lowerBounds, upperBounds);
  // Class-relative earliest-ready time of each enabled clock, captured BEFORE
  // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
  const readyEarliest = enabledTransitions.map((_, k) => baseDBM.getLowerBound(k));
  const initialDBM = baseDBM.letTimePass();
  return new StateClass(initialMarking, initialDBM, enabledTransitions, readyEarliest);
}

/**
 * The virtual transitions of one firing of `t`: every way it can end (`branch-outcomes`),
 * numbered as the flattener numbers its `_b<i>` rows.
 */
export function expandTransition(t: Transition): VirtualTransition[] {
  return outcomes(t).map((outcome, i) => ({
    transition: t,
    branchIndex: i,
    outputPlaces: outcome.places,
    outcome,
  }));
}

/**
 * An enabling condition beyond the count marking, for {@link computeSuccessor}: a transition
 * holds a clock in the intermediate marking only if `between` accepts it, and in the new marking
 * only if `after` does. The ν-aware graph passes a ν-join's name test here: the executor enables
 * a join only while one name is present in every correlated input (NU-020), and a removal that
 * breaks the binding restarts its clock (TIME-012).
 */
export interface EnablingGate {
  readonly between: (t: Transition) => boolean;
  readonly after: (t: Transition) => boolean;
}

export function computeSuccessor(
  net: PetriNet,
  current: StateClass,
  fired: VirtualTransition,
  environmentPlaces: ReadonlySet<string>,
  environmentMode: EnvironmentAnalysisMode,
  untimed = false,
  gate: EnablingGate | null = null,
): StateClass | null {
  const transition = fired.transition;

  // 1. Fire in two halves: the intermediate marking M - Pre(t) (inputs consumed, resets
  //    drained, nothing produced yet), then the new marking.
  const intermediate = consumeInputs(current.marking, transition, environmentPlaces, environmentMode);
  const newMarking = produceOutputs(
    current.marking, intermediate, transition, fired.outcome, environmentPlaces, environmentMode,
  );

  // 2. Determine persistent and newly enabled transitions. A clock persists only when its
  //    transition is not the fired one and stays enabled across the whole firing: in this
  //    class, in the intermediate marking and in the new marking. A transition the firing
  //    disables and re-enables (its token taken and put back, or a reset place refilled by
  //    the outputs) is newly enabled with a fresh interval, as the executors restart its
  //    clock (TIME-012). Surplus tokens keep it enabled throughout, so it stays persistent.
  //    With a `gate`, `current.enabledTransitions` already satisfies it for this class.
  let newEnabledAll = findEnabledTransitions(net, newMarking, environmentPlaces, environmentMode);
  if (gate !== null) newEnabledAll = newEnabledAll.filter(gate.after);

  const persistent: Transition[] = [];
  const persistentIndices: number[] = [];
  for (let i = 0; i < current.enabledTransitions.length; i++) {
    const t = current.enabledTransitions[i]!;
    if (
      t !== transition
      && newEnabledAll.includes(t)
      && isEnabled(t, intermediate, environmentPlaces, environmentMode)
      && (gate === null || gate.between(t))
    ) {
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
  const newLowerBounds = newlyEnabled.map(t => earliest(clockTiming(t, untimed)) / 1000);
  const newUpperBounds = newlyEnabled.map(t => latest(clockTiming(t, untimed)) / 1000);

  let firedDBM = current.firingDomain.fireTransition(
    firedIdx,
    newClockNames,
    newLowerBounds,
    newUpperBounds,
    persistentIndices,
  );

  // fireTransition lays the clocks out persistent-then-newly-enabled, which is
  // path-dependent; put them in canonical order so the class key is (VER-010).
  // The enabled list and the earliest-ready times below are permuted with them,
  // so index k means the same clock in all three.
  let allEnabled: Transition[] = [...persistent, ...newlyEnabled];
  const order = canonicalOrder(allEnabled);
  if (order !== null) {
    allEnabled = permute(allEnabled, order);
    firedDBM = firedDBM.permuted(order);
  }

  // Capture the class-relative earliest-ready time of each clock BEFORE
  // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
  const readyEarliest = allEnabled.map((_, k) => firedDBM.getLowerBound(k));

  const newDBM = firedDBM.letTimePass();

  return new StateClass(newMarking, newDBM, allEnabled, readyEarliest);
}

function findEnabledTransitions(
  net: PetriNet,
  marking: MarkingState,
  environmentPlaces: ReadonlySet<string>,
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
  environmentPlaces: ReadonlySet<string>,
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
 * same rule into its consume loop (`bitmap-net-executor.ts:788`) and
 * `PrecompiledNetExecutor` compiles it to a CONSUME_ALL / CONSUME_ATLEAST
 * opcode resolved at run time (`precompiled-net.ts:440`). Three encodings of
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
  environmentPlaces: ReadonlySet<string>,
  environmentMode: EnvironmentAnalysisMode,
): boolean {
  if (!environmentPlaces.has(place.name)) {
    return marking.tokens(place) >= required;
  }

  switch (environmentMode.type) {
    case 'always-available': return true;
    case 'bounded': return required <= environmentMode.maxTokens;
    case 'ignore': return marking.tokens(place) >= required;
    // Refused at build time; a closed net has no environment places.
    case 'arrivals': throw arrivalsNotModelled('StateClassGraph');
  }
}

/**
 * The first half of a firing: inputs consumed and reset places drained, nothing produced
 * yet. The result is the intermediate marking M - Pre(t) of Berthomieu and Diaz, on which
 * clock persistence is decided (TIME-012); {@link produceOutputs} completes the firing.
 */
function consumeInputs(
  marking: MarkingState,
  transition: Transition,
  environmentPlaces: ReadonlySet<string>,
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

  // Reset places: clear whatever is LEFT after the input loop, not what the
  // pre-firing marking held. Reading the original count overdraws whenever the
  // reset place is also an input — the inputs already took their share — and
  // `removeTokens` throws on the overdraw rather than mis-computing, so the whole
  // route died on a net both executors run happily. Setting the count states the
  // reset directly and cannot overdraw; it is also what the flat encoder emits
  // (`m'_p = postVector[p]` for a reset place, `firingConditions`), so the two
  // agree by construction. Outputs are produced after this, by produceOutputs,
  // so a place that is both reset and an output target ends at its post count
  // ([EXEC-013] AC4: consume, then read, then drain).
  for (const arc of transition.resets) {
    builder.tokens(arc.place, 0);
  }

  return builder.build();
}

/**
 * The second half of a firing: the fired outcome's tokens deposited — one per place an action
 * writes, and for a timeout forward one per token the firing consumed from its `from` place
 * ([IO-014]): a fixed count for `one` / `exactly`, the batch `marking` drained for `all` /
 * `atLeast`. An environment place the analysis supplies ({@link isEnabled}) is not drained; its
 * forward counts the tokens the firing required.
 */
function produceOutputs(
  marking: MarkingState,
  intermediate: MarkingState,
  transition: Transition,
  outcome: Outcome,
  environmentPlaces: ReadonlySet<string>,
  environmentMode: EnvironmentAnalysisMode,
): MarkingState {
  const drained = (from: Place<any>): number => {
    const spec = transition.inputSpecs.find(s => s.place.name === from.name);
    if (spec === undefined) return 0;
    if (environmentPlaces.has(spec.place.name) && environmentMode.type !== 'ignore') return requiredCount(spec);
    const available = marking.tokens(spec.place);
    return available < requiredCount(spec) ? available : inputConsumeCount(spec, available);
  };
  const builder = MarkingState.builder().copyFrom(intermediate);
  for (const { place, deposit } of outcome.deposits) {
    const count = depositCount(deposit, drained);
    if (count > 0) builder.addTokens(place, count);
  }
  return builder.build();
}

function consumeFromPlace(
  builder: ReturnType<typeof MarkingState.builder>,
  place: Place<any>,
  count: number,
  environmentPlaces: ReadonlySet<string>,
  environmentMode: EnvironmentAnalysisMode,
): void {
  if (!environmentPlaces.has(place.name)) {
    builder.removeTokens(place, count);
    return;
  }
  if (environmentMode.type === 'ignore') {
    builder.removeTokens(place, count);
  }
}
