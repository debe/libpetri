import { withTerminalInhibitors } from '../terminal-places.js';
import { completionTransition, inFlightPlace, sourceTransition, splitInFlight, splitNote } from '../in-flight.js';
import { place } from '../../core/place.js';
import type { Place } from '../../core/place.js';
import type { EnvironmentPlace } from '../../core/place.js';
import type { Transition } from '../../core/transition.js';
import type { PetriNet } from '../../core/petri-net.js';
import { outcomes } from './branch-outcomes.js';
import { MarkingState } from '../marking-state.js';
import { StateClassGraph } from './state-class-graph.js';
import type { StateClass } from './state-class.js';
import { computeSCCs, findTerminalSCCs } from './scc-analyzer.js';
import type { EnvironmentAnalysisMode } from './environment-analysis-mode.js';
import { ignore } from './environment-analysis-mode.js';

/** Result of liveness analysis. */
export interface LivenessResult {
  readonly stateClassGraph: StateClassGraph;
  readonly allSCCs: Set<StateClass>[];
  readonly terminalSCCs: Set<StateClass>[];
  readonly goalClasses: Set<StateClass>;
  readonly canReachGoal: Set<StateClass>;
  readonly isGoalLive: boolean;
  readonly isL4Live: boolean;
  readonly isComplete: boolean;
  readonly report: string;
}

/** Information about XOR branch coverage for a single transition. */
export interface XorBranchInfo {
  readonly totalBranches: number;
  readonly takenBranches: Set<number>;
  readonly untakenBranches: Set<number>;
  readonly branchOutputs: ReadonlyArray<ReadonlySet<Place<any>>>;
}

/** Result of XOR branch analysis. */
export interface XorBranchAnalysis {
  readonly transitionBranches: Map<Transition, XorBranchInfo>;
  unreachableBranches(): Map<Transition, Set<number>>;
  isXorComplete(): boolean;
  report(): string;
}

/**
 * Formal analyzer for Time Petri Nets using the State Class Graph method.
 * Implements Berthomieu-Diaz (1991) analysis.
 */
export class TimePetriNetAnalyzer {
  private readonly net: PetriNet;
  /** The net as the caller passed it, before the in-flight split and the terminal rewrite. */
  private readonly callerNet: PetriNet;
  /** The in-flight split line of the report ([VER-004]), or `null` when nothing was split. */
  private readonly inFlightLine: string | null = null;
  private readonly initialMarking: MarkingState;
  private readonly goalPlaces: Set<Place<any>>;
  private readonly maxClasses: number;
  private readonly environmentPlaces: Set<EnvironmentPlace<any>>;
  private readonly environmentMode: EnvironmentAnalysisMode;

  /** @internal Called by builder — use `TimePetriNetAnalyzer.forNet()` instead. */
  static create(
    net: PetriNet,
    initialMarking: MarkingState,
    goalPlaces: Set<Place<any>>,
    maxClasses: number,
    environmentPlaces: Set<EnvironmentPlace<any>>,
    environmentMode: EnvironmentAnalysisMode,
  ): TimePetriNetAnalyzer {
    return new TimePetriNetAnalyzer(net, initialMarking, goalPlaces, maxClasses, environmentPlaces, environmentMode);
  }

  private constructor(
    net: PetriNet,
    initialMarking: MarkingState,
    goalPlaces: Set<Place<any>>,
    maxClasses: number,
    environmentPlaces: Set<EnvironmentPlace<any>>,
    environmentMode: EnvironmentAnalysisMode,
  ) {
    // VER-004: a transition whose output another tests non-monotonically fires in two steps, as
    // the executor fires it. Before the terminal rewrite, whose inhibitor counts as such a test.
    this.callerNet = net;
    const split = splitInFlight(net);
    if (split.type === 'split') {
      net = split.net;
      this.inFlightLine = splitNote(split.split).trimEnd();
    } else if (split.type === 'refused') {
      this.inFlightLine =
        `WARNING: ${split.reason}; the graph fires it in one step, so it can miss runs of the executor.`;
    }
    // EXEC-042: the net's terminal places inhibit every transition, as the runtime stops there.
    // The same instance for a net without terminals.
    this.net = withTerminalInhibitors(net);
    this.initialMarking = initialMarking;
    this.goalPlaces = goalPlaces;
    this.maxClasses = maxClasses;
    this.environmentPlaces = environmentPlaces;
    this.environmentMode = environmentMode;
  }

  static forNet(net: PetriNet): TimePetriNetAnalyzerBuilder {
    return new TimePetriNetAnalyzerBuilder(net);
  }

  /** Performs formal liveness analysis. */
  analyze(): LivenessResult {
    const report: string[] = [];
    report.push('=== TIME PETRI NET FORMAL ANALYSIS ===\n');
    report.push(`Method: State Class Graph (Berthomieu-Diaz 1991)`);
    report.push(`Net: ${this.net.name}`);
    report.push(`Places: ${this.net.places.size}`);
    report.push(`Transitions: ${this.net.transitions.size}`);
    report.push(`Goal places: [${[...this.goalPlaces].map(p => p.name).join(', ')}]\n`);
    if (this.inFlightLine !== null) report.push(`${this.inFlightLine}\n`);

    // Phase 1: Build State Class Graph
    report.push('Phase 1: Building State Class Graph...');
    if (this.environmentPlaces.size > 0) {
      report.push(`  Environment places: ${this.environmentPlaces.size}`);
      report.push(`  Environment mode: ${this.environmentMode.type}`);
    }
    const scg = StateClassGraph.build(this.net, this.initialMarking, this.maxClasses, this.environmentPlaces, this.environmentMode);
    report.push(`  State classes: ${scg.size()}`);
    report.push(`  Edges: ${scg.edgeCount()}`);
    report.push(`  Complete: ${scg.isComplete() ? 'YES' : 'NO (truncated)'}`);

    if (!scg.isComplete()) {
      report.push(`  WARNING: State class graph truncated at ${this.maxClasses} classes. Analysis may be incomplete.`);
    }
    report.push('');

    // Phase 2: Identify goal state classes
    report.push('Phase 2: Identifying goal state classes...');
    const goalClasses = new Set<StateClass>();
    for (const sc of scg.stateClasses()) {
      if (sc.marking.hasTokensInAny(this.goalPlaces)) {
        goalClasses.add(sc);
      }
    }
    report.push(`  Goal state classes: ${goalClasses.size}\n`);

    // Phase 3: Compute SCCs
    report.push('Phase 3: Computing Strongly Connected Components...');
    const successorFn = (sc: StateClass) => scg.successors(sc);
    const allSCCs = computeSCCs(scg.stateClasses(), successorFn);
    const terminalSCCs = findTerminalSCCs(scg.stateClasses(), successorFn);

    report.push(`  Total SCCs: ${allSCCs.length}`);
    report.push(`  Terminal SCCs: ${terminalSCCs.length}\n`);

    // Phase 4: Check goal liveness
    report.push('Phase 4: Verifying Goal Liveness...');
    report.push('  Property: From every reachable state, a goal state is reachable');

    const terminalSCCsWithGoal: Set<StateClass>[] = [];
    const terminalSCCsWithoutGoal: Set<StateClass>[] = [];

    for (const scc of terminalSCCs) {
      let hasGoal = false;
      for (const sc of scc) {
        if (goalClasses.has(sc)) { hasGoal = true; break; }
      }
      (hasGoal ? terminalSCCsWithGoal : terminalSCCsWithoutGoal).push(scc);
    }

    report.push(`  Terminal SCCs with goal: ${terminalSCCsWithGoal.length}`);
    report.push(`  Terminal SCCs without goal: ${terminalSCCsWithoutGoal.length}`);

    const canReachGoal = computeBackwardReachability(scg, goalClasses);
    const statesNotReachingGoal = scg.size() - canReachGoal.size;

    report.push(`  States that can reach goal: ${canReachGoal.size}/${scg.size()}\n`);

    const isGoalLive = terminalSCCsWithoutGoal.length === 0 && statesNotReachingGoal === 0;

    // Phase 5: Check classical liveness (L4)
    report.push('Phase 5: Verifying Classical Liveness (L4)...');
    report.push('  Property: Every transition can fire from every reachable marking');

    // The caller's transitions: a completion step `complete:<t>` of the split net fires for `t`
    // ([VER-004]), so the list never names one.
    const allTransitions = [...this.callerNet.transitions].map(t => t.name);
    const terminalSCCsMissingTransitions: Set<StateClass>[] = [];

    for (const scc of terminalSCCs) {
      const transitionsInSCC = new Set<string>();
      for (const sc of scc) {
        for (const t of scg.enabledTransitions(sc)) {
          const edges = scg.branchEdges(sc, t);
          for (const edge of edges) {
            if (scc.has(edge.target)) {
              transitionsInSCC.add(sourceTransition(this.net, t.name));
            }
          }
        }
      }
      const missing = allTransitions.filter(t => !transitionsInSCC.has(t));
      if (missing.length > 0) {
        terminalSCCsMissingTransitions.push(scc);
        report.push(`  Terminal SCC missing transitions: [${missing.join(', ')}]`);
      }
    }

    const isL4Live = terminalSCCsMissingTransitions.length === 0 && scg.isComplete();

    // Summary
    report.push('\n=== ANALYSIS RESULT ===\n');

    if (isGoalLive && scg.isComplete()) {
      report.push('GOAL LIVENESS VERIFIED');
      report.push('  From every reachable state class, a goal marking is reachable.');
    } else if (isGoalLive && !scg.isComplete()) {
      report.push('GOAL LIVENESS LIKELY (incomplete proof)');
    } else {
      report.push('GOAL LIVENESS VIOLATION');
      if (terminalSCCsWithoutGoal.length > 0) {
        report.push(`  ${terminalSCCsWithoutGoal.length} terminal SCC(s) have no goal state.`);
      }
      if (statesNotReachingGoal > 0) {
        report.push(`  ${statesNotReachingGoal} state class(es) cannot reach goal.`);
      }
    }

    report.push('');

    if (isL4Live) {
      report.push('CLASSICAL LIVENESS (L4) VERIFIED');
    } else {
      report.push('CLASSICAL LIVENESS (L4) NOT VERIFIED');
      if (terminalSCCsMissingTransitions.length > 0) {
        report.push("  Some terminal SCCs don't contain all transitions.");
      }
      if (!scg.isComplete()) {
        report.push('  (State class graph incomplete - cannot prove L4)');
      }
    }

    return {
      stateClassGraph: scg,
      allSCCs,
      terminalSCCs,
      goalClasses,
      canReachGoal,
      isGoalLive,
      isL4Live,
      isComplete: scg.isComplete(),
      report: report.join('\n'),
    };
  }

  /**
   * Analyzes XOR branch coverage for a built state class graph. `net` is the net the caller
   * analysed (default: the graph's own); the result is keyed by its transitions. A XOR transition
   * the analyzer split in flight ([VER-004]) takes its branches in its completion step
   * `complete:<t>`, so they are read off that step.
   */
  static analyzeXorBranches(scg: StateClassGraph, net?: PetriNet): XorBranchAnalysis {
    const result = new Map<Transition, XorBranchInfo>();
    const graphNet = scg.net;
    const inGraph = new Map([...graphNet.transitions].map(t => [t.name, t] as const));
    const source = net ?? graphNet;

    for (const transition of source.transitions) {
      // On the graph's own net a completion step stands for its transition, read below.
      if (net === undefined && sourceTransition(graphNet, transition.name) !== transition.name) continue;
      const completion = inGraph.get(completionTransition(transition.name));
      const flight = place(inFlightPlace(transition.name));
      const split = completion !== undefined && (
        scg.stateClasses().some(sc => scg.branchEdges(sc, completion).length > 0)
        || scg.stateClasses().some(sc => sc.marking.tokens(flight) > 0)
      );
      const label = split ? completion : inGraph.get(transition.name) ?? transition;
      // The graph's virtual transitions: each XOR branch, and a timeout that deposits
      // differently (`branch-outcomes`). On the graph's own net a split transition's start has
      // one outcome, so its completion's are read.
      const allBranches = outcomes(net === undefined && split ? completion : transition);
      if (allBranches.length <= 1) continue;

      const takenBranches = new Set<number>();
      for (const sc of scg.stateClasses()) {
        const edges = scg.branchEdges(sc, label);
        for (const edge of edges) {
          takenBranches.add(edge.branchIndex);
        }
      }

      const untakenBranches = new Set<number>();
      for (let i = 0; i < allBranches.length; i++) {
        if (!takenBranches.has(i)) untakenBranches.add(i);
      }

      result.set(transition, {
        totalBranches: allBranches.length,
        takenBranches,
        untakenBranches,
        branchOutputs: allBranches.map(o => o.places),
      });
    }

    return createXorBranchAnalysis(result);
  }
}

function createXorBranchAnalysis(transitionBranches: Map<Transition, XorBranchInfo>): XorBranchAnalysis {
  return {
    transitionBranches,
    unreachableBranches(): Map<Transition, Set<number>> {
      const result = new Map<Transition, Set<number>>();
      for (const [t, info] of transitionBranches) {
        if (info.untakenBranches.size > 0) {
          result.set(t, info.untakenBranches);
        }
      }
      return result;
    },
    isXorComplete(): boolean {
      for (const info of transitionBranches.values()) {
        if (info.untakenBranches.size > 0) return false;
      }
      return true;
    },
    report(): string {
      if (transitionBranches.size === 0) return 'No XOR transitions in net.';

      const lines: string[] = [];
      lines.push('XOR Branch Coverage Analysis');
      lines.push('============================\n');

      for (const [t, info] of transitionBranches) {
        lines.push(`Transition: ${t.name}`);
        lines.push(`  Branches: ${info.totalBranches}`);
        lines.push(`  Taken: [${[...info.takenBranches].join(', ')}]`);

        if (info.untakenBranches.size > 0) {
          lines.push(`  UNREACHABLE: [${[...info.untakenBranches].join(', ')}]`);
          for (const idx of info.untakenBranches) {
            const places = [...info.branchOutputs[idx]!].map(p => p.name).join(', ');
            lines.push(`    Branch ${idx} outputs: [${places}]`);
          }
        } else {
          lines.push('  All branches reachable');
        }
        lines.push('');
      }

      if (this.isXorComplete()) {
        lines.push('RESULT: All XOR branches are reachable.');
      } else {
        lines.push('RESULT: Some XOR branches are unreachable!');
      }

      return lines.join('\n');
    },
  };
}

function computeBackwardReachability(scg: StateClassGraph, goals: Set<StateClass>): Set<StateClass> {
  const reachable = new Set(goals);
  const queue = [...goals];

  while (queue.length > 0) {
    const current = queue.shift()!;
    for (const pred of scg.predecessors(current)) {
      if (!reachable.has(pred)) {
        reachable.add(pred);
        queue.push(pred);
      }
    }
  }

  return reachable;
}

/** Builder for TimePetriNetAnalyzer. */
export class TimePetriNetAnalyzerBuilder {
  private readonly net: PetriNet;
  private _initialMarking: MarkingState = MarkingState.empty();
  private readonly _goalPlaces = new Set<Place<any>>();
  private _maxClasses = 100_000;
  private readonly _environmentPlaces = new Set<EnvironmentPlace<any>>();
  private _environmentMode: EnvironmentAnalysisMode = ignore();

  constructor(net: PetriNet) {
    this.net = net;
  }

  initialMarking(marking: MarkingState): this {
    this._initialMarking = marking;
    return this;
  }

  goalPlaces(...places: Place<any>[]): this {
    for (const p of places) this._goalPlaces.add(p);
    return this;
  }

  maxClasses(max: number): this {
    this._maxClasses = max;
    return this;
  }

  environmentPlaces(...places: EnvironmentPlace<any>[]): this {
    for (const ep of places) this._environmentPlaces.add(ep);
    return this;
  }

  environmentMode(mode: EnvironmentAnalysisMode): this {
    this._environmentMode = mode;
    return this;
  }

  build(): TimePetriNetAnalyzer {
    if (this._goalPlaces.size === 0) {
      throw new Error('At least one goal place must be specified');
    }
    return TimePetriNetAnalyzer.create(
      this.net,
      this._initialMarking,
      this._goalPlaces,
      this._maxClasses,
      this._environmentPlaces,
      this._environmentMode,
    );
  }
}
