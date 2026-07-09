/**
 * ν-net exact verification via the name-aware state-class-graph name-partition
 * quotient (NU-050, Route B). Bridges {@link NameStateClassGraph} to the
 * {@link SmtVerificationResult} verdict types.
 *
 * {@link verifyViaNameScg} returns `null` when the net is outside the supported
 * mint→matched-join fragment (the caller falls back to the SMT / Route A path);
 * otherwise an exact verdict when the symbolic graph closes, or `unknown` when it
 * truncates (the live correlation pool is unbounded).
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import type { EnvironmentPlace } from '../core/place.js';
import type { MarkingState } from './marking-state.js';
import type { EnvironmentAnalysisMode } from './analysis/environment-analysis-mode.js';
import { classify, type FragmentMode } from './analysis/name-fragment.js';
import { NameStateClassGraph } from './analysis/name-state-class-graph.js';
import type { SmtProperty } from './smt-property.js';
import type { Verdict } from './smt-verification-result.js';

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
): NuScgOutcome | null {
  const fragment = classify(net, fragmentMode, carrierPlaces);
  if (fragment === null) return null;
  // We model no initial colour assignment, so coloured places must start empty.
  for (const p of initial.placesWithTokens()) {
    if (fragment.isColoured(p.name)) return null;
  }

  const scg = NameStateClassGraph.build(net, initial, fragment, maxClasses, environmentPlaces, environmentMode);

  if (!scg.isComplete()) {
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

  const violating = decide(scg, property, sinkPlaces);
  if (violating >= 0) {
    const [trace, transitions] = counterexamplePath(scg, violating);
    return { verdict: { type: 'violated' }, trace, transitions, note: NOTE_EXACT, classCount: scg.classCount() };
  }
  return {
    verdict: { type: 'proven', method: 'ν name-partition SCG (NU-050, Route B)', inductiveInvariant: null },
    trace: [],
    transitions: [],
    note: NOTE_EXACT,
    classCount: scg.classCount(),
  };
}

/** Returns a witnessing class index for a violation, or -1 if the property holds. */
function decide(scg: NameStateClassGraph, property: SmtProperty, sinkPlaces: ReadonlySet<Place<any>>): number {
  const firstWhere = (pred: (i: number) => boolean): number => {
    for (let i = 0; i < scg.classCount(); i++) {
      if (pred(i)) return i;
    }
    return -1;
  };

  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
      return firstWhere(i => scg.markingOf(i).tokens(property.place) > property.bound);
    case 'unreachable':
      return firstWhere(i => {
        const m = scg.markingOf(i);
        for (const p of property.places) {
          if (!m.hasTokens(p)) return false;
        }
        return true;
      });
    case 'mutual-exclusion':
      return firstWhere(i => {
        const m = scg.markingOf(i);
        return m.hasTokens(property.p1) && m.hasTokens(property.p2);
      });
    case 'deadlock-free':
      return firstWhere(i => scg.successorsOf(i).length === 0 && !allTokensInSinks(scg.markingOf(i), sinkPlaces));
    case 'joined-or-dead-lettered':
      return firstWhere(i => scg.successorsOf(i).length === 0 && scg.markingOf(i).hasTokens(property.pending));
  }
}

function allTokensInSinks(m: MarkingState, sinks: ReadonlySet<Place<any>>): boolean {
  const sinkNames = new Set<string>();
  for (const s of sinks) sinkNames.add(s.name);
  for (const p of m.placesWithTokens()) {
    if (!sinkNames.has(p.name)) return false;
  }
  return true;
}

/** Shortest firing sequence from the initial class (0) to `target`. */
function counterexamplePath(scg: NameStateClassGraph, target: number): [MarkingState[], string[]] {
  const n = scg.classCount();
  const parent = new Array<number>(n).fill(-1);
  const via = new Array<string>(n).fill('');
  const visited = new Array<boolean>(n).fill(false);
  visited[0] = true;
  const queue: number[] = [0];
  while (queue.length > 0) {
    const u = queue.shift()!;
    if (u === target) break;
    for (const e of scg.edges) {
      if (e.from === u && !visited[e.to]) {
        visited[e.to] = true;
        parent[e.to] = u;
        via[e.to] = e.transitionName;
        queue.push(e.to);
      }
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
