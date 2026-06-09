/**
 * The ν-aware (name-partition quotient) State Class Graph (NU-050, Route B).
 *
 * Mirrors {@link StateClassGraph} — same Berthomieu-Diaz BFS, same count + DBM
 * successor step (reused verbatim via {@link computeSuccessor}) — but each class
 * additionally carries the abstract {@link NameMarking} partition. A ν-join is
 * enabled only when one shared name is present at the required multiplicity in
 * every correlated input; a mint introduces a globally-fresh name-symbol; dedup
 * is by the symmetry-canonical key so states differing only by a permutation of
 * names collapse. If BFS closes within `maxClasses` the graph is the complete
 * reachable quotient (exact); otherwise it truncates and the verifier reports
 * `unknown` (ν-PN reachability is undecidable).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import type { EnvironmentPlace } from '../../core/place.js';
import type { MarkingState } from '../marking-state.js';
import type { EnvironmentAnalysisMode } from './environment-analysis-mode.js';
import { ignore } from './environment-analysis-mode.js';
import { initialStateClass, expandTransition, computeSuccessor } from './state-class-graph.js';
import { NameMarking, type Sym } from './name-marking.js';
import { NameStateClass } from './name-state-class.js';
import type { NameFragment, Role } from './name-fragment.js';

export interface NameEdge {
  readonly from: number;
  readonly to: number;
  readonly transitionName: string;
}

export class NameStateClassGraph {
  readonly classes: NameStateClass[] = [];
  readonly edges: NameEdge[] = [];
  private readonly _successors: number[][] = [];
  private _complete = true;

  isComplete(): boolean {
    return this._complete;
  }

  classCount(): number {
    return this.classes.length;
  }

  successorsOf(idx: number): readonly number[] {
    return this._successors[idx]!;
  }

  /** The base count-marking of class `idx` (for property queries). */
  markingOf(idx: number): MarkingState {
    return this.classes[idx]!.base.marking;
  }

  static build(
    net: PetriNet,
    initialMarking: MarkingState,
    fragment: NameFragment,
    maxClasses: number,
    environmentPlaces?: Set<EnvironmentPlace<any>>,
    environmentMode?: EnvironmentAnalysisMode,
  ): NameStateClassGraph {
    const envMode = environmentMode ?? ignore();
    const envPlaces = new Set<Place<any>>();
    if (environmentPlaces) {
      for (const ep of environmentPlaces) envPlaces.add(ep.place);
    }

    const graph = new NameStateClassGraph();
    const base0 = initialStateClass(net, initialMarking, envPlaces, envMode);
    // Coloured places start empty in the supported fragment (the verifier guards
    // this), so the initial name partition is empty.
    const initial = new NameStateClass(base0, new NameMarking(), fragment.colouredOrder);

    const indexOf = new Map<string, number>();
    graph.pushClass(initial, indexOf);

    const sym = { next: 0 as Sym };
    const queue: number[] = [0];

    while (queue.length > 0) {
      if (graph.classes.length >= maxClasses) {
        graph._complete = false;
        break;
      }
      const curIdx = queue.shift()!;
      const current = graph.classes[curIdx]!;

      for (const transition of current.base.enabledTransitions) {
        const role = fragment.role(transition.name);
        for (const vt of expandTransition(transition)) {
          const baseSucc = computeSuccessor(net, current.base, vt, envPlaces, envMode);
          if (baseSucc === null || baseSucc.isEmpty()) continue;
          const nameSuccs = nameSuccessors(role, current.names, vt.outputPlaces, fragment, sym);
          for (const nm of nameSuccs) {
            const succ = new NameStateClass(baseSucc, nm, fragment.colouredOrder);
            let toIdx = indexOf.get(succ.key);
            if (toIdx === undefined) {
              toIdx = graph.classes.length;
              graph.pushClass(succ, indexOf);
              queue.push(toIdx);
            }
            graph.addEdge(curIdx, toIdx, transition.name);
          }
        }
      }
    }
    return graph;
  }

  private pushClass(c: NameStateClass, indexOf: Map<string, number>): void {
    const idx = this.classes.length;
    this.classes.push(c);
    this._successors.push([]);
    indexOf.set(c.key, idx);
  }

  private addEdge(from: number, to: number, name: string): void {
    this.edges.push({ from, to, transitionName: name });
    this._successors[from]!.push(to);
  }
}

/**
 * Name-layer successors of one firing. Ordinary passes the layer through; Mint
 * stamps one globally-fresh symbol into the coloured outputs of this branch (one
 * symbol into several = same-mint siblings); Join yields one successor per
 * enabling symbol (none ⇒ the join is name-disabled).
 */
function nameSuccessors(
  role: Role,
  names: NameMarking,
  outputPlaces: ReadonlySet<Place<any>>,
  fragment: NameFragment,
  sym: { next: Sym },
): NameMarking[] {
  switch (role.type) {
    case 'ordinary':
      return [names.copy()];
    case 'mint': {
      const colouredOut = [...outputPlaces].filter(p => fragment.isColoured(p.name)).map(p => p.name);
      const nm = names.copy();
      if (colouredOut.length > 0) {
        const fresh = sym.next++;
        for (const p of colouredOut) nm.add(p, fresh, 1);
      }
      return [nm];
    }
    case 'join': {
      const result: NameMarking[] = [];
      for (const s of enablingSymbols(names, role.colouredIn)) {
        const nm = names.copy();
        for (const [p, req] of role.colouredIn) nm.remove(p, s, req);
        result.push(nm);
      }
      return result;
    }
  }
}

/**
 * Symbols that enable a join: present at the required multiplicity in EVERY
 * correlated input — the exactness core of NU-050 (a count-only check would
 * wrongly fire on two distinct names).
 */
function enablingSymbols(names: NameMarking, colouredIn: ReadonlyArray<readonly [string, number]>): Sym[] {
  if (colouredIn.length === 0) return [];
  const [firstPlace, firstReq] = colouredIn[0]!;
  const result: Sym[] = [];
  for (const s of names.symbolsIn(firstPlace)) {
    if (names.countOf(firstPlace, s) < firstReq) continue;
    let ok = true;
    for (let i = 1; i < colouredIn.length; i++) {
      const [p, req] = colouredIn[i]!;
      if (names.countOf(p, s) < req) {
        ok = false;
        break;
      }
    }
    if (ok) result.push(s);
  }
  return result;
}
