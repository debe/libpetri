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
import type { In } from '../../core/in.js';
import type { Transition } from '../../core/transition.js';
import type { MarkingState } from '../marking-state.js';
import type { EnvironmentAnalysisMode } from './environment-analysis-mode.js';
import { ignore } from './environment-analysis-mode.js';
import { initialStateClass, expandTransition, computeSuccessor } from './state-class-graph.js';
import { NameMarking, type Sym } from './name-marking.js';
import { NameStateClass } from './name-state-class.js';
import type { NameFragment, Role } from './name-fragment.js';
import type { PrioritySemantics } from './priority-semantics.js';

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
    prioritySemantics: PrioritySemantics = 'none',
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

      // The enabled transitions of this class as objects — used by the
      // conflict-only priority prune below (NU-052).
      const enabled = current.base.enabledTransitions;
      for (let idxL = 0; idxL < enabled.length; idxL++) {
        const transition = enabled[idxL]!;
        // NU-052: under CONFLICT semantics, skip a firing the eager,
        // priority-ordered executor would never produce — a conflicting,
        // no-later-ready, strictly-higher-priority transition that actually fires
        // takes the contested token first. `idxL` is L's index in the enabled set
        // (parallel to `readyEarliest`).
        if (
          prioritySemantics === 'conflict' &&
          priorityDominated(
            transition,
            idxL,
            enabled,
            current.base.readyEarliest,
            current.base.marking,
            current.names,
            fragment,
          )
        ) {
          continue;
        }
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

/** Float slack for the class-relative earliest-ready comparison (matches the DBM's own EPSILON). */
const READY_EPS = 1e-9;

/**
 * True if a firing of `l` is pre-empted by conflict-only priority (NU-052): some
 * other enabled transition `h` has strictly higher priority, shares a consumed
 * input place with `l` **under real competition**, becomes ready no later than
 * `l`, and actually fires in this class (produces a name-successor). The executor
 * fires ready transitions in descending priority order within a pass, so `h` takes
 * the contested token and `l` cannot fire — the pruned firing is not
 * runtime-reachable.
 *
 * **Readiness (DBM residual-earliest).** The name-SCG carries a DBM, so a static
 * `earliest(h) <= earliest(l)` does NOT entail "H ready no later than L": their
 * class-relative enabling epochs can put H's clock behind L's. We compare the
 * class-relative earliest-ready times captured on the base class
 * (`StateClass.readyEarliest`, the DBM lower bounds before `letTimePass`): H
 * pre-empts L only when `readyEarliest[H] <= readyEarliest[L] + EPS`. This is
 * fully precise on the zone off-diagonal and subsumes the previously-shipped
 * `earliest 0` case (an immediate H has `readyEarliest[H] === 0 <=
 * readyEarliest[L]`), so no capability is lost.
 *
 * **Real competition (multiplicity).** Sharing a consumed place is not enough: if
 * the place holds enough tokens for H and L at once they do not compete, and
 * pruning L would be unsound — see {@link sharesConsumedInput}.
 *
 * The `willFire` guard is essential on a ν-net: a match (join) transition can be
 * base-enabled yet **name-disabled** (its inputs carry no shared name). Such a
 * join never consumes the contested token, so it must not pre-empt a conflicting
 * drain — otherwise a genuine straggler would strand.
 */
function priorityDominated(
  l: Transition,
  idxL: number,
  enabled: readonly Transition[],
  readyEarliest: readonly number[],
  marking: MarkingState,
  names: NameMarking,
  fragment: NameFragment,
): boolean {
  return enabled.some(
    (h, idxH) =>
      h !== l &&
      h.priority > l.priority &&
      readyEarliest[idxH]! <= readyEarliest[idxL]! + READY_EPS &&
      willFire(h, names, fragment) &&
      sharesConsumedInput(h, l, marking),
  );
}

/**
 * True if base-enabled `h` actually produces a name-successor from this class — a
 * join finds a shared enabling name and a consumer finds a resident symbol.
 * Ordinary and Mint always fire; only a name-disabled join (or an empty-input
 * consumer) does not, and such a transition must not pre-empt a conflicting firing.
 */
function willFire(h: Transition, names: NameMarking, fragment: NameFragment): boolean {
  const role = fragment.role(h.name);
  switch (role.type) {
    case 'join':
      return enablingSymbols(names, role.colouredIn).length > 0;
    case 'consume':
      return names.symbolsIn(role.colouredInput).length > 0;
    case 'ordinary':
    case 'mint':
      return true;
    default: {
      // Exhaustiveness guard: a future Role member is a compile error here,
      // rather than silently defaulting to will-fire=true.
      const _exhaustive: never = role;
      return _exhaustive;
    }
  }
}

/**
 * True if `h` and `l` genuinely compete for a consumed token — they share a
 * consumed input place `p` whose token count in `marking` cannot satisfy both
 * demands at once (`count(p) < demand_h(p) + demand_l(p)`). Read and inhibitor
 * arcs are excluded ({@link Transition.inputPlaces} is consumed inputs only),
 * since they do not remove a token another transition competes for. Compared by
 * place name (name-based Place equality, MOD-024).
 *
 * The multiplicity clause is a soundness guard for the NU-052 prune: if the shared
 * place holds enough tokens for both, `h` does NOT rob `l`, so pruning `l` would
 * drop a runtime-reachable firing.
 */
function sharesConsumedInput(h: Transition, l: Transition, marking: MarkingState): boolean {
  const lIns = new Set<string>();
  for (const p of l.inputPlaces()) lIns.add(p.name);
  for (const p of h.inputPlaces()) {
    if (lIns.has(p.name) && marking.tokens(p) < consumedDemand(h, p.name) + consumedDemand(l, p.name)) {
      return true;
    }
  }
  return false;
}

/**
 * Tokens `t` consumes from the named place on one firing (summed across its input
 * specs referencing that place — normally a single spec). Uses the enablement
 * required-count so `all`/`at-least` demand their minimum, matching the base SCG's
 * consumption model.
 */
function consumedDemand(t: Transition, placeName: string): number {
  let demand = 0;
  for (const spec of t.inputSpecs) {
    if (spec.place.name === placeName) demand += inputRequiredCount(spec);
  }
  return demand;
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
 * The coloured output place names of the fired branch (used by Mint to stamp a
 * fresh symbol, and by Consume to relay the consumed symbol).
 */
function colouredOutputs(outputPlaces: ReadonlySet<Place<any>>, fragment: NameFragment): string[] {
  return [...outputPlaces].filter(p => fragment.isColoured(p.name)).map(p => p.name);
}

/**
 * Name-layer successors of one firing. Ordinary passes the layer through; Mint
 * stamps one globally-fresh symbol into the coloured outputs of this branch (one
 * symbol into several = same-mint siblings); Join yields one successor per
 * enabling symbol (none ⇒ the join is name-disabled); Consume (EXTENDED, NU-051)
 * yields one successor per resident symbol of the single coloured input (count 1,
 * so NONE is dropped), threading that symbol into every coloured output (relay)
 * or dropping it (drain, no coloured output).
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
      const colouredOut = colouredOutputs(outputPlaces, fragment);
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
    case 'consume': {
      // Count is fixed at one, so every resident symbol satisfies the required
      // count — NO base-enabled firing is dropped. Emit EXACTLY ONE symbol per
      // coloured output (relay), keeping the name-layer total == base count.
      const colouredOut = colouredOutputs(outputPlaces, fragment);
      const result: NameMarking[] = [];
      for (const s of names.symbolsIn(role.colouredInput)) {
        const nm = names.copy();
        nm.remove(role.colouredInput, s, 1);
        for (const p of colouredOut) nm.add(p, s, 1);
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
