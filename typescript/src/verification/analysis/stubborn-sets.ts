import type { PetriNet } from '../../core/petri-net.js';
import type { Transition } from '../../core/transition.js';
import { requiredCount } from '../../core/in.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';
import type { MarkingState } from '../marking-state.js';
import { outcomes } from './branch-outcomes.js';

/** One enabling condition of a transition, in the order [VER-024] reads them. */
interface Condition {
  readonly place: string;
  /** Tokens the place needs; `0` for an inhibitor, which needs the place empty. */
  readonly need: number;
  readonly inhibitor: boolean;
}

/**
 * Stubborn sets of [VER-024]: at each class the enumeration expands only the enabled
 * transitions of one stubborn set, which keeps every reachable dead marking
 * (`lean/Libpetri/Novel/Stubborn.lean`). Footprints and indexes are computed once per net;
 * places are compared by name.
 */
export class StubbornSets {
  private readonly transitions: readonly Transition[];
  private readonly index: ReadonlyMap<Transition, number>;
  /** Per transition, every other transition dependent with it. */
  private readonly dependents: readonly (readonly number[])[];
  /** Per transition, its enabling conditions: inputs and reads by place name, then inhibitors. */
  private readonly conditions: readonly (readonly Condition[])[];
  /** Per place, the transitions with an outcome depositing into it. */
  private readonly increasers: ReadonlyMap<string, readonly number[]>;
  /** Per place, the transitions with it among their inputs or resets. */
  private readonly decreasers: ReadonlyMap<string, readonly number[]>;

  constructor(net: PetriNet) {
    this.transitions = [...net.transitions];
    this.index = new Map(this.transitions.map((t, i) => [t, i]));
    const n = this.transitions.length;
    const tests: Set<string>[] = [];
    const writes: Set<string>[] = [];
    const overwrites: Set<string>[] = [];
    const testers = new Map<string, number[]>();
    const writers = new Map<string, number[]>();
    const overwriters = new Map<string, number[]>();
    const increasers = new Map<string, number[]>();
    const decreasers = new Map<string, number[]>();
    const add = (m: Map<string, number[]>, p: string, i: number) => {
      const l = m.get(p);
      if (l === undefined) m.set(p, [i]);
      else if (l[l.length - 1] !== i) l.push(i);
    };
    const conditions: Condition[][] = [];
    this.transitions.forEach((t, i) => {
      const tst = new Set<string>();
      const wr = new Set<string>();
      const ow = new Set<string>();
      const dec = new Set<string>();
      const inc = new Set<string>();
      const enabling: Condition[] = [];
      for (const spec of t.inputSpecs) {
        tst.add(spec.place.name);
        wr.add(spec.place.name);
        dec.add(spec.place.name);
        if (spec.type === 'all' || spec.type === 'at-least') ow.add(spec.place.name);
        enabling.push({ place: spec.place.name, need: requiredCount(spec), inhibitor: false });
      }
      for (const arc of t.reads) {
        tst.add(arc.place.name);
        enabling.push({ place: arc.place.name, need: 1, inhibitor: false });
      }
      // Stable: an input and a read on one place keep the input first.
      enabling.sort((x, y) => compareCodePoints(x.place, y.place));
      const inhibitors = t.inhibitors.map(a => a.place.name).sort(compareCodePoints);
      for (const p of inhibitors) {
        tst.add(p);
        enabling.push({ place: p, need: 0, inhibitor: true });
      }
      for (const arc of t.resets) {
        wr.add(arc.place.name);
        ow.add(arc.place.name);
        dec.add(arc.place.name);
      }
      for (const o of outcomes(t)) {
        for (const d of o.deposits) {
          wr.add(d.place.name);
          inc.add(d.place.name);
        }
      }
      tests.push(tst);
      writes.push(wr);
      overwrites.push(ow);
      conditions.push(enabling);
      for (const p of tst) add(testers, p, i);
      for (const p of wr) add(writers, p, i);
      for (const p of ow) add(overwriters, p, i);
      for (const p of inc) add(increasers, p, i);
      for (const p of dec) add(decreasers, p, i);
    });
    // t and u are dependent when one writes what the other tests, or one overwrites what the
    // other writes ([VER-024] "Footprints").
    const dependents: number[][] = [];
    for (let i = 0; i < n; i++) {
      const dep = new Set<number>();
      const collect = (places: Set<string>, index: Map<string, number[]>) => {
        for (const p of places) for (const j of index.get(p) ?? []) if (j !== i) dep.add(j);
      };
      collect(writes[i]!, testers);
      collect(tests[i]!, writers);
      collect(overwrites[i]!, writers);
      collect(writes[i]!, overwriters);
      dependents.push([...dep].sort((a, b) => a - b));
    }
    this.dependents = dependents;
    this.conditions = conditions;
    this.increasers = increasers;
    this.decreasers = decreasers;
  }

  /**
   * The enabled transitions to expand at `marking`: those of the closure, over every enabled
   * seed, with the fewest enabled members, the code-point-smallest seed breaking ties.
   */
  select(marking: MarkingState, enabled: readonly Transition[]): Transition[] {
    if (enabled.length <= 1) return [...enabled];
    const isEnabled = new Uint8Array(this.transitions.length);
    for (const t of enabled) isEnabled[this.index.get(t)!] = 1;
    const counts = new Map<string, number>();
    for (const p of marking.placesWithTokens()) counts.set(p.name, marking.tokens(p));
    const seeds = [...enabled].sort((x, y) => compareCodePoints(x.name, y.name));
    let best: number[] | null = null;
    for (const seed of seeds) {
      const set = this.closure(this.index.get(seed)!, counts, isEnabled, best?.length ?? Infinity);
      if (set !== null && (best === null || set.length < best.length)) {
        best = set;
        if (best.length === 1) break;
      }
    }
    // In the graph's own order of the enabled transitions, so the BFS discovers classes in the
    // same order in every implementation.
    const chosen = new Set(best!);
    return enabled.filter(t => chosen.has(this.index.get(t)!));
  }

  /**
   * The closure from `seed` under D1 / D2, as the enabled members it holds (in index order), or
   * `null` once it holds `bound` or more of them, since it can no longer win.
   */
  private closure(
    seed: number,
    counts: ReadonlyMap<string, number>,
    isEnabled: Uint8Array,
    bound: number,
  ): number[] | null {
    const inSet = new Uint8Array(this.transitions.length);
    const work = [seed];
    inSet[seed] = 1;
    let enabledCount = 0;
    const push = (j: number) => {
      if (inSet[j] === 0) {
        inSet[j] = 1;
        work.push(j);
      }
    };
    while (work.length > 0) {
      const i = work.pop()!;
      if (isEnabled[i] === 1) {
        if (++enabledCount >= bound) return null;
        for (const j of this.dependents[i]!) push(j);
      } else {
        for (const j of this.scapegoat(i, counts)) push(j);
      }
    }
    const result: number[] = [];
    for (let i = 0; i < inSet.length; i++) if (inSet[i] === 1 && isEnabled[i] === 1) result.push(i);
    return result;
  }

  /** D2: the transitions that can satisfy the first unsatisfied condition of disabled `i`. */
  private scapegoat(i: number, counts: ReadonlyMap<string, number>): readonly number[] {
    for (const c of this.conditions[i]!) {
      const have = counts.get(c.place) ?? 0;
      if (c.inhibitor ? have > 0 : have < c.need) {
        return (c.inhibitor ? this.decreasers : this.increasers).get(c.place) ?? [];
      }
    }
    throw new Error(`stubborn set: transition '${this.transitions[i]!.name}' is disabled with every condition satisfied`);
  }
}
