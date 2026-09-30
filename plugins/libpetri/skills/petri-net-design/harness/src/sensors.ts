/**
 * Design-quality sensors, ported from the net-metrics lab (research/net-metrics/lab: Sensors.java,
 * Bounded.java, Probe.java). Only the sensors that survived rounds 11–17 are here; size is context.
 *
 * Every function below is pure over the public libpetri API except the boundedness LP, which asks
 * the z3 executable (LIBPETRI_Z3 or `z3` on PATH) and degrades to -1 when it is absent.
 */
import { earliest, latest, MAX_DURATION_MS, type EnvironmentPlace, type PetriNet, type Transition } from 'libpetri';
import {
  analysisIgnore,
  analysisAlwaysAvailable,
  flatten,
  IncidenceMatrix,
  MarkingState,
  resolveZ3,
  runZ3Text,
  StateClassGraph,
  type EnvironmentAnalysisMode,
} from 'libpetri/verification';
import type { Candidate, Contract, SensorProfile } from './types.js';
import { allPlaces, arcs, bindStructureOnly, expandNames, insideSubnet, membership, outPlaces, placeByName, signature, withArrivals } from './net-utils.js';

/** Class cap for every untimed state-class graph the sensors build (lab: 200 000). */
export const DEFAULT_MAX_CLASSES = 200_000;

export interface MeasureOptions {
  /** Cap on untimed state classes per graph. Default {@link DEFAULT_MAX_CLASSES}. */
  readonly maxClasses?: number;
  /** How environment places behave in the state-class graphs. Default: ignore (no injection). */
  readonly envMode?: EnvironmentAnalysisMode;
  /** Per-z3-process timeout for the boundedness LP. Default 30 s. */
  readonly z3TimeoutMs?: number;
}

const round3 = (d: number): number => Math.round(d * 1000) / 1000;

// ---------------------------------------------------------------------------------------------
// Structural sensors (no solver)
// ---------------------------------------------------------------------------------------------

export function size(net: PetriNet): SensorProfile['size'] {
  let n = 0;
  for (const t of net.transitions) n += arcs(t).length;
  return { places: allPlaces(net).size, transitions: net.transitions.size, arcs: n };
}

/** Reset count, blast (max resets on one transition), reach (other transitions touching a reset place), crossSubnet. */
export function resetSensors(net: PetriNet): Omit<SensorProfile['resets'], 'multiToken'> {
  const ts = [...net.transitions];
  const mem = membership(net);
  const resetPlaces = new Set<string>();
  let count = 0, blast = 0, cross = 0;
  for (const t of ts) {
    count += t.resets.length;
    blast = Math.max(blast, t.resets.length);
    for (const r of t.resets) {
      resetPlaces.add(r.place.name);
      const ps = mem.get(r.place.name), tsub = mem.get(t.name);
      if (ps === undefined ? tsub !== undefined : !insideSubnet(tsub, ps)) cross++;
    }
  }
  let reach = 0;
  for (const t of ts) {
    if (t.resets.length > 0) continue;
    if (arcs(t).some(a => resetPlaces.has(a.place.name))) reach++;
  }
  return { count, blast, reach, crossSubnet: cross };
}

/** Arcs from a transition outside subnet S to a place internal to S (membership S). */
export function encapsulationViolations(net: PetriNet): number {
  const mem = membership(net);
  let n = 0;
  for (const t of net.transitions) {
    const ts = mem.get(t.name);
    for (const a of arcs(t)) {
      const ps = mem.get(a.place.name);
      if (ps !== undefined && !insideSubnet(ts, ps)) n++;
    }
  }
  return n;
}

const TIMING_KIND = (t: Transition): string => t.timing.type;

/**
 * Structure-only Weisfeiler-Lehman refinement over the typed bipartite graph, names ignored.
 * Transitions start from priority + timing kind; places from a constant (TS `Place` carries no
 * token type at runtime, so the lab's "seed with the token type" refinement is not available).
 * Returns the fraction of transitions whose final colour is shared with another transition; with
 * `undeclaredOnly`, transitions inside subnet instances (name contains '/') do not count.
 *
 * Colours are relabelled to dense integers each round (exact; the lab hashed with String.hashCode).
 */
export function wlSymmetry(net: PetriNet, rounds = 3, undeclaredOnly = false): number {
  const ts = [...net.transitions];
  if (ts.length === 0) return 0;
  const places = [...allPlaces(net).keys()];
  const tArcs = ts.map(t => arcs(t));
  const letter = { in: 'i', out: 'o', inhibitor: 'h', read: 'r', reset: 'x' } as const;
  let pc = new Map<string, string>(places.map(p => [p, 'P']));
  let tc: string[] = ts.map(t => `T${t.priority}${TIMING_KIND(t)}`);
  for (let r = 0; r < rounds; r++) {
    const ids = new Map<string, string>();
    const relabel = (s: string): string => {
      let id = ids.get(s);
      if (id === undefined) { id = String(ids.size); ids.set(s, id); }
      return id;
    };
    const placeNb = new Map<string, string[]>(places.map(p => [p, []]));
    const nextT: string[] = [];
    ts.forEach((_, i) => {
      const nb: string[] = [];
      for (const a of tArcs[i]) {
        nb.push(letter[a.kind] + pc.get(a.place.name));
        placeNb.get(a.place.name)!.push(letter[a.kind] + tc[i]);
      }
      nb.sort();
      nextT.push(relabel(`t${tc[i]}|${nb.join(',')}`));
    });
    const nextP = new Map<string, string>();
    for (const p of places) {
      const nb = placeNb.get(p)!.sort();
      nextP.set(p, relabel(`p${pc.get(p)}|${nb.join(',')}`));
    }
    tc = nextT; pc = nextP;
  }
  const counts = new Map<string, number>();
  for (const c of tc) counts.set(c, (counts.get(c) ?? 0) + 1);
  let shared = 0;
  ts.forEach((t, i) => {
    if (counts.get(tc[i])! < 2) return;
    if (undeclaredOnly && t.name.includes('/')) return;
    shared++;
  });
  return round3(shared / ts.length);
}

function unconstrained(t: Transition): boolean {
  return earliest(t.timing) === 0 && latest(t.timing) >= MAX_DURATION_MS;
}

/** Proof-route eligibility. `envPlaces` are the declared sources that are environment places. */
export function routes(net: PetriNet, envPlaces: ReadonlySet<string>): SensorProfile['routes'] {
  let ordinary = true, nu = false, timed = false;
  for (const t of net.transitions) {
    if (t.inhibitors.length || t.reads.length || t.resets.length) ordinary = false;
    for (const i of t.inputSpecs) {
      if (i.type === 'all' || i.type === 'at-least') ordinary = false;
      if (i.type === 'exactly' && i.count > 1) ordinary = false;
    }
    if (t.matchSpec !== null) nu = true;
    if (!unconstrained(t)) timed = true;
  }
  // output weights > 1: an Out tree naming one place twice on one branch
  if (ordinary) {
    const flat = flatten(net, new Set(), analysisIgnore());
    if (flat.transitions.some(ft => ft.postVector.some(w => w > 1) || ft.preVector.some(w => w > 1))) ordinary = false;
  }
  return { ordinary, enumerable: !timed && !nu && envPlaces.size === 0, nu, timed };
}

/** Existing transitions (same name in both nets) whose arc signature changed. */
export function changeImpact(before: PetriNet, after: PetriNet): { changed: string[] } {
  const old = new Map<string, string>();
  for (const t of before.transitions) old.set(t.name, signature(t).join('|'));
  const changed: string[] = [];
  for (const t of after.transitions) {
    const o = old.get(t.name);
    if (o !== undefined && o !== signature(t).join('|')) changed.push(t.name);
  }
  return { changed: changed.sort() };
}

// ---------------------------------------------------------------------------------------------
// Structural boundedness (sub-invariant LP via z3) + self-guarded-latch rule
// ---------------------------------------------------------------------------------------------

/**
 * Places made bounded by the self-guarded-latch rule (lab round 14): every producer of p consumes
 * p, so p never exceeds its initial marking. A producer guarded only by an inhibitor on p no longer
 * counts: the executor deposits p when the action completes, so the guard stays open while the
 * action runs, and the verifier splits such a producer (VER-004) and can reach p = 2.
 */
export function selfGuardedLatches(net: PetriNet): Set<string> {
  const out = new Set<string>();
  for (const p of allPlaces(net).keys()) {
    let produced = false, guarded = true;
    for (const t of net.transitions) {
      if (![...outPlaces(t.outputSpec)].some(q => q.name === p)) continue;
      produced = true;
      const consumes = t.inputSpecs.some(i => i.place.name === p);
      if (!consumes) { guarded = false; break; }
    }
    if (produced && guarded) out.add(p);
  }
  return out;
}

/**
 * Structurally bounded places: p is bounded iff some y ≥ 0 with y_p ≥ 1 has yᵀC ≤ 0. C is the
 * library's incidence matrix over the XOR-expanded flat net; resets and inhibitors are not in C
 * (resets only remove tokens, so the bound stays sound). Environment places get an injector
 * column, so they and everything they feed come out unbounded. One z3 process, one push/pop per
 * place (the lab ran one process per place; the answers are the same). Returns null when z3 is
 * unavailable or fails.
 */
export async function structurallyBounded(
  net: PetriNet, envPlaces: ReadonlySet<EnvironmentPlace<any>> = new Set(), timeoutMs = 30_000,
): Promise<{ bounded: Set<string>; placeCount: number } | null> {
  let solver;
  try { solver = resolveZ3(); } catch { return null; }
  const flat = flatten(net, new Set(envPlaces), analysisAlwaysAvailable());
  const c = IncidenceMatrix.from(flat).incidence(); // C[t][p]
  const np = flat.places.length;
  const sb: string[] = [];
  for (let q = 0; q < np; q++) sb.push(`(declare-const y${q} Int)(assert (>= y${q} 0))`);
  for (const row of c) {
    const terms: string[] = [];
    row.forEach((w, q) => { if (w !== 0) terms.push(`(* ${w < 0 ? `(- ${-w})` : w} y${q})`); });
    if (terms.length) sb.push(`(assert (<= (+ 0 ${terms.join(' ')}) 0))`);
  }
  for (let p = 0; p < np; p++) sb.push(`(push)(assert (>= y${p} 1))(check-sat)(pop)`);
  let reply;
  try { reply = await runZ3Text(solver, sb.join('\n'), 'sensors-bounded', timeoutMs); } catch { return null; }
  const answers = reply.stdout.split(/\s+/).filter(s => s === 'sat' || s === 'unsat' || s === 'unknown');
  if (answers.length !== np) return null;
  const bounded = new Set<string>();
  answers.forEach((a, p) => { if (a === 'sat') bounded.add(flat.places[p].name); });
  return { bounded, placeCount: np };
}

/** essentialPowerArcs and boundedFraction; both -1 when z3 is unavailable. */
export async function boundedness(
  net: PetriNet, envPlaces: ReadonlySet<EnvironmentPlace<any>> = new Set(), timeoutMs?: number,
): Promise<{ essentialPowerArcs: number; boundedFraction: number }> {
  const lp = await structurallyBounded(net, envPlaces, timeoutMs);
  if (!lp) return { essentialPowerArcs: -1, boundedFraction: -1 };
  const bounded = new Set([...lp.bounded, ...selfGuardedLatches(net)]);
  let essential = 0;
  for (const t of net.transitions) {
    for (const a of [...t.resets, ...t.inhibitors]) if (!bounded.has(a.place.name)) essential++;
  }
  return { essentialPowerArcs: essential, boundedFraction: round3(bounded.size / Math.max(1, lp.placeCount)) };
}

// ---------------------------------------------------------------------------------------------
// Behavioural sensors (untimed state-class graph)
// ---------------------------------------------------------------------------------------------

export interface UntimedProbe {
  /** Class count; negative when the graph did not close within the cap (lab convention). */
  readonly classes: number;
  /** Reset arcs on places that reachably hold > 1 token; -1 when the graph did not close. */
  readonly multiToken: number;
  /** Max non-immediate transitions enabled in one class (over the explored classes). */
  readonly timedWidth: number;
}

export function probeUntimed(
  net: PetriNet, marking: MarkingState, envPlaces: ReadonlySet<EnvironmentPlace<any>> = new Set(),
  opts: MeasureOptions = {},
): UntimedProbe {
  const cap = opts.maxClasses ?? DEFAULT_MAX_CLASSES;
  let scg: StateClassGraph;
  try {
    scg = StateClassGraph.build(net, marking, cap, new Set(envPlaces), opts.envMode ?? analysisIgnore(), { untimed: true });
  } catch {
    return { classes: -1, multiToken: -1, timedWidth: -1 };
  }
  const complete = scg.isComplete();
  const classes = scg.stateClasses();
  const places = [...allPlaces(net).values()];
  const max = new Map<string, number>();
  let timedWidth = 0;
  for (const sc of classes) {
    for (const p of places) {
      const n = sc.marking.tokens(p);
      if (n > (max.get(p.name) ?? 0)) max.set(p.name, n);
    }
    const w = sc.enabledTransitions.filter(t => t.timing.type !== 'immediate').length;
    if (w > timedWidth) timedWidth = w;
  }
  let multi = 0;
  for (const t of net.transitions) for (const r of t.resets) if ((max.get(r.place.name) ?? 0) > 1) multi++;
  return {
    classes: complete ? classes.length : -classes.length,
    multiToken: complete ? multi : -1,
    timedWidth,
  };
}

// ---------------------------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------------------------

/**
 * Declared sources that are environment places: no transition produces into them and the initial
 * marking holds no token there. An arrival generator's supply place is marked initially, so it is
 * not an environment place (round 15: env-fedness must be declared; this only splits the two
 * declared kinds).
 */
export function environmentSources(contract: Contract, net: PetriNet, marking: ReadonlyMap<string, number>): Set<EnvironmentPlace<any>> {
  const produced = new Set<string>();
  for (const t of net.transitions) for (const p of outPlaces(t.outputSpec)) produced.add(p.name);
  const env = new Set<EnvironmentPlace<any>>();
  const places = allPlaces(net);
  for (const s of expandNames(contract.sources, allPlaces(net).keys())) {
    const p = places.get(s);
    if (p && !produced.has(s) && (marking.get(s) ?? 0) === 0) env.add({ place: p });
  }
  return env;
}

export function markingOf(net: PetriNet, marking: ReadonlyMap<string, number>): MarkingState {
  const b = MarkingState.builder();
  for (const [name, n] of marking) if (n > 0) b.tokens(placeByName(net, name), n);
  return b.build();
}

export async function measure(contract: Contract, candidate: Candidate, opts: MeasureOptions = {}): Promise<SensorProfile> {
  const b1 = candidate.build(1);
  const b2 = candidate.build(2);
  const net1 = bindStructureOnly(b1.net);
  const net2 = bindStructureOnly(b2.net);
  const env1 = environmentSources(contract, net1, b1.marking);
  const env2 = environmentSources(contract, net2, b2.marking);

  // state growth is measured on the driven nets: environment inputs fed by harness generators
  const d1 = withArrivals(net1, b1.marking, contract.inputs, 1);
  const d2 = withArrivals(net2, b2.marking, contract.inputs, 2);
  const p1 = probeUntimed(d1.net, markingOf(d1.net, d1.marking), env1, opts);
  const p2 = probeUntimed(d2.net, markingOf(d2.net, d2.marking), env2, opts);
  const truncated = p1.classes < 0 || p2.classes < 0;
  const ratio = p1.classes === 0 ? 0 : Math.abs(p2.classes) / Math.abs(p1.classes);

  const bnd = await boundedness(net1, env1, opts.z3TimeoutMs);
  return {
    size: size(net1),
    resets: { ...resetSensors(net1), multiToken: p2.multiToken },
    encapsulationViolations: encapsulationViolations(net1),
    essentialPowerArcs: bnd.essentialPowerArcs,
    boundedFraction: bnd.boundedFraction,
    undeclaredSymmetry: wlSymmetry(net1, 3, true),
    routes: routes(net1, new Set([...env1].map(e => e.place.name))),
    stateGrowth: { k1: p1.classes, k2: p2.classes, multiplier: round3(truncated ? -ratio : ratio) },
    timedWidth: p1.timedWidth,
  };
}
