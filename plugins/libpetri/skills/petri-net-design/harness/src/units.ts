/**
 * Structural half of the units rule (assume-guarantee over identical per-session instances).
 *
 * Evidence: research/net-metrics/loop/voice-* step 5 — every designer built one subnet instance per
 * session (prefixes s1/, s2/, …) sharing only backend permits and obs/SEARCH. Each design was proven
 * at k = 1 and Unknown at k = 2, because the whole-net state space is a product of the sessions'.
 * The rule replaces the product by one instance checked against an adversary standing for all the
 * others; this module checks the rule's premises and builds that isolation net. Verification is in
 * gates.ts.
 *
 * Premises:
 *  P1  transitions split into instance groups by first path segment `<unit>/` plus host transitions
 *      (no `/`); ≥ 2 groups; every group equals the first modulo its prefix (arcs, cardinalities,
 *      output structure, timing, priority) and so does the initial marking of its places.
 *  P2  no arc from one instance into another's places, and no host transition touching the private
 *      places of two instances.
 *  P3  every shared place (touched by ≥ 2 instances, or by an instance and the host) is conserved: it
 *      lies in the support of a P-semiflow of the composed net whose other support places are
 *      instance places or other shared places. A shared place with initial tokens is a *resource*;
 *      one without is a *mirror* (e.g. obs/SEARCH, conserved together with its resource). No reset
 *      arc on a shared place; no read, inhibitor or reset arc from an instance on a mirror (a mirror
 *      is not given an adversary, so a unit must not test the tokens others put there).
 *  Carriers of a unit: its places in the support of a semiflow that contains a resource and
 *  otherwise only instance places (the places that hold a borrowed token).
 */
import { PetriNet, Transition, and, exactly, outPlace, one, place, type In, type Out, type Place } from 'libpetri';
import { IncidenceMatrix, MarkingState, computePSemiflows, flatten } from 'libpetri/verification';
import { STRUCTURE_ONLY, allPlaces, arcs } from './net-utils.js';

export type UnitsPremise = 'P1' | 'P2' | 'P3';

export interface UnitsStructure {
  readonly ok: true;
  readonly units: readonly string[];
  /** The instance checked in isolation (the first by name). */
  readonly unit: string;
  readonly shared: readonly string[];
  readonly resources: ReadonlyArray<{ readonly place: string; readonly capacity: number }>;
  readonly mirrors: readonly string[];
  /** Carrier places of `unit`. */
  readonly carriers: readonly string[];
  /** Human-readable statement of each premise as it held. */
  readonly premises: readonly string[];
  /** Isolation net of `unit`: steal/return adversary per resource, which may stop once it has returned everything (part a); steal only, never stopping, for part b. `stolen` names the places holding what the adversary took; `ledger` the places counting what it has not (part a only). */
  isolation(withReturn: boolean): { net: PetriNet; marking: Map<string, number>; stolen: string[]; ledger: string[] };
}
export type UnitsAnalysis = UnitsStructure | { readonly ok: false; readonly premise: UnitsPremise; readonly reason: string };

/** The isolation net's adversary switch (part a): steal and return read it, `adversary_stop` consumes it. */
const ADVERSARY = 'ADVERSARY';
/** Prefix of a resource's ledger place (part a): one token per resource token the adversary does not hold. */
const UNSTOLEN = 'UNSTOLEN_';

const prefixOf = (n: string): string | undefined => (n.includes('/') ? n.slice(0, n.indexOf('/')) : undefined);

export function analyseUnits(net: PetriNet, marking: ReadonlyMap<string, number>): UnitsAnalysis {
  // ── P1: groups and identity modulo prefix ─────────────────────────────────
  const groups = new Map<string, Transition[]>();
  const host: Transition[] = [];
  for (const t of net.transitions) {
    const u = prefixOf(t.name);
    if (u === undefined) host.push(t);
    else { const g = groups.get(u) ?? []; g.push(t); groups.set(u, g); }
  }
  const units = [...groups.keys()].sort();
  if (units.length < 2) return { ok: false, premise: 'P1', reason: `fewer than two instance groups (${units.join(', ') || 'none'})` };
  const unitSet = new Set(units);
  const unitOfPlace = (n: string): string | undefined => { const u = prefixOf(n); return u !== undefined && unitSet.has(u) ? u : undefined; };

  const canon = (u: string) => {
    // Another instance's place maps to '#other…', so symmetric cross-instance arcs pass P1 and are named by P2.
    const strip = (n: string) => { const pu = unitOfPlace(n); return pu === u ? '@' + n.slice(u.length) : pu !== undefined ? '#other' + n.slice(pu.length) : n; };
    const out = (o: Out | null): string => {
      if (o === null) return '-';
      switch (o.type) {
        case 'place': return strip(o.place.name);
        case 'and': case 'xor': return `${o.type}(${o.children.map(out).join(',')})`;
        case 'timeout': return `timeout(${o.afterMs},${out(o.child)})`;
        case 'forward-input': return `fwd(${strip(o.from.name)},${strip(o.to.name)})`;
      }
    };
    const sig = groups.get(u)!.map(t => JSON.stringify([
      t.name.slice(u.length),
      t.inputSpecs.map(i => [i.type, strip(i.place.name), 'count' in i ? i.count : 'minimum' in i ? i.minimum : 0]),
      out(t.outputSpec),
      t.inhibitors.map(a => strip(a.place.name)).sort(),
      t.reads.map(a => strip(a.place.name)).sort(),
      t.resets.map(a => strip(a.place.name)).sort(),
      t.timing, t.priority,
      t.matchSpec?.keys.map(k => strip(k.place.name)) ?? null,
    ])).sort();
    const mk = [...marking].filter(([n, c]) => c > 0 && unitOfPlace(n) === u).map(([n, c]) => `${strip(n)}=${c}`).sort();
    return { sig, mk };
  };
  const ref = canon(units[0]!);
  for (const u of units.slice(1)) {
    const c = canon(u);
    const diffT = c.sig.filter(x => !ref.sig.includes(x)).concat(ref.sig.filter(x => !c.sig.includes(x)));
    if (diffT.length > 0) return { ok: false, premise: 'P1', reason: `instance '${u}' differs from '${units[0]}' modulo prefix: ${diffT.slice(0, 2).join(' | ')}` };
    if (c.mk.join() !== ref.mk.join()) return { ok: false, premise: 'P1', reason: `initial marking of '${u}' differs from '${units[0]}' (${c.mk.join(' ')} vs ${ref.mk.join(' ')})` };
  }

  // ── P2: no cross-instance arcs ────────────────────────────────────────────
  const actors = new Map<string, Set<string>>(); // place → units / 'host' touching it
  for (const t of net.transitions) {
    const tu = prefixOf(t.name);
    const touchedUnits = new Set<string>();
    for (const a of arcs(t)) {
      const pu = unitOfPlace(a.place.name);
      if (tu !== undefined && pu !== undefined && pu !== tu) {
        return { ok: false, premise: 'P2', reason: `'${t.name}' (instance '${tu}') has a ${a.kind} arc on '${a.place.name}' of instance '${pu}'` };
      }
      if (pu !== undefined) touchedUnits.add(pu);
      const s = actors.get(a.place.name) ?? new Set<string>(); s.add(tu ?? '#host'); actors.set(a.place.name, s);
    }
    if (tu === undefined && touchedUnits.size > 1) {
      return { ok: false, premise: 'P2', reason: `host transition '${t.name}' touches places of instances ${[...touchedUnits].sort().join(', ')}` };
    }
  }

  // ── P3: shared places conserved by P-semiflows ─────────────────────────────
  const shared = [...actors].filter(([, s]) => [...s].filter(a => a !== '#host').length >= 2 || (s.has('#host') && s.size >= 2))
    .map(([p]) => p).sort();
  if (shared.length === 0) return { ok: false, premise: 'P3', reason: 'no shared places: instances are disjoint (check one instance directly)' };
  const sharedSet = new Set(shared);
  for (const t of net.transitions) for (const r of t.resets) if (sharedSet.has(r.place.name)) {
    return { ok: false, premise: 'P3', reason: `reset arc of '${t.name}' on shared place '${r.place.name}' breaks conservation` };
  }
  const places = allPlaces(net);
  const flat = flatten(net);
  const mb = MarkingState.builder();
  for (const [n, c] of marking) if (c > 0 && places.has(n)) mb.tokens(places.get(n)!, c);
  const semiflows = computePSemiflows(IncidenceMatrix.from(flat), flat, mb.build())
    .map(y => [...y.support].map(i => flat.places[i]!.name));
  const isInstance = (n: string) => unitOfPlace(n) !== undefined;
  const capacity = (n: string) => marking.get(n) ?? 0;
  const conservedBy = new Map<string, string[]>();
  for (const S of shared) {
    const y = semiflows.filter(sup => sup.includes(S) && sup.every(n => n === S || isInstance(n) || sharedSet.has(n)))
      .sort((a, b) => a.length - b.length)[0];
    if (!y) return { ok: false, premise: 'P3', reason: `shared place '${S}' is in no P-semiflow whose other places are instance or shared places: not conserved` };
    conservedBy.set(S, y);
  }
  const resources = shared.filter(S => capacity(S) > 0).map(S => ({ place: S, capacity: capacity(S) }));
  const mirrors = shared.filter(S => capacity(S) === 0);
  for (const t of net.transitions) {
    if (prefixOf(t.name) === undefined) continue;
    for (const a of [...t.reads, ...t.inhibitors, ...t.resets]) if (mirrors.includes(a.place.name)) {
      return { ok: false, premise: 'P3', reason: `instance transition '${t.name}' tests mirror place '${a.place.name}' (read/inhibitor/reset): the adversary cannot model it` };
    }
  }
  if (resources.length === 0) return { ok: false, premise: 'P3', reason: 'no shared place holds initial tokens: nothing for the adversary to steal' };

  const unit = units[0]!;
  const resourceNames = new Set(resources.map(r => r.place));
  const carriers = [...new Set(semiflows
    .filter(sup => sup.some(n => resourceNames.has(n)) && sup.every(n => resourceNames.has(n) || isInstance(n)))
    .flatMap(sup => sup.filter(n => unitOfPlace(n) === unit)))].sort();

  const premises = [
    `P1 ${units.length} identical instances (${units.join(', ')}) modulo prefix`,
    'P2 no cross-instance arcs',
    `P3 shared places conserved by P-semiflows: ${shared.map(S => `${S} ∈ {${conservedBy.get(S)!.join(', ')}}`).join('; ')}`,
    `resources ${resources.map(r => `${r.place}(${r.capacity})`).join(', ')}; mirrors ${mirrors.join(', ') || 'none'}; carriers of ${unit}: ${carriers.join(', ') || 'none'}`,
  ];

  const isolation = (withReturn: boolean) => {
    const keepPlace = (n: string) => unitOfPlace(n) === unit || sharedSet.has(n) || unitOfPlace(n) === undefined;
    const ts = [...groups.get(unit)!, ...host.filter(t => arcs(t).every(a => keepPlace(a.place.name)))];
    const stolen: string[] = [];
    const ledger: string[] = [];
    // With returns the adversary could steal and return forever, so no marking would be quiescent
    // and every quiescence property (deadlockFree, accounting) would hold vacuously, hiding a unit
    // that stalls under contention. It therefore runs while ADVERSARY holds its token and may stop
    // once it has returned everything: a globally quiescent marking leaves no resource with the
    // other units (b), so the unit's own marking is quiescent in isolation after the stop.
    //
    // "Returned everything" is counted, never tested for absence: UNSTOLEN_<R> holds one token per
    // token of R the adversary does not hold, and the stop takes all `capacity` of them. An
    // inhibitor on STOLEN_<R> would be a non-monotone test of steal's output, so the verifier
    // would split steal into a start and a completion (VER-004) and let the stop fire between
    // them, stranding the stolen token where the return can no longer reach it.
    const active: Place<unknown> | null = withReturn ? place(ADVERSARY) : null;
    const stopInputs: In[] = active ? [one(active)] : [];
    for (const r of resources) {
      const S = places.get(r.place)!;
      const tag = r.place.replaceAll('/', '_');
      const X: Place<unknown> = place(`STOLEN_${tag}`);
      stolen.push(X.name);
      if (!active) {
        ts.push(Transition.builder(`steal_${r.place}`).inputs(one(S)).outputs(outPlace(X)).action(STRUCTURE_ONLY).build());
        continue;
      }
      const free: Place<unknown> = place(`${UNSTOLEN}${tag}`);
      ledger.push(free.name);
      stopInputs.push(exactly(r.capacity, free));
      ts.push(Transition.builder(`steal_${r.place}`).inputs(one(S), one(free)).outputs(outPlace(X)).reads(active).action(STRUCTURE_ONLY).build());
      ts.push(Transition.builder(`return_${r.place}`).inputs(one(X)).outputs(and(outPlace(S), outPlace(free))).reads(active).action(STRUCTURE_ONLY).build());
    }
    if (active) ts.push(Transition.builder('adversary_stop').inputs(...stopInputs).build());
    const b = PetriNet.builder(`${net.name}#${unit}`);
    for (const t of ts) b.transition(t);
    const iso = b.build();
    const isoPlaces = allPlaces(iso);
    const m = new Map<string, number>();
    for (const [n, c] of marking) if (c > 0 && isoPlaces.has(n)) m.set(n, c);
    if (active) m.set(active.name, 1);
    for (const r of resources) if (active) m.set(`${UNSTOLEN}${r.place.replaceAll('/', '_')}`, r.capacity);
    return { net: iso, marking: m, stolen, ledger };
  };

  return { ok: true, units, unit, shared, resources, mirrors, carriers, premises, isolation };
}
