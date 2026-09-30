/**
 * Verification gates of the design harness (lab rounds 6, 12, 15, 16, 17).
 *
 * Whole-net verification of a large net times out (r16: a 98 ms counterexample at ×2 became a 300 s
 * Unknown at ×4), so a candidate is gated by three cheap checks instead:
 *
 *  1. **Lint** — structural rules, no verifier. Each names a mechanism the lab saw break a net.
 *  2. **Small scope** — every contract property at k ∈ contract.scales (default 1, 2). Every lab bug
 *     was already Violated at k = 1 in ≤ 4 ms by exhaustive enumeration; name-blind resets need k = 2.
 *  3. **Compositional** — each declared subnet proved alone through `SubnetDef.verify` under
 *     bounded(1) and bounded(2) (MOD-051), or arrivals(≤1) and arrivals(≤2) for a ν subnet or one
 *     that writes an in-out port, so no proof ever needs the composed state space.
 *
 * All three share one wall-clock budget per `runGates` call. libpetri's `timeout` applies per phase
 * (state equation, firing bound, Spacer), so one query can run ≈ 2.5× its timeout (r16); the harness
 * therefore races every query against the remaining budget and reports `unknown` with
 * "harness budget exhausted" when it runs out.
 */
import { type SubnetDef, place, tokenOf, type PetriNet, type Place, type Transition } from 'libpetri';
import {
  MarkingState,
  SmtVerifier,
  arrivals,
  bounded,
  deadlockFree,
  isUntimed,
  mutualExclusion,
  placeBound,
  quiescentCount,
  unreachable,
  type SmtProperty,
  type SmtVerificationResult,
} from 'libpetri/verification';
import type {
  Candidate, Contract, GateReport, LintFinding, PropertyResult, PropertySpec, SubnetCheck,
  NamedProperty,
} from './types.js';
import { analyseUnits, type UnitsPremise } from './units.js';
import { STRUCTURE_ONLY, allPlaces, arcs, insideSubnet, bindStructureOnly, expandNames, globMatches, membership, outPlaces, sortedTransitions, withArrivals } from './net-utils.js';

export const DEFAULT_BUDGET_MS = 10_000;
/**
 * Default class cap for the synchronous state-space routes (enumeration, ν Route B, timed SCG). The
 * budget race cannot pre-empt them, and Route B costs about quadratically in classes (PNID probe:
 * 2k classes 0.9 s, 8k 14 s; the 100 000 default would run ≈ 35 min).
 */
export const DEFAULT_CLASS_CAP = 5_000;
const BUDGET_NOTE = 'harness budget exhausted';
/** How long after the deadline the last-resort timer race gives up on a query that ignored its abort. */
const RACE_GRACE_MS = 1_000;
/** libpetri's Unknown reasons when its total budget ran out or the harness aborted the query. */
const LIBPETRI_STOPPED = /total verification budget of .* exhausted|verification cancelled/;
const NU_SUBNET_NOTE =
  'ν subnet without SubnetCheck.nu (mints or budgets, carriers): no transition would be a declared mint (NU-010), so libpetri could answer only name-blind, which leaves every quiescence property unknown. Declare the ν configuration';

// ─────────────────────────────────────────────────────────────────────────────
// Entry point
// ─────────────────────────────────────────────────────────────────────────────

export async function runGates(
  contract: Contract,
  candidate: Candidate,
  opts?: { budgetMs?: number; experimentalUnits?: boolean },
): Promise<GateReport> {
  const budget = new Budget(opts?.budgetMs ?? DEFAULT_BUDGET_MS);
  const scales = contract.scales ?? [1, 2];

  // 1. Lint, on the smallest scale (structure does not change with k in a well-formed candidate).
  // A build that throws is reported by the small-scope gate (verdict unknown, route 'build').
  let lintFindings: LintFinding[] = [];
  try {
    const { net, marking } = candidate.build(scales[0] ?? 1);
    lintFindings = lint(net, marking, contract, candidate.nu);
  } catch { /* reported below */ }

  // 2. Small scope.
  // At k ≥ 2 the units rule (assume-guarantee over identical instances) is tried first; when its
  // premises fail or one of its checks does not prove, the whole-net check runs and says why.
  const smallScope: Array<{ k: number; results: PropertyResult[] }> = [];
  for (const k of scales) {
    let unitsNote: string | undefined;
    // DISABLED BY DEFAULT (2026-09-27): an adversarial review found the units rule unsound — 14 nets
    // satisfying its premises are reported proven while the composed net violates the property
    // (research/net-metrics/review/units-adversarial/FINDINGS.md). Opt in only for research.
    if (k >= 2 && opts?.experimentalUnits === true) {
      const u = await unitsRuleWith(contract, candidate, k, budget);
      if (u.proven) { smallScope.push({ k, results: [...u.results] }); continue; }
      unitsNote = u.silent ? undefined : u.summary;
    }
    let results = await smallScopeAt(contract, candidate, k, budget);
    if (unitsNote) results = results.map(r => ({ ...r, note: joinNotes([r.note ?? '', unitsNote!]) }));
    smallScope.push({ k, results });
  }

  // 3. Compositional.
  const encapBroken = lintFindings.some(f => f.rule === 'encapsulation' || f.rule === 'reset-across-subnet');
  const compositional: Array<{ subnet: string; results: PropertyResult[] }> = [];
  for (const check of candidate.subnets ?? []) {
    compositional.push({ subnet: check.def.name, results: await compositionalFor(check, budget, encapBroken) });
  }

  const bad = (r: PropertyResult) => r.verdict === 'violated' || r.verdict === 'unknown';
  const passed =
    !lintFindings.some(f => f.severity === 'error') &&
    !smallScope.some(s => s.results.some(bad)) &&
    !compositional.some(c => c.results.some(bad));
  return { lint: lintFindings, smallScope, compositional, passed };
}

// ─────────────────────────────────────────────────────────────────────────────
// Budget: one deadline per runGates call
// ─────────────────────────────────────────────────────────────────────────────

class Budget {
  private readonly deadline: number;
  constructor(totalMs: number) { this.deadline = performance.now() + Math.max(0, totalMs); }
  remaining(): number { return Math.max(0, this.deadline - performance.now()); }
  exhausted(): boolean { return this.remaining() <= 0; }

  /**
   * Runs one query under the remaining budget. The query gets the remaining time as its
   * `totalBudget` and an AbortSignal that fires at the harness deadline ([VER-013]): libpetri then
   * kills its z3 process and returns Unknown ("verification cancelled" / "total verification budget
   * … exhausted"), which {@link fromSmt} maps to 'harness budget exhausted'. The timer race is only
   * the last resort, {@link RACE_GRACE_MS} after the deadline, for a synchronous graph build that
   * cannot observe the abort until it returns.
   */
  async race<T>(start: (budgetMs: number, signal: AbortSignal) => Promise<T>): Promise<T | 'budget'> {
    const ms = this.remaining();
    if (ms <= 0) return 'budget';
    const ac = new AbortController();
    const query = start(Math.max(1, Math.floor(ms)), ac.signal);
    let abortTimer: ReturnType<typeof setTimeout> | undefined;
    let raceTimer: ReturnType<typeof setTimeout> | undefined;
    abortTimer = setTimeout(() => ac.abort(), ms);
    const expiry = new Promise<'budget'>(resolve => { raceTimer = setTimeout(() => resolve('budget'), ms + RACE_GRACE_MS); });
    try {
      return await Promise.race([query, expiry]);
    } finally {
      clearTimeout(abortTimer);
      clearTimeout(raceTimer);
      ac.abort();
      query.catch(() => { /* discarded after losing the race */ });
    }
  }
}

function budgetResult(property: string, ms = 0): PropertyResult {
  return { property, verdict: 'unknown', route: 'budget', ms, note: BUDGET_NOTE };
}

// ─────────────────────────────────────────────────────────────────────────────
// Gate 2: small scope
// ─────────────────────────────────────────────────────────────────────────────

async function smallScopeAt(contract: Contract, candidate: Candidate, k: number, budget: Budget): Promise<PropertyResult[]> {
  let net: PetriNet;
  let marking: ReadonlyMap<string, number>;
  try {
    const built = candidate.build(k);
    const driven = withArrivals(bindStructureOnly(built.net), built.marking, contract.inputs, k);
    net = driven.net;
    marking = driven.marking;
    // environment inputs are driven by harness generators, which become accounting sources
    if (driven.supplies.length > 0) contract = { ...contract, sources: [...contract.sources, ...driven.supplies] };
  } catch (e) {
    return [{ property: '(build)', verdict: 'unknown', route: 'build', ms: 0, note: `candidate.build(${k}) threw: ${errMsg(e)}` }];
  }
  return verifyOn(net, marking, contract, candidate.nu, contract.properties, budget);
}

/** A query: a contract property, or a ready SmtProperty (the units rule's hold-and-wait check). */
type Query = NamedProperty | { readonly name: string; readonly smt: SmtProperty; readonly timingDependent?: undefined };

interface VerifyOpts {
  /** Extra sink place names (units rule: shared places and the adversary's STOLEN places). */
  readonly extraSinks?: readonly string[];
  /** SMT route only: enumeration off, linear bound and semiflow invariants on (units rule, part c). */
  readonly smtOnly?: boolean;
}

/** Checks each query on one net and marking, under the shared budget. */
async function verifyOn(
  net: PetriNet,
  marking: ReadonlyMap<string, number>,
  contract: Contract,
  nu: Candidate['nu'],
  queries: readonly Query[],
  budget: Budget,
  opts: VerifyOpts = {},
): Promise<PropertyResult[]> {
  const places = allPlaces(net);

  const missingMarked = [...marking.keys()].filter(n => !places.has(n));
  if (missingMarked.length > 0) {
    return [{
      property: '(initial marking)', verdict: 'unknown', route: 'contract', ms: 0,
      note: `contract error: initial marking names places not in the net: ${missingMarked.join(', ')}`,
    }];
  }
  const mb = MarkingState.builder();
  for (const [name, count] of marking) if (count > 0) mb.tokens(places.get(name)!, count);
  const initial = mb.build();

  const sinkNames = expandNames([...contract.sinks, ...(opts.extraSinks ?? [])], places.keys());
  const sinks = sinkNames.filter(n => places.has(n)).map(n => places.get(n)!);
  const missingSinks = sinkNames.filter(n => !places.has(n));
  const sourceNames = expandNames(contract.sources, places.keys());
  const timed = !isUntimed(net);
  const sourceTokens = sourceNames.reduce((acc, s) => acc + (marking.get(s) ?? 0), 0);

  // ν configuration (Candidate.nu): every name must resolve, or the query would run without that declaration.
  const nuBudgets = nu?.budgets ?? [];
  const nuCarriers = nu?.carriers ?? [];
  const nuMints = nu?.mints ?? [];
  const missingNu = [...nuBudgets, ...nuCarriers].filter(n => !places.has(n));
  if (missingNu.length > 0) {
    return queries.map(p => ({
      property: p.name, verdict: 'unknown' as const, route: 'contract', ms: 0,
      note: `contract error: nu configuration names places not in the net: ${missingNu.join(', ')}`,
    }));
  }
  const transitionNames = new Set([...net.transitions].map(t => t.name));
  const missingMints = nuMints.filter(n => !transitionNames.has(n));
  if (missingMints.length > 0) {
    return queries.map(p => ({
      property: p.name, verdict: 'unknown' as const, route: 'contract', ms: 0,
      note: `contract error: nu configuration names mint transitions not in the net: ${missingMints.join(', ')}`,
    }));
  }

  const results: PropertyResult[] = [];
  const expanded: Query[] = [
    ...perUnitProperties(queries.filter((q): q is NamedProperty => 'spec' in q), places.keys()),
    ...queries.filter(q => 'smt' in q),
  ];
  for (const prop of expanded) {
    if (budget.exhausted()) { results.push(budgetResult(prop.name)); continue; }

    const resolved = 'smt' in prop ? { property: prop.smt } : resolveProperty(prop.spec, places, { sourceTokens, sources: sourceNames });
    if ('error' in resolved) {
      results.push({ property: prop.name, verdict: 'unknown', route: 'contract', ms: 0, note: `contract error: ${resolved.error}` });
      continue;
    }

    const notes: string[] = [];
    if ('spec' in prop && prop.spec.kind === 'deadlockFree' && missingSinks.length > 0) {
      notes.push(`declared sinks not in the net (ignored): ${missingSinks.join(', ')}`);
    }

    const t0 = performance.now();
    let outcome: SmtVerificationResult | 'budget';
    try {
      outcome = await budget.race((budgetMs, signal) => {
        const cap = classCap(budgetMs);
        const v = SmtVerifier.forNet(net).initialMarking(initial).property(resolved.property).timeout(budgetMs)
          .totalBudget(budgetMs).signal(signal)
          .enumerationMaxClasses(opts.smtOnly ? 0 : cap).nuMaxClasses(cap);
        // [VER-023] a timing-dependent Violated is checked on the timed state-class graph.
        if (prop.timingDependent && timed) v.timedCounterexampleCheck(true);
        if (opts.smtOnly) v.linearBound(true).semiflowInvariants(true);
        if (sinks.length > 0) v.sinkPlaces(...sinks);
        if (nuBudgets.length > 0) v.budgetPlaces(...nuBudgets.map(n => places.get(n)!));
        if (nuMints.length > 0) v.mintTransitions(...nuMints);
        if (nuCarriers.length > 0) v.carrierPlaces(...nuCarriers.map(n => places.get(n)!));
        if (needsExtended(net, nu)) v.fragmentMode('extended');
        return v.verify();
      });
    } catch (e) {
      results.push({ property: prop.name, verdict: 'unknown', route: 'error', ms: round(performance.now() - t0), note: `verifier threw: ${errMsg(e)}` });
      continue;
    }
    const ms = round(performance.now() - t0);
    if (outcome === 'budget') { results.push({ ...budgetResult(prop.name, ms), note: joinNotes([...notes, BUDGET_NOTE]) }); continue; }

    if (prop.timingDependent && timed && outcome.verdict.type === 'violated') {
      const timing = outcome.counterexampleTiming;
      if (timing === 'spurious-under-timing') {
        // The timed graph closed and nothing violates: the property holds under the net's timing
        // (a timed claim only, VER-023). Not violated — which is the claim a timing-dependent property makes.
        results.push({
          property: prop.name, verdict: 'proven', route: 'timed-scg', ms,
          note: joinNotes([...notes, `untimed counterexample [${outcome.counterexampleTransitions.join(', ')}] is spurious under timing: the timed state-class graph closed with no violation, so the property holds under the net's timing only (VER-023)`]),
        });
        continue;
      }
      notes.push(timing === 'timed-confirmed'
        ? 'counterexample confirmed under timing (VER-023): the trace is a timed run of the priority-blind timed state-class graph'
        : `timing-dependent property on a timed net: counterexample timing ${timing ?? 'unknown'}; this untimed Violated may be spurious (lab round 8)`);
    }
    results.push(fromSmt(prop.name, outcome, ms, notes));
  }
  return results;
}

/** PropertySpec → SmtProperty over the net's places; an error string when a name does not resolve. */
/**
 * The EXTENDED ν fragment is needed for carriers, for join relays (NU-054), and when the design asks
 * for it; BASE would decline those nets (sound, but no verdict).
 */
export function needsExtended(net: PetriNet, nu: Candidate['nu']): boolean {
  if (!nu) return false;
  if (nu.fragmentMode) return nu.fragmentMode === 'extended';
  if ((nu.carriers ?? []).length > 0) return true;
  for (const t of net.transitions) if ((t.matchSpec?.relays?.length ?? 0) > 0) return true;
  return false;
}

/**
 * Per-unit expansion: a `placeBound` whose place is a pattern becomes one check per matching place;
 * a `mutualExclusion` whose sides are both patterns pairs places with the same captured segments
 * (session s1's A with session s1's B). Other kinds resolve patterns as place sets.
 */
export function perUnitProperties(props: readonly NamedProperty[], names: Iterable<string>): NamedProperty[] {
  const all = [...names];
  const out: NamedProperty[] = [];
  for (const p of props) {
    const s = p.spec;
    if (s.kind === 'placeBound' && s.place.includes('*')) {
      const hits = expandNames([s.place], all);
      for (const h of hits) out.push({ ...p, name: hits.length > 1 ? `${p.name} [${h}]` : p.name, spec: { ...s, place: h } });
    } else if (s.kind === 'mutualExclusion' && s.a.includes('*') && s.b.includes('*')) {
      const ma = globMatches(s.a, all), mb = globMatches(s.b, all);
      const keys = [...ma.keys()].filter(k => mb.has(k)).sort();
      if (keys.length === 0) out.push(p);
      for (const k of keys) out.push({ ...p, name: `${p.name} [${k}]`, spec: { ...s, a: ma.get(k)!, b: mb.get(k)! } });
    } else out.push(p);
  }
  return out;
}

function resolveProperty(
  spec: PropertySpec,
  places: ReadonlyMap<string, Place<any>>,
  ctx: { sourceTokens: number; sources: readonly string[] } | null,
): { property: SmtProperty } | { error: string } {
  const need = (patterns: readonly string[]): Place<any>[] | string => {
    const names = expandNames(patterns, places.keys());
    const missing = names.filter(n => !places.has(n));
    return missing.length > 0 ? `property names places not in the net: ${missing.join(', ')}` : names.map(n => places.get(n)!);
  };
  switch (spec.kind) {
    case 'deadlockFree':
      return { property: deadlockFree() };
    case 'accounting': {
      if (ctx === null) return { error: 'accounting needs a fixed input count; not checkable here' };
      const ps = need(spec.outcomes);
      if (typeof ps === 'string') return { error: ps };
      const missingSources = ctx.sources.filter(s => !places.has(s));
      if (missingSources.length > 0) return { error: `declared sources not in the net: ${missingSources.join(', ')}` };
      if (ctx.sources.length === 0) return { error: 'accounting needs declared contract sources' };
      const n = ctx.sourceTokens * (spec.perUnit ?? 1);
      return { property: quiescentCount(ps, n, n) };
    }
    case 'mutualExclusion': {
      const ps = need([spec.a, spec.b]);
      return typeof ps === 'string' ? { error: ps } : { property: mutualExclusion(ps[0]!, ps[1]!) };
    }
    case 'placeBound': {
      const ps = need([spec.place]);
      return typeof ps === 'string' ? { error: ps } : { property: placeBound(ps[0]!, spec.bound) };
    }
    case 'unreachable': {
      const ps = need(spec.places);
      return typeof ps === 'string' ? { error: ps } : { property: unreachable(new Set(ps)) };
    }
  }
}

function fromSmt(property: string, r: SmtVerificationResult, ms: number, notes: string[]): PropertyResult {
  const v = r.verdict;
  if (v.type === 'unknown' && LIBPETRI_STOPPED.test(v.reason)) {
    return { property, verdict: 'unknown', route: 'budget', ms, note: joinNotes([BUDGET_NOTE, ...notes]) };
  }
  if (v.type === 'unknown' && /does not resolve/.test(v.reason)) {
    return { property, verdict: 'unknown', route: 'contract', ms, note: joinNotes([`contract error: ${v.reason}`, ...notes]) };
  }
  if (v.type === 'unknown') notes = [v.reason, ...notes];
  if (v.type === 'violated' && r.counterexampleConfirmed === false) notes = [...notes, 'counterexample not confirmed by replay'];
  const note = joinNotes(notes);
  return {
    property, verdict: v.type, route: r.route, ms,
    ...(v.type === 'violated' ? { trace: [...r.counterexampleTransitions] } : {}),
    ...(note ? { note } : {}),
  };
}

// ─────────────────────────────────────────────────────────────────────────────
// Gate 2b: units rule (assume-guarantee over identical per-session instances)
// ─────────────────────────────────────────────────────────────────────────────

export const UNITS_ROUTE = 'units(assume-guarantee)';

export interface UnitsOutcome {
  /** Premises P1–P3 held. */
  readonly applicable: boolean;
  /** The premise that failed, when not applicable. */
  readonly premise?: UnitsPremise;
  readonly reason?: string;
  /** No instance groups at all: the rule is irrelevant, say nothing. */
  readonly silent: boolean;
  readonly premises: readonly string[];
  /** (a) local liveness and safety of one instance against a steal/return adversary. */
  readonly a: readonly PropertyResult[];
  /** (b) no hold-and-wait: steal-only adversary, no quiescent marking with a carrier marked. */
  readonly b: readonly PropertyResult[];
  /** (c) properties on shared places, on the composed net by the SMT route. */
  readonly c: readonly PropertyResult[];
  readonly proven: boolean;
  /** One 'proven' result per contract property when `proven`, else empty. */
  readonly results: readonly PropertyResult[];
  readonly summary: string;
  readonly ms: number;
}

/**
 * The units rule at scale k, stand-alone (tests, reports). runGates calls it for every k ≥ 2.
 *
 * Soundness sketch. P1–P3 make the composed net k copies of one instance that interact only by
 * moving tokens of conserved shared places. From one instance's view the others can take a
 * resource token at any time and give it back later: the steal/return adversary over-approximates
 * them, so (a) holds for every instance in every composition. (b) shows an instance never rests
 * holding a borrowed token when the others never return theirs, so no set of instances can wait on
 * each other while holding resources (Coffman: no hold-and-wait), and a globally quiescent marking
 * leaves every resource token with the shared places or the instance itself. (a)'s adversary may
 * therefore stop once it has returned everything, which makes that marking quiescent in isolation
 * too; without the stop, steal and return would fire forever, no isolated marking would be
 * quiescent, and every quiescence property would hold vacuously. Properties on shared places are global,
 * so (c) checks them on the composed net, where they follow from the P-semiflow.
 */
export async function checkUnits(contract: Contract, candidate: Candidate, k: number, opts?: { budgetMs?: number }): Promise<UnitsOutcome> {
  return unitsRuleWith(contract, candidate, k, new Budget(opts?.budgetMs ?? DEFAULT_BUDGET_MS));
}

async function unitsRuleWith(contract: Contract, candidate: Candidate, k: number, budget: Budget): Promise<UnitsOutcome> {
  const t0 = performance.now();
  const none = (premise: UnitsPremise | undefined, reason: string, silent = false): UnitsOutcome => ({
    applicable: false, ...(premise ? { premise } : {}), reason, silent, premises: [], a: [], b: [], c: [], proven: false, results: [],
    summary: `units rule not applicable${premise ? ` (${premise} failed)` : ''}: ${reason}`, ms: round(performance.now() - t0),
  });
  let net: PetriNet, marking: ReadonlyMap<string, number>, driven: Contract = contract;
  try {
    const built = candidate.build(k);
    const d = withArrivals(bindStructureOnly(built.net), built.marking, contract.inputs, k);
    net = d.net; marking = d.marking;
    if (d.supplies.length > 0) driven = { ...contract, sources: [...contract.sources, ...d.supplies] };
  } catch (e) {
    return none(undefined, `build failed: ${errMsg(e)}`, true);
  }
  if (candidate.nu || [...net.transitions].some(t => t.matchSpec !== null)) return none(undefined, 'ν nets are out of scope for the units rule');
  const st = analyseUnits(net, marking);
  if (!st.ok) return none(st.premise, st.reason, st.premise === 'P1' && /fewer than two instance groups/.test(st.reason));

  // Split the properties: anything naming a shared place is global (c); the rest is per instance (a).
  const composedNames = [...allPlaces(net).keys()];
  const sharedSet = new Set(st.shared);
  const namesOf = (sp: PropertySpec): string[] => expandNames(
    sp.kind === 'accounting' ? sp.outcomes : sp.kind === 'mutualExclusion' ? [sp.a, sp.b]
      : sp.kind === 'placeBound' ? [sp.place] : sp.kind === 'unreachable' ? sp.places : [], composedNames);
  const global = contract.properties.filter(p => namesOf(p.spec).some(n => sharedSet.has(n)));
  const local = contract.properties.filter(p => !global.includes(p));

  const isoA = st.isolation(true);
  const isoNames = new Set(allPlaces(isoA.net).keys());
  const present = (ns: readonly string[]) => ns.filter(n => n.includes('*') || isoNames.has(n));
  const isoContract: Contract = {
    ...driven,
    sources: expandNames(driven.sources, isoNames).filter(n => isoNames.has(n)),
    sinks: present(contract.sinks),
  };
  const extraSinks = [...st.shared, ...isoA.stolen];
  const a = await verifyOn(isoA.net, isoA.marking, isoContract, undefined, local, budget, { extraSinks });

  const isoB = st.isolation(false);
  const carrierPlaces = st.carriers.map(n => allPlaces(isoB.net).get(n)!).filter(Boolean);
  const b = carrierPlaces.length === 0
    ? [{ property: 'no hold-and-wait', verdict: 'proven' as const, route: 'structural', ms: 0, note: 'no carrier places: the instance never holds a borrowed token' }]
    : await verifyOn(isoB.net, isoB.marking, isoContract, undefined,
      [{ name: 'no hold-and-wait', smt: quiescentCount(carrierPlaces, 0, 0) }], budget, { extraSinks: [...st.shared, ...isoB.stolen] });

  const c = await verifyOn(net, marking, driven, undefined, global, budget, { smtOnly: true });

  const ms = round(performance.now() - t0);
  const all = [...a, ...b, ...c];
  const proven = all.length > 0 && all.every(r => r.verdict === 'proven');
  const failed = all.filter(r => r.verdict !== 'proven');
  const part = (r: PropertyResult) => (a.includes(r) ? '(a)' : b.includes(r) ? '(b)' : '(c)');
  const note = `units rule at k=${k}: ${st.premises.join('; ')}; (a) ${a.length} local check(s) and (b) no hold-and-wait on ${st.unit} in isolation, (c) ${c.length} global check(s) on the composed net — all proven`;
  const summary = proven ? note
    : `units rule premises held but not every check proved: ${failed.map(r => `${part(r)} ${r.property} ${r.verdict}${r.trace ? ` [${r.trace.join(', ')}]` : ''}`).join('; ')}`;
  return {
    applicable: true, silent: false, premises: st.premises, a, b, c, proven, summary, ms,
    results: proven ? contract.properties.map(p => ({ property: p.name, verdict: 'proven' as const, route: UNITS_ROUTE, ms, note })) : [],
  };
}

// ─────────────────────────────────────────────────────────────────────────────
// Gate 3: compositional
// ─────────────────────────────────────────────────────────────────────────────

async function compositionalFor(check: SubnetCheck, budget: Budget, encapBroken: boolean): Promise<PropertyResult[]> {
  const results: PropertyResult[] = [];
  let def: SubnetDef<void>;
  let synthNames: Map<string, Place<any>>;
  try {
    // Actions may be omitted in a candidate; CORE-043 rejects an output spec with passthrough().
    def = check.def.bindActionsWithResolver(() => STRUCTURE_ONLY);
    synthNames = syntheticPlaces(def);
  } catch (e) {
    return [{ property: '(subnet)', verdict: 'unknown', route: 'build', ms: 0, note: `subnet '${check.def.name}' could not be prepared: ${errMsg(e)}` }];
  }
  // ν subnet: verify only with its ν configuration (mints or budget, carriers, EXTENDED fragment).
  // Without it no transition is a declared mint (NU-010), so libpetri keeps the net off both ν routes
  // and can answer only name-blind: an unknown for every quiescence property.
  const isNu = [...def.body.transitions].some(t => t.matchSpec !== null);
  if (isNu && !check.nu) {
    return check.properties.map(p => ({
      property: p.name, verdict: 'unknown' as const, route: 'compositional', ms: 0, note: NU_SUBNET_NOTE,
    }));
  }
  const nuNames = [...(check.nu?.budgets ?? []), ...(check.nu?.carriers ?? [])];
  const missingNu = nuNames.filter(n => !synthNames.has(n));
  if (missingNu.length > 0) {
    return check.properties.map(p => ({
      property: p.name, verdict: 'unknown' as const, route: 'contract', ms: 0,
      note: `contract error: subnet nu configuration names places not in '${check.def.name}': ${missingNu.join(', ')}`,
    }));
  }
  const bodyTransitions = new Set([...def.body.transitions].map(t => t.name));
  const missingMints = (check.nu?.mints ?? []).filter(n => !bodyTransitions.has(n));
  if (missingMints.length > 0) {
    return check.properties.map(p => ({
      property: p.name, verdict: 'unknown' as const, route: 'contract', ms: 0,
      note: `contract error: subnet nu configuration names mint transitions not in '${check.def.name}': ${missingMints.join(', ')}`,
    }));
  }
  // bounded(k) keeps each input port topped up forever. Two kinds of subnet cannot be decided that
  // way, so they get arrivals(≤k) instead, the small-scope reading the whole-net gate uses too:
  //  - a subnet that writes an in-out port deposits into an environment place, which breaks the
  //    Bounded(k) premise, and libpetri answers unknown for every property (VER-006 AC3);
  //  - a ν subnet mints a name per input, and endless inputs leave endless names in flight, so the
  //    name-aware graph cannot close (NU-050) and the answer is unknown again.
  const writtenInout = [...def.iface.ports.values()]
    .filter(port => port.direction === 'inout'
      && [...def.body.transitions].some(t => [...outPlaces(t.outputSpec)].some(p => p.name === port.place.name)))
    .map(port => port.name);
  const arrivalsWhy = writtenInout.length > 0
    ? `arrivals(≤k) instead of bounded(k): the subnet writes in-out port${writtenInout.length > 1 ? 's' : ''} ${writtenInout.map(n => `'${n}'`).join(', ')}, and bounded(k) describes the executor only when nothing deposits into an environment place (VER-006 AC3)`
    : isNu ? 'arrivals(≤k) instead of bounded(k): a ν subnet under endless inputs has endless names in flight, which the name-aware graph cannot close (NU-050)'
    : null;
  // A token that reached an output or in-out port has left the subnet: deadlockFree excuses it.
  const portSinks = [...def.iface.ports.values()].filter(port => port.direction !== 'input').map(port => port.place.name);
  const generators = new Map(check.inputs.map(port => [port, () => tokenOf<unknown>({ port })] as const));
  const glueNote = encapBroken
    ? 'lint found arcs from outside a subnet into its internal places: this proof does not cover that host glue (r17)'
    : undefined;

  // Exact accounting needs mandatory arrivals, arrivals(k, k) (libpetri issue 14). It applies to
  // every input port, so it states "k inputs, k outcomes" only for a single-input subnet; with more
  // ports (a cancel port, say) it would force k of each, so those keep the upper bound.
  const exactAccounting = check.inputs.length === 1;
  for (const prop of check.properties) {
    const accounting = prop.spec.kind === 'accounting';
    for (const k of [1, 2]) {
      const name = `${prop.name} @${accounting ? (exactAccounting ? `arrivals(${k}..${k})` : `arrivals(≤${k})`) : arrivalsWhy ? `arrivals(≤${k})` : `bounded(${k})`}`;
      const resolved: { property: SmtProperty } | { error: string } = prop.spec.kind === 'accounting'
        ? (() => {
            const outs = expandNames(prop.spec.outcomes, synthNames.keys());
            const missing = outs.filter(n => !synthNames.has(n));
            return missing.length > 0 ? { error: `property names places not in the net: ${missing.join(', ')}` }
              : { property: quiescentCount(outs.map(n => synthNames.get(n)!), exactAccounting ? k * (prop.spec.perUnit ?? 1) : 0, k * (prop.spec.perUnit ?? 1)) };
          })()
        : resolveProperty(prop.spec, synthNames, null);
      if ('error' in resolved) {
        results.push({ property: name, verdict: 'unknown', route: 'contract', ms: 0, note: `contract error: ${resolved.error}` });
        continue;
      }
      if (budget.exhausted()) { results.push(budgetResult(name)); continue; }
      const t0 = performance.now();
      let outcome;
      try {
        outcome = await budget.race((budgetMs, signal) => def.verify(
          { params: undefined, portInputGenerators: generators, properties: [resolved.property] },
          {
            environmentMode: accounting ? (exactAccounting ? arrivals(k, k) : arrivals(k)) : arrivalsWhy ? arrivals(k) : bounded(k),
            configure: (v, synth) => {
              const cap = classCap(budgetMs);
              v.timeout(budgetMs).totalBudget(budgetMs).signal(signal).enumerationMaxClasses(cap).nuMaxClasses(cap);
              const inSynth = allPlaces(synth);
              const pick = (ns: readonly string[]) => ns.map(n => inSynth.get(synthNames.get(n)!.name)!).filter(Boolean);
              if (prop.spec.kind === 'deadlockFree') {
                const sinks = pick(portSinks);
                if (sinks.length > 0) v.sinkPlaces(...sinks);
              }
              if (check.nu) {
                if (check.nu.budgets.length > 0) v.budgetPlaces(...pick(check.nu.budgets));
                // The synthetic net names the subnet's transitions `sut/<name>` (MOD-051).
                if ((check.nu.mints ?? []).length > 0) v.mintTransitions(...check.nu.mints!.map(n => `sut/${n}`));
                if ((check.nu.carriers ?? []).length > 0) v.carrierPlaces(...pick(check.nu.carriers!));
                v.fragmentMode('extended');
              }
              return v;
            },
          }));
      } catch (e) {
        results.push({ property: name, verdict: 'unknown', route: 'error', ms: round(performance.now() - t0), note: `SubnetDef.verify threw: ${errMsg(e)}` });
        continue;
      }
      const ms = round(performance.now() - t0);
      if (outcome === 'budget') { results.push(budgetResult(name, ms)); continue; }
      const r = [...outcome.perProperty.values()][0];
      if (r === undefined) { results.push({ property: name, verdict: 'unknown', route: 'error', ms, note: 'SubnetDef.verify returned no result' }); continue; }
      const notes = glueNote ? [glueNote] : [];
      if (!accounting && arrivalsWhy) notes.push(arrivalsWhy);
      if (accounting && !exactAccounting) notes.push(`upper bound only (≤ ${k * (prop.spec.kind === 'accounting' ? prop.spec.perUnit ?? 1 : 1)} outcomes): the subnet has ${check.inputs.length} input ports and mandatory arrivals would force k on each — "none lost" is checked by the small-scope gate`);
      results.push(fromSmt(name, r, ms, notes));
    }
  }
  return results;
}

/**
 * Property place names (as written in the subnet body) → places of SubnetDef.verify's synthetic net:
 * a port place becomes `harness_{in,out,io}_<port>`, every other body place `sut/<name>` (MOD-051).
 */
function syntheticPlaces(def: SubnetDef<void>): Map<string, Place<any>> {
  const m = new Map<string, Place<any>>();
  const portByPlace = new Map<string, string>();
  for (const port of def.iface.ports.values()) {
    const dir = port.direction === 'input' ? 'in' : port.direction === 'output' ? 'out' : 'io';
    portByPlace.set(port.place.name, `harness_${dir}_${port.name}`);
  }
  for (const [name] of allPlaces(def.body)) {
    const target = portByPlace.get(name) ?? `sut/${name}`;
    m.set(name, place(target));
  }
  return m;
}

// ─────────────────────────────────────────────────────────────────────────────
// Gate 1: lint
// ─────────────────────────────────────────────────────────────────────────────

/** Structural lint. Deterministic: transitions by name, arcs in declaration order. */
export function lint(
  net: PetriNet, marking: ReadonlyMap<string, number>, contract: Contract, nu?: Candidate['nu'],
): LintFinding[] {
  const out: LintFinding[] = [];
  const ts = sortedTransitions(net);
  const producers = new Map<string, Transition[]>();
  const consumers = new Map<string, Transition[]>();
  const push = (m: Map<string, Transition[]>, k: string, t: Transition) => { const l = m.get(k); if (l) { if (!l.includes(t)) l.push(t); } else m.set(k, [t]); };
  for (const t of ts) {
    for (const p of outPlaces(t.outputSpec)) push(producers, p.name, t);
    for (const i of t.inputSpecs) push(consumers, i.place.name, t);
  }
  const sources = new Set(expandNames(contract.sources, allPlaces(net).keys()));

  // dead-power-arc (r12): a reset/read/inhibitor on a place nothing ever writes or takes from and
  // that starts empty — typically a by-name reference to a place composition renamed away.
  for (const t of ts) {
    const power: Array<[string, Place<any>]> = [
      ...t.resets.map(a => ['reset', a.place] as [string, Place<any>]),
      ...t.reads.map(a => ['read', a.place] as [string, Place<any>]),
      ...t.inhibitors.map(a => ['inhibitor', a.place] as [string, Place<any>]),
    ];
    for (const [kind, p] of power) {
      if (producers.has(p.name) || consumers.has(p.name) || (marking.get(p.name) ?? 0) > 0 || sources.has(p.name)) continue;
      out.push({
        rule: 'dead-power-arc', severity: 'error', transition: t.name, place: p.name,
        message: `${kind} arc of '${t.name}' on '${p.name}', which no transition produces into or consumes from and which starts empty: the arc ${kind === 'inhibitor' ? 'never blocks' : 'never sees a token'}. Usually a by-name reference to a place that composition renamed (r12).`,
      });
    }
  }

  // reset-across-subnet / encapsulation (r4, r9, r17): an arc from a transition outside subnet S
  // to a place internal to S. Resets get their own rule; every other arc kind is 'encapsulation'.
  const mem = membership(net);
  for (const t of ts) {
    const ts_ = mem.get(t.name);
    for (const a of arcs(t)) {
      const ps = mem.get(a.place.name);
      if (ps === undefined || insideSubnet(ts_, ps)) continue; // nested instances sit inside their outer subnet
      const from = ts_ === undefined ? 'host transition' : `transition of subnet '${ts_}'`;
      out.push(a.kind === 'reset'
        ? {
            rule: 'reset-across-subnet', severity: 'warning', transition: t.name, place: a.place.name,
            message: `${from} '${t.name}' resets '${a.place.name}', internal to subnet '${ps}': a dependency no subnet contract can state, so the subnet cannot be proved alone (r4, r17).`,
          }
        : {
            rule: 'encapsulation', severity: 'warning', transition: t.name, place: a.place.name,
            message: `${from} '${t.name}' has a${a.kind === 'in' || a.kind === 'inhibitor' ? 'n' : ''} ${a.kind} arc on '${a.place.name}', internal to subnet '${ps}': talk to the subnet through its ports (r17).`,
          });
    }
  }

  // reset-on-source-fed (r6, r15): places downstream of a declared source, following input arcs
  // (place → consuming transition → output places). A reset there destroys events.
  const fed = new Set(expandNames([...contract.sources, ...(contract.inputs ?? []).map(i => i.place)], allPlaces(net).keys()));
  for (let changed = true; changed;) {
    changed = false;
    for (const t of ts) {
      if (!t.inputSpecs.some(i => fed.has(i.place.name))) continue;
      for (const p of outPlaces(t.outputSpec)) if (!fed.has(p.name)) { fed.add(p.name); changed = true; }
    }
  }
  for (const t of ts) {
    for (const r of t.resets) {
      if (!fed.has(r.place.name)) continue;
      out.push({
        rule: 'reset-on-source-fed', severity: 'warning', transition: t.name, place: r.place.name,
        message: `'${t.name}' resets '${r.place.name}', which is fed by a declared source: an event held there is lost without an outcome. Only the accounting property can see this (r6, r15).`,
      });
    }
  }

  // duplicate-input-arc (r8): two input specs on one place crashed StateClassGraph. Transition.build
  // rejects them since CORE-030 AC3, so this is a backstop for a net assembled some other way.
  for (const t of ts) {
    const seen = new Map<string, number>();
    for (const i of t.inputSpecs) seen.set(i.place.name, (seen.get(i.place.name) ?? 0) + 1);
    for (const [p, n] of seen) if (n > 1) out.push({
      rule: 'duplicate-input-arc', severity: 'error', transition: t.name, place: p,
      message: `'${t.name}' has ${n} input specs on '${p}': use one spec with a count (exactly(n) / atLeast(n)) (r8).`,
    });
  }

  out.push(...lintNuCarriers(ts, nu));
  return out;
}

/**
 * nu-undeclared-carrier (r3; PNID validation Figs. 9, 12, 13). Structure cannot tell a relay from a
 * mint, so the rule asks the candidate to say which is which instead of guessing from ancestry (a
 * guess a budget or resource refund defeats: the refund closes a cycle and every transition becomes
 * every other's ancestor).
 *
 * For every ν-join (match-spec transition) and each of its key places, each non-join producer of the
 * key place must be a *declared* mint or relay:
 *  - a declared mint: listed in Candidate.nu.mints, or consuming a declared budget place. libpetri
 *    reads a write of a key as a fresh name only for such a transition (NU-010); an undeclared one
 *    keeps the net off both ν routes, and every quiescence property comes back unknown;
 *  - a declared relay: it consumes a declared carrier, or a key place while carriers are declared
 *    (the EXTENDED consume role).
 * A producer that is neither is flagged, and so is one whose other inputs are produced upstream
 * without being declared carriers or budgets (unless it is listed in `mints`): its name may come from
 * upstream, so it has to be declared one way or the other. Joins that write a key place back are
 * outside the fragment; the verifier then falls back to its sound name-blind over-approximation, so
 * they are not flagged here. A net with match specs and no declared budget is an error too: without
 * one Route A (the coloured encoding) is unavailable, and Route B closes only when something else
 * bounds the names in flight.
 */
function lintNuCarriers(ts: readonly Transition[], nu: Candidate['nu']): LintFinding[] {
  const out: LintFinding[] = [];
  const joins = ts.filter(t => t.matchSpec !== null);
  if (joins.length === 0) return out;
  const budgets = new Set(nu?.budgets ?? []);
  const carriers = new Set(nu?.carriers ?? []);
  const mints = new Set(nu?.mints ?? []);
  if (budgets.size === 0) {
    out.push({
      rule: 'nu-undeclared-carrier', severity: 'error', transition: joins[0]!.name,
      message: `ν-net (match specs on ${joins.map(j => `'${j.name}'`).join(', ')}) without a declared budget place: Route A cannot run, and Route B closes only when something else bounds the names in flight. Declare Candidate.nu.budgets (NU-040).`,
    });
  }
  const keys = new Set(joins.flatMap(j => j.matchSpec!.keys.map(k => k.place.name)));
  const produced = new Set(ts.flatMap(t => [...outPlaces(t.outputSpec)].map(p => p.name)));
  const relayInput = (p: string) => carriers.has(p) || (keys.has(p) && carriers.size > 0);

  const flagged = new Set<string>();
  for (const join of joins) {
    for (const key of join.matchSpec!.keys.map(k => k.place.name)) {
      for (const t of ts) {
        if (t.matchSpec !== null || ![...outPlaces(t.outputSpec)].some(p => p.name === key)) continue;
        if (flagged.has(t.name) || mints.has(t.name)) continue;
        const inputs = t.inputSpecs.map(i => i.place.name);
        const undeclared = inputs.filter(p => !budgets.has(p) && !relayInput(p) && produced.has(p));
        if (undeclared.length > 0) {
          flagged.add(t.name);
          out.push({
            rule: 'nu-undeclared-carrier', severity: 'error', transition: t.name, place: key,
            message: `'${t.name}' produces '${key}', a key of ν-join '${join.name}', from ${undeclared.map(p => `'${p}'`).join(', ')}, which is neither a declared budget nor a declared carrier. If the name comes from upstream, declare those places in Candidate.nu.carriers (EXTENDED fragment); if '${t.name}' mints with freshName(), declare it in Candidate.nu.mints or its supply in Candidate.nu.budgets (r3, NU-010, PNID 13(b)).`,
          });
          continue;
        }
        const declaredMint = inputs.some(p => budgets.has(p));
        if (declaredMint || inputs.some(relayInput)) continue;
        flagged.add(t.name);
        out.push({
          rule: 'nu-undeclared-carrier', severity: 'error', transition: t.name, place: key,
          message: `'${t.name}' writes '${key}', a key of ν-join '${join.name}', without consuming a name, and is not a declared mint. libpetri reads such a write as a fresh name only for a declared mint (NU-010); as it stands the net is kept off both ν routes and every quiescence property comes back unknown. If '${t.name}' mints with freshName(), declare it in Candidate.nu.mints or consume a declared budget place.`,
        });
      }
    }
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// helpers
// ─────────────────────────────────────────────────────────────────────────────

function joinNotes(notes: readonly string[]): string | undefined {
  const n = notes.filter(s => s.length > 0);
  return n.length > 0 ? n.join('; ') : undefined;
}

/**
 * Class cap for a synchronous route given the remaining budget: Route B's measured cost
 * t ≈ 0.9 s · (n / 2000)², solved for n, never above {@link DEFAULT_CLASS_CAP}.
 */
function classCap(remainingMs: number): number {
  return Math.max(50, Math.min(DEFAULT_CLASS_CAP, Math.floor(2000 * Math.sqrt(Math.max(0, remainingMs) / 900))));
}

function round(ms: number): number { return Math.round(ms * 10) / 10; }

function errMsg(e: unknown): string { return e instanceof Error ? e.message : String(e); }
