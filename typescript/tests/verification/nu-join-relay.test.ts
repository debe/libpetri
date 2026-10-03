import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { deadlockFree, placeBound, unreachable, type SmtProperty } from '../../src/verification/smt-property.js';
import { classify, type FragmentMode } from '../../src/verification/analysis/name-fragment.js';
import { NameStateClassGraph, nameSuccessors } from '../../src/verification/analysis/name-state-class-graph.js';
import { expandTransition } from '../../src/verification/analysis/state-class-graph.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { computePSemiflows } from '../../src/verification/invariant/p-invariant-computer.js';
import { buildColouredPlan } from '../../src/verification/z3/name-coloured-encoder.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, forwardInput, outPlace, timeout, xor, type Out } from '../../src/core/out.js';
import { matchKey, matchSpec, relayKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { produces } from '../fixtures/producing-actions.js';
import {
  FIG_12C_ROWS, JOIN_CHAIN_ROWS, JOIN_CHAIN_SPLIT_ROWS, N1_CORR_ROWS, UNION_ROWS, pnidNet, withoutRelays,
} from '../fixtures/pnid-nets.js';
import { describeZ3 } from '../fixtures/z3.js';
import { compareScript } from '../fixtures/script-parity.js';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { allMints } from '../fixtures/all-mints.js';
import { declaredMints } from '../../src/verification/analysis/name-fragment.js';

/**
 * [NU-054] join relay in the analysers: classification under EXTENDED / BASE (AC4, AC5), Route B
 * name successors (AC3 and the PNID fixtures of the test derivation), Route A agreement (AC6) and
 * the orbit dedup of [VER-012] with a relay step.
 */

type Rows = Parameters<typeof pnidNet>[1];

const FIG_12C_CARRIERS = ['P1', 'B1', 'B2', 'C1', 'D1'];

interface Run {
  readonly rows: Rows;
  readonly marking: ReadonlyArray<readonly [string, number]>;
  readonly property: (p: (n: string) => any) => SmtProperty;
  readonly sinks?: readonly string[];
  readonly budgets?: readonly string[];
  readonly carriers?: readonly string[];
  readonly mode?: FragmentMode;
  /** Truncate Route B at one class so a bounded quiescence query defers to Route A (NU-053). */
  readonly forceRouteA?: boolean;
  /** Skip the VER-015 linear bound, which runs first and proves some bounds before Route A. */
  readonly noLinearBound?: boolean;
}

async function verify(r: Run): Promise<SmtVerificationResult> {
  const { net, places } = pnidNet('relay', r.rows);
  const p = (n: string) => {
    const x = places.get(n);
    if (x === undefined) throw new Error(`no place ${n}`);
    return x;
  };
  let v = SmtVerifier.forNet(net)
    .enumerationMaxClasses(0)
    .initialMarking(m => { for (const [n, k] of r.marking) m.tokens(p(n), k); })
    .property(r.property(p))
    .fragmentMode(r.mode ?? 'extended')
    .timeout(30_000);
  if (r.sinks) v = v.sinkPlaces(...r.sinks.map(p));
  if (r.budgets) {
    v = v.budgetPlaces(...r.budgets.map(p));
  } else {
    // Without the budget declaration the mints are declared by name (NU-010): the transitions
    // that consume an initially marked place, which is where each fixture's budget sits.
    const marked = new Set(r.marking.map(([n]) => n));
    v = v.mintTransitions(
      ...[...net.transitions].filter(t => t.inputSpecs.some(s => marked.has(s.place.name))).map(t => t.name),
    );
  }
  if (r.carriers) v = v.carrierPlaces(...r.carriers.map(p));
  if (r.forceRouteA) v = v.nuMaxClasses(1);
  if (r.noLinearBound) v = v.linearBound(false);
  return v.verify();
}

const ROUTE_A_NOTE = 'name-colouring over k colour slots';

// ─── classification (AC4) ────────────────────────────────────────────────────

describe('NU-054 classification', () => {
  const key = <T>(p: ReturnType<typeof place<T>>) => matchKey(p, (v: T) => nameId(String(v)));
  const relay = <T>(p: ReturnType<typeof place<T>>) => relayKey(p, (v: T) => nameId(String(v)));

  it('EXTENDED: relay targets join the coloured set and the join carries them', () => {
    const { net } = pnidNet('12c', FIG_12C_ROWS);
    const f = classify(net, 'extended', new Set(FIG_12C_CARRIERS), allMints(net));
    expect(f).not.toBeNull();
    expect(f!.isColoured('P5')).toBe(true);
    const e = f!.role('e');
    expect(e.type).toBe('join');
    expect(e.type === 'join' && [...e.relayTo]).toEqual(['P5']);
    // f and g drain: no relay target.
    const g = f!.role('g');
    expect(g.type === 'join' && g.relayTo.size).toBe(0);
  });

  it('EXTENDED: a join producing a coloured place it does not declare is still a re-mint', () => {
    const { net } = pnidNet('12c', withoutRelays(FIG_12C_ROWS));
    expect(classify(net, 'extended', new Set(FIG_12C_CARRIERS), allMints(net))).toBeNull();
  });

  it('BASE ignores the declaration: the relaying join is rejected as before', () => {
    const { net } = pnidNet('12c', FIG_12C_ROWS);
    expect(classify(net, 'base', new Set(), allMints(net))).toBeNull();
    const { net: chain } = pnidNet('chain', JOIN_CHAIN_ROWS);
    expect(classify(chain, 'base', new Set(), allMints(chain))).toBeNull();
    expect(classify(chain, 'extended', new Set(), allMints(chain))).not.toBeNull();
  });

  /** fork: S → A, B (mint); j: A, B (+ extra) → C relaying to C; k: C, D joins C downstream. */
  function relayNet(extra: 'offKey' | 'read' | 'inhibitor' | 'reset' | 'none') {
    const s = place<string>('S');
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');
    const d = place<string>('D');
    const done = place<string>('done');
    const x = place<string>('X');
    const fork = Transition.builder('fork').inputs(one(s)).outputs(andPlaces(a, b, d)).action(produces()).build();
    let jb = Transition.builder('j')
      .inputs(one(a), one(b), ...(extra === 'offKey' ? [one(c)] : []))
      .outputs(outPlace(c))
      .match(matchSpec(key(a), key(b), relay(c)))
      .action(produces());
    if (extra === 'read') jb = jb.read(c);
    if (extra === 'inhibitor') jb = jb.inhibitor(c);
    const k = Transition.builder('k').inputs(one(c), one(d)).outputs(outPlace(done))
      .match(matchSpec(key(c), key(d))).action(produces()).build();
    const other = extra === 'reset'
      ? [Transition.builder('r').inputs(one(x)).reset(c).build()]
      : [];
    return PetriNet.builder('relay').transitions(fork, jb.build(), k, ...other).build();
  }

  it('accepts the plain relay under EXTENDED', () => {
    expect(classify(relayNet('none'), 'extended', new Set(), allMints(relayNet('none')))).not.toBeNull();
  });

  it('rejects a relay target the join also consumes off-key (NU-051 AC7)', () => {
    expect(classify(relayNet('offKey'), 'extended', new Set(), allMints(relayNet('offKey')))).toBeNull();
  });

  it('a relay target no join consumes is coloured all the same, and its read arc rejects', () => {
    const s = place<string>('S');
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');
    const x = place<string>('X');
    const y = place<string>('Y');
    const fork = Transition.builder('fork').inputs(one(s)).outputs(andPlaces(a, b)).action(produces()).build();
    const j = Transition.builder('j').inputs(one(a), one(b)).outputs(outPlace(c))
      .match(matchSpec(key(a), key(b), relay(c))).action(produces()).build();
    const plain = PetriNet.builder('sinkRelay').transitions(fork, j).build();
    const f = classify(plain, 'extended', new Set(), allMints(plain));
    expect(f?.isColoured('C')).toBe(true);
    const watcher = Transition.builder('w').inputs(one(x)).outputs(outPlace(y)).read(c).action(produces()).build();
    const read = PetriNet.builder('sinkRelayRead').transitions(fork, j, watcher).build();
    expect(classify(read, 'extended', new Set(), allMints(read))).toBeNull();
  });

  for (const arc of ['read', 'inhibitor', 'reset'] as const) {
    it(`rejects a relay target carrying a ${arc} arc`, () => {
      expect(classify(relayNet(arc), 'extended', new Set(), allMints(relayNet(arc)))).toBeNull();
    });
  }
});

// ─── Route B verdicts (AC3, PNID fixtures) ───────────────────────────────────

describe('NU-054 Route B decides join chains and correlated self-loops', () => {
  it('AC3: the join chain reaches done (Violated) and is deadlock-free (Proven)', async () => {
    const reach = await verify({ rows: JOIN_CHAIN_ROWS, marking: [['S', 1]], property: p => unreachable(new Set([p('done')])) });
    expect(reach.verdict.type).toBe('violated');
    expect(reach.route).toBe('nu-scg');
    expect(reach.counterexampleTransitions).toEqual(['fork', 'j1', 'j2']);
    const dlf = await verify({ rows: JOIN_CHAIN_ROWS, marking: [['S', 1]], property: () => deadlockFree(), sinks: ['done'] });
    expect(dlf.verdict.type).toBe('proven');
    expect(dlf.route).toBe('nu-scg');
  });

  it('AC3: with D from an independent mint, done is unreachable — no two names are equated', async () => {
    const r = await verify({
      rows: JOIN_CHAIN_SPLIT_ROWS, marking: [['S', 1], ['S2', 1]], property: p => unreachable(new Set([p('done')])),
    });
    expect(r.verdict.type).toBe('proven');
    expect(r.route).toBe('nu-scg');
  });

  it('the join chain without the declaration falls back (quiescence Unknown)', async () => {
    const r = await verify({ rows: withoutRelays(JOIN_CHAIN_ROWS), marking: [['S', 1]], property: () => deadlockFree(), sinks: ['done'] });
    expect(r.verdict.type).toBe('unknown');
    expect(r.report).toContain('EXTENDED) declined');
  });

  for (const k of [1, 2]) {
    it(`Fig. 12(c) at k=${k}: deadlockFree and placeBound(OR, 2) hold (paper: sound, bounded)`, async () => {
      const base = { rows: FIG_12C_ROWS, marking: [['R', k]] as const, sinks: ['R'], carriers: FIG_12C_CARRIERS };
      const dlf = await verify({ ...base, property: () => deadlockFree(), budgets: ['R'] });
      expect(dlf.verdict.type).toBe('proven');
      expect(dlf.route).toBe('nu-scg');
      // No budget declared, so the reachability-safety query goes to Route B rather than Route A.
      const bound = await verify({ ...base, property: p => placeBound(p('OR'), 2) });
      expect(bound.verdict.type).toBe('proven');
      expect(bound.route).toBe('nu-scg');
    });
  }

  it('Fig. 12(c) without the declaration: deadlockFree Unknown (EXTENDED declined)', async () => {
    const r = await verify({
      rows: withoutRelays(FIG_12C_ROWS), marking: [['R', 1]], property: () => deadlockFree(),
      sinks: ['R'], budgets: ['R'], carriers: FIG_12C_CARRIERS,
    });
    expect(r.verdict.type).toBe('unknown');
    expect(r.report).toContain('EXTENDED) declined');
  });

  it('Fig. 6(a) N1 correlated: deadlockFree Violated with the trace A, C', async () => {
    const r = await verify({ rows: N1_CORR_ROWS, marking: [['SUPPLY', 1]], property: () => deadlockFree(), sinks: ['E_done'], budgets: ['SUPPLY'] });
    expect(r.verdict.type).toBe('violated');
    expect(r.route).toBe('nu-scg');
    expect(r.counterexampleTransitions).toEqual(['A', 'C']);
    const k2 = await verify({ rows: N1_CORR_ROWS, marking: [['SUPPLY', 2]], property: () => deadlockFree(), sinks: ['E_done'], budgets: ['SUPPLY'] });
    expect(k2.verdict.type).toBe('violated');
    expect(k2.route).toBe('nu-scg');
    const before = await verify({
      rows: withoutRelays(N1_CORR_ROWS), marking: [['SUPPLY', 1]], property: () => deadlockFree(), sinks: ['E_done'], budgets: ['SUPPLY'],
    });
    expect(before.verdict.type).toBe('unknown');
  });

  it('S union N ⊕ M: deadlockFree Violated with the trace a, through Route B', async () => {
    const r = await verify({ rows: UNION_ROWS, marking: [['SUPPLY', 1]], property: () => deadlockFree(), sinks: ['d_done'], budgets: ['SUPPLY'], carriers: ['q'] });
    expect(r.verdict.type).toBe('violated');
    expect(r.route).toBe('nu-scg');
    expect(r.counterexampleTransitions).toEqual(['a']);
  });
});

// ─── BASE (AC5) ──────────────────────────────────────────────────────────────

describe('NU-054 under BASE', () => {
  it('Fig. 12(c): the verdict is the one without the declaration, and the report names it ignored', async () => {
    const run = (rows: Rows) => verify({
      rows, marking: [['R', 1]], property: () => deadlockFree(), sinks: ['R'], budgets: ['R'], mode: 'base',
    });
    const withRelay = await run(FIG_12C_ROWS);
    const without = await run(withoutRelays(FIG_12C_ROWS));
    expect(withRelay.verdict).toEqual(without.verdict);
    expect(withRelay.route).toBe(without.route);
    expect(withRelay.report).toContain(
      "NOTE: ν relay declarations ignored under BASE fragment mode (NU-054): 'e' -> 'P5'; " +
      "select fragmentMode('extended') to analyse the joins as relays.",
    );
    expect(without.report).not.toContain('NU-054');
  });
});

// ─── Route A vs Route B (AC6) ────────────────────────────────────────────────

describeZ3('NU-054 Route A (coloured IC3) agrees with Route B', () => {
  interface Pair {
    readonly name: string;
    /** Route B: no budget for a reachability-safety query, the default class cap otherwise. */
    readonly routeB: Run;
    /** Route A: budget declared; quiescence forced past a truncated Route B. */
    readonly routeA: Run;
    readonly expected: 'proven' | 'violated';
  }
  const bound12c = (n: number): Omit<Run, 'budgets'> => ({
    rows: FIG_12C_ROWS, marking: [['R', 2]], property: p => placeBound(p('OR'), n), sinks: ['R'], carriers: FIG_12C_CARRIERS,
  });
  const n1 = { rows: N1_CORR_ROWS, marking: [['SUPPLY', 1]] as const, sinks: ['E_done'] };
  const union = { rows: UNION_ROWS, marking: [['SUPPLY', 1]] as const, property: () => deadlockFree(), sinks: ['d_done'], carriers: ['q'], budgets: ['SUPPLY'] };
  const chainReach = { rows: JOIN_CHAIN_ROWS, marking: [['S', 1]] as const, property: (p: (n: string) => any) => unreachable(new Set([p('done')])) };
  const splitReach = { rows: JOIN_CHAIN_SPLIT_ROWS, marking: [['S', 1], ['S2', 1]] as const, property: (p: (n: string) => any) => unreachable(new Set([p('done')])) };
  const PAIRS: Pair[] = [
    { name: 'Fig. 12(c) placeBound(OR, 2), k=2', routeB: bound12c(2), routeA: { ...bound12c(2), budgets: ['R'] }, expected: 'proven' },
    { name: 'Fig. 12(c) placeBound(OR, 1), k=2', routeB: bound12c(1), routeA: { ...bound12c(1), budgets: ['R'] }, expected: 'violated' },
    {
      name: 'N1 deadlockFree, k=1',
      routeB: { ...n1, property: () => deadlockFree(), budgets: ['SUPPLY'] },
      routeA: { ...n1, property: () => deadlockFree(), budgets: ['SUPPLY'], forceRouteA: true },
      expected: 'violated',
    },
    {
      name: 'N1 unreachable(E_done), k=1',
      routeB: { ...n1, property: p => unreachable(new Set([p('E_done')])) },
      routeA: { ...n1, property: p => unreachable(new Set([p('E_done')])), budgets: ['SUPPLY'] },
      expected: 'violated',
    },
    {
      // The self-loop nets to zero on its key: B keeps one token of the case in Y1.
      name: 'N1 placeBound(Y1, 1), k=1',
      routeB: { ...n1, property: p => placeBound(p('Y1'), 1) },
      routeA: { ...n1, property: p => placeBound(p('Y1'), 1), budgets: ['SUPPLY'] },
      expected: 'proven',
    },
    { name: 'S union deadlockFree, k=1', routeB: union, routeA: { ...union, forceRouteA: true }, expected: 'violated' },
    { name: 'join chain unreachable(done)', routeB: chainReach, routeA: { ...chainReach, budgets: ['S'] }, expected: 'violated' },
    { name: 'split chain unreachable(done)', routeB: splitReach, routeA: { ...splitReach, budgets: ['S', 'S2'] }, expected: 'proven' },
  ];
  for (const pair of PAIRS) {
    it(pair.name, async () => {
      const b = await verify(pair.routeB);
      expect(b.route).toBe('nu-scg');
      expect(b.verdict.type).toBe(pair.expected);
      // Route A itself is under test: the VER-015 bound, which precedes it, is switched off.
      const a = await verify({ ...pair.routeA, noLinearBound: true });
      expect(a.route).toBe('smt');
      expect(a.report).toContain(ROUTE_A_NOTE);
      expect(a.verdict.type).toBe(pair.expected);
    }, 60_000);
  }
});

describe('NU-054 Route A plan', () => {
  function planOf(rows: Rows, marking: ReadonlyArray<readonly [string, number]>, budgets: string[], mode: FragmentMode) {
    const { net, places } = pnidNet('plan', rows);
    const m = MarkingState.builder();
    for (const [n, k] of marking) m.tokens(places.get(n)!, k);
    const initial = m.build();
    const flat = flatten(net);
    const semiflows = computePSemiflows(IncidenceMatrix.from(flat), flat, initial);
    return { flat, plan: buildColouredPlan(net, flat, initial, declaredMints(net, new Set(budgets), new Set()), mode, new Set(), () => semiflows) };
  }

  it('colours a relay target no join consumes, and produces on it from the join', () => {
    const { flat, plan } = planOf(
      [['m', ['S'], ['A', 'B']], ['j', ['A', 'B'], ['C'], { match: ['A', 'B'], relay: ['C'] }]],
      [['S', 1]], ['S'], 'extended',
    );
    expect(plan).not.toBeNull();
    const c = flat.placeIndex.get('C')!;
    expect(plan!.isColoured[c]).toBe(true);
    const j = plan!.classes[flat.transitions.findIndex(t => t.name === 'j')]!;
    expect(j.kind === 'join' && j.relayOut).toEqual([c]);
  });

  it('the N1 self-loop keeps its key among the relay outputs; BASE declines the relaying join', () => {
    const { flat, plan } = planOf(N1_CORR_ROWS, [['SUPPLY', 1]], ['SUPPLY'], 'extended');
    expect(plan).not.toBeNull();
    const idx = (n: string) => flat.placeIndex.get(n)!;
    const b = plan!.classes[flat.transitions.findIndex(t => t.name === 'B')]!;
    expect(b.kind === 'join' && [...b.relayOut].sort()).toEqual([idx('Y1'), idx('q'), idx('w')].sort());
    expect(planOf(N1_CORR_ROWS, [['SUPPLY', 1]], ['SUPPLY'], 'base').plan).toBeNull();
  });
});

// ─── a join's timeout writes into a relay target ─────────────────────────────

describeZ3('NU-054 a join timeout write into a relay target', () => {
  const key = <T>(p: ReturnType<typeof place<T>>) => matchKey(p, (v: T) => nameId(String(v)));
  const relay = <T>(p: ReturnType<typeof place<T>>) => relayKey(p, (v: T) => nameId(String(v)));

  /**
   * The AC3 join chain with j1's relay into C written two ways: by the action, or by the executor
   * on timeout (`child`). j1 also consumes the uncoloured Z, so a forward of a non-key input can be
   * stated.
   */
  function chainWithTimeout(child: (a: any, z: any, c: any) => Out) {
    const [s, a, b, c, d, z, done] = ['S', 'A', 'B', 'C', 'D', 'Z', 'done'].map(n => place<string>(n));
    const fork = Transition.builder('fork').inputs(one(s!)).outputs(andPlaces(a!, b!, d!)).action(produces()).build();
    const j1 = Transition.builder('j1').inputs(one(a!), one(b!), one(z!))
      .outputs(xor(outPlace(c!), timeout(10, child(a, z, c))))
      .match(matchSpec(key(a!), key(b!), relay(c!))).action(produces()).build();
    const j2 = Transition.builder('j2').inputs(one(c!), one(d!)).outputs(outPlace(done!))
      .match(matchSpec(key(c!), key(d!))).action(produces()).build();
    const net = PetriNet.builder('chain-timeout').transitions(fork, j1, j2).build();
    return { net, s: s!, z: z!, done: done! };
  }

  function deadlock({ net, s, z, done }: ReturnType<typeof chainWithTimeout>) {
    return SmtVerifier.forNet(net).enumerationMaxClasses(0)
      .initialMarking(m => { m.tokens(s, 1).tokens(z, 1); })
      .property(deadlockFree()).sinkPlaces(done).budgetPlaces(s)
      .fragmentMode('extended').timeout(2_000).verify();
  }

  // The executor checks every token a join deposits in a relay target, timeout branches
  // included. A unit token (`outPlace` under `timeout`) or a forward of a non-key input carries no
  // name or another one, so that firing fails and deposits nothing: A and B are gone, D is
  // stranded and the net deadlocks. The name layer would relay the matched name into C instead
  // and let j2 fire, a wrong `proven`. Only a forward of a match key relays the matched name, and
  // only that timeout write keeps the join in the fragment, for Route B and Route A alike.
  it.each([
    ['a unit token', (_a: any, _z: any, c: any) => outPlace(c)],
    ['the non-key Z', (_a: any, z: any, c: any) => forwardInput(z, c)],
  ] as const)('a timeout writing %s into the relay target is out of the fragment', async (_what, child) => {
    const n = chainWithTimeout(child);
    const r = await deadlock(n);
    expect(r.verdict.type, r.report).not.toBe('proven');
    expect(r.report).toContain('Route B (EXTENDED) declined');
    expect(r.report).not.toContain('ν-encoding: name-coloured');
    expect(classify(n.net, 'extended', new Set(), allMints(n.net))).toBeNull();
  }, 30_000);

  it('a timeout forwarding a match key into the relay target stays in the fragment', async () => {
    const n = chainWithTimeout((a, _z, c) => forwardInput(a, c));
    expect(classify(n.net, 'extended', new Set(), allMints(n.net))).not.toBeNull();
    const r = await deadlock(n);
    expect(r.route).toBe('nu-scg');
    expect(r.verdict.type, r.report).toBe('proven');
  }, 30_000);
});

// ─── orbit dedup with a relay step (VER-012) ─────────────────────────────────

describe('NU-054 relay step and the orbit dedup', () => {
  /**
   * The dedup emits one successor per distinct pre-step signature. A relay step removes `s` from
   * the keys and adds it back to the relay targets, so a transposition of two symbols with equal
   * pre-step signatures fixes the layer and maps one successor onto the other: equal keys. Check
   * that on every reachable class: the keys the library emits equal the keys a per-symbol step
   * (no dedup) produces.
   */
  const CASES = [
    { name: 'N1 correlated, SUPPLY 3', rows: N1_CORR_ROWS, marking: [['SUPPLY', 3]] as const, carriers: [] as string[] },
    { name: 'Fig. 12(c), R 3', rows: FIG_12C_ROWS, marking: [['R', 3]] as const, carriers: FIG_12C_CARRIERS },
    // Two enabling symbols of `j` whose signatures differ off the keys (one still holds `E`):
    // they must not collapse, and the dedup must not read the post-step layer.
    {
      name: 'relay beside an undrained carrier, S 2',
      rows: [
        ['m', ['S'], ['A', 'B', 'E']],
        ['t', ['E'], []],
        ['j', ['A', 'B'], ['C'], { match: ['A', 'B'], relay: ['C'] }],
        ['k', ['C'], ['done']],
      ] as Rows,
      marking: [['S', 2]] as const,
      carriers: ['E'],
    },
  ];
  for (const c of CASES) {
    it(`${c.name}: deduplicated successors cover every per-symbol successor`, () => {
      const { net, places } = pnidNet('orbit', c.rows);
      const m = MarkingState.builder();
      for (const [n, k] of c.marking) m.tokens(places.get(n)!, k);
      const fragment = classify(net, 'extended', new Set(c.carriers), allMints(net))!;
      expect(fragment).not.toBeNull();
      const g = NameStateClassGraph.build(net, m.build(), fragment, 100_000);
      expect(g.isComplete()).toBe(true);
      let relaySteps = 0;
      let collapsed = 0;
      for (const cls of g.classes) {
        for (const t of cls.base.enabledTransitions) {
          const role = fragment.role(t.name);
          if (role.type !== 'join' || role.relayTo.size === 0) continue;
          for (const vt of expandTransition(t)) {
            const emitted = nameSuccessors(role, cls.names, vt.outputPlaces, fragment, { next: 0 })
              .map(step => step.after.canonicalKey(fragment.colouredOrder));
            // Per-symbol reference step: every enabling symbol, no dedup.
            const [first, firstReq] = role.colouredIn[0]!;
            const reference = new Set<string>();
            let enabling = 0;
            for (const s of cls.names.symbolsIn(first)) {
              if (cls.names.countOf(first, s) < firstReq) continue;
              if (!role.colouredIn.every(([p, req]) => cls.names.countOf(p, s) >= req)) continue;
              enabling++;
              const nm = cls.names.copy();
              for (const [p, req] of role.colouredIn) nm.remove(p, s, req);
              for (const p of vt.outputPlaces) if (role.relayTo.has(p.name)) nm.add(p.name, s, 1);
              reference.add(nm.canonicalKey(fragment.colouredOrder));
            }
            expect(new Set(emitted)).toEqual(reference);
            expect(emitted.length).toBe(reference.size);
            relaySteps++;
            if (enabling > reference.size) collapsed++;
          }
        }
      }
      expect(relaySteps).toBeGreaterThan(0);
      // The fixture exercises the dedup: some relay step had two enabling symbols of one orbit.
      expect(collapsed).toBeGreaterThan(0);
    });
  }
});

// ─── SMT script parity (VER-013) ─────────────────────────────────────────────

describe('NU-054 SMT script parity (VER-013 AC1)', () => {
  // The relay fixtures of spec/verification-fixtures/nu-relay-fixtures.json: the shared schema,
  // with each net inline as rows [transition, inputs, outputs, match keys, relay targets]. Their
  // goldens under spec/verification-fixtures/scripts/<id>/ are written by Rust only
  // (scripts/smt-script-parity.py --update); a diff is a finding, never a golden edit.
  const root = resolve(dirname(fileURLToPath(import.meta.url)), '../../../spec/verification-fixtures');
  const relayFixtures: readonly RelayFixture[] =
    JSON.parse(readFileSync(join(root, 'nu-relay-fixtures.json'), 'utf8')).fixtures;
  const scriptsDir = join(root, 'scripts');

  it('lists the relay fixtures', () => {
    expect(relayFixtures.length).toBeGreaterThan(0);
  });

  for (const fixture of relayFixtures) {
    it(fixture.id, () => {
      const rows: Rows = fixture.rows.map(([t, ins, outs, match, relay]) =>
        match.length > 0 ? [t, ins, outs, { match, relay }] as const : [t, ins, outs] as const);
      const { net, places } = pnidNet(fixture.net, rows);
      const p = (n: string) => {
        const x = places.get(n);
        if (x === undefined) throw new Error(`fixture references unknown place '${n}'`);
        return x;
      };
      const prop = fixture.property;
      const verifier = SmtVerifier.forNet(net)
        .enumerationMaxClasses(0)
        .initialMarking(m => { for (const [n, k] of Object.entries(fixture.marking)) m.tokens(p(n), k); })
        .property(prop.type === 'deadlock-free' ? deadlockFree()
          : prop.type === 'place-bound' ? placeBound(p(prop.place!), prop.bound!)
          : prop.type === 'unreachable' ? unreachable(new Set([p(prop.place!)]))
          : (() => { throw new Error(`unknown relay fixture property '${prop.type}'`); })())
        .certificateCheck(true)
        .counterexampleReplay(true)
        .timeout(30_000);
      if (fixture.sinkPlaces?.length) verifier.sinkPlaces(...fixture.sinkPlaces.map(p));
      if (fixture.budgetPlaces?.length) verifier.budgetPlaces(...fixture.budgetPlaces.map(p));
      if (fixture.carrierPlaces?.length) verifier.carrierPlaces(...fixture.carrierPlaces.map(p));
      if (fixture.fragmentMode !== undefined) verifier.fragmentMode(fixture.fragmentMode);
      const scripts = verifier.encodeScripts();
      const dir = join(scriptsDir, fixture.id);
      compareScript(fixture.id, join(dir, 'horn.smt2'), scripts.horn);
      compareScript(fixture.id, join(dir, 'certificate.smt2'), scripts.certificate);
      compareScript(fixture.id, join(dir, 'bound.smt2'), scripts.bound);
      compareScript(fixture.id, join(dir, 'state-equation.smt2'), scripts.stateEquation);
    });
  }
});

/** A row of `nu-relay-fixtures.json`: transition, inputs, outputs, match keys, relay targets. */
type RelayRow = readonly [string, string[], string[], string[], string[]];

interface RelayFixture {
  readonly id: string;
  readonly net: string;
  readonly rows: readonly RelayRow[];
  readonly marking: Readonly<Record<string, number>>;
  readonly property: { readonly type: string; readonly place?: string; readonly bound?: number };
  readonly sinkPlaces?: readonly string[];
  readonly budgetPlaces?: readonly string[];
  readonly carrierPlaces?: readonly string[];
  readonly fragmentMode?: FragmentMode;
}
