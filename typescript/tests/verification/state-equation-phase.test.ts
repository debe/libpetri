import { describe, it, expect } from 'vitest';
import { mkdtempSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import { stateEquationConditions } from '../../src/verification/z3/smt-encoder.js';
import { vectorize, violationPredicate } from '../../src/verification/z3/abstract-replayer.js';
import {
  decodeCandidate, encodeStateEquationQuery, formatInequality, holdsAt, refinementCertificate,
  type MarkingInequality,
} from '../../src/verification/z3/state-equation-query.js';
import { refutingTrap } from '../../src/verification/z3/trap-refinement.js';
import { checkInductiveExact } from '../../src/verification/z3/invariant-synthesis.js';
import { searchWithinCounts } from '../../src/verification/z3/parikh-search.js';
import {
  checkRankingExact, decodeBoundedRun, encodeBoundedRun, replayRun,
} from '../../src/verification/z3/bounded-run.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { environmentPlace, place, type Place } from '../../src/core/place.js';
import { one, all } from '../../src/core/in.js';
import { andPlaces, outPlace, xor } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * VER-018 (state-equation phase) and VER-019 (firing bound).
 *
 * The join of a compiled workflow: `route` sends data down one arm and an empty
 * marker down the other; a data arm writes `hasdata` with its `ready`, an empty arm
 * `ready` alone; `mergeStart` takes both readies with `all(hasdata)`, `mergeSkip` both
 * readies under `inhibitor(hasdata)`. The marking equation admits `mergeSkip` firing
 * after a data token arrived, stranding `hasdata`; only the inhibitor rules that out.
 */
function joinWithSkip() {
  const start = place('start'), aData = place('aData'), aEmpty = place('aEmpty');
  const bData = place('bData'), bEmpty = place('bEmpty');
  const hasdata = place('hasdata'), ready0 = place('ready0'), ready1 = place('ready1');
  const done = place('done'), skipped = place('skipped');
  const t = (name: string) => Transition.builder(name).action(produces());
  const net = PetriNet.builder('joinWithSkip').transitions(
    t('route').inputs(one(start)).outputs(xor(andPlaces(aData, bEmpty), andPlaces(aEmpty, bData))).build(),
    t('armAData').inputs(one(aData)).outputs(andPlaces(hasdata, ready0)).build(),
    t('armAEmpty').inputs(one(aEmpty)).outputs(outPlace(ready0)).build(),
    t('armBData').inputs(one(bData)).outputs(andPlaces(hasdata, ready1)).build(),
    t('armBEmpty').inputs(one(bEmpty)).outputs(outPlace(ready1)).build(),
    t('mergeStart').inputs(one(ready0), one(ready1), all(hasdata)).outputs(outPlace(done)).build(),
    t('mergeSkip').inputs(one(ready0), one(ready1)).inhibitors(hasdata).outputs(outPlace(skipped)).build(),
  ).build();
  const m0 = MarkingState.builder().tokens(start, 1).build();
  return { net, m0, done, skipped, hasdata, ready0, ready1 };
}

/**
 * The brief's queue-and-bundle: a producer fires up to `n` times into `q` until the
 * signal arrives, and the bundler takes `all(q)` with the signal (`bundleEmpty` takes
 * the signal alone when the queue is empty). Cancellable: the signal may never come.
 */
function queueAndBundle(n: number, cancellable = false) {
  const budget = place('budget'), q = place('q'), src = place('src'), s = place('s');
  const out = place('out'), cancelled = place('cancelled');
  const t = (name: string) => Transition.builder(name).action(produces());
  const transitions = [
    t('produce').inputs(one(budget)).inhibitors(s, out).outputs(outPlace(q)).build(),
    t('signal').inputs(one(src)).outputs(outPlace(s)).build(),
    t('bundle').inputs(all(q), one(s)).outputs(outPlace(out)).build(),
    t('bundleEmpty').inputs(one(s)).inhibitors(q).outputs(outPlace(out)).build(),
  ];
  if (cancellable) transitions.push(t('cancel').inputs(one(src)).outputs(outPlace(cancelled)).build());
  const net = PetriNet.builder(`queue${n}`).transitions(...transitions).build();
  const m0 = MarkingState.builder().tokens(budget, n).tokens(src, 1).build();
  return { net, m0, q, out, budget, cancelled };
}

function inequality(flat: ReturnType<typeof flatten>, terms: Record<string, number>, constant: number): MarkingInequality {
  const weights = flat.places.map((p) => BigInt(terms[p.name] ?? 0));
  return { weights, constant: BigInt(constant), origin: 'inductive' };
}

function markingOf(flat: ReturnType<typeof flatten>, tokens: Record<string, number>): number[] {
  return flat.places.map((p) => tokens[p.name] ?? 0);
}

describe('state-equation phase (VER-018) — building blocks', () => {
  it('bounds a consume-all place from above and gives an exact place an equation (VER-016 relaxation)', () => {
    const { net, m0 } = queueAndBundle(3);
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (n: string) => flat.placeIndex.get(n)!;
    const rows = stateEquationConditions(flat, m0, flat.transitions.map((_, k) => `n${k}`), flat.places.map((_, i) => `m${i}`));
    expect(rows).toHaveLength(flat.places.length);
    expect(rows.find((r) => r.includes(` m${idx('q')} `))).toMatch(/^\(<= m\d+ \(\+ 0 /);
    expect(rows.find((r) => r.includes(` m${idx('budget')} `))).toMatch(/^\(= m\d+ \(\+ 3 /);
  });

  it('accepts the join inequality as inductive under the exact step relation, and rejects a weaker cousin', () => {
    const { net, m0 } = joinWithSkip();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const initial = vectorize(m0, flat);
    expect(checkInductiveExact(flat, initial, inequality(flat, { hasdata: 1, ready0: -1, ready1: -1 }, 0))).toBe(true);
    // Arm B raises hasdata without ready0.
    expect(checkInductiveExact(flat, initial, inequality(flat, { hasdata: 1, ready0: -1 }, 0))).toBe(false);
  });

  it('finds an initially marked trap the candidate empties, counting a consume-all arc as a removal', () => {
    const a = place('a'), b = place('b'), c = place('c');
    const t = (name: string) => Transition.builder(name).action(produces());
    // {a, b} is a trap: ab moves a token a -> b, ba moves it back.
    const loop = PetriNet.builder('loop').transitions(
      t('ab').inputs(one(a)).outputs(outPlace(b)).build(),
      t('ba').inputs(one(b)).outputs(outPlace(a)).build(),
    ).build();
    const flat = flatten(loop, new Set(), alwaysAvailable());
    const trap = refutingTrap(flat, markingOf(flat, { a: 1 }), markingOf(flat, {}));
    expect(trap).not.toBeNull();
    expect(formatInequality(flat, trap!)).toBe('a + b >= 1');
    // drain: all(b) -> c empties b without feeding {a, b}: no longer a trap.
    const drained = PetriNet.builder('drained').transitions(
      t('ab').inputs(one(a)).outputs(outPlace(b)).build(),
      t('ba').inputs(one(b)).outputs(outPlace(a)).build(),
      t('drain').inputs(all(b)).outputs(outPlace(c)).build(),
    ).build();
    const flat2 = flatten(drained, new Set(), alwaysAvailable());
    expect(refutingTrap(flat2, markingOf(flat2, { a: 1 }), markingOf(flat2, { c: 1 }))).toBeNull();
  });

  it('searches runs within the firing counts and finds the violation they reach', () => {
    const { net, m0, out, budget, cancelled } = queueAndBundle(2, true);
    const flat = flatten(net, new Set(), alwaysAvailable());
    const bad = violationPredicate(flat, deadlockFree(), new Set<Place<any>>([out, budget, cancelled]));
    const counts = (produce: number) =>
      flat.transitions.map((ft) => (ft.name === 'produce' ? produce : ft.name === 'cancel' ? 1 : 0));
    // Both units produced and the signal cancelled: nothing is enabled and q strands.
    const found = searchWithinCounts(flat, vectorize(m0, flat), counts(2), bad);
    expect(found.kind).toBe('found');
    if (found.kind === 'found') expect(found.steps).toEqual(['produce', 'produce', 'cancel']);
    // One unit leaves the producer enabled, so no run within these counts is quiescent.
    expect(searchWithinCounts(flat, vectorize(m0, flat), counts(1), bad).kind).toBe('none');
  });

  /**
   * The guard split. `gatedStrand` strands `q` behind a gate that never opens. The net is
   * the same either way; only whether `sig` is declared an environment place differs, so
   * the two searches differ in injection and in nothing else.
   *
   * `found` must survive injection: the run fires only counted transitions, and `gate`
   * stays disabled under relax-env enablement because `gateOpen` is not injectable, so
   * the marking really is stuck against any environment. `none` must not survive it.
   */
  function gatedStrand(injectable: boolean) {
    const start = place('start'), q = place('q'), gateOpen = place('gateOpen'), done = place('done');
    const sig = environmentPlace<unknown>('sig');
    const t = (name: string) => Transition.builder(name).action(produces());
    const net = PetriNet.builder('gated').transitions(
      t('fill').inputs(one(start)).outputs(outPlace(q)).build(),
      t('gate').inputs(one(sig.place), one(gateOpen)).outputs(outPlace(done)).build(),
    ).build();
    const m0 = MarkingState.builder().tokens(start, 1).build();
    const flat = flatten(net, injectable ? new Set([sig]) : new Set(), alwaysAvailable());
    return {
      flat,
      initial: vectorize(m0, flat),
      bad: violationPredicate(flat, deadlockFree(), new Set<Place<any>>([done])),
      counts: (fill: number) => flat.transitions.map((ft) => (ft.name === 'fill' ? fill : 0)),
    };
  }

  it('searches a net the environment can inject into, and reports a witness it reaches', () => {
    const env = gatedStrand(true);
    expect(env.flat.environmentInjection.size).toBe(1);
    // Before the guard split this was `exhausted` at once, so the leg never ran at all.
    const found = searchWithinCounts(env.flat, env.initial, env.counts(1), env.bad);
    expect(found.kind).toBe('found');
    if (found.kind === 'found') expect(found.steps).toEqual(['fill']);
  });

  it('downgrades a completed search to exhausted under injection, where it would answer none', () => {
    // Counts that permit no firing: the initial marking is not quiescent, so nothing is bad
    // and the search completes having explored every run it is allowed.
    const plain = gatedStrand(false);
    expect(plain.flat.environmentInjection.size).toBe(0);
    expect(searchWithinCounts(plain.flat, plain.initial, plain.counts(0), plain.bad).kind).toBe('none');

    const env = gatedStrand(true);
    const outcome = searchWithinCounts(env.flat, env.initial, env.counts(0), env.bad);
    expect(outcome.kind).toBe('exhausted');
    // The search ran before reporting, rather than refusing at the door.
    if (outcome.kind === 'exhausted') {
      expect(outcome.reason).toContain('environment injection');
      expect(outcome.nodes).toBeGreaterThan(0);
    }
  });

  it('encodes the query with the refinements and reads a candidate back', () => {
    const { net, m0, done, skipped } = joinWithSkip();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const refinement = inequality(flat, { hasdata: 1, ready0: -1, ready1: -1 }, 0);
    const script = encodeStateEquationQuery(flat, m0, deadlockFree(), new Set([done, skipped]), [], [refinement]);
    expect(script).toContain('(set-logic QF_LIA)');
    expect(script).toContain(`(declare-const n${flat.transitions.length - 1} Int)`);
    const h = flat.placeIndex.get('hasdata')!, r0 = flat.placeIndex.get('ready0')!, r1 = flat.placeIndex.get('ready1')!;
    expect(script).toContain(`(assert (<= (+ m${h} (- m${r0}) (- m${r1})) 0))`);
    const candidate = decodeCandidate(`sat\n(\n  (define-fun m${h} () Int\n    1)\n  (define-fun n0 () Int\n    1)\n)`, flat.places.length, flat.transitions.length);
    expect(candidate!.marking[h]).toBe(1);
    expect(candidate!.counts[0]).toBe(1);
    expect(holdsAt(refinement, candidate!.marking)).toBe(false);
    expect(formatInequality(flat, refinement)).toBe('hasdata <= ready0 + ready1');
    const certificate = refinementCertificate(flat.places.length, flat.transitions.length, [refinement]);
    expect(certificate).toContain(`(x!${flat.places.length + flat.transitions.length - 1} Int)`);
    expect(certificate).toContain(`(<= (+ x!${h} (- x!${r0}) (- x!${r1})) 0)`);
  });
});

describe('firing bound (VER-019) — building blocks', () => {
  it('re-checks a ranking exactly and rejects one some firing does not lower', () => {
    const { net, m0 } = queueAndBundle(3);
    const flat = flatten(net, new Set(), alwaysAvailable());
    const initial = vectorize(m0, flat);
    const weights = (w: Record<string, number>) => flat.places.map((p) => BigInt(w[p.name] ?? 0));
    const bound = checkRankingExact(flat, initial, weights({ budget: 1, src: 2, s: 1 }));
    expect(bound?.bound).toBe(5n);
    // Without a weight on s, bundleEmpty (s -> out) lowers nothing.
    expect(checkRankingExact(flat, initial, weights({ budget: 1, src: 2 }))).toBeNull();
  });

  it('encodes a bounded run with one selector per step and replays only a real firing sequence', () => {
    const { net, m0, out, budget, cancelled } = queueAndBundle(1, true);
    const flat = flatten(net, new Set(), alwaysAvailable());
    const script = encodeBoundedRun(flat, vectorize(m0, flat), deadlockFree(), new Set([out, budget, cancelled]), [], 2);
    expect(script).toContain('(declare-const s1 Int)');
    expect(script).toContain(`(assert (=> (= s0 ${flat.transitions.length}) (= s1 ${flat.transitions.length})))`);
    const bad = violationPredicate(flat, deadlockFree(), new Set<Place<any>>([out, budget, cancelled]));
    const t = (name: string) => flat.transitions.findIndex((ft) => ft.name === name);
    expect(replayRun(flat, vectorize(m0, flat), [t('produce'), t('cancel')], bad)?.steps).toEqual(['produce', 'cancel']);
    expect(replayRun(flat, vectorize(m0, flat), [t('bundle')], bad)).toBeNull();
    expect(decodeBoundedRun(`sat\n(\n  (define-fun s0 () Int\n    ${t('produce')})\n  (define-fun s1 () Int\n    ${flat.transitions.length})\n)`, flat.transitions.length, 2)).toEqual([t('produce')]);
  });
});

describeZ3('state-equation phase (VER-018) — end to end', () => {
  it('proves the join with the inequality the inhibitor makes inductive, certified', async () => {
    const { net, m0, done, skipped } = joinWithSkip();
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(done, skipped).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('state-equation');
    expect(result.report).toContain('Refinement (inductive): hasdata <= ready0 + ready1');
    expect(result.report).toContain('Certificate check: PASSED (init, consecution, safety)');
    expect(result.discoveredInvariants).toEqual(['hasdata <= ready0 + ready1']);
  });

  it('keeps the verdict the fixpoint query reaches when both phases are off', async () => {
    const { net, m0, done, skipped } = joinWithSkip();
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(done, skipped)
      .stateEquationPhase(false).firingBound(false).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('IC3/PDR');
    expect(result.report).not.toContain('VER-018');
  });

  it('queue and bundle: the queue is empty at every quiescence once the signal came (proven, certified)', async () => {
    const { net, m0, out, budget } = queueAndBundle(3);
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(out, budget).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('state-equation');
    expect(result.report).toContain('Refinement (relative): 3*out + q <= 3');
    expect(result.report).toContain('Certificate check: PASSED (init, consecution, safety)');
  });

  it('queue and bundle: the queue strands when the signal never comes (violated, with the run)', async () => {
    const { net, m0, out, budget, cancelled, q } = queueAndBundle(3, true);
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(out, budget, cancelled).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTransitions.at(-1)).toBe('cancel');
    expect(result.counterexampleTrace.at(-1)!.tokens(q)).toBeGreaterThan(0);
  });

  it('dumps each of its queries under its own phase name (VER-013)', async () => {
    const dump = mkdtempSync(join(tmpdir(), 'libpetri-state-equation-'));
    process.env['LIBPETRI_SMT_DUMP'] = dump;
    try {
      const { net, m0, done, skipped } = joinWithSkip();
      const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
        .property(deadlockFree()).sinkPlaces(done, skipped).timeout(30_000).verify();
      expect(result.verdict.type, result.report).toBe('proven');
      // The candidate, the inequality excluding it, the unsat, and the certificate check.
      expect(readdirSync(dump).filter((n) => n.endsWith('.smt2')).sort()).toEqual([
        '001-state-equation.smt2', '002-invariant.smt2', '003-state-equation.smt2', '004-certificate.smt2',
      ]);
    } finally {
      delete process.env['LIBPETRI_SMT_DUMP'];
      rmSync(dump, { recursive: true, force: true });
    }
  });

  it('reports the first query through encodeScripts(), and none when the phase is off', () => {
    const { net, m0, done, skipped } = joinWithSkip();
    const on = SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).sinkPlaces(done, skipped).encodeScripts();
    expect(on.stateEquation).toContain('; State-equation phase (VER-018)');
    const off = SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).sinkPlaces(done, skipped)
      .stateEquationPhase(false).encodeScripts();
    expect(off.stateEquation).toBeNull();
  });
});

describeZ3('firing bound (VER-019) — end to end', () => {
  it('proves the queue by a bounded model check to its firing bound', async () => {
    const { net, m0, out, budget } = queueAndBundle(3);
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(out, budget).stateEquationPhase(false).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('bounded-model-check');
    expect(result.report).toContain('Bound: 5 firings');
    expect(result.report).toContain('Certificate check: not applicable (bounded model check to the firing bound)');
  });

  it('finds the cancelled queue by a bounded run and replays it', async () => {
    const { net, m0, out, budget, cancelled } = queueAndBundle(3, true);
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(out, budget, cancelled).stateEquationPhase(false).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.report).toContain('Status: a bounded run reaches a violation (replayed)');
  });

  it('names the transitions an unbounded net repeats and leaves it to the fixpoint query', async () => {
    const p0 = place('p0'), p1 = place('p1'), p2 = place('p2');
    const t = (name: string) => Transition.builder(name).action(produces());
    const net = PetriNet.builder('ring').transitions(
      t('t0').inputs(one(p0)).outputs(outPlace(p1)).build(),
      t('t1').inputs(one(p1)).outputs(outPlace(p2)).build(),
      t('t2').inputs(one(p2)).outputs(outPlace(p0)).build(),
    ).build();
    const result = await SmtVerifier.forNet(net).enumerationMaxClasses(0)
      .initialMarking(MarkingState.builder().tokens(p0, 1).build())
      .property(placeBound(p0, 1)).linearBound(false).stateEquationPhase(false).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.report).toContain('no firing bound — the marking equation lets t0, t1, t2 repeat; not attempted');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('IC3/PDR');
  });
});
