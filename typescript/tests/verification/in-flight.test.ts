import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition, type TransitionBuilder } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { all, atLeast, one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { tokenOf, type Token } from '../../src/core/token.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { mutualExclusion, placeBound, unreachable, type SmtProperty } from '../../src/verification/smt-property.js';
import { OpenNetContract, verifyOpenNet } from '../../src/verification/open-net/index.js';
import { inFlightTransitions, splitInFlight } from '../../src/verification/in-flight.js';
import { TimePetriNetAnalyzer } from '../../src/verification/analysis/time-petri-net-analyzer.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * In-flight actions and the atomic-firing premise of verification ([VER-004], [EXEC-001],
 * [EXEC-003]).
 *
 * The executor consumes a firing's inputs when the action starts and deposits its outputs when
 * the action completes, and other transitions fire in between. For monotone arcs that
 * interleaving is one of the atomic model's own runs. It is not when another transition tests
 * one of the in-flight transition's places with an inhibitor, reset, `all` or `atLeast` arc.
 * Mirrors `rust/libpetri/tests/inflight_atomicity.rs`.
 */

const p = place<number>('p');
const q = place<number>('q');
const r = place<number>('r');
const go = place<number>('go');

interface Backend {
  readonly name: string;
  make(net: PetriNet, tokens: Map<Place<any>, Token<any>[]>): { run(ms: number): Promise<Marking> };
}

const backends: Backend[] = [
  { name: 'BitmapNetExecutor', make: (net, t) => new BitmapNetExecutor(net, t) },
  { name: 'PrecompiledNetExecutor', make: (net, t) => new PrecompiledNetExecutor(net, t) },
];

/** Forwards a token into `into` after 50 ms. */
const slow = (into: Place<number>): TransitionAction => async ctx => {
  await new Promise(resolve => setTimeout(resolve, 50));
  ctx.output(into, 1);
};

/** Forwards a token into `into` at once. */
const quick = (into: Place<number>): TransitionAction => async ctx => {
  ctx.output(into, 1);
};

/** `t: p + go → p`, priority 1, so it starts before `u`; `u: q + <test of p> → r`. */
function net(name: string, action: TransitionAction, test: (b: TransitionBuilder) => TransitionBuilder): PetriNet {
  const t = Transition.builder('t').priority(1).inputs(one(p), one(go)).outputs(outPlace(p)).action(action).build();
  const u = test(Transition.builder('u').inputs(one(q))).outputs(outPlace(r)).action(quick(r)).build();
  return PetriNet.builder(name).transitions(t, u).build();
}

interface Case {
  readonly name: string;
  readonly build: (action: TransitionAction) => PetriNet;
  readonly p: number;
  readonly property: SmtProperty;
}

const cases: Case[] = [
  { name: 'inhibitor', build: a => net('inflight-inhibitor', a, b => b.inhibitor(p)), p: 1, property: unreachable(new Set([r])) },
  { name: 'reset', build: a => net('inflight-reset', a, b => b.reset(p)), p: 1, property: mutualExclusion(p, r) },
  {
    name: 'all',
    build: a => PetriNet.builder('inflight-all').transitions(
      Transition.builder('t').priority(1).inputs(one(p), one(go)).outputs(outPlace(p)).action(a).build(),
      Transition.builder('u').inputs(all(p), one(q)).outputs(outPlace(r)).action(quick(r)).build(),
    ).build(),
    p: 2,
    property: mutualExclusion(p, r),
  },
  {
    name: 'atLeast',
    build: a => PetriNet.builder('inflight-at-least').transitions(
      Transition.builder('t').priority(1).inputs(one(p), one(go)).outputs(outPlace(p)).action(a).build(),
      Transition.builder('u').inputs(atLeast(2, p), one(q)).outputs(outPlace(r)).action(quick(r)).build(),
    ).build(),
    p: 3,
    property: mutualExclusion(p, r),
  },
];

function tokens(counts: [Place<number>, number][]): Map<Place<any>, Token<any>[]> {
  return new Map(counts.map(([pl, n]) => [pl, Array.from({ length: n }, () => tokenOf(1))]));
}

const count = (m: Marking, pl: Place<any>) => m.peekTokens(pl).length;

describe('the executor fires other transitions while an action is in flight', () => {
  for (const backend of backends) {
    for (const c of cases) {
      it(`${backend.name} ${c.name}: u sees p emptier than any atomic marking`, async () => {
        const m = await backend.make(c.build(slow(p)), tokens([[p, c.p], [q, 1], [go, 1]])).run(2000);
        expect(count(m, r)).toBe(1);
        expect(count(m, p)).toBe(1);
      });
    }

    // TypeScript does not start a transition again while it is in flight, so the one-transition
    // guard holds here (Rust starts it twice); two guarded transitions still both start.
    it(`${backend.name}: the guard holds for one transition, not for two`, async () => {
      const one_ = await backend.make(guardNet(slow(busy)), tokens([[req, 2]])).run(2000);
      expect(count(one_, busy)).toBe(1);
      const two = await backend.make(twoGuardsNet(slow(busy)), tokens([[req, 1], [req2, 1]])).run(2000);
      expect(count(two, busy)).toBe(2);
    });
  }
});

/**
 * TypeScript deposits every output in the completion phase ([EXEC-042] implementation status),
 * so an action that resolves at once still leaves its outputs out of the firing pass: the same
 * interleavings happen without any delay.
 */
describe('an action that resolves at once', () => {
  for (const backend of backends) {
    for (const c of cases) {
      it(`${backend.name} ${c.name}`, async () => {
        const m = await backend.make(c.build(quick(p)), tokens([[p, c.p], [q, 1], [go, 1]])).run(2000);
        expect(count(m, r) > 0 && count(m, p) > 0).toBe(true);
      });
    }
  }
});

const req = place<number>('req');
const req2 = place<number>('req2');
const busy = place<number>('busy');

/** Two guarded starts, `start` and `start2`, sharing `busy`. */
function twoGuardsNet(action: TransitionAction): PetriNet {
  return PetriNet.builder('inflight-two-guards').transitions(
    Transition.builder('start').inputs(one(req)).inhibitor(busy).outputs(outPlace(busy)).action(action).build(),
    Transition.builder('start2').inputs(one(req2)).inhibitor(busy).outputs(outPlace(busy)).action(action).build(),
  ).build();
}

/** `start: req + inhibitor(busy) → busy`, the usual one-at-a-time guard. */
function guardNet(action: TransitionAction): PetriNet {
  return PetriNet.builder('inflight-guard').transitions(
    Transition.builder('start').inputs(one(req)).inhibitor(busy).outputs(outPlace(busy)).action(action).build(),
  ).build();
}

describe('the split', () => {
  it('splits a transition whose output another tests non-monotonically, and nothing else', () => {
    const n = cases[0]!.build(slow(p));
    expect(inFlightTransitions(n)).toEqual(['t']);
    const split = splitInFlight(n);
    expect(split.type).toBe('split');
    if (split.type !== 'split') return;
    expect([...split.net.transitions].map(t => t.name)).toEqual(['t', 'complete:t', 'u']);
    expect([...split.net.places].map(pl => pl.name)).toEqual(['p', 'go', 'q', 'r', 'inflight:t']);
    // Idempotent: the completion step is never split again.
    expect(splitInFlight(split.net).type).toBe('atomic');
    // An environment step stays atomic.
    expect(inFlightTransitions(n, new Set(['t']))).toEqual([]);
  });

  it('splits a producer of a terminal place', () => {
    const a = place('a');
    const done = place<number>('done');
    const n = PetriNet.builder('terminal').transitions(
      Transition.builder('t').inputs(one(a)).outputs(outPlace(done)).action(quick(done)).build(),
    ).terminal(done).build();
    expect(inFlightTransitions(n)).toEqual(['t']);
  });

  it('a verifier reused after an option change scripts what a fresh one does', () => {
    // The rewrites are derived per run from the caller's configuration, so the second call
    // must not reuse the first call's (split or atomic) net.
    const fresh = (atomic: boolean) => SmtVerifier.forNet(guardNet(slow(busy)))
      .initialMarking(m => m.tokens(req, 2))
      .property(placeBound(busy, 1))
      .assumeAtomicFiring(atomic)
      .encodeScripts().horn;
    expect(fresh(false)).not.toBe(fresh(true));
    for (const first of [false, true]) {
      const reused = SmtVerifier.forNet(guardNet(slow(busy)))
        .initialMarking(m => m.tokens(req, 2))
        .property(placeBound(busy, 1))
        .assumeAtomicFiring(first);
      expect(reused.encodeScripts().horn).toBe(fresh(first));
      expect(reused.assumeAtomicFiring(!first).encodeScripts().horn).toBe(fresh(!first));
      // A second run with the same options scripts the same again.
      expect(reused.encodeScripts().horn).toBe(fresh(!first));
    }
  });

  it('a verifier reused after the marking or sinks change sees the new ones', () => {
    const reused = SmtVerifier.forNet(guardNet(slow(busy)))
      .initialMarking(m => m.tokens(req, 2))
      .property(placeBound(busy, 1));
    reused.encodeScripts();
    reused.initialMarking(m => m.tokens(req, 3)).sinkPlaces(busy);
    const fresh = SmtVerifier.forNet(guardNet(slow(busy)))
      .initialMarking(m => m.tokens(req, 3))
      .sinkPlaces(busy)
      .property(placeBound(busy, 1))
      .encodeScripts().horn;
    expect(reused.encodeScripts().horn).toBe(fresh);
  });

  it('the analyzer fires the split transition in two steps', () => {
    const result = TimePetriNetAnalyzer.forNet(guardNet(slow(busy)))
      .initialMarking(MarkingState.builder().tokens(req, 2).build())
      .goalPlaces(busy)
      .build()
      .analyze();
    expect(result.report).toContain('In-flight actions (VER-004): start is verified in two steps');
  });
});

describeZ3('the verifier models the in-flight interleaving (VER-004)', () => {
  const verify = (n: PetriNet, pCount: number, property: SmtProperty, classes: number, atomic = false) =>
    SmtVerifier.forNet(n)
      .initialMarking(m => m.tokens(p, pCount).tokens(q, 1).tokens(go, 1))
      .property(property)
      .enumerationMaxClasses(classes)
      .assumeAtomicFiring(atomic)
      .timeout(30_000)
      .verify();

  for (const c of cases) {
    for (const classes of [50_000, 0]) {
      it(`${c.name} (classes=${classes}): what the executor reaches is not proven away`, async () => {
        const result = await verify(c.build(slow(p)), c.p, c.property, classes);
        expect(result.verdict.type, result.report).toBe('violated');
      });
    }
  }

  it('the guard: two starts, then two completions', async () => {
    const result = await SmtVerifier.forNet(guardNet(slow(busy)))
      .initialMarking(m => m.tokens(req, 2))
      .property(placeBound(busy, 1))
      .timeout(30_000)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTransitions).toEqual(['start', 'start', 'complete:start', 'complete:start']);
    expect(result.report).toContain('In-flight actions (VER-004): start is verified in two steps');
  });

  it('assumeAtomicFiring restores the atomic verdict and says so', async () => {
    for (const classes of [50_000, 0]) {
      const result = await SmtVerifier.forNet(guardNet(slow(busy)))
        .initialMarking(m => m.tokens(req, 2))
        .property(placeBound(busy, 1))
        .enumerationMaxClasses(classes)
        .assumeAtomicFiring(true)
        .timeout(30_000)
        .verify();
      expect(result.verdict.type, result.report).toBe('proven');
      expect(result.report).toContain('ASSUMPTION: every firing is atomic (the assume-atomic-firing option)');
    }
  });

  it('a verifier reused after assumeAtomicFiring changes answers for the new setting', async () => {
    const reused = SmtVerifier.forNet(guardNet(slow(busy)))
      .initialMarking(m => m.tokens(req, 2))
      .property(placeBound(busy, 1))
      .timeout(30_000);
    const atomic = await reused.assumeAtomicFiring(true).verify();
    expect(atomic.verdict.type, atomic.report).toBe('proven');
    const split = await reused.assumeAtomicFiring(false).verify();
    expect(split.verdict.type, split.report).toBe('violated');
    expect(split.report).toContain('In-flight actions (VER-004): start is verified in two steps');
    expect(split.report).not.toContain('ASSUMPTION: every firing is atomic');
    const again = await reused.assumeAtomicFiring(true).verify();
    expect(again.verdict.type, again.report).toBe('proven');
    expect(again.report).toContain('ASSUMPTION: every firing is atomic (the assume-atomic-firing option)');
  });

  it('a net without non-monotone tests of outputs scripts the same either way', () => {
    const a = place('a');
    const b = place<number>('b');
    const n = PetriNet.builder('plain').transitions(
      Transition.builder('t').inputs(one(a)).outputs(outPlace(b)).action(quick(b)).build(),
    ).build();
    const scripts = (atomic: boolean) => SmtVerifier.forNet(n)
      .initialMarking(m => m.tokens(a, 1))
      .property(placeBound(b, 1))
      .assumeAtomicFiring(atomic)
      .encodeScripts().horn;
    expect(scripts(false)).toBe(scripts(true));
  });

  it('a ν-join the split would cut in two is refused', async () => {
    const a = place<string>('a');
    const b = place<string>('b');
    const joined = place<string>('joined');
    const late = place('late');
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, (v: string) => nameId(v)), matchKey(b, (v: string) => nameId(v))))
      .outputs(outPlace(joined))
      .action(async ctx => { ctx.output(joined, ''); })
      .build();
    const watch = Transition.builder('watch').inputs(one(late)).inhibitor(joined).build();
    const n = PetriNet.builder('nu-in-flight').transitions(join, watch).build();
    const result = await SmtVerifier.forNet(n)
      .initialMarking(m => m.tokens(late, 1))
      .property(placeBound(joined, 1))
      .verify();
    expect(result.verdict.type, result.report).toBe('unknown');
    if (result.verdict.type === 'unknown') {
      expect(result.verdict.reason).toContain("transition 'join'");
      expect(result.verdict.reason).toContain('ν-join');
    }
  });

  it('the open-net verifier splits too, on both routes', async () => {
    const contract = OpenNetContract.builder()
      .initialMarking(m => m.tokens(req, 2))
      .expect('busy', 1, busy)
      .rest(req)
      .build();
    for (const maxClasses of [50_000, 0]) {
      const split = await verifyOpenNet(guardNet(slow(busy)), contract, { maxClasses });
      expect(split.verdict.type, split.report).toBe('violated');
      expect(split.report).toContain('In-flight actions (VER-004): start is verified in two steps');
      const atomic = await verifyOpenNet(guardNet(slow(busy)), contract, { maxClasses, assumeAtomicFiring: true });
      expect(atomic.verdict.type, atomic.report).toBe('proven');
      expect(atomic.report).toContain('ASSUMPTION: every firing is atomic');
    }
  });
});
