import { describe, it, expect, vi } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { StateSpaceCache } from '../../src/verification/state-space-cache.js';
import { stateSpaceBuildCount, buildStateSpace, decideOverStateSpace } from '../../src/verification/scg-verifier.js';
import { deadlockFree, placeBound, unreachable } from '../../src/verification/smt-property.js';
import type { SmtProperty } from '../../src/verification/smt-property.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * [VER-017] "Reusing the state space across queries": an explicit `StateSpaceCache` builds the
 * state-class graph once per net and initial marking, and changes no verdict, witness or route.
 */

/** A pipeline `p0 -> t0 -> … -> pn`: `n + 1` classes from one token in `p0`. */
function pipeline(n: number) {
  const places: Place<any>[] = [place('p0')];
  const transitions = [];
  for (let i = 0; i < n; i++) {
    const next = place(`p${i + 1}`);
    places.push(next);
    transitions.push(Transition.builder(`t${i}`).inputs(one(places[i]!)).outputs(outPlace(next))
      .action(produces()).build());
  }
  const net = PetriNet.builder(`pipeline${n}`).transitions(...transitions).build();
  return { net, places, m0: MarkingState.builder().tokens(places[0]!, 1).build() };
}

/** Runs `fn` and counts the graphs it built, via the route's internal build hook. */
async function builds<T>(fn: () => Promise<T>): Promise<[T, number]> {
  const before = stateSpaceBuildCount();
  const value = await fn();
  return [value, stateSpaceBuildCount() - before];
}

/** What must be identical with and without the cache. */
function observable(r: SmtVerificationResult) {
  return {
    verdict: r.verdict,
    route: r.route,
    trace: r.counterexampleTrace.map(m => m.toString()),
    transitions: [...r.counterexampleTransitions],
    confirmed: r.counterexampleConfirmed,
  };
}

const REUSED = 'Bounded state-space enumeration: reused cached state space';
const CACHED_TRUNCATION = 'Bounded state-space enumeration: cached truncation at';

describe('VER-017 AC7 — a state-space cache builds once and changes no answer', () => {
  const { net, places, m0 } = pipeline(6);
  const sink = places[6]!;
  const queries: [string, (v: SmtVerifier) => SmtVerifier][] = [
    ['deadlock-free with sink (proven)', v => v.property(deadlockFree()).sinkPlaces(sink)],
    ['deadlock-free without sink (violated)', v => v.property(deadlockFree())],
    ['place bound (proven)', v => v.property(placeBound(sink, 1))],
    ['unreachable (proven)', v => v.property(unreachable(new Set([places[0]!, sink])))],
    ['place bound 0 on the sink (violated)', v => v.property(placeBound(sink, 0))],
  ];

  it('the second and later queries build no graph and answer exactly as without the cache', async () => {
    const cache = new StateSpaceCache();
    const [cached, built] = await builds(async () => {
      const out: SmtVerificationResult[] = [];
      for (const [, q] of queries) {
        out.push(await q(SmtVerifier.forNet(net).initialMarking(m0).stateSpaceCache(cache)).verify());
      }
      return out;
    });
    expect(built).toBe(1);

    const uncached: SmtVerificationResult[] = [];
    for (const [, q] of queries) uncached.push(await q(SmtVerifier.forNet(net).initialMarking(m0)).verify());

    for (let i = 0; i < queries.length; i++) {
      expect(observable(cached[i]!), queries[i]![0]).toEqual(observable(uncached[i]!));
      expect(cached[i]!.route).toBe('enumeration');
      expect(uncached[i]!.report).not.toContain(REUSED);
    }
    // The violated witnesses really are the shortest firing sequence.
    expect(cached[1]!.verdict.type).toBe('violated');
    expect(cached[1]!.counterexampleTransitions).toEqual(['t0', 't1', 't2', 't3', 't4', 't5']);
    expect(cached[4]!.verdict.type).toBe('violated');

    // The first query built; every later one says it reused the cached graph.
    expect(cached[0]!.report).not.toContain(REUSED);
    for (const r of cached.slice(1)) {
      expect(r.report).toContain(
        'Bounded state-space enumeration: reused cached state space (7 classes) (VER-017).',
      );
      // The existing lines stay.
      expect(r.report).toContain('=== Bounded state-space enumeration (VER-017) ===');
      expect(r.report).toContain('  State classes: 7');
    }
  });

  it('without a cache every query builds', async () => {
    const [, built] = await builds(async () => {
      for (const [, q] of queries) await q(SmtVerifier.forNet(net).initialMarking(m0)).verify();
    });
    expect(built).toBe(queries.length);
  });

  it('clear() drops the cached graph', async () => {
    const cache = new StateSpaceCache();
    const q = () => SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).sinkPlaces(sink)
      .stateSpaceCache(cache).verify();
    const [, built] = await builds(async () => {
      await q();
      await q();
      cache.clear();
      await q();
    });
    expect(built).toBe(2);
  });
});

describeZ3('VER-017 AC8 — a cached truncation declines without building, a larger budget replaces it', () => {
  const { net, places, m0 } = pipeline(6); // 7 classes
  const sink = places[6]!;
  const q = (cache: StateSpaceCache, budget: number) =>
    SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).sinkPlaces(sink)
      .enumerationMaxClasses(budget).stateSpaceCache(cache).timeout(30_000).verify();

  it('budget <= B declines at once; budget > B builds and replaces the entry', async () => {
    const cache = new StateSpaceCache();

    const [first, b1] = await builds(() => q(cache, 4));
    expect(b1).toBe(1);
    expect(first.report).toContain('Bounded state-space enumeration truncated at 4 classes');
    expect(first.report).not.toContain(CACHED_TRUNCATION);
    expect(first.route).not.toBe('enumeration');

    for (const budget of [4, 3, 1]) {
      const [r, b] = await builds(() => q(cache, budget));
      expect(b, `budget ${budget}`).toBe(0);
      expect(r.report).toContain(
        `Bounded state-space enumeration: cached truncation at ${budget} classes (VER-017); ` +
        'verifying via the SMT pipeline.',
      );
      // The existing truncation line stays.
      expect(r.report).toContain(`Bounded state-space enumeration truncated at ${budget} classes`);
      expect(r.report).toContain('Phase 1: Flattening net...');
      expect(r.verdict.type).toBe(first.verdict.type);
    }

    // A larger budget that still truncates builds and replaces: 5 is then the remembered bound.
    const [r5, b5] = await builds(() => q(cache, 5));
    expect(b5).toBe(1);
    expect(r5.report).toContain('Bounded state-space enumeration truncated at 5 classes');
    const [r5again, b5again] = await builds(() => q(cache, 5));
    expect(b5again).toBe(0);
    expect(r5again.report).toContain('cached truncation at 5 classes');

    // A budget large enough to close builds once more; the closed graph then serves.
    const [closed, bc] = await builds(() => q(cache, 100));
    expect(bc).toBe(1);
    expect(closed.route).toBe('enumeration');
    const [reused, br] = await builds(() => q(cache, 8));
    expect(br).toBe(0);
    expect(reused.report).toContain('reused cached state space (7 classes)');
  });

  it('a closed graph of C classes is answered as truncated for a budget <= C, without building', async () => {
    const cache = new StateSpaceCache();
    await q(cache, 100);
    for (const budget of [7, 3]) {
      const [r, b] = await builds(() => q(cache, budget));
      expect(b).toBe(0);
      expect(r.route).not.toBe('enumeration');
      expect(r.report).toContain(`cached truncation at ${budget} classes`);
      // The same route as a cold query at that budget.
      const cold = await q(new StateSpaceCache(), budget);
      expect(r.route).toBe(cold.route);
      expect(r.verdict).toEqual(cold.verdict);
    }
  });
});

describe('VER-017 AC9 — a different initial marking or net never hits another entry', () => {
  it('a different initial marking misses, and gets its own answer', async () => {
    const { net, places, m0 } = pipeline(6);
    const cache = new StateSpaceCache();
    const other = MarkingState.builder().tokens(places[3]!, 1).build(); // 4 classes
    const q = (m: MarkingState) => SmtVerifier.forNet(net).initialMarking(m)
      .property(deadlockFree()).stateSpaceCache(cache).verify();

    const [a, ba] = await builds(() => q(m0));
    const [b, bb] = await builds(() => q(other));
    expect(ba).toBe(1);
    expect(bb).toBe(1);
    expect(b.report).not.toContain(REUSED);
    expect(b.report).toContain('  State classes: 4');
    expect(b.counterexampleTransitions).toEqual(['t3', 't4', 't5']);
    expect(a.counterexampleTransitions).toEqual(['t0', 't1', 't2', 't3', 't4', 't5']);

    // Each marking then hits its own entry.
    const [again, bg] = await builds(() => q(MarkingState.builder().tokens(places[3]!, 1).build()));
    expect(bg).toBe(0);
    expect(again.report).toContain('reused cached state space (4 classes)');
  });

  it('a different net instance misses, even when structurally identical', async () => {
    const cache = new StateSpaceCache();
    const first = pipeline(6);
    const second = pipeline(6);
    const q = (p: ReturnType<typeof pipeline>) => SmtVerifier.forNet(p.net).initialMarking(p.m0)
      .property(deadlockFree()).stateSpaceCache(cache).verify();
    const [, b1] = await builds(() => q(first));
    const [r2, b2] = await builds(() => q(second));
    expect(b1).toBe(1);
    expect(b2).toBe(1);
    expect(r2.report).not.toContain(REUSED);
  });

  it('a structurally different net misses', async () => {
    const cache = new StateSpaceCache();
    const short = pipeline(3);
    const long = pipeline(6);
    await SmtVerifier.forNet(short.net).initialMarking(short.m0).property(deadlockFree()).stateSpaceCache(cache).verify();
    const [r, b] = await builds(() => SmtVerifier.forNet(long.net).initialMarking(long.m0)
      .property(deadlockFree()).stateSpaceCache(cache).verify());
    expect(b).toBe(1);
    expect(r.report).toContain('  State classes: 7');
  });
});

describe('VER-017 AC10 — concurrent queries sharing a cache build once', () => {
  it('Promise.all of verifies through one cache builds the graph once', async () => {
    const { net, places, m0 } = pipeline(6);
    const cache = new StateSpaceCache();
    const props: [SmtProperty, Place<any>[]][] = [
      [deadlockFree(), [places[6]!]],
      [deadlockFree(), []],
      [placeBound(places[6]!, 1), []],
      [unreachable(new Set([places[0]!, places[6]!])), []],
    ];
    const [results, built] = await builds(() => Promise.all(props.map(([p, sinks]) =>
      SmtVerifier.forNet(net).initialMarking(m0).property(p).sinkPlaces(...sinks)
        .stateSpaceCache(cache).verify())));
    expect(built).toBe(1);
    expect(results.map(r => r.verdict.type)).toEqual(['proven', 'violated', 'proven', 'proven']);
    expect(results.every(r => r.route === 'enumeration')).toBe(true);
  });
});

describe('VER-017 — a net with terminals hits the cache across queries', () => {
  const START = place<string>('start');
  const FAST = place<string>('fast');
  const SLOW = place<string>('slow');
  const DONE = place<string>('done');
  const LATE = place<string>('late');

  function forkNet(): PetriNet {
    const fork = Transition.builder('fork').inputs(one(START))
      .outputs(and(outPlace(FAST), outPlace(SLOW))).action(produces()).build();
    const finish = Transition.builder('finish').inputs(one(FAST)).outputs(outPlace(DONE)).action(produces()).build();
    const slow = Transition.builder('slowArm').inputs(one(SLOW)).outputs(outPlace(LATE)).action(produces()).build();
    return PetriNet.builder('terminalFork').transitions(fork, finish, slow).terminal(DONE).build();
  }

  it('is keyed on the caller net, not the per-verify terminal rewrite', async () => {
    const net = forkNet();
    const cache = new StateSpaceCache();
    const queries: ((v: SmtVerifier) => SmtVerifier)[] = [
      v => v.property(deadlockFree()),
      v => v.property(placeBound(DONE, 1)),
      v => v.property(placeBound(LATE, 0)),
    ];
    const [cached, built] = await builds(async () => {
      const out: SmtVerificationResult[] = [];
      for (const q of queries) {
        out.push(await q(SmtVerifier.forNet(net).initialMarking(m => m.tokens(START, 1)).stateSpaceCache(cache)).verify());
      }
      return out;
    });
    expect(built).toBe(1);
    for (const r of cached.slice(1)) expect(r.report).toContain(REUSED);

    for (let i = 0; i < queries.length; i++) {
      const plain = await queries[i]!(SmtVerifier.forNet(net).initialMarking(m => m.tokens(START, 1))).verify();
      expect(observable(cached[i]!)).toEqual(observable(plain));
      expect(cached[i]!.route).toBe('enumeration');
    }
    expect(cached[0]!.verdict.type).toBe('proven');
    expect(cached[2]!.verdict.type).toBe('violated');
  });
});

describe('VER-017 — a witness from a cached graph starts at the caller\'s own initial marking', () => {
  it('the first trace marking is the caller\'s marking, as on a cold query', async () => {
    const A = place('a');
    const B = place('b');
    const C = place('c');
    const join = Transition.builder('join').inputs(one(A), one(B)).outputs(outPlace(C)).action(produces()).build();
    const net = PetriNet.builder('join').transitions(join).build();
    // Two equal markings, listed alike from the same places: one cache entry, two objects.
    const ab = MarkingState.builder().tokens(A, 1).tokens(B, 1).build();
    const ba = MarkingState.builder().tokens(A, 1).tokens(B, 1).build();
    const cache = new StateSpaceCache();
    const q = (m: MarkingState, c: StateSpaceCache | null) => {
      const v = SmtVerifier.forNet(net).initialMarking(m).property(deadlockFree());
      return (c === null ? v : v.stateSpaceCache(c)).verify();
    };

    await q(ab, cache);
    const [hit, built] = await builds(() => q(ba, cache));
    expect(built).toBe(0);
    expect(hit.report).toContain(REUSED);
    const cold = await q(ba, null);
    expect(hit.verdict.type).toBe('violated');
    expect(hit.counterexampleTrace[0]).toBe(ba);
    expect(hit.counterexampleTrace[0]!.placesWithTokens().map(p => p.name))
      .toEqual(cold.counterexampleTrace[0]!.placesWithTokens().map(p => p.name));
    expect(observable(hit)).toEqual(observable(cold));
  });
});

describe('VER-017 — a build that throws leaves no entry behind', () => {
  it('the next query builds afresh and answers as a cold one', async () => {
    const { net, places, m0 } = pipeline(6);
    const cache = new StateSpaceCache();
    const q = () => SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).sinkPlaces(places[6]!)
      .stateSpaceCache(cache).verify();
    const spy = vi.spyOn(StateClassGraph, 'build').mockImplementationOnce(() => {
      throw new Error('boom');
    });
    try {
      await expect(q()).rejects.toThrow('boom');
    } finally {
      spy.mockRestore();
    }
    const [r, b] = await builds(q);
    expect(b).toBe(1);
    expect(r.report).not.toContain(REUSED);
    expect(r.report).not.toContain(CACHED_TRUNCATION);
    expect(r.route).toBe('enumeration');
    expect(r.verdict.type).toBe('proven');
  });
});

describe('VER-017 — the whole witness is identical with and without the cache', () => {
  it('a differently-listed equal marking misses, so every trace marking lists as on a cold query', async () => {
    const X = place('x');
    const Y = place('y');
    const A = place('a');
    const B = place('b');
    const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B)).action(produces()).build();
    const net = PetriNet.builder('listing').transitions(t).build();
    const xya = MarkingState.builder().tokens(X, 1).tokens(Y, 1).tokens(A, 1).build();
    // Same counts, different listing, and the caller's own Place objects for x and y.
    const X2 = place('x');
    const Y2 = place('y');
    const yxa = MarkingState.builder().tokens(Y2, 1).tokens(X2, 1).tokens(A, 1).build();
    const cache = new StateSpaceCache();
    const q = (m: MarkingState, c: StateSpaceCache | null) => {
      const v = SmtVerifier.forNet(net).initialMarking(m).property(placeBound(B, 0));
      return (c === null ? v : v.stateSpaceCache(c)).verify();
    };
    await q(xya, cache);
    const hit = await q(yxa, cache);
    const cold = await q(yxa, null);
    expect(hit.verdict.type).toBe('violated');
    const listing = (r: SmtVerificationResult) => r.counterexampleTrace.map(m => m.placesWithTokens());
    expect(listing(hit).map(ps => ps.map(p => p.name))).toEqual(listing(cold).map(ps => ps.map(p => p.name)));
    expect(listing(hit).length).toBe(2);
    for (let i = 0; i < listing(hit).length; i++) {
      listing(hit)[i]!.forEach((p, j) => expect(p, `trace[${i}] place ${j}`).toBe(listing(cold)[i]![j]));
    }
    // And a second query listed the same way hits.
    const [again, b] = await builds(() => q(MarkingState.builder().tokens(Y2, 1).tokens(X2, 1).tokens(A, 1).build(), cache));
    expect(b).toBe(0);
    expect(again.report).toContain(REUSED);
    expect(listing(again).map(ps => ps.map(p => p.name))).toEqual(listing(cold).map(ps => ps.map(p => p.name)));
  });
});

describe('VER-017 — decideOverStateSpace refuses a truncated graph', () => {
  it('returns truncated instead of a verdict read off a partial graph', () => {
    const { net, m0 } = pipeline(6);
    const partial = buildStateSpace(net, m0, 3);
    expect(partial.isComplete()).toBe(false);
    // Without the guard the partial graph has a quiescent-looking frontier: a false `violated`.
    expect(decideOverStateSpace(partial, deadlockFree(), new Set()).kind).toBe('truncated');
  });
});

describe('VER-017 — StateSpaceCache exposes only clear()', () => {
  it('has no public resolve', () => {
    expect(Object.getOwnPropertyNames(StateSpaceCache.prototype).sort()).toEqual(['clear', 'constructor']);
  });
});
