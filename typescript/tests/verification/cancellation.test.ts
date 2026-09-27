import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { StateSpaceCache } from '../../src/verification/state-space-cache.js';
import { stateSpaceBuildCount } from '../../src/verification/scg-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { verifyOpenNet } from '../../src/verification/open-net/verify-open-net.js';
import { OpenNetContract } from '../../src/verification/open-net/contract.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';
import { FIG_11B_ROWS, pnidNet } from '../fixtures/pnid-nets.js';

/**
 * [VER-013] cancellation: `SmtVerifier.signal(AbortSignal)` rides the total budget's stop — every
 * deadline poll sees it — and the verdict is `unknown` with `verification cancelled during <phase>`.
 * The z3-process half (a running solver killed at once) is in `stub-z3.test.ts`.
 */

/** `k` independent one-shot transitions: 2^k reachable markings, an untimed net. */
function toggles(k: number) {
  const b = PetriNet.builder(`toggles-${k}`);
  const a = Array.from({ length: k }, (_, i) => place(`a${i}`));
  for (let i = 0; i < k; i++) {
    b.transition(Transition.builder(`t${i}`).inputs(one(a[i]!)).outputs(outPlace(place(`b${i}`))).action(produces()).build());
  }
  const net = b.build();
  return { net, verifier: () => SmtVerifier.forNet(net).initialMarking(m => { for (const p of a) m.tokens(p, 1); }).property(placeBound(a[0]!, 1)) };
}

/**
 * A signal that reports itself aborted once `afterMs` have passed. An `AbortController` cannot
 * fire during a synchronous graph build on the same thread (its abort runs on the event loop),
 * so this stands in for a cancellation arriving mid-build — what the deadline polls must see.
 */
function abortsAfter(afterMs: number): AbortSignal {
  const at = performance.now() + afterMs;
  return {
    get aborted() { return performance.now() >= at; },
    addEventListener() {},
    removeEventListener() {},
  } as unknown as AbortSignal;
}

const reasonOf = (r: { verdict: { type: string; reason?: string }; report: string }) => {
  expect(r.verdict.type, r.report).toBe('unknown');
  return (r.verdict as { reason: string }).reason;
};

describe('cancellation (VER-013)', () => {
  it('a signal aborted before the call returns unknown at once, report line included', async () => {
    const controller = new AbortController();
    controller.abort();
    const result = await toggles(3).verifier().signal(controller.signal).verify();
    expect(reasonOf(result)).toBe('verification cancelled during net preparation');
    expect(result.report).toContain('UNKNOWN: verification cancelled during net preparation');
  });

  it('stops the enumeration build at its next poll and leaves the cache as it found it (AC12)', async () => {
    const { verifier } = toggles(14); // 16 384 classes: seconds to build
    const cache = new StateSpaceCache();
    const t0 = performance.now();
    const cut = await verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).signal(abortsAfter(30)).verify();
    expect(reasonOf(cut)).toBe('verification cancelled during state-space enumeration');
    expect(cut.route).toBe('enumeration');
    expect(performance.now() - t0).toBeLessThan(1_000);
    // Not recorded as a truncation: a later query with the same class budget builds.
    const before = stateSpaceBuildCount();
    const full = await verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).verify();
    expect(stateSpaceBuildCount() - before).toBe(1);
    expect(full.report).not.toContain('cached truncation');
  }, 60_000);

  it('stops a Route B build the same way', async () => {
    const { net, places } = pnidNet('P-Fig11b', FIG_11B_ROWS);
    const result = await SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(places.get('clerk')!, 2).build())
      .property(placeBound(places.get('order_clerk')!, 100_000)).nuMaxClasses(20_000)
      .signal(abortsAfter(30)).verify();
    expect(reasonOf(result)).toBe('verification cancelled during Route B (ν name-partition graph)');
  });

  it('a call cancelled before it starts returns the cancellation reason ahead of any other refusal', async () => {
    const controller = new AbortController();
    controller.abort();
    // The property names a place the net does not declare: the vacuity refusal would return
    // `unknown` for its own reason, but the call was cancelled before it started.
    const result = await toggles(3).verifier().property(placeBound(place('absent'), 1)).signal(controller.signal).verify();
    expect(reasonOf(result)).toBe('verification cancelled during net preparation');
  });

  it('two verify() calls sharing a cache: each honours its own signal and budget, one build (AC9/AC11/AC12)', async () => {
    // The cache holds no pending build: resolveStateSpace is synchronous and runPipeline does not
    // await before the enumeration, so the first call's build completes before its promise is
    // returned and the second call cannot wait on it. The second call still sees its own stop.
    const { verifier } = toggles(10);
    const cache = new StateSpaceCache();
    const controller = new AbortController();
    controller.abort();
    const before = stateSpaceBuildCount();
    const [first, cancelled, spent, reused] = await Promise.all([
      verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).verify(),
      verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).signal(controller.signal).verify(),
      verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).totalBudget(0).verify(),
      verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).verify(),
    ]);
    expect(stateSpaceBuildCount() - before).toBe(1);
    expect(first.verdict.type, first.report).toBe('proven');
    expect(reasonOf(cancelled)).toBe('verification cancelled during net preparation');
    expect(reasonOf(spent)).toBe('total verification budget of 0 ms exhausted during net preparation');
    expect(reused.verdict.type, reused.report).toBe('proven');
    expect(reused.report).toContain('cached');
  });

  it('a budget and a signal: whichever stops first names the reason', async () => {
    const controller = new AbortController();
    controller.abort();
    const result = await toggles(3).verifier().totalBudget(60_000).signal(controller.signal).verify();
    expect(reasonOf(result)).toBe('verification cancelled during net preparation');
  });
});

describe('cancellation of open-net verification (VER-013, VER-022)', () => {
  it('a signal aborted before the call leaves the verdict unknown with the cancellation reason', async () => {
    const input = place('in');
    const out = place('out');
    const net = PetriNet.builder('open')
      .transition(Transition.builder('t').inputs(one(input)).outputs(outPlace(out)).action(produces()).build())
      .build();
    const contract = OpenNetContract.builder().arrive(1, input).expect('delivered', 1, out).build();
    const controller = new AbortController();
    controller.abort();
    const result = await verifyOpenNet(net, contract, { signal: controller.signal });
    expect(result.verdict.type).toBe('unknown');
    expect((result.verdict as { reason: string }).reason).toBe('verification cancelled during open-net state-class graph');
  });
});
