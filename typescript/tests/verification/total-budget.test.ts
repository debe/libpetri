import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { StateSpaceCache } from '../../src/verification/state-space-cache.js';
import { stateSpaceBuildCount } from '../../src/verification/scg-verifier.js';
import { placeBound, unreachable } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed, window } from '../../src/core/timing.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';

/** [VER-013] the optional total wall-clock budget of `SmtVerifier.verify()`. */

/** `k` independent one-shot transitions: 2^k reachable markings, an untimed net. */
function toggles(k: number): { net: PetriNet; verifier: () => SmtVerifier } {
  const b = PetriNet.builder(`toggles-${k}`);
  // One Place object per name: the state-space cache keys the marking by Place identity.
  const a = Array.from({ length: k }, (_, i) => place(`a${i}`));
  for (let i = 0; i < k; i++) {
    b.transition(Transition.builder(`t${i}`).inputs(one(a[i]!)).outputs(outPlace(place(`b${i}`))).build());
  }
  const net = bindProducers(b.build());
  return {
    net,
    verifier: () => SmtVerifier.forNet(net)
      .initialMarking(m => { for (const p of a) m.tokens(p, 1); })
      .property(placeBound(a[0]!, 1)),
  };
}

function reasonOf(result: { verdict: { type: string; reason?: string }; report: string }): string {
  expect(result.verdict.type, result.report).toBe('unknown');
  return (result.verdict as { reason: string }).reason;
}

describe('total budget (VER-013)', () => {
  it('a spent budget is unknown with the canonical reason, in the report too', async () => {
    const result = await toggles(3).verifier().totalBudget(0).verify();
    const reason = reasonOf(result);
    expect(reason).toBe('total verification budget of 0 ms exhausted during net preparation');
    expect(result.report).toContain(`UNKNOWN: ${reason}`);
    expect(result.report).toContain('Total budget: 0 ms');
  });

  it('stops the enumeration build, within the budget, and leaves the cache as it found it (AC10)', async () => {
    const { verifier } = toggles(14); // 16 384 classes: over a second to build
    const cache = new StateSpaceCache();

    const t0 = performance.now();
    const cut = await verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).totalBudget(40).verify();
    const elapsed = performance.now() - t0;
    expect(reasonOf(cut)).toBe('total verification budget of 40 ms exhausted during state-space enumeration');
    expect(cut.route).toBe('enumeration');
    expect(elapsed).toBeLessThan(40 + 800);

    // With more time and the same class budget, the query builds rather than declines: the cut
    // build was not recorded as a truncation at 50 000 classes.
    const before = stateSpaceBuildCount();
    const full = await verifier().stateSpaceCache(cache).enumerationMaxClasses(50_000).verify();
    expect(stateSpaceBuildCount() - before).toBe(1);
    expect(full.verdict.type, full.report).toBe('proven');
    expect(full.route).toBe('enumeration');
    expect(full.report).not.toContain('cached truncation');
  }, 60_000); // the full build is over a second alone, several under a loaded parallel run

  it('rejects a negative or non-finite budget', () => {
    expect(() => toggles(1).verifier().totalBudget(-1)).toThrow(/non-negative/);
    expect(() => toggles(1).verifier().totalBudget(Number.NaN)).toThrow(/non-negative/);
  });
});

describeZ3('total budget unset or ample (VER-013 AC8)', () => {
  /** A timed net, so the SMT pipeline decides it with z3. */
  function watchdog(): SmtVerifier {
    const req = place<string>('REQ');
    const calling = place<string>('CALLING');
    const net = bindProducers(PetriNet.builder('watchdog')
      .transition(Transition.builder('start').inputs(one(req)).outputs(outPlace(calling)).build())
      .transition(Transition.builder('answer').timing(window(0, 2)).inputs(one(calling)).outputs(outPlace(place('RESP'))).build())
      .transition(Transition.builder('watchdog').timing(delayed(5)).inputs(one(calling)).outputs(outPlace(place('TIMEOUT'))).build())
      .build());
    return SmtVerifier.forNet(net).initialMarking(m => m.tokens(req, 1));
  }

  it('an ample budget changes nothing but the report header line', async () => {
    for (const property of [unreachable(new Set([place('TIMEOUT')])), placeBound(place('REQ'), 1)]) {
      const unset = await watchdog().property(property).verify();
      const ample = await watchdog().property(property).totalBudget(600_000).verify();
      expect(unset.report).not.toContain('Total budget');
      expect(ample.verdict).toEqual(unset.verdict);
      expect(ample.route).toBe(unset.route);
      expect(ample.counterexampleTransitions).toEqual(unset.counterexampleTransitions);
      expect(ample.report.replace('Total budget: 600000 ms\n', '')).toBe(unset.report);
    }
  });
});
