import { describe, it, expect, vi } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// All tests in this file require Z3 WASM which is slow to initialize.
const Z3_TIMEOUT = 60_000;

// Test seam: replace the decoder with one returning a decoded set that CANNOT
// be chained to a violating state — the bad state lies 4 abstract steps from
// M0 and no intermediate waypoint is provided, so the bounded BFS (gap 3)
// must fail and the verifier must DOWNGRADE the violated verdict to unknown.
// This exercises the full wiring the way a spurious CEX / decoder mismatch
// would, without needing Z3 itself to misbehave.
vi.mock('../../src/verification/z3/counterexample-decoder.js', async (importOriginal) => {
  const mod = await importOriginal<typeof import('../../src/verification/z3/counterexample-decoder.js')>();
  return {
    ...mod,
    decode: (ctx: any, answer: any, flatNet: any) => {
      const real = mod.decode(ctx, answer, flatNet);
      // Keep only the initial marking {A: 1} as a waypoint.
      const m0 = MarkingState.builder().tokens(place('A'), 1).build();
      return { ...real, states: new Set([m0]) };
    },
  };
});

describe('SmtVerifier replay downgrade (unchainable decoded set seam)', () => {
  it('an unchainable decoded set downgrades the violated verdict to unknown', async () => {
    // A -> B -> C -> D -> E chain; placeBound(E, 0) is genuinely violated, but
    // the (mocked) decoded set holds only M0, and E is 4 steps away.
    const names = ['A', 'B', 'C', 'D', 'E'] as const;
    const places = names.map(n => place(n));
    const transitions = [];
    for (let i = 0; i + 1 < places.length; i++) {
      transitions.push(
        Transition.builder(`T${i}`).inputs(one(places[i]!)).outputs(outPlace(places[i + 1]!)).build(),
      );
    }
    const net = PetriNet.builder('LongChain').transitions(...transitions).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(places[0]!, 1))
      .property(placeBound(places[4]!, 0))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('unknown');
    if (result.verdict.type === 'unknown') {
      expect(result.verdict.reason).toBe(
        'counterexample failed abstract replay — spurious CEX or decoder mismatch',
      );
    }
    expect(result.counterexampleConfirmed).toBeNull();
    expect(result.counterexampleTrace).toHaveLength(0);
    // The report must carry the evidence: replay failure detail, the decoded
    // set, and the raw Z3 answer.
    expect(result.report).toContain('Counterexample replay: FAILED');
    expect(result.report).toContain('Decoded states (order-free set, 1)');
    expect(result.report).toContain('{A:1}');
    expect(result.report).toContain('Raw Z3 answer:');
    expect(result.report).not.toContain('VIOLATED');
  }, Z3_TIMEOUT);

  it('counterexampleReplay(false) bypasses the downgrade (verdict stays violated)', async () => {
    const pA = place('A');
    const pB = place('B');
    const t = Transition.builder('T').inputs(one(pA)).outputs(outPlace(pB)).build();
    const net = PetriNet.builder('TwoStep').transitions(t).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 0))
      .counterexampleReplay(false)
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBeNull();
  }, Z3_TIMEOUT);
});
