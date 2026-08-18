import { describe, it, expect, vi } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// All tests in this file require Z3 WASM which is slow to initialize.
// Tests are set to a generous timeout.
const Z3_TIMEOUT = 60_000;

// Test seam: wrap the real Spacer runner and corrupt the proven answer into
// `forall vars. Reachable(vars) = true` — a well-formed certificate that is
// deliberately wrong (it admits every marking, so VC3 must fail). This
// exercises the full verifier wiring: extraction succeeds, the safety VC
// fails, and the proven verdict must downgrade to unknown.
vi.mock('../../src/verification/z3/spacer-runner.js', async (importOriginal) => {
  const mod = await importOriginal<typeof import('../../src/verification/z3/spacer-runner.js')>();
  return {
    ...mod,
    createSpacerRunner: async (timeoutMs: number) => {
      const runner = await mod.createSpacerRunner(timeoutMs);
      return {
        ...runner,
        query: async (errorExpr: any, reachableDecl?: any) => {
          const result = await runner.query(errorExpr, reachableDecl);
          if (result.type !== 'proven') return result;
          const ctx: any = runner.ctx;
          const Int = ctx.Int;
          const qa = Int.const('qa');
          const qb = Int.const('qb');
          const reachable = ctx.Function.declare('Reachable', Int.sort(), Int.sort(), ctx.Bool.sort());
          const corrupted = ctx.ForAll([qa, qb], reachable.call(qa, qb).eq(ctx.Bool.val(true)));
          return { ...result, answer: corrupted };
        },
      };
    },
  };
});

describe('SmtVerifier certificate downgrade (corrupted answer seam)', () => {
  it('a wrong invariant downgrades the proven verdict to unknown', async () => {
    // Env-injection net: no P-invariant survives the injector column, so the
    // corrupted certificate cannot be rescued by invariant strengthening.
    const pIn = environmentPlace('IN');
    const pOut = place('OUT');
    const tConsume = Transition.builder('consume').inputs(one(pIn)).outputs(outPlace(pOut)).build();
    const tDrain = Transition.builder('drain').inputs(one(pOut)).build();
    const net = PetriNet.builder('EnvNet').transitions(tConsume, tDrain).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(() => {})
      .environmentPlaces(pIn)
      .environmentMode(bounded(2))
      .property(placeBound(pOut, 2))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('unknown');
    if (result.verdict.type === 'unknown') {
      expect(result.verdict.reason).toMatch(
        /^certificate check failed: safety \(VC3\) was not UNSAT - solver returned SATISFIABLE/,
      );
      expect(result.verdict.reason).toMatch(
        /the IC3 certificate could not be independently re-validated against the unstrengthened step relation, so PROVEN is withheld$/,
      );
    }
    expect(result.report).toContain('  Certificate check: FAILED');
    expect(result.report).toContain('Uncertified invariant: true');
    // The downgrade reason says "PROVEN is withheld"; no PROVEN verdict is reported.
    expect(result.report).not.toContain('PROVEN (IC3/PDR)');
    expect(result.report).not.toContain('PROVEN (structural)');
  }, Z3_TIMEOUT);
});
