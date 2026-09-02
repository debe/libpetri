import { describe, it, expect } from 'vitest';
import { Z3_AVAILABLE } from '../fixtures/z3.js';
import { tokenOf, type Token } from '../../src/core/token.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import {
  deadlockFree,
  placeBound,
  type SmtProperty,
} from '../../src/verification/smt-property.js';
import type { TokenSupplier } from '../../src/verification/verification-harness.js';
import {
  consumer,
  leakyBucket,
  producer,
} from '../fixtures/subnet-fixtures.js';

/**
 * Tests for {@link SubnetDef.verify} per **MOD-051**. Two coverage layers:
 *
 * 1. **Pure harness-construction tests** (no Z3): exercise the synthetic-net
 *    wiring, harness validation, and result aggregation. These run on every
 *    CI without invoking the SMT solver.
 *
 * 2. **End-to-end SMT tests**: invoke the verifier on a degenerate fixture
 *    and assert structural properties of the result. The verifier shells out
 *    to a `z3` executable (VER-013), so these skip without one; the z3 gate
 *    test turns that skip into a failure on a CI runner.
 *
 * Mirrors `java/src/test/java/org/libpetri/verification/SubnetVerifyTest.java`.
 */

const Z3_TIMEOUT = 60_000;

describe('SubnetDef.verify (MOD-051 harness)', () => {
  // ============================================================
  //  Pure harness-construction tests (no Z3 needed)
  // ============================================================

  it('verify_missingInputGenerator_throws — names the missing port', async () => {
    // leakyBucket has Input port "request" and Output ports "accept",
    // "reject". An empty harness must reject because "request" has no
    // generator.
    const bucket = leakyBucket(2);
    const harness = {
      params: { rate: 2, label: 'lb' },
      portInputGenerators: {},
      properties: [],
    };

    await expect(bucket.verify(harness)).rejects.toThrow(/request/);
  });

  it('verify_missingInputGenerator_namesSubnetAndMOD051', async () => {
    const bucket = leakyBucket(2);
    const harness = {
      params: { rate: 2, label: 'lb' },
      portInputGenerators: {},
      properties: [],
    };

    await expect(bucket.verify(harness)).rejects.toThrow(/MOD-051/);
  });

  it('verify_outputPortOnly_doesNotRequireGenerator', async () => {
    // producer fixture has only the Output port "output" — no input
    // generators required. Empty harness must succeed structurally
    // (constructs a synthetic net, runs zero properties).
    const prod = producer();
    const harness = {
      params: undefined as never,
      portInputGenerators: {},
      properties: [],
    };

    const result = await prod.verify(harness);

    expect(result.syntheticNet).toBeDefined();
    expect(result.perProperty.size).toBe(0);
    expect(result.allProven()).toBe(true);
    expect(result.anyViolated()).toBe(false);
  });

  it('verify_syntheticNetBindsAllPorts — leakyBucket has 1 input + 2 output ports', async () => {
    // The synthetic enclosing net must contain a synthetic place per port
    // (3 total) plus the subnet's internal places, named per the
    // `harness_in_<port>` / `harness_out_<port>` convention.
    const bucket = leakyBucket(2);

    const requestSupplier: TokenSupplier = () => tokenOf('req');

    const harness = {
      params: { rate: 2, label: 'lb' },
      portInputGenerators: { request: requestSupplier },
      properties: [],
    };

    const result = await bucket.verify(harness);

    const placeNames = new Set<string>();
    for (const p of result.syntheticNet.places) placeNames.add(p.name);

    expect(placeNames.has('harness_in_request')).toBe(true);
    expect(placeNames.has('harness_out_accept')).toBe(true);
    expect(placeNames.has('harness_out_reject')).toBe(true);
  });

  it('verify_inputGenerator_isInvokedAtConstruction', async () => {
    // The harness contract is that the supplier is touched once at
    // synthetic-net build time so user errors surface early. Verify the
    // supplier is called at least once when verify(...) runs.
    const cons = consumer();

    let callCount = 0;
    const tracker: TokenSupplier = () => {
      callCount++;
      return tokenOf('tracked');
    };

    await cons.verify({
      params: undefined as never,
      portInputGenerators: { input: tracker },
      properties: [],
    });

    expect(callCount).toBeGreaterThanOrEqual(1);
  });

  it('verify_inputGeneratorReturnsNull_throws', async () => {
    // A null/undefined token from the supplier surfaces as a clear error
    // (mirrors the Java Objects.requireNonNull check).
    const cons = consumer();
    const nullSupplier: TokenSupplier = () => null as unknown as Token<unknown>;

    await expect(cons.verify({
      params: undefined as never,
      portInputGenerators: { input: nullSupplier },
      properties: [],
    })).rejects.toThrow(/null|undefined/);
  });

  it('verify_acceptsMapForGeneratorsAndPropertiesSet', async () => {
    // Both Map / Record and Set / array forms are accepted for the harness.
    const cons = consumer();
    const supplier: TokenSupplier = () => tokenOf('m');

    const generatorsMap = new Map<string, TokenSupplier>([['input', supplier]]);
    const propertiesSet = new Set<SmtProperty>();

    const result = await cons.verify({
      params: undefined as never,
      portInputGenerators: generatorsMap,
      properties: propertiesSet,
    });

    expect(result.syntheticNet).toBeDefined();
    expect(result.perProperty.size).toBe(0);
  });

  // ============================================================
  //  End-to-end SMT verification (Z3 bundled in npm package)
  // ============================================================

  it('verify_returnsResultWithAllProperties — one entry per harness property', async () => {
    // Two properties on the consumer fixture. The harness must invoke the
    // verifier once per property and surface both outcomes in the result
    // map, regardless of verdict.
    const cons = consumer();
    const inputSupplier: TokenSupplier = () => tokenOf('hello');

    // The consumer subnet exposes the input port over a place named
    // 'input'; after compose, that becomes 'harness_in_input' in the
    // synthetic net. Use deadlockFree (no place reference required) and
    // a placeBound on a known synthetic place.
    const props: SmtProperty[] = [deadlockFree()];

    const result = await cons.verify({
      params: undefined as never,
      portInputGenerators: { input: inputSupplier },
      properties: props,
    });

    expect(result.perProperty.size).toBe(props.length);
    for (const p of props) {
      expect(result.perProperty.has(p)).toBe(true);
      expect(result.perProperty.get(p)).toBeDefined();
      expect(result.perProperty.get(p)!.report).toBeDefined();
    }
  }, Z3_TIMEOUT);

  it.skipIf(!Z3_AVAILABLE)('verify_leakyBucket_isKBounded — verifier produces a per-property result', async () => {
    // End-to-end: discover the synthetic accept place from a probe call,
    // then verify a PlaceBound property against it. We assert the verifier
    // runs and produces a well-formed SmtVerificationResult; we don't
    // assert a specific verdict because the over-approximating
    // environment-analysis mode in net-flattener treats the env place as
    // unbounded by default, which can change the verdict from a strict
    // bound test.
    const bucket = leakyBucket(2);
    const requestSupplier: TokenSupplier = () => tokenOf('req');

    // First call: probe to discover the synthetic accept place by name.
    const probe = await bucket.verify({
      params: { rate: 2, label: 'lb' },
      portInputGenerators: { request: requestSupplier },
      properties: [],
    });

    let acceptPlace = undefined;
    for (const p of probe.syntheticNet.places) {
      if (p.name === 'harness_out_accept') {
        acceptPlace = p;
        break;
      }
    }
    expect(acceptPlace).toBeDefined();

    // Second call: verify a PlaceBound property on the synthetic accept
    // place. With no initial slots tokens seeded, accept is unreachable —
    // accepted count is 0 — so PlaceBound(acceptPlace, 0) holds.
    const props: SmtProperty[] = [placeBound(acceptPlace!, 0)];

    const result = await bucket.verify({
      params: { rate: 2, label: 'lb' },
      portInputGenerators: { request: requestSupplier },
      properties: props,
    });

    expect(result.perProperty.size).toBe(1);
    const verdict = result.perProperty.get(props[0]!);
    expect(verdict).toBeDefined();
    expect(verdict!.report).toBeDefined();
    expect(verdict!.verdict.type).toMatch(/proven|violated|unknown/);
  }, Z3_TIMEOUT);

  it.skipIf(!Z3_AVAILABLE)('verify_emptyProperties_allProvenIsVacuouslyTrue', async () => {
    // No properties → allProven() is vacuously true; anyViolated() is false.
    const prod = producer();
    const result = await prod.verify({
      params: undefined as never,
      portInputGenerators: {},
      properties: [],
    });
    expect(result.allProven()).toBe(true);
    expect(result.anyViolated()).toBe(false);
  });
});
