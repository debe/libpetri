import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import {
  deadlockFree, mutualExclusion, placeBound, unreachable, type SmtProperty,
} from '../../src/verification/smt-property.js';
import type { Place } from '../../src/core/place.js';
import { verificationNets } from '../fixtures/verification-nets.js';

// Cross-language verdict-parity runner (C4). The shared expectations live in
// spec/verification-fixtures/fixtures.json; each language builds the named
// nets in its own test code and asserts `expected` with certificate checking
// AND counterexample replay ON. A disagreement with `expected` is a parity
// FINDING — report it prominently; never adjust the fixture to make it pass.
const Z3_TIMEOUT = 60_000;

interface FixtureProperty {
  readonly type: string;
  readonly places?: readonly string[];
  readonly place?: string;
  readonly bound?: number;
}

interface Fixture {
  readonly id: string;
  readonly net: string;
  readonly netDescription: string;
  readonly property: FixtureProperty;
  /** Expected terminal places (VER-002 sink semantics); absent for closed nets. */
  readonly sinkPlaces?: readonly string[];
  readonly expected: 'proven' | 'violated' | 'unknown';
  readonly expectReportContains?: string;
}

const here = dirname(fileURLToPath(import.meta.url));
const fixturesPath = resolve(here, '../../../spec/verification-fixtures/fixtures.json');
const fixtures: readonly Fixture[] = JSON.parse(readFileSync(fixturesPath, 'utf8')).fixtures;

function placeOf(places: ReadonlyMap<string, Place<any>>, name: string): Place<any> {
  const p = places.get(name);
  if (p == null) throw new Error(`fixture references unknown place '${name}'`);
  return p;
}

function toProperty(spec: FixtureProperty, places: ReadonlyMap<string, Place<any>>): SmtProperty {
  switch (spec.type) {
    case 'deadlock-free':
      return deadlockFree();
    case 'mutual-exclusion':
      return mutualExclusion(placeOf(places, spec.places![0]!), placeOf(places, spec.places![1]!));
    case 'place-bound':
      return placeBound(placeOf(places, spec.place!), spec.bound!);
    case 'unreachable':
      return unreachable(new Set([placeOf(places, spec.place!)]));
    default:
      throw new Error(`unmapped fixture property type '${spec.type}'`);
  }
}

describe('verdict parity (spec/verification-fixtures/fixtures.json)', () => {
  it('loads the shared fixtures and has a builder for every named net', () => {
    expect(fixtures.length).toBeGreaterThan(0);
    for (const f of fixtures) {
      expect(verificationNets, `missing TS builder for fixture net '${f.net}'`).toHaveProperty(f.net);
    }
  });

  for (const fixture of fixtures) {
    it(`${fixture.id} -> ${fixture.expected}`, async () => {
      const built = verificationNets[fixture.net]!();
      const verifier = SmtVerifier.forNet(built.net)
        .initialMarking(built.initialMarking)
        .property(toProperty(fixture.property, built.places))
        .certificateCheck(true) // independent IC3-certificate layer ON
        .counterexampleReplay(true) // abstract replay layer ON
        .timeout(30_000);
      if (built.environmentPlaces.length > 0) {
        verifier
          .environmentPlaces(...built.environmentPlaces)
          .environmentMode(built.environmentMode!);
      }
      if (fixture.sinkPlaces != null && fixture.sinkPlaces.length > 0) {
        verifier.sinkPlaces(...fixture.sinkPlaces.map(n => placeOf(built.places, n)));
      }
      const result = await verifier.verify();

      expect(
        result.verdict.type,
        `parity FINDING for '${fixture.id}': expected ${fixture.expected}, ` +
          `got ${result.verdict.type}\n--- report ---\n${result.report}`,
      ).toBe(fixture.expected);

      if (fixture.expectReportContains != null) {
        expect(result.report).toContain(fixture.expectReportContains);
      }

      // Observability for the replay layer: a violated parity verdict should
      // normally be replay-confirmed. An unconfirmed one is not a parity
      // failure (the fixture only fixes the verdict) but is worth surfacing.
      if (result.verdict.type === 'violated' && result.counterexampleConfirmed !== true) {
        console.warn(
          `[verdict-parity] '${fixture.id}': violated but counterexampleConfirmed=` +
            `${result.counterexampleConfirmed}`,
        );
      }
    }, Z3_TIMEOUT);
  }
});
