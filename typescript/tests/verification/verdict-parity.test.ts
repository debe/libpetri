import { it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import {
  deadlockFree, mutualExclusion, placeBound, terminatesAtSink, unreachable, type SmtProperty,
} from '../../src/verification/smt-property.js';
import type { Place } from '../../src/core/place.js';
import { verificationNets } from '../fixtures/verification-nets.js';

// Cross-language verdict-parity runner (C4). The shared expectations live in
// spec/verification-fixtures/fixtures.json; each language builds the named
// nets in its own test code and asserts `expected` with certificate checking
// AND counterexample replay ON. A disagreement with `expected` is a parity
// FINDING — report it prominently; never adjust the fixture to make it pass.
const Z3_TIMEOUT = 60_000;

/**
 * The line every implementation prints when the ν name-aware state-class-graph
 * verifier (NU-050 Route B) — not the SMT / Route A encoders — decided the query.
 * Fixtures marked `route: 'B'` assert it BEFORE their verdict, so a silent
 * fall-back to Route A fails loudly instead of passing vacuously.
 */
const ROUTE_B_MARKER = 'ν-net Route B: name-aware state-class graph (NU-050)';

export interface FixtureProperty {
  readonly type: string;
  readonly places?: readonly string[];
  readonly place?: string;
  readonly bound?: number;
}

export interface Fixture {
  readonly id: string;
  readonly net: string;
  readonly netDescription: string;
  readonly property: FixtureProperty;
  /**
   * Expected terminal places (VER-002 sink semantics): DeadlockFree is violated by a
   * quiescent marking that strands a token OUTSIDE them, TerminatesAtSink by one that
   * marks NONE of them. Absent for closed nets.
   */
  readonly sinkPlaces?: readonly string[];
  /**
   * Conditional sinks (VER-014): marker place name -> places where a token may rest
   * while the marker holds a token; the marker itself is at rest when marked.
   * Declared in object order. Absent = no conditional declarations.
   */
  readonly sinkPlacesWhen?: Readonly<Record<string, readonly string[]>>;
  /** ν budget places (NU-040): put a reachability-safety query on Route A's coloured encoding. */
  readonly budgetPlaces?: readonly string[];
  readonly semiflowInvariants?: boolean;
  /** VER-016: encode the state equation with firing counters (default off). */
  readonly stateEquation?: boolean;
  /** `'B'` = decided by the ν name-aware SCG verifier (NU-050 Route B); absent = Route A. */
  readonly route?: string;
  readonly expected: 'proven' | 'violated' | 'unknown';
  readonly expectReportContains?: string;
}

const here = dirname(fileURLToPath(import.meta.url));
export const fixturesPath = resolve(here, '../../../spec/verification-fixtures/fixtures.json');
export const fixtures: readonly Fixture[] = JSON.parse(readFileSync(fixturesPath, 'utf8')).fixtures;

export function placeOf(places: ReadonlyMap<string, Place<any>>, name: string): Place<any> {
  const p = places.get(name);
  if (p == null) throw new Error(`fixture references unknown place '${name}'`);
  return p;
}

/** Declares the fixture's `sinkPlacesWhen` entries (VER-014) on `verifier`, in object order. */
export function applySinkPlacesWhen(
  verifier: SmtVerifier,
  fixture: Fixture,
  places: ReadonlyMap<string, Place<any>>,
): void {
  for (const [marker, rest] of Object.entries(fixture.sinkPlacesWhen ?? {})) {
    verifier.sinkPlacesWhen(placeOf(places, marker), ...rest.map(n => placeOf(places, n)));
  }
}

export function toProperty(spec: FixtureProperty, places: ReadonlyMap<string, Place<any>>): SmtProperty {
  switch (spec.type) {
    case 'deadlock-free':
      return deadlockFree();
    case 'terminates-at-sink':
      return terminatesAtSink();
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

describeZ3('verdict parity (spec/verification-fixtures/fixtures.json)', () => {
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
      .enumerationMaxClasses(0)
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
      applySinkPlacesWhen(verifier, fixture, built.places);
      if (fixture.budgetPlaces != null && fixture.budgetPlaces.length > 0) {
        verifier.budgetPlaces(...fixture.budgetPlaces.map(n => placeOf(built.places, n)));
      }
      // Optional shared-schema fields: [VER-007]'s semiflow union, [VER-016]'s state equation.
      verifier.semiflowInvariants(fixture.semiflowInvariants === true);
      verifier.stateEquation(fixture.stateEquation === true);
      const result = await verifier.verify();

      // The route marker is checked FIRST: a `route: 'B'` fixture that silently
      // fell back to Route A would pin nothing, so name that failure directly
      // rather than letting it surface as a confusing verdict mismatch.
      const routeB = fixture.route === 'B';
      if (routeB) {
        expect(
          result.report,
          `ROUTE FINDING for '${fixture.id}': fixture declares route "B" but the report does ` +
            'not name the ν name-aware state-class graph — the query fell back to Route A, so ' +
            `the Route B deadlock predicate was never exercised\n--- report ---\n${result.report}`,
        ).toContain(ROUTE_B_MARKER);
      }

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
      // Route B is exempt: its counterexample is a path of the name-partition
      // graph, not of the flat abstract semantics, so it reports
      // counterexampleConfirmed = null by construction.
      if (!routeB && result.verdict.type === 'violated' && result.counterexampleConfirmed !== true) {
        console.warn(
          `[verdict-parity] '${fixture.id}': violated but counterexampleConfirmed=` +
            `${result.counterexampleConfirmed}`,
        );
      }
    }, Z3_TIMEOUT);
  }
});
