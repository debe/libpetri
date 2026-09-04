import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { verificationNets } from '../fixtures/verification-nets.js';
import { fixtures, fixturesPath, placeOf, toProperty } from './verdict-parity.test.js';

/**
 * Cross-language SMT script parity (VER-013 AC1). For every fixture the scripts
 * this verifier would send to z3 (`SmtVerifier.encodeScripts()`) must equal the
 * committed goldens under `spec/verification-fixtures/scripts/<id>/`, byte for
 * byte. The goldens are written by the Rust verifier
 * (`scripts/smt-script-parity.py --update`); the Java and Python suites diff them
 * too. A diff is a parity FINDING in whichever emitter drifted, never a reason to
 * edit a golden by hand.
 *
 * No solver is needed: the encoders are pure text.
 */
const scriptsDir = join(dirname(fixturesPath), 'scripts');

function firstDifference(expected: string, actual: string): string {
  const e = expected.split('\n');
  const a = actual.split('\n');
  for (let i = 0; i < Math.min(e.length, a.length); i++) {
    if (e[i] !== a[i]) return `line ${i + 1}:\n  golden: ${e[i]}\n  actual: ${a[i]}`;
  }
  return `one text is a prefix of the other (golden ${e.length} lines, actual ${a.length} lines)`;
}

function compare(id: string, golden: string, actual: string | null): void {
  if (!existsSync(golden)) {
    expect(actual, `SCRIPT PARITY FINDING [${id}]: this encoding emits ${golden} but no golden exists (run scripts/smt-script-parity.py --update)`).toBeNull();
    return;
  }
  const expected = readFileSync(golden, 'utf8');
  expect(actual, `SCRIPT PARITY FINDING [${id}]: ${golden} exists but this encoding emits no such script`).not.toBeNull();
  if (actual !== expected) {
    expect.fail(`SCRIPT PARITY FINDING [${id}]: ${golden} differs from the Rust golden at ${firstDifference(expected, actual!)} — report the divergence, never edit the golden by hand`);
  }
}

describe('SMT script parity with the Rust goldens (VER-013 AC1)', () => {
  for (const fixture of fixtures) {
    it(fixture.id, () => {
      const built = verificationNets[fixture.net]!();
      const verifier = SmtVerifier.forNet(built.net)
        .initialMarking(built.initialMarking)
        .property(toProperty(fixture.property, built.places))
        .certificateCheck(true)
        .counterexampleReplay(true)
        .timeout(30_000);
      if (built.environmentPlaces.length > 0) {
        verifier.environmentPlaces(...built.environmentPlaces).environmentMode(built.environmentMode!);
      }
      if (fixture.sinkPlaces != null && fixture.sinkPlaces.length > 0) {
        verifier.sinkPlaces(...fixture.sinkPlaces.map(n => placeOf(built.places, n)));
      }
      if (fixture.budgetPlaces != null && fixture.budgetPlaces.length > 0) {
        verifier.budgetPlaces(...fixture.budgetPlaces.map(n => placeOf(built.places, n)));
      }
      // Optional shared-schema field: [VER-007]'s semiflow union.
      verifier.semiflowInvariants(fixture.semiflowInvariants === true);
      const scripts = verifier.encodeScripts();
      const dir = join(scriptsDir, fixture.id);
      compare(fixture.id, join(dir, 'horn.smt2'), scripts.horn);
      compare(fixture.id, join(dir, 'certificate.smt2'), scripts.certificate);
    });
  }
});
