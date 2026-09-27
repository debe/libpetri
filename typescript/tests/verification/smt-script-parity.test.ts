import { describe, it } from 'vitest';
import { dirname, join } from 'node:path';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { verificationNets, withFixtureTerminals } from '../fixtures/verification-nets.js';
import { compareScript as compare } from '../fixtures/script-parity.js';
import { applySinkPlacesWhen, fixtures, fixturesPath, placeOf, toProperty } from './verdict-parity.test.js';

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

describe('SMT script parity with the Rust goldens (VER-013 AC1)', () => {
  for (const fixture of fixtures) {
    it(fixture.id, () => {
      const built = verificationNets[fixture.net]!();
      // EXEC-042: a fixture's `terminals` are declared on the net, never on the verifier.
      const verifier = SmtVerifier.forNet(withFixtureTerminals(built, fixture.terminals))
      .enumerationMaxClasses(0)
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
      applySinkPlacesWhen(verifier, fixture, built.places);
      if (fixture.budgetPlaces != null && fixture.budgetPlaces.length > 0) {
        verifier.budgetPlaces(...fixture.budgetPlaces.map(n => placeOf(built.places, n)));
      }
      // Optional shared-schema fields: [VER-007]'s semiflow union, [VER-016]'s state equation.
      verifier.semiflowInvariants(fixture.semiflowInvariants === true);
      verifier.stateEquation(fixture.stateEquation === true);
      const scripts = verifier.encodeScripts();
      const dir = join(scriptsDir, fixture.id);
      compare(fixture.id, join(dir, 'horn.smt2'), scripts.horn);
      compare(fixture.id, join(dir, 'certificate.smt2'), scripts.certificate);
      // VER-015 AC4: the linear state-equation bound query, pinned wherever the property
      // has a linear demand — on the flat path and ahead of a name-coloured encoding alike.
      compare(fixture.id, join(dir, 'bound.smt2'), scripts.bound);
      // VER-018 AC7: the state-equation phase's first query, pinned wherever the phase runs.
      compare(fixture.id, join(dir, 'state-equation.smt2'), scripts.stateEquation);
    });
  }
});
