import { describe, it, expect } from 'vitest';
import {
  assessCounterexample, certificateDowngradeReason,
} from '../../src/verification/smt-verifier.js';
import type { CertificateCheckOutcome } from '../../src/verification/z3/certificate-checker.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bounded } from '../../src/verification/analysis/environment-analysis-mode.js';

// The verdict-mapping seams are pure: no Z3 context, no WASM boot. These tests
// pin the user-visible strings that the four implementations share.

const NO_SINKS: ReadonlySet<Place<any>> = new Set();

describe('certificateDowngradeReason', () => {
  it('passed keeps the verdict', () => {
    expect(certificateDowngradeReason({ type: 'passed', invariant: 'A + B = 1' })).toBeNull();
  });

  it('a failed VC names the condition and quotes the solver detail', () => {
    const outcome: CertificateCheckOutcome = {
      type: 'failed',
      vc: 'consecution (VC2)',
      detail: 'solver returned SATISFIABLE (witness: p0=2, p1=1)',
      invariant: 'true',
    };
    expect(certificateDowngradeReason(outcome)).toBe(
      'certificate check failed: consecution (VC2) was not UNSAT - solver returned ' +
        'SATISFIABLE (witness: p0=2, p1=1); the IC3 certificate could not be ' +
        'independently re-validated against the unstrengthened step relation, so ' +
        'PROVEN is withheld',
    );
  });

  it('covers all three VC labels', () => {
    for (const vc of ['initiation (VC1)', 'consecution (VC2)', 'safety (VC3)'] as const) {
      const reason = certificateDowngradeReason({
        type: 'failed', vc, detail: 'solver returned UNKNOWN (timeout)', invariant: 'true',
      });
      expect(reason).toBe(
        `certificate check failed: ${vc} was not UNSAT - solver returned UNKNOWN ` +
          '(timeout); the IC3 certificate could not be independently re-validated ' +
          'against the unstrengthened step relation, so PROVEN is withheld',
      );
    }
  });

  it('an unavailable check withholds PROVEN without implicating a VC', () => {
    const outcome: CertificateCheckOutcome = {
      type: 'unavailable',
      reason: 'invariant missing (Z3 produced no inductive-invariant answer)',
      invariant: null,
    };
    expect(certificateDowngradeReason(outcome)).toBe(
      'certificate check could not run: invariant missing (Z3 produced no ' +
        'inductive-invariant answer); PROVEN is withheld without an independently ' +
        'validated certificate',
    );
  });
});

describe('assessCounterexample', () => {
  /** A -> B -> C -> ... chain net. */
  function chainNet(...names: string[]) {
    const places = names.map(n => place(n));
    const transitions = [];
    for (let i = 0; i + 1 < places.length; i++) {
      transitions.push(
        Transition.builder(`T${i}`).inputs(one(places[i]!)).outputs(outPlace(places[i + 1]!)).build(),
      );
    }
    const flatNet = flatten(PetriNet.builder('Chain').transitions(...transitions).build());
    const m0 = MarkingState.builder().tokens(places[0]!, 1).build();
    return { places, flatNet, m0 };
  }

  it('confirms a chain and returns it in firing order', () => {
    const { places, flatNet, m0 } = chainNet('A', 'B', 'C');
    const assessment = assessCounterexample(
      flatNet, m0, new Set([m0]), placeBound(places[2]!, 0), NO_SINKS,
    );
    expect(assessment.kind).toBe('confirmed');
    if (assessment.kind === 'confirmed') {
      expect(assessment.firings).toEqual(['T0', 'T1']);
      expect(assessment.trace.map(String)).toEqual(['{A:1}', '{B:1}', '{C:1}']);
    }
  });

  it('labels an injection step inject(<place>)', () => {
    const e = environmentPlace('E');
    const out = place('OUT');
    const t = Transition.builder('T').inputs(one(e.place)).outputs(outPlace(out)).build();
    const flatNet = flatten(
      PetriNet.builder('EnvNet').transitions(t).build(), new Set([e]), bounded(2),
    );
    const m0 = MarkingState.empty();

    const assessment = assessCounterexample(
      flatNet, m0, new Set([m0]), placeBound(out, 0), NO_SINKS,
    );
    expect(assessment.kind).toBe('confirmed');
    if (assessment.kind === 'confirmed') {
      expect(assessment.firings).toEqual(['inject(E)', 'T']);
    }
  });

  it('nothing decoded leaves the verdict standing, unconfirmed', () => {
    const { places, flatNet, m0 } = chainNet('A', 'B');
    const assessment = assessCounterexample(
      flatNet, m0, new Set(), placeBound(places[1]!, 0), NO_SINKS,
    );
    expect(assessment.kind).toBe('unconfirmed');
    if (assessment.kind === 'unconfirmed') {
      expect(assessment.note).toBe(
        'no counterexample states could be decoded from the Spacer answer, so the ' +
          'abstract replay could not run',
      );
    }
  });

  it('a truncated search leaves the verdict standing, unconfirmed', () => {
    const { places, flatNet, m0 } = chainNet('A', 'B', 'C', 'D', 'E');
    const assessment = assessCounterexample(
      flatNet, m0, new Set([m0]), placeBound(places[4]!, 0), NO_SINKS,
    );
    expect(assessment.kind).toBe('unconfirmed');
    if (assessment.kind === 'unconfirmed') {
      expect(assessment.note).toMatch(/^abstract replay did not complete: /);
    }
  });

  it('M0 absent from the decoded set leaves the verdict standing, unconfirmed', () => {
    const { places, flatNet, m0 } = chainNet('A', 'B', 'C');
    const elsewhere = MarkingState.builder().tokens(places[1]!, 1).build();
    const assessment = assessCounterexample(
      flatNet, m0, new Set([elsewhere]), placeBound(places[2]!, 0), NO_SINKS,
    );
    expect(assessment.kind).toBe('unconfirmed');
    if (assessment.kind === 'unconfirmed') {
      expect(assessment.note).toContain('initial marking is not among the decoded states');
    }
  });

  it('a completed search with no chain downgrades, with the canonical reason', () => {
    const { places, flatNet, m0 } = chainNet('A', 'B');
    const assessment = assessCounterexample(
      flatNet, m0, new Set([m0]), placeBound(places[1]!, 5), NO_SINKS,
    );
    expect(assessment.kind).toBe('downgraded');
    if (assessment.kind === 'downgraded') {
      expect(assessment.reason).toBe(
        'counterexample replay found no firing chain to the violation under the ' +
          'abstract semantics, so VIOLATED is withheld',
      );
    }
  });
});
