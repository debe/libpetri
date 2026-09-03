import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one, atLeast } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import type { FlatNet } from '../../src/verification/encoding/flat-net.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import {
  canonicalInvariantOrder, computePInvariants, computePSemiflows, validateInvariantsExact,
} from '../../src/verification/invariant/p-invariant-computer.js';
import { alwaysAvailable, bounded, ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import {
  branchPlaceBound, deadlockFree, mutualExclusion, placeBound, unreachable,
} from '../../src/verification/smt-property.js';
import { encode } from '../../src/verification/z3/smt-encoder.js';
import { vcScript } from '../../src/verification/z3/certificate-checker.js';
import { buildColouredPlan, encodeColoured } from '../../src/verification/z3/name-coloured-encoder.js';

/**
 * VER-013 AC1: the scripts this verifier sends to z3 are byte-identical to the Rust
 * reference. The goldens under `tests/fixtures/smt-golden/` were written by the Rust
 * verifier (`LIBPETRI_SMT_DUMP`) for the nets rebuilt here; a diff is a parity
 * finding in whichever emitter drifted, never a reason to edit the golden.
 *
 * No solver is needed: the encoders are pure text.
 */
const GOLDEN_DIR = join(dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'smt-golden');

function golden(name: string): string {
  return readFileSync(join(GOLDEN_DIR, name), 'utf8');
}

/** The certificate block a golden certificate script carries (its third block). */
function certificateOf(script: string): string {
  const start = script.indexOf('(define-fun');
  const end = script.indexOf('\n\n(declare-const');
  return script.slice(start, end);
}

/** The invariants exactly as the verifier hands them to the encoders. */
function encoderInvariants(flat: FlatNet, m0: MarkingState) {
  const matrix = IncidenceMatrix.from(flat);
  return canonicalInvariantOrder(validateInvariantsExact(matrix, computePInvariants(matrix, flat, m0), flat, m0).valid);
}

function validatedSemiflows(flat: FlatNet, m0: MarkingState) {
  const matrix = IncidenceMatrix.from(flat);
  return validateInvariantsExact(matrix, computePSemiflows(matrix, flat, m0), flat, m0).valid;
}

describe('SMT script parity with the Rust reference (VER-013 AC1)', () => {
  it('chain: p0(1) -> p1, placeBound(p1, 0)', () => {
    const p0 = place('p0');
    const p1 = place('p1');
    const t = Transition.builder('t').inputs(one(p0)).outputs(outPlace(p1)).build();
    const flat = flatten(PetriNet.builder('chain').transitions(t).build(), new Set(), ignore());
    const m0 = MarkingState.builder().tokens(p0, 1).build();
    const encoding = encode(flat, m0, placeBound(p1, 0), encoderInvariants(flat, m0), new Set(), true);
    expect(encoding.smt2).toBe(golden('chain-horn.smt2'));
  });

  // arcs: inhibitor + read + reset + at-least + sink + env injection
  const A = place('A');
  const B = place('B');
  const C = place('C');
  const R = place('R');
  const S = place('S');
  const E = environmentPlace('E');

  function arcsNet(): PetriNet {
    const t1 = Transition.builder('t1')
      .inputs(one(A), one(E.place))
      .inhibitors(B)
      .reads(C)
      .resets(R)
      .outputs(outPlace(S))
      .build();
    const t2 = Transition.builder('t2').inputs(atLeast(1, B)).outputs(andPlaces(A, R)).build();
    return PetriNet.builder('arcs').transitions(t1, t2).build();
  }

  it('arcs: deadlockFree with a sink and alwaysAvailable injection', () => {
    const flat = flatten(arcsNet(), new Set([E]), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(A, 1).tokens(C, 1).tokens(B, 2).build();
    const invariants = encoderInvariants(flat, m0);
    const sinks = new Set<Place<any>>([S]);
    expect(encode(flat, m0, deadlockFree(), invariants, sinks, true).smt2).toBe(golden('arcs-horn.smt2'));
    const cert = golden('arcs-certificate.smt2');
    expect(vcScript(certificateOf(cert), flat, m0, deadlockFree(), sinks, invariants)).toBe(cert);
  });

  it('arcs: unreachable with bounded(2) injection', () => {
    const flat = flatten(arcsNet(), new Set([E]), bounded(2));
    const m0 = MarkingState.builder().tokens(A, 1).build();
    const invariants = encoderInvariants(flat, m0);
    const property = unreachable(new Set([S, A]));
    expect(encode(flat, m0, property, invariants, new Set(), true).smt2).toBe(golden('unreach-horn.smt2'));
    const cert = golden('unreach-certificate.smt2');
    expect(vcScript(certificateOf(cert), flat, m0, property, new Set(), invariants)).toBe(cert);
  });

  it('mutex: mutual exclusion on a one-token cycle', () => {
    const x = place('X');
    const y = place('Y');
    const xy = Transition.builder('XtoY').inputs(one(x)).outputs(outPlace(y)).build();
    const yx = Transition.builder('YtoX').inputs(one(y)).outputs(outPlace(x)).build();
    const flat = flatten(PetriNet.builder('cycle').transitions(xy, yx).build(), new Set(), ignore());
    const m0 = MarkingState.builder().tokens(x, 1).build();
    const invariants = encoderInvariants(flat, m0);
    // Listed Y-first on purpose: the script orders the places by index.
    const property = mutualExclusion(y, x);
    expect(encode(flat, m0, property, invariants, new Set(), true).smt2).toBe(golden('mutex-horn.smt2'));
    const cert = golden('mutex-certificate.smt2');
    expect(vcScript(certificateOf(cert), flat, m0, property, new Set(), invariants)).toBe(cert);
  });

  it('nu scatter-gather with a declared budget: the name-coloured encoder', () => {
    const source = place('source');
    const budget = place('budget');
    const pending = place('pending');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const merged = place<string>('merged');
    const fork = Transition.builder('fork')
      .inputs(one(source), one(budget))
      .outputs(andPlaces(a, b, pending))
      .build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b), one(pending))
      .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
      .outputs(andPlaces(merged, budget))
      .build();
    const net = PetriNet.builder('nu').transitions(fork, join).build();
    const flat = flatten(net, new Set(), ignore());
    const m0 = MarkingState.builder().tokens(source, 3).tokens(budget, 2).build();
    const plan = buildColouredPlan(net, flat, m0, new Set(['budget']), 'base', new Set(), validatedSemiflows(flat, m0));
    expect(plan, 'the scatter-gather net is in the coloured fragment').not.toBeNull();
    const encoding = encodeColoured(plan!, flat, m0, branchPlaceBound(budget, 2), encoderInvariants(flat, m0), new Set());
    expect(encoding).not.toBeNull();
    expect(encoding!.smt2).toBe(golden('nu-bound-horn-coloured.smt2'));
  });
});
