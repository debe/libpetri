import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, mutualExclusion, unreachable } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import {
  encode, encodeNet, encodeStepRelationSmt2, equationPlaces, stateEquationConditions,
} from '../../src/verification/z3/smt-encoder.js';
import { decodeStateSet } from '../../src/verification/z3/counterexample-decoder.js';
import { vcScript } from '../../src/verification/z3/certificate-checker.js';
import { placeholderCertificate } from '../../src/verification/smt-verifier.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { one, all } from '../../src/core/in.js';
import { andPlaces, outPlace, xor } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * VER-016 state equation with firing counters.
 *
 * The fork-or-halt net of the VER-015 tests: p0(1) → f → AND(a, b) | halt; a → ga → ra;
 * b → gb → rb; ra + rb → join → done. Places in flat order: a, b, done, halt, p0, ra, rb.
 */
function forkOrHalt() {
  const p0 = place('p0'), a = place('a'), b = place('b'), ra = place('ra'), rb = place('rb');
  const halt = place('halt'), done = place('done');
  const f = Transition.builder('f').inputs(one(p0)).outputs(xor(andPlaces(a, b), outPlace(halt))).action(produces()).build();
  const ga = Transition.builder('ga').inputs(one(a)).outputs(outPlace(ra)).action(produces()).build();
  const gb = Transition.builder('gb').inputs(one(b)).outputs(outPlace(rb)).action(produces()).build();
  const join = Transition.builder('join').inputs(one(ra), one(rb)).outputs(outPlace(done)).action(produces()).build();
  const net = PetriNet.builder('forkOrHalt').transitions(f, ga, gb, join).build();
  const m0 = MarkingState.builder().tokens(p0, 1).build();
  return { net, m0, p0, a, b, ra, rb, halt, done };
}

describe('state equation (VER-016) — encoding', () => {
  it('is off by default and byte-identical to the positional encode()', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const prop = unreachable(new Set([ra, rb, halt]));
    const positional = encode(flat, m0, prop, [], new Set(), true);
    const named = encodeNet(flat, m0, prop, [], { produceProofs: true });
    expect(named.smt2).toBe(positional.smt2);
    expect(named.counterCount).toBe(0);
  });

  it('adds one counter per flat transition, zero at the start, incremented by its own rule', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const P = flat.places.length;
    const T = flat.transitions.length; // f expands to two flat transitions
    expect(T).toBe(5);
    const enc = encodeNet(flat, m0, unreachable(new Set([ra, rb, halt])), [], { stateEquation: true });
    expect(enc.counterCount).toBe(T);
    expect(enc.smt2).toContain(`(declare-fun Reachable (${new Array(P + T).fill('Int').join(' ')}) Bool)`);
    // Init: M0 then T zeros.
    const m0Line = enc.smt2.split('\n').find(l => l.startsWith('(assert (Reachable '))!;
    expect(m0Line.trim().split(' ').length - 2).toBe(P + T);
    expect(m0Line.endsWith(' 0 0 0 0 0))')).toBe(true);
    // Rule k increments n_k and copies the others; counters are non-negative.
    expect(enc.smt2).toContain('(= n0p (+ n0 1))');
    expect(enc.smt2).toContain('(= n1p n1)');
    expect(enc.smt2).toContain('(>= n4p 0)');
    // Counters are quantified in every rule and unconstrained in the error rule.
    expect(enc.smt2).toContain('(n0 Int)');
    expect(enc.smt2).toContain('(n0p Int)');
    const errorRule = enc.smt2.slice(enc.smt2.lastIndexOf('(assert (forall'));
    expect(errorRule).toContain(`(Reachable ${[...Array(P).keys()].map(i => `m${i}`).join(' ')} n0 n1 n2 n3 n4)`);
    expect(errorRule).not.toContain('n0p');
  });

  it('conjoins the marking equation over every exact place, in transition order', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (n: string) => flat.placeIndex.get(n)!;
    const conds = stateEquationConditions(flat, m0, ['n0', 'n1', 'n2', 'n3', 'n4'], flat.places.map((_, i) => `m${i}`));
    expect(conds).toHaveLength(flat.places.length);
    // f's branches are flat transitions 0 (AND(a,b)) and 1 (halt), in enumeration order.
    expect(conds).toContain(`(= m${idx('p0')} (+ 1 (- n0) (- n1)))`);
    expect(conds).toContain(`(= m${idx('halt')} (+ 0 n1))`);
    expect(conds).toContain(`(= m${idx('a')} (+ 0 n0 (- n2)))`);
    expect(conds).toContain(`(= m${idx('done')} (+ 0 n4))`);
    // The encoding carries them over the primed variables in every transition rule.
    const enc = encodeNet(flat, m0, unreachable(new Set([ra, rb, halt])), [], { stateEquation: true });
    expect(enc.smt2.split(`(= m${idx('p0')}p (+ 1 (- n0p) (- n1p)))`).length - 1).toBe(5);
  });

  it('leaves consume-all and injected places out of the equation', () => {
    const q = place('q'), r = place('r'), s = place('s');
    const env = environmentPlace('env');
    const t = Transition.builder('t').inputs(all(q)).outputs(outPlace(r)).action(produces()).build();
    const u = Transition.builder('u').inputs(one(env.place)).outputs(outPlace(s)).action(produces()).build();
    const net = PetriNet.builder('mixed').transitions(t, u).build();
    const flat = flatten(net, new Set([env]), alwaysAvailable());
    const exact = equationPlaces(flat).map(p => flat.places[p]!.name);
    expect(exact).toEqual(['r', 's']);
    const enc = encodeNet(flat, MarkingState.builder().tokens(q, 2).build(), mutualExclusion(r, s), [], { stateEquation: true });
    expect(enc.smt2).not.toContain(`(= m${flat.placeIndex.get('q')}p (+ 2`);
    expect(enc.smt2).not.toContain(`(= m${flat.placeIndex.get('env')}p (+ 0`);
    // The injection rule carries the counters unchanged.
    expect(enc.smt2).toContain('(= n0p n0)\n            (= n1p n1)');
  });

  it('the raw step relation moves the counters but carries no equation', () => {
    const { net } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const step = encodeStepRelationSmt2(flat, true);
    expect(step).toContain('(= n2p (+ n2 1))');
    expect(step).not.toContain('(+ 1 (- n0p) (- n1p))');
    expect(encodeStepRelationSmt2(flat)).not.toContain('n0');
  });

  it('the certificate candidate re-states the equation and the VCs range over the counters', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const P = flat.places.length;
    const script = vcScript(placeholderCertificate(P + 5), flat, m0, unreachable(new Set([ra, rb, halt])), new Set(), [], [], true);
    expect(script).toContain('(declare-const n4 Int)');
    expect(script).toContain('(declare-const n4p Int)');
    expect(script).toContain(`(= m${flat.placeIndex.get('p0')} (+ 1 (- n0) (- n1)))`);
    expect(script).toContain(`(= m${flat.placeIndex.get('p0')}p (+ 1 (- n0p) (- n1p)))`);
    expect(script).toContain('(>= n0 0)');
  });

  it('the decoder reads the marking from the leading places of a counter-carrying fact', () => {
    const { net, a, b } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const P = flat.places.length;
    const fact = `(Reachable ${[...Array(P).keys()].map(i => (flat.places[i]!.name === 'a' || flat.places[i]!.name === 'b' ? '1' : '0')).join(' ')} 1 0 0 0 0)`;
    const plain = decodeStateSet(fact, flat);
    expect(plain.size).toBe(0);
    const withCounters = decodeStateSet(fact, flat, 5);
    expect(withCounters.size).toBe(1);
    const m = [...withCounters][0]!;
    expect(m.tokens(a)).toBe(1);
    expect(m.tokens(b)).toBe(1);
    expect(m.placesWithTokens().length).toBe(2);
  });
});

describeZ3('state equation (VER-016) — end to end', () => {
  it('a proven deadlock-freedom keeps its verdict and passes the certificate check', async () => {
    const { net, m0, done, halt, ra, rb } = forkOrHalt();
    const result = await SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(done, halt).stateEquation(true).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.report).toContain('State equation: encoded over 5 firing counters (VER-016)');
    expect(result.report).toContain('Certificate check: PASSED (init, consecution, safety)');
    void ra; void rb;
  });

  it('a genuine violation stays violated and its counterexample replays', async () => {
    const { net, m0, done } = forkOrHalt();
    const result = await SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(done).stateEquation(true).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTrace.at(-1)!.tokens(place('halt'))).toBe(1);
  });

  it('encodeScripts() reflects the option', () => {
    const { net, m0, done } = forkOrHalt();
    const off = SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0).property(deadlockFree()).sinkPlaces(done).encodeScripts();
    const on = SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0).property(deadlockFree()).sinkPlaces(done).stateEquation(true).encodeScripts();
    expect(off.horn).not.toContain('n0p');
    expect(on.horn).toContain('n0p');
    expect(on.certificate).toContain('(x!7 Int)');
    expect(off.certificate).not.toContain('(x!7 Int)');
  });
});
