import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, terminatesAtSink } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import { encode, encodePropertyViolation, resolveEnvInjection } from '../../src/verification/z3/smt-encoder.js';
import { satisfiesBad, vectorize } from '../../src/verification/z3/abstract-replayer.js';
import { describeSinks, strandingExcuses, strandsToken } from '../../src/verification/rest-set.js';
import { verifyViaNameScg } from '../../src/verification/nu-scg-verifier.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace, xor, and } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';
import { verificationNets } from '../fixtures/verification-nets.js';

/**
 * VER-014 conditional sinks: a token may rest in a place while a marker is marked.
 *
 * The net: p0(1) → t → AND(a, b); a → ta → done; b → tb → done unless `halt` is
 * marked; a → h → halt (an XOR alternative to ta). Reachable quiescent markings:
 * {done:2}, {halt:1, done:1}, {halt:1, b:1}. The last one is the designed terminal
 * that a plain sink declaration cannot excuse: `b` holds pending work the halt
 * legitimately stopped.
 */
function haltNet() {
  const p0 = place('p0'), a = place('a'), b = place('b'), done = place('done'), halt = place('halt');
  const t = Transition.builder('t').inputs(one(p0)).outputs(andPlaces(a, b)).action(produces()).build();
  const ta = Transition.builder('ta').inputs(one(a)).outputs(xor(outPlace(done), outPlace(halt))).action(produces()).build();
  const tb = Transition.builder('tb').inputs(one(b)).inhibitor(halt).outputs(outPlace(done)).action(produces()).build();
  const net = PetriNet.builder('haltNet').transitions(t, ta, tb).build();
  const m0 = MarkingState.builder().tokens(p0, 1).build();
  return { net, m0, p0, a, b, done, halt };
}

describe('conditional sinks (VER-014) — rest set', () => {
  it('strandingExcuses: sinks and markers never strand; conditional places name their markers', () => {
    const { net, done, halt, b } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (p: { name: string }) => flat.placeIndex.get(p.name)!;
    const ex = strandingExcuses(flat, new Set([done]), [{ marker: halt, places: new Set([b]) }]);
    expect(ex[idx(done)]).toBeNull();
    expect(ex[idx(halt)]).toBeNull();
    expect(ex[idx(b)]).toEqual([idx(halt)]);
    expect(ex[idx(place('a'))]).toEqual([]);
    expect(ex[idx(place('p0'))]).toEqual([]);
  });

  it('strandingExcuses: two markers excusing one place are listed in place-index order, once each', () => {
    const { net, halt, b } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (p: { name: string }) => flat.placeIndex.get(p.name)!;
    const done = place('done');
    const ex = strandingExcuses(flat, new Set(), [
      { marker: halt, places: new Set([b]) },
      { marker: done, places: new Set([b]) },
      { marker: halt, places: new Set([b]) },
    ]);
    expect(ex[idx(b)]).toEqual([idx(done), idx(halt)].sort((x, y) => x - y));
  });

  it('strandingExcuses: an unresolved marker or place contributes nothing', () => {
    const { net, b } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const ghost = place('ghost');
    const ex = strandingExcuses(flat, new Set([ghost]), [{ marker: ghost, places: new Set([b, ghost]) }]);
    expect(ex[flat.placeIndex.get(b.name)!]).toEqual([]);
  });

  it('strandsToken: the marker excuses its places only while marked', () => {
    const { b, done, halt } = haltNet();
    const cond = [{ marker: halt, places: new Set([b]) }];
    const sinks = new Set([done]);
    expect(strandsToken(MarkingState.builder().tokens(halt, 1).tokens(b, 1).build(), sinks, cond)).toBe(false);
    expect(strandsToken(MarkingState.builder().tokens(b, 1).build(), sinks, cond)).toBe(true);
    expect(strandsToken(MarkingState.builder().tokens(halt, 1).tokens(place('a'), 1).build(), sinks, cond)).toBe(true);
    expect(strandsToken(MarkingState.builder().tokens(halt, 1).build(), sinks, cond)).toBe(false);
    expect(strandsToken(MarkingState.builder().tokens(done, 2).build(), sinks, cond)).toBe(false);
    expect(strandsToken(MarkingState.empty(), sinks, cond)).toBe(false);
  });

  it('describeSinks renders declarations in order', () => {
    const a = place('a'), b = place('b'), h = place('h'), p = place('p');
    expect(describeSinks(new Set(), [])).toBeNull();
    expect(describeSinks(new Set([a, b]), [])).toBe('sinks: a, b');
    expect(describeSinks(new Set([a]), [{ marker: h, places: new Set([b]) }, { marker: p, places: new Set() }]))
      .toBe('sinks: a; when h: b; when p');
    expect(describeSinks(new Set(), [{ marker: h, places: new Set([a, b]) }])).toBe('when h: a, b');
  });
});

describe('conditional sinks (VER-014) — encoder and replay agree', () => {
  it('the flat encoder conjoins the marker being unmarked into the stranded disjunct', () => {
    const { net, b, done, halt } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const mVars = flat.places.map((_, i) => `m${i}`);
    const idx = (p: { name: string }) => flat.placeIndex.get(p.name)!;
    const bad = encodePropertyViolation(
      flat, deadlockFree(), mVars, new Set([done]), resolveEnvInjection(flat),
      [{ marker: halt, places: new Set([b]) }],
    );
    expect(bad).toContain(`(and (>= m${idx(b)} 1) (= m${idx(halt)} 0))`);
    expect(bad).not.toContain(`(>= m${idx(done)} 1)`);
    expect(bad).not.toContain(`(>= m${idx(halt)} 1)`);
    // Without the declaration the same place is an unconditional disjunct.
    const plain = encodePropertyViolation(flat, deadlockFree(), mVars, new Set([done]), resolveEnvInjection(flat));
    expect(plain).toContain(`(>= m${idx(b)} 1)`);
    expect(plain).toContain(`(>= m${idx(halt)} 1)`);
  });

  it('encode() without conditional sinks is byte-identical to before', () => {
    const { net, m0, done } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const before = encode(flat, m0, deadlockFree(), [], new Set([done]), false);
    const after = encode(flat, m0, deadlockFree(), [], new Set([done]), false, []);
    expect(after.smt2).toBe(before.smt2);
  });

  it('the replayer reads the same predicate the encoder emits', () => {
    const { net, b, done, halt } = haltNet();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const cond = [{ marker: halt, places: new Set([b]) }];
    const haltedWithB = vectorize(MarkingState.builder().tokens(halt, 1).tokens(b, 1).build(), flat);
    const haltedWithA = vectorize(MarkingState.builder().tokens(halt, 1).tokens(place('a'), 1).build(), flat);
    // {halt:1, b:1} is quiescent (tb is inhibited): stranded without the excuse, at rest with it.
    expect(satisfiesBad(haltedWithB, flat, deadlockFree(), new Set([done]))).toBe(true);
    expect(satisfiesBad(haltedWithB, flat, deadlockFree(), new Set([done]), cond)).toBe(false);
    // {halt:1, a:1} is not quiescent (ta can fire), so never a violation.
    expect(satisfiesBad(haltedWithA, flat, deadlockFree(), new Set([done]), cond)).toBe(false);
    // TerminatesAtSink ignores the conditional declaration.
    expect(satisfiesBad(haltedWithB, flat, terminatesAtSink(), new Set([done]), cond)).toBe(true);
  });

  it('Route B decides the same predicate on a ν-net', () => {
    // nuMixedTerminal quiesces at {done:1, stuck:1}: violated with `done` a plain sink,
    // proven once `stuck` may rest while `done` is marked.
    const built = verificationNets['nuMixedTerminal']!();
    const m0 = MarkingState.builder();
    built.initialMarking(m0);
    const done = built.places.get('done')!;
    const stuck = built.places.get('stuck')!;
    const run = (cond: { marker: typeof done; places: Set<typeof done> }[]) => verifyViaNameScg(
      built.net, m0.build(), deadlockFree(), new Set([done]), new Set(), alwaysAvailable(),
      10_000, 'base', new Set(), 'none', cond,
    );
    expect(run([])!.verdict.type).toBe('violated');
    expect(run([{ marker: done, places: new Set([stuck]) }])!.verdict.type).toBe('proven');
  });
});

describeZ3('conditional sinks (VER-014) — end to end', () => {
  it('a halt that strands pending work is a violation until the work is excused under the halt', async () => {
    const { net, m0, b, done, halt } = haltNet();
    const base = () => SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0).property(deadlockFree()).sinkPlaces(done).timeout(30_000);

    const plain = await base().verify();
    expect(plain.verdict.type, plain.report).toBe('violated');
    expect(plain.counterexampleConfirmed).toBe(true);
    const witness = plain.counterexampleTrace.at(-1)!;
    expect(witness.tokens(halt)).toBe(1);

    // The marker alone: halt is at rest, b is still stranded under it.
    const markerOnly = await base().sinkPlacesWhen(halt).verify();
    expect(markerOnly.verdict.type, markerOnly.report).toBe('violated');
    expect(markerOnly.counterexampleTrace.at(-1)!.tokens(b)).toBe(1);

    // b may rest while halted: nothing is stranded in any quiescent marking.
    const excused = await base().sinkPlacesWhen(halt, b).verify();
    expect(excused.verdict.type, excused.report).toBe('proven');
    expect(excused.report).toContain('Property: Deadlock-freedom (sinks: done; when halt: b)');

    // TerminatesAtSink reads only the unconditional sinks: {halt:1, b:1} marks none.
    const reaches = await base().property(terminatesAtSink()).sinkPlacesWhen(halt, b).verify();
    expect(reaches.verdict.type, reaches.report).toBe('violated');
  });

  it('a marker that is not marked at quiescence excuses nothing', async () => {
    const built = verificationNets['deadEndChain']!();
    const p0 = built.places.get('p0')!;
    const p2 = built.places.get('p2')!;
    const base = () => SmtVerifier.forNet(built.net)
      .enumerationMaxClasses(0).initialMarking(built.initialMarking).property(deadlockFree()).timeout(30_000);
    // p0 is empty by the time the chain quiesces at {p2:1}.
    const unmarked = await base().sinkPlacesWhen(p0, p2).verify();
    expect(unmarked.verdict.type, unmarked.report).toBe('violated');
    // p2 as its own marker: the resting token is the designed terminal.
    const marker = await base().sinkPlacesWhen(p2).verify();
    expect(marker.verdict.type, marker.report).toBe('proven');
    expect(marker.report).toContain('Property: Deadlock-freedom (when p2)');
  });
});
