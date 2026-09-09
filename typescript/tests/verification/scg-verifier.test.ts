import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier, assessCounterexample } from '../../src/verification/smt-verifier.js';
import { rethrowIfProgrammingError } from '../../src/verification/programming-error.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { deadlockFree, placeBound, unreachable } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { isUntimed, verifyViaStateClassGraph } from '../../src/verification/scg-verifier.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { all, exactly, one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed } from '../../src/core/timing.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * VER-017 bounded state-space enumeration.
 *
 * A pipeline `p0 -> t0 -> p1 -> t1 -> … -> pn`: the reachable state space is one
 * class per stage, but its *diameter* is the length, which is what makes the
 * fixpoint search expensive and enumeration trivial.
 */
function pipeline(n: number, opts: { timed?: boolean } = {}) {
  const places = [place('p0')];
  const transitions = [];
  for (let i = 0; i < n; i++) {
    const next = place(`p${i + 1}`);
    places.push(next);
    const b = Transition.builder(`t${i}`).inputs(one(places[i]!)).outputs(outPlace(next)).action(produces());
    transitions.push((opts.timed === true ? b.timing(delayed(10)) : b).build());
  }
  const net = PetriNet.builder(`pipeline${n}`).transitions(...transitions).build();
  return { net, places, m0: MarkingState.builder().tokens(places[0]!, 1).build() };
}

describe('bounded state-space enumeration (VER-017) — route', () => {
  it('decides deadlock-freedom exactly, with no solver at all', async () => {
    const { net, places, m0 } = pipeline(6);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[6]!).timeout(30_000).verify();

    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('state-space enumeration (VER-017)');
    expect(result.report).toContain('=== Bounded state-space enumeration (VER-017) ===');
    expect(result.report).toContain('  State classes: 7');
    // No solver phase ran at all.
    expect(result.report).not.toContain('Phase 4: IC3/PDR');
    expect(result.report).not.toContain('Solver: z3');
  });

  it('reports a violation with a real firing sequence', async () => {
    // The token comes to rest in p6, which is NOT declared a sink: stranded.
    const { net, m0 } = pipeline(6);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).timeout(30_000).verify();

    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTransitions).toEqual(['t0', 't1', 't2', 't3', 't4', 't5']);
    expect(result.counterexampleTrace.at(-1)!.tokens(place('p6'))).toBe(1);
  });

  it('decides reachability-safety over the same graph', async () => {
    const { net, places, m0 } = pipeline(4);
    const bound = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(placeBound(places[4]!, 1)).timeout(30_000).verify();
    expect(bound.verdict.type, bound.report).toBe('proven');

    const unreach = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(unreachable(new Set([places[0]!, places[4]!]))).timeout(30_000).verify();
    expect(unreach.verdict.type, unreach.report).toBe('proven');
  });

  it('declines past its class budget and says so, leaving the SMT pipeline to answer', async () => {
    const { net, places, m0 } = pipeline(6);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[6]!)
      .enumerationMaxClasses(3) // the graph has 7 classes
      .timeout(30_000).verify();
    expect(result.report).toContain('Bounded state-space enumeration truncated at 3 classes');
    expect(result.report).toContain('Phase 1: Flattening net...');
  });

  it('enumerationMaxClasses(0) turns the route off', async () => {
    const { net, places, m0 } = pipeline(4);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[4]!)
      .enumerationMaxClasses(0).timeout(30_000).verify();
    expect(result.report).not.toContain('Bounded state-space enumeration');
    expect(result.report).toContain('Phase 1: Flattening net...');
  });

  it('is skipped on a timed net, whose enumeration would be the weaker timed claim', async () => {
    const timed = pipeline(4, { timed: true });
    expect(isUntimed(timed.net)).toBe(false);
    expect(isUntimed(pipeline(4).net)).toBe(true);

    const result = await SmtVerifier.forNet(timed.net).initialMarking(timed.m0)
      .property(deadlockFree()).sinkPlaces(timed.places[4]!).timeout(30_000).verify();
    expect(result.report).not.toContain('Bounded state-space enumeration');
  });

  it('is skipped when environment places are registered', async () => {
    const inp = environmentPlace<string>('IN');
    const out = place<string>('OUT');
    const t = Transition.builder('T').inputs(one(inp.place)).outputs(outPlace(out)).action(produces()).build();
    const net = PetriNet.builder('env').transitions(t).build();
    const result = await SmtVerifier.forNet(net).initialMarking(MarkingState.empty())
      .property(placeBound(out, 5))
      .environmentPlaces(inp).environmentMode(alwaysAvailable())
      .timeout(30_000).verify();
    expect(result.report).not.toContain('Bounded state-space enumeration');
  });

  it('names the deciding route and says invariants were not computed', async () => {
    // A consumer reading fields rather than the report must be able to tell why
    // `invariants` is empty: not computed on this route, rather than none exist.
    const { net, places, m0 } = pipeline(4);
    const enumerated = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[4]!).timeout(30_000).verify();
    expect(enumerated.route).toBe('enumeration');
    expect(enumerated.invariants).toEqual([]);
    expect(enumerated.report).toContain('  P-invariants: not computed (no encoding is built on this route)');

    const solved = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[4]!)
      .enumerationMaxClasses(0).timeout(30_000).verify();
    expect(solved.route).not.toBe('enumeration');
  });

  it('an enumeration counterexample is ordered, so it reports as confirmed', async () => {
    // The graph path is a firing sequence: nothing to replay, and a consumer
    // keying "are these steps ordered" off the field gets the right answer.
    const { net, m0 } = pipeline(4);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).timeout(30_000).verify();
    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTransitions).toEqual(['t0', 't1', 't2', 't3']);
  });

  it('the route function itself reports truncation rather than a verdict', () => {
    const { net, places, m0 } = pipeline(6);
    const truncated = verifyViaStateClassGraph(net, m0, deadlockFree(), new Set([places[6]!]), 3);
    expect(truncated.kind).toBe('truncated');
    const decided = verifyViaStateClassGraph(net, m0, deadlockFree(), new Set([places[6]!]), 1000);
    expect(decided.kind).toBe('decided');
    expect(decided.kind === 'decided' && decided.verdict.type).toBe('proven');
  });
});

describeZ3('bounded state-space enumeration (VER-017) — agrees with the solver', () => {
  it('both routes return the same verdict on the same net', async () => {
    const { net, places, m0 } = pipeline(5);
    for (const [prop, sinks] of [
      [deadlockFree(), [places[5]!]],
      [placeBound(places[5]!, 1), []],
    ] as const) {
      const enumerated = await SmtVerifier.forNet(net).initialMarking(m0)
        .property(prop).sinkPlaces(...sinks).timeout(30_000).verify();
      const solved = await SmtVerifier.forNet(net).initialMarking(m0)
        .property(prop).sinkPlaces(...sinks).enumerationMaxClasses(0).timeout(30_000).verify();
      expect(enumerated.report).toContain('Bounded state-space enumeration');
      expect(solved.report).not.toContain('Bounded state-space enumeration');
      expect(enumerated.verdict.type, `${enumerated.report}\n---\n${solved.report}`).toBe(solved.verdict.type);
    }
  });
});

// An open net never comes to rest, so a quiescence property there is vacuously
// true. The verdict is correct and says nothing; the report must say which.
describeZ3('open nets and vacuous quiescence (VER-006)', () => {
  function openNet() {
    const src = environmentPlace<number>('src');
    const inp = place('in'), done = place('done');
    const trigger = Transition.builder('trigger').inputs(one(src.place))
      .outputs(outPlace(inp)).action(produces()).build();
    const step = Transition.builder('step').inputs(one(inp))
      .outputs(outPlace(done)).action(produces()).build();
    return { net: PetriNet.builder('open').transitions(trigger, step).build(), src, done };
  }

  it('warns that a quiescence property is vacuous when nothing can ever be quiescent', async () => {
    const { net, src, done } = openNet();
    const result = await SmtVerifier.forNet(net).initialMarking(MarkingState.empty())
      .property(deadlockFree()).sinkPlaces(done)
      .environmentPlaces(src).environmentMode(alwaysAvailable())
      .enumerationMaxClasses(0).timeout(30_000).verify();

    // True, but only because the trigger is always enabled — never a deadlock.
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.report).toContain('NOTE: no marking of this net can be quiescent');
  });

  it('says nothing of the kind for a closed net, whose quiescence is real', async () => {
    const { net, places, m0 } = pipeline(3);
    const result = await SmtVerifier.forNet(net).initialMarking(m0)
      .property(deadlockFree()).sinkPlaces(places[3]!)
      .enumerationMaxClasses(0).timeout(30_000).verify();
    expect(result.report).not.toContain('no marking of this net can be quiescent');
  });
});

// A catch that degrades a result must not launder a defect into a verdict: once a
// bug and a real limitation arrive as the same `Unknown`, the bug is invisible.
describe('programming errors are never verdicts', () => {
  it('re-throws a TypeError and a ReferenceError, and passes everything else through', () => {
    expect(() => rethrowIfProgrammingError(new TypeError('x is not a function'))).toThrow(TypeError);
    expect(() => rethrowIfProgrammingError(new ReferenceError('x is not defined'))).toThrow(ReferenceError);
    // A deep net overflowing the stack IS the capacity limit `unknown` reports.
    expect(() => rethrowIfProgrammingError(new RangeError('Maximum call stack size exceeded'))).not.toThrow();
    // The conditions the catches were written for pass through untouched.
    expect(() => rethrowIfProgrammingError(new Error('z3 exited with status 1'))).not.toThrow();
    expect(() => rethrowIfProgrammingError('solver died')).not.toThrow();
  });

  it('a replayer defect surfaces instead of reading as an exhausted search', () => {
    // assessCounterexample catches to keep a replayer fault from crashing the
    // verifier; a TypeError there must still reach the caller.
    const { net, m0 } = pipeline(2);
    const flat = flatten(net, new Set(), alwaysAvailable());
    const notAMarking = { tokens: 'not a function' } as any;
    expect(() => assessCounterexample(flat, notAMarking, new Set([notAMarking]), deadlockFree(), new Set()))
      .toThrow(TypeError);
  });
});

// A reset arc on a place the same transition also consumes: both executors run
// this, so the enumeration route must too. It used to clear the PRE-firing count
// after the inputs had already drawn, overdrawing and throwing.
describe('reset arcs in the enumeration route (VER-010 AC2)', () => {
  function resetAndInput(inputSpec) {
    const p = place('p'), q = place('q');
    const t = Transition.builder('t').inputs(inputSpec(p)).reset(p)
      .outputs(outPlace(q)).action(produces()).build();
    return { net: PetriNet.builder('reset-input').transitions(t).build(), p, q };
  }

  for (const [label, spec] of [['one(p)', one], ['all(p)', all]]) {
    it(`decides a net whose transition consumes and resets the same place — ${label}`, async () => {
      const { net, p, q } = resetAndInput(spec);
      const m0 = MarkingState.builder().tokens(p, 3).build();
      const result = await SmtVerifier.forNet(net).initialMarking(m0)
        .property(placeBound(q, 5)).timeout(30_000).verify();
      expect(result.verdict.type, result.report).toBe('proven');
      expect(result.route).toBe('enumeration');
    });
  }

  it('drains the place exactly as the executors do: the transition fires once', () => {
    const { net, p, q } = resetAndInput(one);
    const graph = StateClassGraph.build(net, MarkingState.builder().tokens(p, 3).build(), 1000);
    // p goes 3 -> 0 (input takes one, the reset clears the rest), q gets exactly 1,
    // and t cannot re-enable on a residue.
    const counts = [...new Set(graph.stateClasses().map(sc => sc.marking.tokens(p)))].sort((a, b) => a - b);
    expect(counts).toEqual([0, 3]);
    expect(graph.stateClasses().every(sc => sc.marking.tokens(q) <= 1)).toBe(true);
  });
});

// Commoner's theorem governs ORDINARY nets. The siphon/trap fixpoints read only
// the pre/post vectors, so on a net with a read, inhibitor or reset arc, or an arc
// weight above one, they answer about a strictly more permissive net — and turning
// that answer into `proven` is a false proof. Each net below is genuinely dead at
// its initial marking; both executors confirm it.
describe('the structural shortcut refuses nets it does not govern', () => {
  const run = (net, m0) => SmtVerifier.forNet(net).initialMarking(m0)
    .property(deadlockFree()).enumerationMaxClasses(0).timeout(30_000).verify();

  it('a read arc: the gate used to prove a net that cannot fire at all', async () => {
    // t1 needs a token in g to fire, and only t2 can put one there, but t2 needs g too.
    const a = place('a'), g = place('g');
    const t1 = Transition.builder('t1').inputs(one(a)).read(g).outputs(outPlace(g)).action(produces()).build();
    const t2 = Transition.builder('t2').inputs(one(g)).outputs(outPlace(a)).action(produces()).build();
    const net = PetriNet.builder('read-gate').transitions(t1, t2).build();
    const r = await run(net, MarkingState.builder().tokens(a, 1).build());
    expect(r.verdict.type === 'proven' && r.verdict.method === 'structural',
      `a dead net was proven deadlock-free structurally:\n${r.report}`).toBe(false);
  });

  it('an arc weight above one', async () => {
    const a = place('a');
    const t = Transition.builder('t').inputs(exactly(2, a)).outputs(outPlace(a)).action(produces()).build();
    const net = PetriNet.builder('weighted').transitions(t).build();
    const r = await run(net, MarkingState.builder().tokens(a, 1).build());
    expect(r.verdict.type === 'proven' && r.verdict.method === 'structural', r.report).toBe(false);
  });

  it('an inhibitor arc', async () => {
    const a = place('a'), b = place('b');
    const t = Transition.builder('t').inputs(one(a)).inhibitor(b).outputs(outPlace(a)).action(produces()).build();
    const net = PetriNet.builder('inhibited').transitions(t).build();
    const r = await run(net, MarkingState.builder().tokens(a, 1).tokens(b, 1).build());
    expect(r.verdict.type === 'proven' && r.verdict.method === 'structural', r.report).toBe(false);
  });

  it('still takes the shortcut on an ordinary net, where the theorem does hold', async () => {
    // A token circulating a ring: every siphon holds a marked trap, and nothing
    // about the net is outside what the fixpoints model.
    const a = place('a'), b = place('b');
    const t1 = Transition.builder('t1').inputs(one(a)).outputs(outPlace(b)).action(produces()).build();
    const t2 = Transition.builder('t2').inputs(one(b)).outputs(outPlace(a)).action(produces()).build();
    const net = PetriNet.builder('ring').transitions(t1, t2).build();
    const r = await run(net, MarkingState.builder().tokens(a, 1).build());
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.verdict.type === 'proven' && r.verdict.method).toBe('structural');
  });
});
