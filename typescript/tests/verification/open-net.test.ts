import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { produces } from '../fixtures/producing-actions.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, andPlaces, outPlace, xor } from '../../src/core/out.js';
import { deadline, delayed } from '../../src/core/timing.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { OpenNetContract, closeOpenNet, verifyOpenNet } from '../../src/verification/open-net/index.js';
import { countPhrase } from '../../src/verification/smt-property.js';

/**
 * VER-022 open-net verification against a contract.
 *
 * The subnet under test is a node gadget in the shape n8n-libpetri compiles: one input edge
 * carrying data or empty, one output with two outgoing edges, a shared budget and a halt.
 *
 *   X/start: one(X/in) one(_budget) one(X/idle) inhibitor(_halt) → X/running
 *   X/run:   one(X/running) → and( xor( and( xor(and(e1/data, e2/data), and(e1/empty, e2/empty)), X/routed ),
 *                                        and(_halt, _budget) ),
 *                                   X/idle )
 *   X/done:  one(X/routed) → and(_budget, X/done)
 *   X/skip:  one(X/in_empty) inhibitor(_halt) → and(e1/empty, e2/empty, X/skipped)
 */
const P = {
  in: place('X/in'), inEmpty: place('X/in_empty'), idle: place('X/idle'), budget: place('_budget'),
  halt: place('_halt'), running: place('X/running'), routed: place('X/routed'), done: place('X/done'),
  skipped: place('X/skipped'), e1Data: place('e1/data'), e1Empty: place('e1/empty'),
  e2Data: place('e2/data'), e2Empty: place('e2/empty'), trace: place('X/trace'),
};

interface Defects {
  /** The skip writes e1's empty but nothing for e2: an edge with neither data nor empty. */
  readonly skipForgetsE2?: boolean;
  /** The run's data branch also writes e1's empty. */
  readonly runWritesBoth?: boolean;
  /** Done keeps the budget unit. */
  readonly noRefund?: boolean;
  /** The run leaves a token on an internal place nothing consumes. */
  readonly leak?: boolean;
  /** A transition that can fire forever while the node runs. */
  readonly spin?: boolean;
  /** The start is delayed; the untimed claim must not care. */
  readonly timedStart?: boolean;
}

function gadget(defects: Defects = {}): PetriNet {
  const startBuilder = Transition.builder('X/start')
    .inputs(one(P.in), one(P.budget), one(P.idle)).inhibitor(P.halt)
    .outputs(outPlace(P.running)).action(produces());
  const start = (defects.timedStart === true ? startBuilder.timing(delayed(50)) : startBuilder).build();
  const data = defects.runWritesBoth === true
    ? andPlaces(P.e1Data, P.e1Empty, P.e2Data)
    : andPlaces(P.e1Data, P.e2Data);
  const routes = xor(data, andPlaces(P.e1Empty, P.e2Empty));
  const success = defects.leak === true
    ? and(routes, outPlace(P.routed), outPlace(P.trace))
    : and(routes, outPlace(P.routed));
  const run = Transition.builder('X/run').inputs(one(P.running))
    .outputs(and(xor(success, andPlaces(P.halt, P.budget)), outPlace(P.idle))).action(produces()).build();
  const done = Transition.builder('X/done').inputs(one(P.routed))
    .outputs(defects.noRefund === true ? outPlace(P.done) : andPlaces(P.budget, P.done))
    .action(produces()).build();
  const skip = Transition.builder('X/skip').inputs(one(P.inEmpty)).inhibitor(P.halt)
    .outputs(defects.skipForgetsE2 === true
      ? andPlaces(P.e1Empty, P.skipped)
      : andPlaces(P.e1Empty, P.e2Empty, P.skipped))
    .action(produces()).build();
  const transitions = [start, run, done, skip];
  if (defects.spin === true) {
    transitions.push(Transition.builder('X/spin').inputs(one(P.running))
      .outputs(outPlace(P.running)).action(produces()).build());
  }
  return PetriNet.builder('X').transitions(...transitions).build();
}

/** The node contract as n8n-libpetri states it, for a budget of `budget`. */
function contract(opts: { terminal?: boolean; budget?: number; termination?: boolean } = {}): OpenNetContract {
  const k = opts.budget ?? 1;
  const builder = OpenNetContract.builder()
    .initialMarking(m => m.tokens(P.idle, 1).tokens(P.budget, k))
    .arrive(1, P.in, P.inEmpty)
    .arriveAtMost(1, P.halt)
    .expect('e1', 1, P.e1Data, P.e1Empty)
    .expect('e2', 1, P.e2Data, P.e2Empty)
    .expect('idle', 1, P.idle)
    .expect('budget', k, P.budget)
    .expect('history', 1, P.done, P.skipped);
  if (opts.terminal !== false) builder.terminal(P.halt, P.in, P.inEmpty);
  if (opts.termination === false) builder.requireTermination(false);
  return builder.build();
}

describe('open-net verification (VER-022): graph route', () => {
  it('proves a well-formed gadget, halts included', async () => {
    const r = await verifyOpenNet(gadget(), contract());
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.route).toBe('enumeration');
    expect(r.graphComplete).toBe(true);
    expect(r.violations).toEqual([]);
    expect(r.report).toContain('=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===');
    expect(r.report).toContain('e1 = exactly 1 across {e1/data, e1/empty}');
    expect(r.report).toContain('Terminal: when _halt: X/in, X/in_empty');
  });

  it('proves it for a budget of two as well', async () => {
    const r = await verifyOpenNet(gadget(), contract({ budget: 2 }));
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('names the edge a broken skip leaves with neither data nor empty, with its port trace', async () => {
    const r = await verifyOpenNet(gadget({ skipForgetsE2: true }), contract());
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.violations.map(v => v.subject)).toEqual(['e2']);
    const v = r.violations[0]!;
    expect(v.kind).toBe('clause');
    expect(v.detail).toBe('exactly 1 across {e2/data, e2/empty} at quiescence, found 0');
    expect(v.confirmed).toBe(true);
    // Shortest witness: the empty arrives, the halt is declined, the skip fires.
    expect([...v.transitions].sort()).toEqual(['X/skip', 'env:arrive[0]:X/in_empty', 'env:decline[1]']);
    expect(v.markings).toHaveLength(v.transitions.length + 1);
    const skip = v.portTrace.find(s => s.transition === 'X/skip')!;
    expect(skip.environment).toBeNull();
    expect(skip.changes).toEqual([
      { place: 'X/in_empty', delta: -1 }, { place: 'e1/empty', delta: 1 }, { place: 'X/skipped', delta: 1 },
    ]);
    expect(v.portTrace.find(s => s.transition === 'env:arrive[0]:X/in_empty')!.environment).toBe('arrival');
    expect(v.markings.at(-1)!.tokens(P.e2Empty) + v.markings.at(-1)!.tokens(P.e2Data)).toBe(0);
    expect(r.report).toContain('[e2] clause: exactly 1 across {e2/data, e2/empty} at quiescence, found 0');
    expect(r.report).toContain('Port trace:');
  });

  it('a declared skip waives the output edge a skipping node never writes, and keeps its upper bound', async () => {
    // The very net the case above calls broken. Whether writing no output edge is a defect or
    // a designed skip is the contract's to say, not the verifier's: a node that can legitimately
    // skip needs its edge clauses conditional on having run, which is what a terminal on
    // X/skipped states. The upper bounds are not waived, so a double write is still caught.
    const declared = OpenNetContract.builder()
      .initialMarking(m => m.tokens(P.idle, 1).tokens(P.budget, 1))
      .arrive(1, P.in, P.inEmpty)
      .arriveAtMost(1, P.halt)
      .expect('e1', 1, P.e1Data, P.e1Empty)
      .expect('e2', 1, P.e2Data, P.e2Empty)
      .expect('idle', 1, P.idle)
      .expect('budget', 1, P.budget)
      .expect('history', 1, P.done, P.skipped)
      .terminal(P.halt, P.in, P.inEmpty)
      .terminal(P.skipped)
      .build();
    expect((await verifyOpenNet(gadget({ skipForgetsE2: true }), declared)).verdict.type).toBe('proven');
    // Still a violation when the run writes an edge twice: that breaks an upper bound.
    const both = await verifyOpenNet(gadget({ runWritesBoth: true }), declared);
    expect(both.verdict.type, both.report).toBe('violated');
    expect(both.violations.map(v => v.subject)).toEqual(['e1']);
  });

  it('reports an edge that receives both data and empty, and keeps that bound under a halt', async () => {
    const r = await verifyOpenNet(gadget({ runWritesBoth: true }), contract());
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.violations.map(v => v.subject)).toEqual(['e1']);
    expect(r.violations[0]!.detail).toContain('found 2');
  });

  it('reports a budget unit the gadget keeps', async () => {
    const r = await verifyOpenNet(gadget({ noRefund: true }), contract());
    expect(r.violations.map(v => v.subject), r.report).toEqual(['budget']);
    expect(r.violations[0]!.detail).toBe('exactly 1 across {_budget} at quiescence, found 0');
  });

  it('names an internal place a run leaves a token on', async () => {
    const r = await verifyOpenNet(gadget({ leak: true }), contract());
    expect(r.violations.map(v => [v.kind, v.subject]), r.report).toEqual([['stranded', 'X/trace']]);
  });

  it('reports a run that never comes to rest as a lasso', async () => {
    const r = await verifyOpenNet(gadget({ spin: true }), contract());
    expect(r.violations.map(v => v.kind), r.report).toEqual(['termination']);
    const v = r.violations[0]!;
    expect(v.cycleStart).not.toBeNull();
    expect(v.transitions.slice(v.cycleStart!)).toEqual(['X/spin']);
    expect(v.markings[v.cycleStart!]!.toString()).toBe(v.markings.at(-1)!.toString());
    expect(r.report).toContain('Firing sequence: env:arrive[0]:X/in, X/start, then repeating X/spin');
  });

  it('with termination waived, the same spinning gadget meets its contract', async () => {
    const r = await verifyOpenNet(gadget({ spin: true }), contract({ termination: false }));
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('makes the untimed claim: a delayed start changes nothing', async () => {
    const plain = await verifyOpenNet(gadget(), contract());
    const timed = await verifyOpenNet(gadget({ timedStart: true }), contract());
    expect(timed.verdict.type, timed.report).toBe('proven');
    expect(timed.classCount).toBe(plain.classCount);
  });

  it('without a designed terminal, a halt strands the arrival and waives nothing', async () => {
    const r = await verifyOpenNet(gadget(), contract({ terminal: false }));
    expect(r.verdict.type, r.report).toBe('violated');
    // Clauses in contract order, then stranded places in code-point order.
    expect(r.violations.map(v => v.subject)).toEqual(['e1', 'e2', 'history', 'X/in', 'X/in_empty', '_halt']);
  });

  it('a clause over places the net never writes counts zero there, and the report says so', async () => {
    const e3 = [place('e3/data'), place('e3/empty')];
    const c = OpenNetContract.builder()
      .initialMarking(m => m.tokens(P.idle, 1).tokens(P.budget, 1))
      .arrive(1, P.in, P.inEmpty)
      .expect('e1', 1, P.e1Data, P.e1Empty)
      .expect('e2', 1, P.e2Data, P.e2Empty)
      .expect('e3', 1, ...e3)
      .expect('idle', 1, P.idle)
      .expect('budget', 1, P.budget)
      .expect('history', 1, P.done, P.skipped)
      .rest(P.halt)
      .build();
    const r = await verifyOpenNet(gadget(), c);
    expect(r.violations.map(v => v.subject), r.report).toContain('e3');
    expect(r.report).toContain('Not declared by the net: e3/data, e3/empty');
  });

  it('delivers exactly n arrivals, and at most n may deliver none', async () => {
    const q = place('q'), out = place('out');
    const relay = PetriNet.builder('relay').transitions(
      Transition.builder('t').inputs(one(q)).outputs(outPlace(out)).action(produces()).build(),
    ).build();
    const exactly = await verifyOpenNet(relay, OpenNetContract.builder().arrive(2, q).expect('out', 2, out).build());
    expect(exactly.verdict.type, exactly.report).toBe('proven');

    const atMost = await verifyOpenNet(relay, OpenNetContract.builder().arriveAtMost(2, q).expect('out', 2, out).build());
    expect(atMost.verdict.type, atMost.report).toBe('violated');
    expect(atMost.violations[0]!.detail).toBe('exactly 2 across {out} at quiescence, found 0');

    const between = await verifyOpenNet(relay, OpenNetContract.builder().arriveAtMost(2, q).expectBetween('out', 0, 2, out).build());
    expect(between.verdict.type, between.report).toBe('proven');
  });

  it('a graph that does not close is unknown without the SMT route, and says why', async () => {
    const r = await verifyOpenNet(gadget(), contract(), { maxClasses: 3, smt: false });
    expect(r.verdict.type).toBe('unknown');
    expect(r.graphComplete).toBe(false);
    expect(r.verdict.type === 'unknown' && r.verdict.reason)
      .toBe('the state-class graph did not close within 3 classes, and the SMT route is disabled');
  });
});

describe('open-net verification (VER-022): the closure and the contract', () => {
  it('closes the net with ordinary places and transitions', () => {
    const closed = closeOpenNet(gadget(), contract());
    expect(closed.initialMarking.tokens(place('env:arrivals[0]'))).toBe(1);
    expect(closed.initialMarking.tokens(place('env:optional[1]'))).toBe(1);
    expect(closed.initialMarking.tokens(P.idle)).toBe(1);
    expect([...closed.environment.keys()]).toEqual([
      'env:arrive[0]:X/in', 'env:arrive[0]:X/in_empty', 'env:arrive?[1]:_halt', 'env:decline[1]',
    ]);
    expect(closed.environment.get('env:decline[1]')).toEqual({ kind: 'decline', group: 1 });
    expect(closed.undeclared).toEqual([]);
    expect([...closed.net.places].filter(p => p.name === 'X/in')).toHaveLength(1);
  });

  it('refuses a net whose names the closure would reuse', () => {
    const clash = PetriNet.builder('clash').transitions(
      Transition.builder('t').inputs(one(place('env:arrivals[0]'))).build(),
    ).build();
    expect(() => closeOpenNet(clash, OpenNetContract.builder().arrive(1, place('q')).build()))
      .toThrow(/already declares/);
  });

  it('validates the contract as it is built', () => {
    expect(() => OpenNetContract.builder().arriveAtMost(0, P.in)).toThrow(/max >= 1/);
    expect(() => OpenNetContract.builder().arriveBetween(2, 1, P.in)).toThrow(/0 <= min <= max/);
    expect(() => OpenNetContract.builder().arrive(Infinity, P.in)).toThrow(/finite/);
    expect(() => OpenNetContract.builder().arrive(1)).toThrow(/names no place/);
    expect(() => OpenNetContract.builder().expect('a', 1, P.idle).expect('a', 1, P.budget))
      .toThrow(/duplicate clause name 'a'/);
    expect(() => OpenNetContract.builder().expectBetween('a', 2, 1, P.idle)).toThrow(/0 <= min <= max/);
    expect(() => OpenNetContract.builder().expect('', 1, P.idle)).toThrow(/needs a name/);
  });

  it('phrases counts the way the report prints them', () => {
    expect(countPhrase(1, 1)).toBe('exactly 1');
    expect(countPhrase(0, 1)).toBe('at most 1');
    expect(countPhrase(2, Infinity)).toBe('at least 2');
    expect(countPhrase(0, Infinity)).toBe('any number');
    expect(countPhrase(1, 3)).toBe('between 1 and 3');
  });

  it('lists the ports in first-mention order, markers included', () => {
    expect(contract().places().map(p => p.name)).toEqual([
      'X/idle', '_budget', 'X/in', 'X/in_empty', '_halt', 'e1/data', 'e1/empty', 'e2/data', 'e2/empty',
      'X/done', 'X/skipped',
    ]);
  });
});

describe('open-net verification (VER-022): environment transitions', () => {
  // A node that asks its environment and runs again on every answer: N/run either finishes or
  // sends a request; the environment answers at most twice, from a budget of its own, or ends.
  const inp = place('N/in'), running = place('N/running'), request = place('N/request');
  const reply = place('N/reply'), done = place('N/done');
  const rounds = place('env/rounds'), ended = place('env/ended');
  const node = PetriNet.builder('N').transitions(
    Transition.builder('N/start').inputs(one(inp)).outputs(outPlace(running)).action(produces()).build(),
    Transition.builder('N/resume').inputs(one(reply)).outputs(outPlace(running)).action(produces()).build(),
    Transition.builder('N/run').inputs(one(running)).outputs(xor(outPlace(request), outPlace(done)))
      .action(produces()).build(),
  ).build();
  // No actions: an environment transition never runs, so passthrough() is fine even with outputs.
  const again = Transition.builder('env/again').inputs(one(request), one(rounds)).outputs(outPlace(reply)).build();
  const end = Transition.builder('env/end').inputs(one(request)).outputs(outPlace(ended)).build();
  const contract = (doneAtLeast: number) => OpenNetContract.builder()
    .initialMarking(m => m.tokens(rounds, 2))
    .arrive(1, inp)
    .expectBetween('done', doneAtLeast, 1, done)
    .environment(again, end)
    .build();

  it('proves a node against an environment that answers what it sends, and never strands the environment', async () => {
    const r = await verifyOpenNet(node, contract(0));
    // env/rounds keeps what the environment did not spend and env/ended keeps the ended
    // exchanges: both are the environment's own places, so neither is stranded.
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.report).toContain('Environment transitions: env/again, env/end');
  });

  it('marks the environment transitions in the port trace', async () => {
    const r = await verifyOpenNet(node, contract(1));
    expect(r.violations.map(v => v.subject), r.report).toEqual(['done']);
    const step = r.violations[0]!.portTrace.find(s => s.transition === 'env/end')!;
    expect(step.environment).toBe('transition');
    expect(step.changes).toEqual([{ place: 'N/request', delta: -1 }, { place: 'env/ended', delta: 1 }]);
    expect(r.report).toMatch(/\d+\. env\/end \[environment\] {2}N\/request -1, env\/ended \+1/);
  });

  it('keeps the environment\'s own places apart and out of the undeclared list', () => {
    const closed = closeOpenNet(node, contract(0));
    expect(closed.environment.get('env/again')).toEqual({ kind: 'transition' });
    expect(closed.environmentPlaces.map(p => p.name).sort()).toEqual(['env/ended', 'env/rounds']);
    expect(closed.undeclared).toEqual([]);
  });

  it('refuses an environment transition named like one of the net\'s, or declared twice', () => {
    const clash = Transition.builder('N/run').inputs(one(request)).build();
    expect(() => closeOpenNet(node, OpenNetContract.builder().arrive(1, inp).environment(clash).build()))
      .toThrow(/already declares/);
    expect(() => OpenNetContract.builder().environment(end, end)).toThrow(/duplicate environment transition 'env\/end'/);
  });
});

describe('untimed exploration (VER-004, used by VER-022)', () => {
  it('reaches a marking the timing excludes', () => {
    const p = place('p'), a = place('a'), b = place('b');
    const t1 = Transition.builder('t1').inputs(one(p)).outputs(outPlace(a)).timing(deadline(5)).action(produces()).build();
    const t2 = Transition.builder('t2').inputs(one(p)).outputs(outPlace(b)).timing(delayed(10)).action(produces()).build();
    const net = PetriNet.builder('race').transitions(t1, t2).build();
    const m0 = MarkingState.builder().tokens(p, 1).build();
    const timed = StateClassGraph.build(net, m0, 100);
    const untimed = StateClassGraph.build(net, m0, 100, undefined, undefined, { untimed: true });
    expect(timed.stateClasses().some(sc => sc.marking.hasTokens(b))).toBe(false);
    expect(untimed.stateClasses().some(sc => sc.marking.hasTokens(b))).toBe(true);
  });
});

describeZ3('open-net verification (VER-022): SMT route', () => {
  it('with termination waived, proves the well-formed gadget through existing properties', async () => {
    const r = await verifyOpenNet(gadget(), contract({ termination: false }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.route).toBe('smt');
    expect(r.report).toContain('=== SMT route ===');
    expect(r.report).toContain('State-class graph: skipped');
  }, 180_000);

  it('decides termination by a firing bound when the graph is not built', async () => {
    const r = await verifyOpenNet(gadget(), contract(), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.report).toMatch(/\[termination\] Firing bound \(VER-019\): every run has at most \d+ firings/);
  }, 180_000);

  it('leaves termination undecided when no firing bound exists, and names what repeats', async () => {
    const r = await verifyOpenNet(gadget({ spin: true }), contract(), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('unknown');
    expect(r.verdict.type === 'unknown' && r.verdict.reason)
      .toContain('termination: no firing bound: the marking equation lets X/spin repeat');
  }, 180_000);

  it('names the broken edge on the SMT route too', async () => {
    const r = await verifyOpenNet(gadget({ skipForgetsE2: true }), contract({ termination: false }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.route).toBe('smt');
    expect(r.violations.map(v => v.subject)).toContain('e2');
  }, 180_000);

  it('decides a lower bound above 1 through the quiescent count', async () => {
    const r = await verifyOpenNet(gadget(), contract({ budget: 2 }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.report).toContain('[budget] Quiescent count: exactly 2 across {_budget}; lower bound waived while {_halt} is marked: proven');
  }, 180_000);

  it('carries the certificates its proven queries returned, labelled by contract part', async () => {
    const r = await verifyOpenNet(gadget(), contract({ termination: false }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('proven');
    // The proof evidence is the conjunction of the parts' invariants, not nothing.
    const invariant = r.verdict.type === 'proven' ? r.verdict.inductiveInvariant : null;
    expect(invariant, r.report).not.toBeNull();
    expect(invariant).toContain('[stranding]');
  }, 180_000);

  it('skips a count clause no marking can fail, and says so rather than going silent', async () => {
    const anything = OpenNetContract.builder()
      .initialMarking(m => m.tokens(P.idle, 1).tokens(P.budget, 1))
      .arrive(1, P.in, P.inEmpty)
      .arriveAtMost(1, P.halt)
      .expect('e1', 1, P.e1Data, P.e1Empty)
      .expect('e2', 1, P.e2Data, P.e2Empty)
      .expect('idle', 1, P.idle)
      .expect('budget', 1, P.budget)
      // Between 0 and ∞ across the history places: every marking satisfies it.
      .expectBetween('history', 0, Infinity, P.done, P.skipped)
      .terminal(P.halt, P.in, P.inEmpty)
      .requireTermination(false)
      .build();
    const r = await verifyOpenNet(gadget(), anything, { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.report).toContain('[history] any number across {X/done, X/skipped} at quiescence: proven (no query needed)');
  }, 180_000);

  it('names the stranded place on the SMT route too, with the same widening the graph applies', async () => {
    // The stranding attribution is the one predicate the two routes compute by different
    // means, and getting it wrong is how a per-place row reports a stranding the complete
    // graph proves cannot happen: it has to ask "marked AND unexcused", not "marked". The
    // graph route reaches the same verdict on this gadget above, so the two are diffable.
    const r = await verifyOpenNet(gadget({ leak: true }), contract({ termination: false }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.route).toBe('smt');
    expect(r.violations.map(v => [v.kind, v.subject]), r.report).toEqual([['stranded', 'X/trace']]);
    // Nothing excused by the terminal is named: _halt's excused arrivals may rest.
    expect(r.violations[0]!.detail).toContain('X/trace holds a token at quiescence');
  }, 180_000);

  it('reports the count a broken gadget leaves, found by the solver', async () => {
    const r = await verifyOpenNet(gadget({ noRefund: true }), contract({ termination: false }), { maxClasses: 0 });
    expect(r.verdict.type, r.report).toBe('violated');
    const budget = r.violations.find(v => v.subject === 'budget')!;
    expect(budget.detail).toMatch(/^exactly 1 across \{_budget\} at quiescence/);
  }, 180_000);
});
