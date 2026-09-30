import { it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound, unreachable } from '../../src/verification/smt-property.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { delayed, window, type Timing } from '../../src/core/timing.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * [VER-003] `counterexampleTiming` and the opt-in timed counterexample check of [VER-023].
 *
 * The fixture is the lab's watchdog net (research/net-metrics/lab/TimedNets.java,
 * `watchdogs(2, false)`): per call `i`, `start_i: REQ_i -> CALLING_i`, `answer_i: CALLING_i ->
 * RESP_i` at `window(0, 2)`, and `watchdog_i: CALLING_i -> TIMEOUT_i` at `delayed(5)`. The
 * answer always wins the race, so `TIMEOUT_0` is unreachable under timing, while the untimed
 * abstraction reaches it by `start_0, watchdog_0`.
 */

const REQ = (i: number) => place<string>(`REQ_${i}`);
const CALLING = (i: number) => place<string>(`CALLING_${i}`);
const RESP = (i: number) => place<string>(`RESP_${i}`);
const TIMEOUT = (i: number) => place<string>(`TIMEOUT_${i}`);

function watchdogs(n: number, watchdogTiming: Timing = delayed(5)): PetriNet {
  const b = PetriNet.builder(`watchdog-timing-${n}`);
  for (let i = 0; i < n; i++) {
    b.transition(Transition.builder(`start_${i}`).inputs(one(REQ(i))).outputs(outPlace(CALLING(i))).build());
    b.transition(Transition.builder(`answer_${i}`).timing(window(0, 2))
      .inputs(one(CALLING(i))).outputs(outPlace(RESP(i))).build());
    b.transition(Transition.builder(`watchdog_${i}`).timing(watchdogTiming)
      .inputs(one(CALLING(i))).outputs(outPlace(TIMEOUT(i))).build());
  }
  return bindProducers(b.build());
}

function verifier(net: PetriNet, n = 2): SmtVerifier {
  return SmtVerifier.forNet(net).mintTransitions(...allMints(net))
    .initialMarking(m => { for (let i = 0; i < n; i++) m.tokens(REQ(i), 1); })
    .property(unreachable(new Set([TIMEOUT(0)])));
}

/** fork mints one name into A and B; `join` (delayed(1)) matches them by name into `accepted`. */
function timedNuNet(): { net: PetriNet; slot: Place<any>; accepted: Place<string> } {
  const slot = place('slot');
  const a = place<string>('A');
  const bb = place<string>('B');
  const accepted = place<string>('accepted');
  const key = (v: string) => nameId(v);
  const fork = Transition.builder('fork').inputs(one(slot)).outputs(andPlaces(a, bb)).build();
  const join = Transition.builder('join').timing(delayed(1))
    .inputs(one(a), one(bb))
    .match(matchSpec(matchKey(a, key), matchKey(bb, key)))
    .outputs(outPlace(accepted))
    .build();
  return { net: bindProducers(PetriNet.builder('nu-timed').transitions(fork, join).build()), slot, accepted };
}

describeZ3('counterexampleTiming (VER-003) and the timed check (VER-023)', () => {
  it('check off: violated, untimed-abstraction, report unchanged', async () => {
    const result = await verifier(watchdogs(2)).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTiming).toBe('untimed-abstraction');
    expect(result.report).not.toContain('Timed counterexample check');
  });

  it('check on: spurious-under-timing, verdict and untimed trace kept, class count reported', async () => {
    const off = await verifier(watchdogs(2)).verify();
    const on = await verifier(watchdogs(2)).timedCounterexampleCheck(true).verify();
    expect(on.verdict.type, on.report).toBe('violated');
    expect(on.counterexampleTiming).toBe('spurious-under-timing');
    expect(on.route).toBe(off.route);
    expect(on.counterexampleTransitions).toEqual(off.counterexampleTransitions);
    expect(on.counterexampleConfirmed).toBe(off.counterexampleConfirmed);
    expect(on.report).toContain('=== Timed counterexample check (VER-023) ===');
    // "Two parallel watchdogs close in 10 classes with no TIMEOUT marking" (VER-023).
    expect(on.report).toContain('  Timed state classes: 10');
    expect(on.report).toContain(
      '  SPURIOUS UNDER TIMING: the timed state-class graph closed with 10 classes and none of them ' +
      "violates the property, so it holds under the net's timing — a timed claim only.",
    );
    expect(on.report.startsWith(off.report.replace(/\n\n=== RESULT[\s\S]*$/, ''))).toBe(true);
  });

  it('a watchdog faster than the answer: timed-confirmed, trace replaced by the timed path', async () => {
    const result = await verifier(watchdogs(1, delayed(1)), 1).timedCounterexampleCheck(true).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('timed-confirmed');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTransitions).toEqual(['start_0', 'watchdog_0']);
    expect(result.counterexampleTrace.map(m => m.hasTokens(TIMEOUT(0)))).toEqual([false, false, true]);
    expect(result.report).toContain('REPLACED by the shortest timed-graph path');
  });

  it('timed-confirmed marks the replaced trace confirmed, even where the untimed one was not replayed', async () => {
    const result = await verifier(watchdogs(1, delayed(1)), 1)
      .stateEquationPhase(false)
      .firingBound(false)
      .counterexampleReplay(false)
      .timedCounterexampleCheck(true)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('timed-confirmed');
    expect(result.counterexampleConfirmed).toBe(true);
  });

  it('a class budget below the timed graph: timed-undecided', async () => {
    const result = await verifier(watchdogs(2)).timedCounterexampleCheck(true).enumerationMaxClasses(3).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('timed-undecided');
    expect(result.report).toContain('  UNDECIDED: the timed state-class graph exceeded 3 classes (enumerationMaxClasses).');
  });

  it('a total budget that runs out during the check: timed-undecided, verdict kept', async () => {
    // Four cyclic toggles with staggered windows beside the watchdog: the SMT pipeline still
    // finds the untimed witness quickly, but the timed graph runs past 200 000 classes.
    const b = PetriNet.builder('watchdog-with-toggles');
    for (const t of watchdogs(1).transitions) b.transition(t);
    for (let i = 0; i < 4; i++) {
      b.transition(Transition.builder(`t${i}`).timing(window(i + 1, 2 * i + 3))
        .inputs(one(place(`a${i}`))).outputs(outPlace(place(`b${i}`))).build());
      b.transition(Transition.builder(`u${i}`).timing(window(i + 2, 3 * i + 4))
        .inputs(one(place(`b${i}`))).outputs(outPlace(place(`a${i}`))).build());
    }
    const result = await SmtVerifier.forNet(bindProducers(b.build())).mintTransitions(...allMints(bindProducers(b.build())))
      .initialMarking(m => { m.tokens(REQ(0), 1); for (let i = 0; i < 4; i++) m.tokens(place(`a${i}`), 1); })
      .property(unreachable(new Set([TIMEOUT(0)])))
      .enumerationMaxClasses(10_000_000)
      .timedCounterexampleCheck(true)
      .totalBudget(3_000)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('timed-undecided');
    expect(result.report).toContain(
      '  UNDECIDED: the total verification budget of 3000 ms ran out before the timed state-class graph closed.',
    );
    expect(result.elapsedMs).toBeLessThan(3_000 + 1_000);
  }, 30_000);

  it('an untimed net: untimed-net, whatever the route or option', async () => {
    const net = bindProducers(PetriNet.builder('untimed')
      .transition(Transition.builder('start_0').inputs(one(REQ(0))).outputs(outPlace(CALLING(0))).build())
      .transition(Transition.builder('watchdog_0').inputs(one(CALLING(0))).outputs(outPlace(TIMEOUT(0))).build())
      .build());
    for (const on of [false, true]) {
      const result = await verifier(net, 1).timedCounterexampleCheck(on).verify();
      expect(result.verdict.type, result.report).toBe('violated');
      expect(result.counterexampleTiming).toBe('untimed-net');
    }
  });

  it('environment places registered: the check does not run, untimed-abstraction', async () => {
    const ext = environmentPlace<string>('EXT');
    const b = PetriNet.builder('watchdog-env');
    for (const t of watchdogs(2).transitions) b.transition(t);
    b.transition(Transition.builder('ext_in').inputs(one(ext.place)).outputs(outPlace(place('EXT_SEEN'))).build());
    const result = await verifier(bindProducers(b.build()))
      .environmentPlaces(ext)
      .environmentMode(alwaysAvailable())
      .timedCounterexampleCheck(true)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('untimed-abstraction');
    expect(result.report).not.toContain('Timed counterexample check');
  });

  it('a Route B verdict on a timed ν-net: timed-exact', async () => {
    const { net, slot, accepted } = timedNuNet();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .initialMarking(m => m.tokens(slot, 1))
      .property(unreachable(new Set([accepted as Place<any>])))
      .timedCounterexampleCheck(true)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.route).toBe('nu-scg');
    expect(result.counterexampleTiming).toBe('timed-exact');
  });

  it('ν-matching transitions outside Route B: the check does not run, untimed-abstraction', async () => {
    // A declared budget puts reachability-safety on Route A's coloured encoding, not Route B;
    // the timed state-class graph is name-blind, so it must not be consulted.
    const { net, slot, accepted } = timedNuNet();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .initialMarking(m => m.tokens(slot, 1))
      .budgetPlaces(slot)
      .property(unreachable(new Set([accepted as Place<any>])))
      .timedCounterexampleCheck(true)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.route).toBe('smt');
    expect(result.counterexampleTiming).toBe('untimed-abstraction');
    expect(result.report).not.toContain('Timed counterexample check');
  });

  it('a verdict other than violated carries no timing', async () => {
    for (const on of [false, true]) {
      const result = await verifier(watchdogs(2)).property(placeBound(REQ(0), 1)).timedCounterexampleCheck(on).verify();
      expect(result.verdict.type, result.report).toBe('proven');
      expect(result.counterexampleTiming).toBeNull();
    }
  });
});

describeZ3('the timed check on quiescence properties (VER-023 AC3)', () => {
  it('a lone delayed(5) transition still fires out of its class: the deadlock is after it', async () => {
    const s = place<string>('S');
    const x = place<string>('X');
    const net = bindProducers(PetriNet.builder('delayed-deadlock')
      .transition(Transition.builder('d').timing(delayed(5)).inputs(one(s)).outputs(outPlace(x)).build())
      .build());
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .initialMarking(m => m.tokens(s, 1))
      .property(deadlockFree())
      .timedCounterexampleCheck(true)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming).toBe('timed-confirmed');
    expect(result.counterexampleTransitions).toEqual(['d']);
  });

  it('a deadlock only the untimed abstraction reaches is spurious under timing', async () => {
    const s = place<string>('S');
    const a = place<string>('A');
    const done = place<string>('DONE');
    const stuck = place<string>('STUCK');
    const net = bindProducers(PetriNet.builder('race-deadlock')
      .transition(Transition.builder('start').inputs(one(s)).outputs(outPlace(a)).build())
      .transition(Transition.builder('fast').timing(window(0, 2)).inputs(one(a)).outputs(outPlace(done)).build())
      .transition(Transition.builder('slow').timing(delayed(5)).inputs(one(a)).outputs(outPlace(stuck)).build())
      .build());
    const run = (on: boolean) => SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .initialMarking(m => m.tokens(s, 1))
      .property(deadlockFree())
      .sinkPlaces(done)
      .timedCounterexampleCheck(on)
      .verify();
    const off = await run(false);
    expect(off.verdict.type, off.report).toBe('violated');
    expect(off.counterexampleTiming).toBe('untimed-abstraction');
    const on = await run(true);
    expect(on.verdict.type, on.report).toBe('violated');
    expect(on.counterexampleTiming).toBe('spurious-under-timing');
  });
});
