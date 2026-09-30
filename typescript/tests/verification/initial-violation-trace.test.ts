import { expect, it } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { deadlockFree, mutualExclusion, placeBound, type SmtProperty } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { fork } from '../../src/core/transition-action.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * The fixpoint query reports a violation of the initial marking itself as the empty firing
 * sequence: one marking (M0), no transition, confirmed — with the replay on or off. It used to
 * report `violated` with no trace at all (the refutation proof has no step to decode), which no
 * one can replay.
 */

const p = place<number>('p');
const q = place<number>('q');
const r = place<number>('r');

const net = () => PetriNet.builder('initial')
  .transition(Transition.builder('t').inputs(one(p)).outputs(outPlace(q)).action(fork()).build())
  .place(r)
  .build();

describeZ3('an initial violation on the fixpoint query', () => {
  const pr = () => MarkingState.builder().tokens(p, 1).tokens(r, 1).build();
  const cases: [string, SmtProperty, Place<any>[], () => MarkingState][] = [
    ['placeBound', placeBound(p, 0), [], pr],
    ['mutualExclusion', mutualExclusion(p, r), [], pr],
    // Quiescent at M0 with a stranded token in r.
    ['deadlockFree', deadlockFree(), [q], () => MarkingState.builder().tokens(r, 1).build()],
  ];
  for (const [name, property, sinks, marking] of cases) {
    for (const replay of [true, false]) {
      it(`is the empty trace (${name}, replay ${replay})`, async () => {
        const result = await SmtVerifier.forNet(net())
          .initialMarking(marking())
          .property(property)
          .sinkPlaces(...sinks)
          .enumerationMaxClasses(0)
          .linearBound(false)
          .stateEquationPhase(false)
          .firingBound(false)
          .counterexampleReplay(replay)
          .verify();
        expect(result.verdict.type, result.report).toBe('violated');
        expect(result.route, result.report).toBe('smt');
        expect(result.counterexampleTrace, result.report).toHaveLength(1);
        expect(result.counterexampleTransitions, result.report).toEqual([]);
        expect(result.counterexampleConfirmed, result.report).toBe(true);
        expect(result.report).toContain('the initial marking violates the property');
      }, 30_000);
    }
  }
});
