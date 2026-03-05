import { describe, it, expect } from 'vitest';
import { StateClass } from '../../../src/verification/analysis/state-class.js';
import { DBM } from '../../../src/verification/analysis/dbm.js';
import { MarkingState } from '../../../src/verification/marking-state.js';
import { Transition } from '../../../src/core/transition.js';
import { place } from '../../../src/core/place.js';
import { one } from '../../../src/core/in.js';
import { outPlace } from '../../../src/core/out.js';
import { immediate, delayed } from '../../../src/core/timing.js';

describe('StateClass', () => {
  const pA = place('A');
  const pB = place('B');

  const t1 = Transition.builder('t1')
    .inputs(one(pA))
    .outputs(outPlace(pB))
    .build();

  const t2 = Transition.builder('t2')
    .inputs(one(pB))
    .outputs(outPlace(pA))
    .timing(delayed(1000))
    .build();

  it('construction and basic queries', () => {
    const marking = MarkingState.builder().tokens(pA, 1).build();
    const dbm = DBM.create(['t1'], [0], [Infinity]);
    const sc = new StateClass(marking, dbm, [t1]);

    expect(sc.isEmpty()).toBe(false);
    expect(sc.enabledTransitions).toHaveLength(1);
    expect(sc.enabledTransitions[0]).toBe(t1);
  });

  it('isEmpty when DBM is empty', () => {
    const marking = MarkingState.empty();
    const dbm = DBM.empty([]);
    const sc = new StateClass(marking, dbm, []);

    expect(sc.isEmpty()).toBe(true);
  });

  it('canFire checks enabled and upper bound', () => {
    const marking = MarkingState.builder().tokens(pA, 1).build();
    const dbm = DBM.create(['t1'], [0], [5]).letTimePass();
    const sc = new StateClass(marking, dbm, [t1]);

    expect(sc.canFire(t1)).toBe(true);
    expect(sc.canFire(t2)).toBe(false);
  });

  it('transitionIndex returns correct index', () => {
    const marking = MarkingState.builder().tokens(pA, 1).build();
    const dbm = DBM.create(['t1', 't2'], [0, 1], [5, 10]).letTimePass();
    const sc = new StateClass(marking, dbm, [t1, t2]);

    expect(sc.transitionIndex(t1)).toBe(0);
    expect(sc.transitionIndex(t2)).toBe(1);
  });

  it('equals compares marking and DBM', () => {
    const m1 = MarkingState.builder().tokens(pA, 1).build();
    const m2 = MarkingState.builder().tokens(pA, 1).build();
    const dbm1 = DBM.create(['t1'], [0], [5]);
    const dbm2 = DBM.create(['t1'], [0], [5]);
    const dbm3 = DBM.create(['t1'], [0], [10]);

    const sc1 = new StateClass(m1, dbm1, [t1]);
    const sc2 = new StateClass(m2, dbm2, [t1]);
    const sc3 = new StateClass(m1, dbm3, [t1]);

    expect(sc1.equals(sc2)).toBe(true);
    expect(sc1.equals(sc3)).toBe(false);
  });
});
