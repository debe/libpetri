import { describe, it, expect } from 'vitest';
import { DBM } from '../../../src/verification/analysis/dbm.js';

describe('DBM', () => {
  it('creates initial DBM with correct bounds', () => {
    const dbm = DBM.create(['t1', 't2'], [1, 2], [5, 10]);

    expect(dbm.isEmpty()).toBe(false);
    expect(dbm.clockCount()).toBe(2);
    expect(dbm.getLowerBound(0)).toBe(1);
    expect(dbm.getUpperBound(0)).toBe(5);
    expect(dbm.getLowerBound(1)).toBe(2);
    expect(dbm.getUpperBound(1)).toBe(10);
  });

  it('creates empty DBM', () => {
    const dbm = DBM.empty(['t1']);

    expect(dbm.isEmpty()).toBe(true);
    expect(dbm.clockCount()).toBe(1);
    expect(dbm.getLowerBound(0)).toBe(0);
    expect(dbm.getUpperBound(0)).toBe(Infinity);
    expect(dbm.canFire(0)).toBe(false);
  });

  it('detects empty zone from contradictory constraints', () => {
    // lower > upper → empty
    const dbm = DBM.create(['t1'], [10], [5]);
    expect(dbm.isEmpty()).toBe(true);
  });

  it('letTimePass sets lower bounds to 0', () => {
    const dbm = DBM.create(['t1', 't2'], [3, 5], [10, 20]);

    expect(dbm.getLowerBound(0)).toBe(3);
    expect(dbm.getLowerBound(1)).toBe(5);

    const after = dbm.letTimePass();
    expect(after.getLowerBound(0)).toBe(0);
    expect(after.getLowerBound(1)).toBe(0);
    expect(after.getUpperBound(0)).toBe(10);
    expect(after.getUpperBound(1)).toBe(20);
  });

  it('canFire after time passage', () => {
    const dbm = DBM.create(['t1'], [3], [10]);
    expect(dbm.canFire(0)).toBe(false); // lower=3, not yet fireable

    const after = dbm.letTimePass();
    expect(after.canFire(0)).toBe(true);
  });

  it('fireTransition computes successor zone', () => {
    // Two transitions: t1 in [1,5], t2 in [2,10]
    let dbm = DBM.create(['t1', 't2'], [1, 2], [5, 10]);
    dbm = dbm.letTimePass();

    // Fire t1 (index 0), t2 persists, no new transitions
    const successor = dbm.fireTransition(0, [], [], [], [1]);

    expect(successor.isEmpty()).toBe(false);
    expect(successor.clockCount()).toBe(1);
    expect(successor.clockNames[0]).toBe('t2');
    // After firing t1 at time θ₁, t2's remaining time is θ₂ - θ₁
    expect(successor.getLowerBound(0)).toBeGreaterThanOrEqual(0);
  });

  it('fireTransition with new transitions', () => {
    let dbm = DBM.create(['t1'], [0], [5]);
    dbm = dbm.letTimePass();

    // Fire t1, no persistent, new transition t2
    const successor = dbm.fireTransition(0, ['t2'], [1], [8], []);

    expect(successor.isEmpty()).toBe(false);
    expect(successor.clockCount()).toBe(1);
    expect(successor.clockNames[0]).toBe('t2');
    expect(successor.getLowerBound(0)).toBe(1);
    expect(successor.getUpperBound(0)).toBe(8);
  });

  it('equality with epsilon comparison', () => {
    const a = DBM.create(['t1'], [1], [5]);
    const b = DBM.create(['t1'], [1], [5]);
    const c = DBM.create(['t1'], [1], [6]);

    expect(a.equals(b)).toBe(true);
    expect(a.equals(c)).toBe(false);
  });

  it('empty DBMs are equal', () => {
    const a = DBM.empty(['t1']);
    const b = DBM.empty(['t2']);
    expect(a.equals(b)).toBe(true);
  });

  it('toString formats bounds', () => {
    const dbm = DBM.create(['t1'], [1], [5]);
    expect(dbm.toString()).toContain('t1');
    expect(dbm.toString()).toContain('[1,5]');
  });

  it('empty toString', () => {
    expect(DBM.empty([]).toString()).toBe('DBM[empty]');
  });

  it('Floyd-Warshall tightens inter-clock constraints', () => {
    // t1 in [0,3], t2 in [0,5]
    const dbm = DBM.create(['t1', 't2'], [0, 0], [3, 5]);
    // After canonicalization, the inter-clock constraint should be tightened
    expect(dbm.isEmpty()).toBe(false);
    expect(dbm.getUpperBound(0)).toBe(3);
    expect(dbm.getUpperBound(1)).toBe(5);
  });
});

// VER-010/011: the zone key is the FULL canonical matrix, and clock order is a
// presentation detail the graph normalises away.
describe('DBM zone identity', () => {
  it('permuted() reorders clocks without changing the zone', () => {
    // f ∈ [0,1] fires first; u ∈ [2,4] and v ∈ [0,1] persist, w is newly enabled.
    const base = DBM.create(['f', 'u', 'v'], [0, 2, 0], [1, 4, 1]);
    const a = base.fireTransition(0, ['w'], [0], [1], [1, 2]).letTimePass(); // clocks u, v, w
    const b = a.permuted([2, 0, 1]); // clocks w, u, v
    expect(b.clockNames).toEqual(['w', 'u', 'v']);
    expect(b.getLowerBound(1)).toBe(a.getLowerBound(0));
    expect(b.getUpperBound(1)).toBe(a.getUpperBound(0));
    expect(b.getUpperBound(0)).toBe(a.getUpperBound(2));
    // Permuting back restores the exact matrix.
    expect(b.permuted([1, 2, 0]).equals(a)).toBe(true);
    expect(b.permuted([1, 2, 0]).zoneKey()).toBe(a.zoneKey());
    // The projection string follows the clock order; the zone did not change.
    expect(b.toString()).not.toBe(a.toString());
  });

  it('zoneKey() separates zones that share every per-clock projection', () => {
    // Zone A: u − v ≥ 1 (u and v aged together under f), w fresh and unrelated.
    const a = DBM.create(['f', 'u', 'v'], [0, 2, 0], [1, 4, 1])
      .fireTransition(0, ['w'], [0], [1], [1, 2])
      .letTimePass();
    // Zone B: u − w ≥ 1, v fresh and unrelated — built with the roles of v and w
    // swapped, then permuted into the same clock order.
    const b = DBM.create(['f', 'u', 'w'], [0, 2, 0], [1, 4, 1])
      .fireTransition(0, ['v'], [0], [1], [1, 2])
      .letTimePass()
      .permuted([0, 2, 1]);
    expect(a.clockNames).toEqual(['u', 'v', 'w']);
    expect(b.clockNames).toEqual(['u', 'v', 'w']);
    // Identical projections: the old key would have merged these two classes.
    expect(a.toString()).toBe(b.toString());
    // Different zones: the difference constraint sits between different clocks.
    expect(a.equals(b)).toBe(false);
    expect(a.zoneKey()).not.toBe(b.zoneKey());
  });

  it('zoneKey() of an empty zone is stable', () => {
    expect(DBM.empty(['t1']).zoneKey()).toBe('DBM[empty]');
  });
});
