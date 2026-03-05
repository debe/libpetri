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
