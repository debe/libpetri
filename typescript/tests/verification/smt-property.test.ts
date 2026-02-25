import { describe, it, expect } from 'vitest';
import {
  deadlockFree, mutualExclusion, placeBound, unreachable,
  propertyDescription,
} from '../../src/verification/smt-property.js';
import { place } from '../../src/core/place.js';

describe('SmtProperty', () => {
  it('deadlockFree factory', () => {
    const prop = deadlockFree();
    expect(prop.type).toBe('deadlock-free');
  });

  it('mutualExclusion factory', () => {
    const p1 = place('A');
    const p2 = place('B');
    const prop = mutualExclusion(p1, p2);
    expect(prop.type).toBe('mutual-exclusion');
    expect(prop.p1.name).toBe('A');
    expect(prop.p2.name).toBe('B');
  });

  it('placeBound factory', () => {
    const p = place('X');
    const prop = placeBound(p, 5);
    expect(prop.type).toBe('place-bound');
    expect(prop.place.name).toBe('X');
    expect(prop.bound).toBe(5);
  });

  it('unreachable factory', () => {
    const p1 = place('A');
    const p2 = place('B');
    const prop = unreachable(new Set([p1, p2]));
    expect(prop.type).toBe('unreachable');
    expect(prop.places.size).toBe(2);
  });

  it('propertyDescription for each type', () => {
    expect(propertyDescription(deadlockFree())).toBe('Deadlock-freedom');

    const p1 = place('A');
    const p2 = place('B');
    expect(propertyDescription(mutualExclusion(p1, p2))).toContain('Mutual exclusion');
    expect(propertyDescription(placeBound(p1, 3))).toContain('bounded by 3');
    expect(propertyDescription(unreachable(new Set([p1, p2])))).toContain('Unreachability');
  });
});
