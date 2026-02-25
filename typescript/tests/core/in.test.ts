import { describe, it, expect } from 'vitest';
import { one, exactly, all, atLeast, requiredCount, consumptionCount } from '../../src/core/in.js';
import { place } from '../../src/core/place.js';

describe('In', () => {
  const p = place<string>('P');

  describe('One', () => {
    it('creates one spec', () => {
      const spec = one(p);
      expect(spec.type).toBe('one');
      expect(spec.place).toBe(p);
    });

    it('requires 1 token', () => {
      expect(requiredCount(one(p))).toBe(1);
    });

    it('consumes exactly 1', () => {
      expect(consumptionCount(one(p), 5)).toBe(1);
      expect(consumptionCount(one(p), 1)).toBe(1);
    });
  });

  describe('Exactly', () => {
    it('creates exactly spec', () => {
      const spec = exactly(3, p);
      expect(spec.type).toBe('exactly');
      expect(spec.count).toBe(3);
    });

    it('rejects count < 1', () => {
      expect(() => exactly(0, p)).toThrow('count must be >= 1');
      expect(() => exactly(-1, p)).toThrow('count must be >= 1');
    });

    it('requires count tokens', () => {
      expect(requiredCount(exactly(5, p))).toBe(5);
    });

    it('consumes exactly count', () => {
      expect(consumptionCount(exactly(3, p), 10)).toBe(3);
      expect(consumptionCount(exactly(3, p), 3)).toBe(3);
    });
  });

  describe('All', () => {
    it('creates all spec', () => {
      const spec = all(p);
      expect(spec.type).toBe('all');
    });

    it('requires 1 token', () => {
      expect(requiredCount(all(p))).toBe(1);
    });

    it('consumes all available', () => {
      expect(consumptionCount(all(p), 7)).toBe(7);
      expect(consumptionCount(all(p), 1)).toBe(1);
    });
  });

  describe('AtLeast', () => {
    it('creates atLeast spec', () => {
      const spec = atLeast(3, p);
      expect(spec.type).toBe('at-least');
      expect(spec.minimum).toBe(3);
    });

    it('rejects minimum < 1', () => {
      expect(() => atLeast(0, p)).toThrow('minimum must be >= 1');
    });

    it('requires minimum tokens', () => {
      expect(requiredCount(atLeast(5, p))).toBe(5);
    });

    it('consumes all available', () => {
      expect(consumptionCount(atLeast(3, p), 10)).toBe(10);
      expect(consumptionCount(atLeast(3, p), 3)).toBe(3);
    });
  });

  describe('consumptionCount validation', () => {
    it('throws if not enough tokens available', () => {
      expect(() => consumptionCount(one(p), 0)).toThrow('Cannot consume');
      expect(() => consumptionCount(exactly(3, p), 2)).toThrow('Cannot consume');
      expect(() => consumptionCount(all(p), 0)).toThrow('Cannot consume');
      expect(() => consumptionCount(atLeast(5, p), 4)).toThrow('Cannot consume');
    });
  });
});
