import { describe, it, expect } from 'vitest';
import {
  and, andPlaces, xor, xorPlaces, outPlace, timeout, timeoutPlace,
  forwardInput, allPlaces, enumerateBranches,
} from '../../src/core/out.js';
import { place } from '../../src/core/place.js';

describe('Out', () => {
  const a = place('A');
  const b = place('B');
  const c = place('C');
  const d = place('D');

  describe('factory functions', () => {
    it('creates place spec', () => {
      const spec = outPlace(a);
      expect(spec.type).toBe('place');
      expect(spec.place).toBe(a);
    });

    it('creates AND spec', () => {
      const spec = and(outPlace(a), outPlace(b));
      expect(spec.type).toBe('and');
      expect(spec.children).toHaveLength(2);
    });

    it('creates AND from places', () => {
      const spec = andPlaces(a, b, c);
      expect(spec.type).toBe('and');
      expect(spec.children).toHaveLength(3);
    });

    it('AND requires at least 1 child', () => {
      expect(() => and()).toThrow('at least 1');
    });

    it('creates XOR spec', () => {
      const spec = xor(outPlace(a), outPlace(b));
      expect(spec.type).toBe('xor');
      expect(spec.children).toHaveLength(2);
    });

    it('creates XOR from places', () => {
      const spec = xorPlaces(a, b);
      expect(spec.type).toBe('xor');
    });

    it('XOR requires at least 2 children', () => {
      expect(() => xor(outPlace(a))).toThrow('at least 2');
    });

    it('creates timeout spec', () => {
      const spec = timeout(5000, outPlace(a));
      expect(spec.type).toBe('timeout');
      expect(spec.afterMs).toBe(5000);
    });

    it('creates timeout place shorthand', () => {
      const spec = timeoutPlace(3000, a);
      expect(spec.type).toBe('timeout');
      expect(spec.child.type).toBe('place');
    });

    it('timeout rejects non-positive duration', () => {
      expect(() => timeout(0, outPlace(a))).toThrow('positive');
      expect(() => timeout(-1, outPlace(a))).toThrow('positive');
    });

    it('creates forward-input spec', () => {
      const spec = forwardInput(a, b);
      expect(spec.type).toBe('forward-input');
      expect(spec.from).toBe(a);
      expect(spec.to).toBe(b);
    });
  });

  describe('allPlaces', () => {
    it('single place', () => {
      const places = allPlaces(outPlace(a));
      expect(places.size).toBe(1);
      expect(places.has(a)).toBe(true);
    });

    it('AND collects all', () => {
      const places = allPlaces(andPlaces(a, b, c));
      expect(places.size).toBe(3);
    });

    it('XOR collects all', () => {
      const places = allPlaces(xorPlaces(a, b));
      expect(places.size).toBe(2);
    });

    it('nested structure', () => {
      const spec = xor(andPlaces(a, b), andPlaces(c, d));
      const places = allPlaces(spec);
      expect(places.size).toBe(4);
    });

    it('timeout delegates to child', () => {
      const places = allPlaces(timeout(1000, outPlace(a)));
      expect(places.size).toBe(1);
      expect(places.has(a)).toBe(true);
    });

    it('forward-input uses "to" place', () => {
      const places = allPlaces(forwardInput(a, b));
      expect(places.size).toBe(1);
      expect(places.has(b)).toBe(true);
    });
  });

  describe('enumerateBranches', () => {
    it('single place = one branch with one place', () => {
      const branches = enumerateBranches(outPlace(a));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.has(a)).toBe(true);
    });

    it('AND = single branch with all places', () => {
      const branches = enumerateBranches(andPlaces(a, b));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.size).toBe(2);
    });

    it('XOR = one branch per child', () => {
      const branches = enumerateBranches(xorPlaces(a, b));
      expect(branches).toHaveLength(2);
    });

    it('XOR of ANDs', () => {
      const spec = xor(andPlaces(a, b), andPlaces(c, d));
      const branches = enumerateBranches(spec);
      expect(branches).toHaveLength(2);
      expect(branches[0]!.size).toBe(2);
      expect(branches[1]!.size).toBe(2);
    });

    it('AND of XORs = Cartesian product', () => {
      const spec = and(xorPlaces(a, b), xorPlaces(c, d));
      const branches = enumerateBranches(spec);
      expect(branches).toHaveLength(4);
      // Each branch should have 2 places (one from each XOR)
      for (const branch of branches) {
        expect(branch.size).toBe(2);
      }
    });
  });
});
