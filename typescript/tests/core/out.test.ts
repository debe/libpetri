import { describe, it, expect } from 'vitest';
import {
  and, andPlaces, xor, xorPlaces, outOne, outExactly, timeout, timeoutPlace,
  forwardInput, allPlaces, enumerateBranches,
} from '../../src/core/out.js';
import { place } from '../../src/core/place.js';

describe('Out', () => {
  const a = place('A');
  const b = place('B');
  const c = place('C');
  const d = place('D');

  describe('factory functions', () => {
    it('creates one spec', () => {
      const spec = outOne(a);
      expect(spec.type).toBe('one');
      expect(spec.place).toBe(a);
    });

    it('creates exactly spec', () => {
      const spec = outExactly(3, a);
      expect(spec.type).toBe('exactly');
      expect(spec.place).toBe(a);
      expect(spec.count).toBe(3);
    });

    it('exactly rejects count < 1', () => {
      expect(() => outExactly(0, a)).toThrow('>= 1');
      expect(() => outExactly(-1, a)).toThrow('>= 1');
    });

    it('exactly rejects non-integer count', () => {
      expect(() => outExactly(1.5, a)).toThrow('integer');
    });

    it('creates AND spec', () => {
      const spec = and(outOne(a), outOne(b));
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
      const spec = xor(outOne(a), outOne(b));
      expect(spec.type).toBe('xor');
      expect(spec.children).toHaveLength(2);
    });

    it('creates XOR from places', () => {
      const spec = xorPlaces(a, b);
      expect(spec.type).toBe('xor');
    });

    it('XOR requires at least 2 children', () => {
      expect(() => xor(outOne(a))).toThrow('at least 2');
    });

    it('creates timeout spec', () => {
      const spec = timeout(5000, outOne(a));
      expect(spec.type).toBe('timeout');
      expect(spec.afterMs).toBe(5000);
    });

    it('creates timeout place shorthand', () => {
      const spec = timeoutPlace(3000, a);
      expect(spec.type).toBe('timeout');
      expect(spec.child.type).toBe('one');
    });

    it('timeout rejects non-positive duration', () => {
      expect(() => timeout(0, outOne(a))).toThrow('positive');
      expect(() => timeout(-1, outOne(a))).toThrow('positive');
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
      const places = allPlaces(outOne(a));
      expect(places.size).toBe(1);
      expect(places.has(a)).toBe(true);
    });

    it('exactly contributes its place (no multiplicity in allPlaces)', () => {
      const places = allPlaces(outExactly(5, a));
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
      const places = allPlaces(timeout(1000, outOne(a)));
      expect(places.size).toBe(1);
      expect(places.has(a)).toBe(true);
    });

    it('forward-input uses "to" place', () => {
      const places = allPlaces(forwardInput(a, b));
      expect(places.size).toBe(1);
      expect(places.has(b)).toBe(true);
    });
  });

  describe('enumerateBranches (multiset)', () => {
    it('single one = one branch with count 1', () => {
      const branches = enumerateBranches(outOne(a));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.get(a)).toBe(1);
    });

    it('exactly = one branch with count N', () => {
      const branches = enumerateBranches(outExactly(3, a));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.get(a)).toBe(3);
    });

    it('AND = single branch with all counts', () => {
      const branches = enumerateBranches(andPlaces(a, b));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.size).toBe(2);
      expect(branches[0]!.get(a)).toBe(1);
      expect(branches[0]!.get(b)).toBe(1);
    });

    it('AND with repeated place sums counts', () => {
      const branches = enumerateBranches(andPlaces(a, a, a));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.size).toBe(1);
      expect(branches[0]!.get(a)).toBe(3);
    });

    it('AND mixed exactly and one sums', () => {
      const branches = enumerateBranches(and(outExactly(2, a), outOne(a)));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.get(a)).toBe(3);
    });

    it('AND of two exactly sums', () => {
      const branches = enumerateBranches(and(outExactly(2, a), outExactly(3, a)));
      expect(branches).toHaveLength(1);
      expect(branches[0]!.get(a)).toBe(5);
    });

    it('XOR = one branch per child, each with count 1', () => {
      const branches = enumerateBranches(xorPlaces(a, b));
      expect(branches).toHaveLength(2);
      expect(branches[0]!.get(a)).toBe(1);
      expect(branches[1]!.get(b)).toBe(1);
    });

    it('XOR same place different counts indexed separately', () => {
      const branches = enumerateBranches(xor(outOne(a), outExactly(3, a)));
      expect(branches).toHaveLength(2);
      expect(branches[0]!.get(a)).toBe(1);
      expect(branches[1]!.get(a)).toBe(3);
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
      for (const branch of branches) {
        expect(branch.size).toBe(2);
      }
    });
  });
});
