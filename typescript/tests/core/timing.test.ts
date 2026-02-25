import { describe, it, expect } from 'vitest';
import {
  immediate, deadline, delayed, window, exact,
  earliest, latest, hasDeadline, MAX_DURATION_MS,
} from '../../src/core/timing.js';

describe('Timing', () => {
  describe('Immediate', () => {
    const t = immediate();
    it('type is immediate', () => expect(t.type).toBe('immediate'));
    it('earliest is 0', () => expect(earliest(t)).toBe(0));
    it('latest is MAX', () => expect(latest(t)).toBe(MAX_DURATION_MS));
    it('has no deadline', () => expect(hasDeadline(t)).toBe(false));
  });

  describe('Deadline', () => {
    const t = deadline(5000);
    it('type is deadline', () => expect(t.type).toBe('deadline'));
    it('earliest is 0', () => expect(earliest(t)).toBe(0));
    it('latest is deadline', () => expect(latest(t)).toBe(5000));
    it('has deadline', () => expect(hasDeadline(t)).toBe(true));

    it('rejects non-positive', () => {
      expect(() => deadline(0)).toThrow('positive');
      expect(() => deadline(-1)).toThrow('positive');
    });
  });

  describe('Delayed', () => {
    const t = delayed(1000);
    it('type is delayed', () => expect(t.type).toBe('delayed'));
    it('earliest is delay', () => expect(earliest(t)).toBe(1000));
    it('latest is MAX', () => expect(latest(t)).toBe(MAX_DURATION_MS));
    it('has no deadline', () => expect(hasDeadline(t)).toBe(false));

    it('rejects negative', () => {
      expect(() => delayed(-1)).toThrow('non-negative');
    });

    it('allows zero delay', () => {
      expect(earliest(delayed(0))).toBe(0);
    });
  });

  describe('Window', () => {
    const t = window(100, 5000);
    it('type is window', () => expect(t.type).toBe('window'));
    it('earliest is lower bound', () => expect(earliest(t)).toBe(100));
    it('latest is upper bound', () => expect(latest(t)).toBe(5000));
    it('has deadline', () => expect(hasDeadline(t)).toBe(true));

    it('rejects negative earliest', () => {
      expect(() => window(-1, 100)).toThrow('non-negative');
    });

    it('rejects latest < earliest', () => {
      expect(() => window(100, 50)).toThrow('>= earliest');
    });

    it('allows equal bounds', () => {
      const w = window(100, 100);
      expect(earliest(w)).toBe(100);
      expect(latest(w)).toBe(100);
    });
  });

  describe('Exact', () => {
    const t = exact(500);
    it('type is exact', () => expect(t.type).toBe('exact'));
    it('earliest equals atMs', () => expect(earliest(t)).toBe(500));
    it('latest equals atMs', () => expect(latest(t)).toBe(500));
    it('has deadline', () => expect(hasDeadline(t)).toBe(true));

    it('rejects negative', () => {
      expect(() => exact(-1)).toThrow('non-negative');
    });

    it('allows zero', () => {
      expect(earliest(exact(0))).toBe(0);
    });
  });
});
