import { describe, it, expect } from 'vitest';
import { inputArc, outputArc, inhibitorArc, readArc, resetArc, hasGuard, matchesGuard } from '../../src/core/arc.js';
import { place } from '../../src/core/place.js';

describe('Arc', () => {
  const p = place<number>('P');

  it('creates input arc without guard', () => {
    const arc = inputArc(p);
    expect(arc.type).toBe('input');
    expect(arc.place).toBe(p);
    expect(arc.guard).toBeUndefined();
    expect(hasGuard(arc)).toBe(false);
  });

  it('creates input arc with guard', () => {
    const arc = inputArc(p, (v) => v > 10);
    expect(arc.type).toBe('input');
    expect(hasGuard(arc)).toBe(true);
    expect(matchesGuard(arc, 20)).toBe(true);
    expect(matchesGuard(arc, 5)).toBe(false);
  });

  it('guard-less input arc matches anything', () => {
    const arc = inputArc(p);
    expect(matchesGuard(arc, 42)).toBe(true);
    expect(matchesGuard(arc, 0)).toBe(true);
  });

  it('creates output arc', () => {
    const arc = outputArc(p);
    expect(arc.type).toBe('output');
    expect(arc.place).toBe(p);
  });

  it('creates inhibitor arc', () => {
    const arc = inhibitorArc(p);
    expect(arc.type).toBe('inhibitor');
    expect(arc.place).toBe(p);
  });

  it('creates read arc', () => {
    const arc = readArc(p);
    expect(arc.type).toBe('read');
    expect(arc.place).toBe(p);
  });

  it('creates reset arc', () => {
    const arc = resetArc(p);
    expect(arc.type).toBe('reset');
    expect(arc.place).toBe(p);
  });
});
