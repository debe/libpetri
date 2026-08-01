import { describe, it, expect } from 'vitest';
import { inputArc, outputArc, inhibitorArc, readArc, resetArc } from '../../src/core/arc.js';
import { place } from '../../src/core/place.js';

describe('Arc', () => {
  const p = place<number>('P');

  it('creates input arc', () => {
    const arc = inputArc(p);
    expect(arc.type).toBe('input');
    expect(arc.place).toBe(p);
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
