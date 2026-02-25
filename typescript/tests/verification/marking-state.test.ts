import { describe, it, expect } from 'vitest';
import { MarkingState } from '../../src/verification/marking-state.js';
import { place } from '../../src/core/place.js';

describe('MarkingState', () => {
  const pA = place('A');
  const pB = place('B');
  const pC = place('C');

  it('empty marking has no tokens', () => {
    const m = MarkingState.empty();
    expect(m.isEmpty()).toBe(true);
    expect(m.tokens(pA)).toBe(0);
    expect(m.hasTokens(pA)).toBe(false);
    expect(m.totalTokens()).toBe(0);
  });

  it('builder sets token counts', () => {
    const m = MarkingState.builder()
      .tokens(pA, 2)
      .tokens(pB, 1)
      .build();

    expect(m.tokens(pA)).toBe(2);
    expect(m.tokens(pB)).toBe(1);
    expect(m.tokens(pC)).toBe(0);
    expect(m.hasTokens(pA)).toBe(true);
    expect(m.hasTokens(pC)).toBe(false);
    expect(m.isEmpty()).toBe(false);
    expect(m.totalTokens()).toBe(3);
  });

  it('builder with zero count removes place', () => {
    const m = MarkingState.builder()
      .tokens(pA, 3)
      .tokens(pA, 0)
      .build();

    expect(m.tokens(pA)).toBe(0);
    expect(m.isEmpty()).toBe(true);
  });

  it('builder rejects negative count', () => {
    expect(() => MarkingState.builder().tokens(pA, -1)).toThrow('negative');
  });

  it('addTokens increments', () => {
    const m = MarkingState.builder()
      .tokens(pA, 2)
      .addTokens(pA, 3)
      .build();

    expect(m.tokens(pA)).toBe(5);
  });

  it('hasTokensInAny checks multiple places', () => {
    const m = MarkingState.builder()
      .tokens(pB, 1)
      .build();

    expect(m.hasTokensInAny([pA, pB])).toBe(true);
    expect(m.hasTokensInAny([pA, pC])).toBe(false);
  });

  it('toString shows sorted places', () => {
    const m = MarkingState.builder()
      .tokens(pB, 2)
      .tokens(pA, 1)
      .build();

    const str = m.toString();
    expect(str).toBe('{A:1, B:2}');
  });

  it('empty marking toString', () => {
    expect(MarkingState.empty().toString()).toBe('{}');
  });
});
