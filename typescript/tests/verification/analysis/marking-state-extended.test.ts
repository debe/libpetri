import { describe, it, expect } from 'vitest';
import { MarkingState } from '../../../src/verification/marking-state.js';
import { place } from '../../../src/core/place.js';

describe('MarkingState extended operations', () => {
  const pA = place('A');
  const pB = place('B');

  describe('removeTokens', () => {
    it('removes tokens from a place', () => {
      const m = MarkingState.builder()
        .tokens(pA, 5)
        .removeTokens(pA, 2)
        .build();

      expect(m.tokens(pA)).toBe(3);
    });

    it('removes all tokens (to zero)', () => {
      const m = MarkingState.builder()
        .tokens(pA, 3)
        .removeTokens(pA, 3)
        .build();

      expect(m.tokens(pA)).toBe(0);
      expect(m.hasTokens(pA)).toBe(false);
    });

    it('throws on insufficient tokens', () => {
      expect(() =>
        MarkingState.builder()
          .tokens(pA, 2)
          .removeTokens(pA, 5)
      ).toThrow('Cannot remove');
    });
  });

  describe('copyFrom', () => {
    it('copies all token counts from another marking', () => {
      const source = MarkingState.builder()
        .tokens(pA, 3)
        .tokens(pB, 7)
        .build();

      const copy = MarkingState.builder()
        .copyFrom(source)
        .build();

      expect(copy.tokens(pA)).toBe(3);
      expect(copy.tokens(pB)).toBe(7);
      expect(copy.totalTokens()).toBe(10);
    });

    it('overwrites existing values', () => {
      const source = MarkingState.builder().tokens(pA, 5).build();

      const copy = MarkingState.builder()
        .tokens(pA, 1)
        .copyFrom(source)
        .build();

      expect(copy.tokens(pA)).toBe(5);
    });
  });
});
