import { describe, it, expect } from 'vitest';
import { isProven, isViolated } from '../../src/verification/smt-verification-result.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';

describe('SmtVerificationResult', () => {
  const baseResult: Omit<SmtVerificationResult, 'verdict'> = {
    report: 'test report',
    invariants: [],
    discoveredInvariants: [],
    counterexampleTrace: [],
    counterexampleTransitions: [],
    elapsedMs: 100,
    statistics: { places: 2, transitions: 1, invariantsFound: 0, structuralResult: 'test' },
  };

  it('isProven returns true for proven verdict', () => {
    const result: SmtVerificationResult = {
      ...baseResult,
      verdict: { type: 'proven', method: 'IC3/PDR', inductiveInvariant: null },
    };
    expect(isProven(result)).toBe(true);
    expect(isViolated(result)).toBe(false);
  });

  it('isViolated returns true for violated verdict', () => {
    const result: SmtVerificationResult = {
      ...baseResult,
      verdict: { type: 'violated' },
    };
    expect(isProven(result)).toBe(false);
    expect(isViolated(result)).toBe(true);
  });

  it('unknown verdict', () => {
    const result: SmtVerificationResult = {
      ...baseResult,
      verdict: { type: 'unknown', reason: 'timeout' },
    };
    expect(isProven(result)).toBe(false);
    expect(isViolated(result)).toBe(false);
    expect(result.verdict.type).toBe('unknown');
  });
});
