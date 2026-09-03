import { describe, it, expect } from 'vitest';
import { z3Available } from '../../src/verification/z3/z3-process.js';

/**
 * CI gate for the z3 executable (VER-013), the TypeScript mirror of Rust's
 * `tests/z3_gate.rs` and Java's `Z3BinaryGateTest`.
 *
 * Every solver-backed suite (`describeZ3`) skips itself when no usable `z3`
 * resolves, so the verifier could ship unverified because the checks did not run.
 * Locally that skip is a legitimate choice; on a CI runner (`CI` set) it is a red
 * build. This file carries no skip of its own.
 */
describe('z3 gate', () => {
  it('a usable z3 executable must resolve on a CI runner', () => {
    const available = z3Available();
    if (process.env['CI'] == null) return; // developer machine: skipping is legitimate
    expect(
      available,
      'no usable z3 executable resolves (PATH or LIBPETRI_Z3, >= 4.8.0), so the verdict-parity ' +
        'runner, the certificate check and the counterexample replay skipped themselves. Fix the ' +
        'runner rather than relaxing this assertion.',
    ).toBe(true);
  });
});
