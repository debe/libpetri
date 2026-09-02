import { describe } from 'vitest';
import { z3Available } from '../../src/verification/z3/z3-process.js';

/**
 * Whether a usable `z3` executable resolves (`LIBPETRI_Z3` or `PATH`, >= 4.8.0).
 * Solver-backed suites skip themselves without one; `z3-gate.test.ts` turns that
 * skip into a failure on a CI runner (VER-013).
 */
export const Z3_AVAILABLE = z3Available();

/** `describe` for suites that run the solver. */
export const describeZ3 = describe.skipIf(!Z3_AVAILABLE);
