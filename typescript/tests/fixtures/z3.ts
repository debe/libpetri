import { describe } from 'vitest';
import { readdirSync } from 'node:fs';
import { z3Available } from '../../src/verification/z3/z3-process.js';

/**
 * Whether a usable `z3` executable resolves (`LIBPETRI_Z3` or `PATH`, >= 4.8.0).
 * Solver-backed suites skip themselves without one; `z3-gate.test.ts` turns that
 * skip into a failure on a CI runner (VER-013).
 */
export const Z3_AVAILABLE = z3Available();

/** `describe` for suites that run the solver. */
export const describeZ3 = describe.skipIf(!Z3_AVAILABLE);

/** The files of a `LIBPETRI_SMT_DUMP` directory in dump order. */
export function dumpedFiles(dir: string): string[] {
  return readdirSync(dir).sort((a, b) => parseInt(a, 10) - parseInt(b, 10) || (a < b ? -1 : a > b ? 1 : 0));
}

/**
 * A dump file's name without its counter (`001-horn.smt2` → `horn.smt2`). The counter is
 * process-wide, so any earlier dump in the process, as with the variable exported, moves it.
 */
export function dumpPhase(name: string): string {
  return name.replace(/^\d+-/, '');
}
