import { expect } from 'vitest';
import { existsSync, readFileSync } from 'node:fs';

/**
 * The golden diff of the SMT script parity tests (VER-013 AC1): `smt-script-parity.test.ts` over
 * `fixtures.json`, and the NU-054 relay parity in `nu-join-relay.test.ts` over
 * `nu-relay-fixtures.json`. Goldens are written by Rust only (`scripts/smt-script-parity.py
 * --update`); a diff is a parity FINDING in whichever emitter drifted, never a reason to edit one.
 */
function firstDifference(expected: string, actual: string): string {
  const e = expected.split('\n');
  const a = actual.split('\n');
  for (let i = 0; i < Math.min(e.length, a.length); i++) {
    if (e[i] !== a[i]) return `line ${i + 1}:\n  golden: ${e[i]}\n  actual: ${a[i]}`;
  }
  return `one text is a prefix of the other (golden ${e.length} lines, actual ${a.length} lines)`;
}

/** Asserts that `actual` is byte-identical to the golden at `golden`, and absent when it is. */
export function compareScript(id: string, golden: string, actual: string | null): void {
  if (!existsSync(golden)) {
    expect(actual, `SCRIPT PARITY FINDING [${id}]: this encoding emits ${golden} but no golden exists (run scripts/smt-script-parity.py --update)`).toBeNull();
    return;
  }
  const expected = readFileSync(golden, 'utf8');
  expect(actual, `SCRIPT PARITY FINDING [${id}]: ${golden} exists but this encoding emits no such script`).not.toBeNull();
  if (actual !== expected) {
    expect.fail(`SCRIPT PARITY FINDING [${id}]: ${golden} differs from the Rust golden at ${firstDifference(expected, actual!)} — report the divergence, never edit the golden by hand`);
  }
}
