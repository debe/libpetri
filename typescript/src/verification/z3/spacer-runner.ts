/**
 * @module spacer-runner
 *
 * Runs Z3 Spacer on a HORN script through one `z3` process (VER-013) and
 * classifies the reply in verdict terms.
 *
 * HORN/Spacer convention (shared with the Rust and Java verifiers and corroborated
 * by the certificate check): with the query `(assert (not Error))`, z3 prints `sat`
 * when the property is PROVEN (an inductive invariant excluding every violating
 * state exists) and `unsat` when it is VIOLATED (no such invariant; the refutation
 * proof carries the counterexample states).
 */
import { failureReason, runZ3Text, timeoutBudget, type Z3Solver } from './z3-process.js';
import { classifyFirstLine, extractInvariant } from './smt-text.js';

/** Result of a Spacer query. */
export type QueryResult = QueryProven | QueryViolated | QueryUnknown;

/** Property proven (z3 `sat`). */
export interface QueryProven {
  readonly type: 'proven';
  /**
   * The `(define-fun …)` block of the model, verbatim (the certificate the
   * certificate checker re-validates), or `null` when no model printed.
   */
  readonly invariantFormula: string | null;
}

/** Property violated (z3 `unsat`). */
export interface QueryViolated {
  readonly type: 'violated';
  /** The raw solver reply; the refutation proof in it is decoded by the counterexample decoder. */
  readonly answer: string;
}

/** Solver could not determine (timeout, resource limit, transport failure). */
export interface QueryUnknown {
  readonly type: 'unknown';
  readonly reason: string;
}

/**
 * Runs `smt2` with `fp.engine=spacer`. `phase` names the dump files (`horn` or
 * `horn-coloured`).
 */
export async function runZ3Spacer(
  solver: Z3Solver,
  timeoutMs: number,
  smt2: string,
  phase: string,
): Promise<QueryResult> {
  let reply;
  try {
    reply = await runZ3Text(solver, smt2, phase, timeoutMs, ['fp.engine=spacer']);
  } catch (e: any) {
    return { type: 'unknown', reason: String(e?.message ?? e) };
  }
  const stdout = reply.stdout.trim();

  // The verdict is a LINE anywhere in the reply, never its first bytes: the script
  // asks for both (get-proof) and (get-model), one of which answers `(error …)` on
  // either branch, and a build is free to print a warning first.
  switch (classifyFirstLine(stdout)) {
    // unsat => no inductive invariant excludes the bad state => VIOLATED.
    case 'unsat':
      return { type: 'violated', answer: stdout };
    // sat => an inductive invariant exists => PROVEN.
    case 'sat':
      return { type: 'proven', invariantFormula: extractInvariant(stdout) };
    case 'unknown':
      return { type: 'unknown', reason: 'Z3 answered unknown' };
    default:
      // No verdict at all: the `-T` backstop, the watchdog, an `(error …)` on
      // either stream, in that order (VER-013).
      return { type: 'unknown', reason: failureReason(reply, timeoutBudget(timeoutMs)) };
  }
}
