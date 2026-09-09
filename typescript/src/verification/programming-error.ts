/**
 * @module programming-error
 *
 * Telling a verification failure apart from a bug.
 *
 * The pipeline is full of `catch` blocks that turn a failure into `Unknown`, or
 * into a weaker but still well-formed result. Every one of them was written for a
 * real condition — the solver died, the transport timed out, the replay search ran
 * out of budget — and every one of them quietly acquires a second meaning: *any*
 * defect in the code it guards. Once both arrive as the same verdict they cannot
 * be told apart, and a bug becomes a permanently plausible weaker answer instead
 * of a loud failure. That is the most expensive failure shape this verifier has:
 * a report that looks right and proves less.
 *
 * So the taxonomy is explicit. A `TypeError` or `ReferenceError` is never a
 * verdict — it is a defect in libpetri or in a caller's net, and it propagates. A
 * `RangeError` *is* a verdict: a stack overflow on a deep net is the capacity
 * limit `Unknown` exists to report. Everything else — a dead solver, a bad reply,
 * an exhausted budget — is the condition the catch was written for and passes
 * through untouched.
 */

/**
 * Re-throws `e` when it is a programming defect rather than a verification
 * outcome. Call it first in any `catch` that degrades a result.
 */
export function rethrowIfProgrammingError(e: unknown): void {
  if (e instanceof TypeError || e instanceof ReferenceError) throw e;
}
