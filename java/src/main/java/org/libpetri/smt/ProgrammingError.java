package org.libpetri.smt;

/**
 * Telling a verification failure apart from a bug.
 *
 * <p>The pipeline is full of {@code catch} blocks that turn a failure into {@code Unknown},
 * or into a weaker but still well-formed result. Every one of them was written for a real
 * condition — the solver died, the transport timed out, the replay search ran out of budget
 * — and every one of them quietly acquires a second meaning: <em>any</em> defect in the code
 * it guards. Once both arrive as the same verdict they cannot be told apart, and a bug
 * becomes a permanently plausible weaker answer instead of a loud failure. That is the most
 * expensive failure shape this verifier has: a report that looks right and proves less.
 *
 * <p>So the taxonomy is explicit. A {@link NullPointerException}, {@link ClassCastException},
 * {@link IndexOutOfBoundsException} or {@link ArrayStoreException} is never a verdict — it is
 * a defect in libpetri or in a caller's net, and it propagates. A {@link StackOverflowError}
 * <em>is</em> a verdict: a deep net overflowing the stack is the capacity limit
 * {@code Unknown} exists to report, which is why it is deliberately absent from the list
 * above (the TypeScript verifier makes the same split, re-throwing {@code TypeError} /
 * {@code ReferenceError} and keeping {@code RangeError}). Everything else — a dead solver, a
 * bad reply, an exhausted budget, an {@link ArithmeticException} from a deliberate
 * {@code Math.*Exact} overflow probe — is the condition the catch was written for and passes
 * through untouched.
 *
 * <p>Most of this verifier's catches name a narrow checked or domain exception
 * ({@code Z3ProcessException}, {@code IOException}, {@code NumberFormatException}) and are
 * safe by construction: a defect cannot reach them. This helper is for the few that catch
 * {@code RuntimeException} wholesale.
 */
public final class ProgrammingError {

    private ProgrammingError() {}

    /**
     * Re-throws {@code e} when it is a programming defect rather than a verification
     * outcome. Call it first in any {@code catch} that degrades a result.
     */
    public static void rethrowIfProgrammingError(Throwable e) {
        switch (e) {
            case NullPointerException npe -> throw npe;
            case ClassCastException cce -> throw cce;
            case IndexOutOfBoundsException ioobe -> throw ioobe;
            case ArrayStoreException ase -> throw ase;
            default -> {
                // Not a defect: the condition the caller's catch was written for.
            }
        }
    }
}
