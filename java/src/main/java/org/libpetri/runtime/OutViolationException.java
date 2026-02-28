package org.libpetri.runtime;

/**
 * Exception thrown when output validation fails.
 *
 * <p>This occurs when a transition's action does not satisfy the declared
 * output specification:
 * <ul>
 *   <li>AND-split: not all required outputs were produced</li>
 *   <li>XOR-split: zero or more than one branch was produced</li>
 * </ul>
 *
 * <p>This exception indicates a programming error in the transition action
 * that violates the structural contract declared in the net definition.
 *
 * @see org.libpetri.core.Arc.Out
 */
public class OutViolationException extends RuntimeException {

    /**
     * Creates a new OutViolationException with the given message.
     *
     * @param message description of the violation
     */
    public OutViolationException(String message) {
        super(message);
    }

    /**
     * Creates a new OutViolationException with the given message and cause.
     *
     * @param message description of the violation
     * @param cause underlying cause
     */
    public OutViolationException(String message, Throwable cause) {
        super(message, cause);
    }
}
