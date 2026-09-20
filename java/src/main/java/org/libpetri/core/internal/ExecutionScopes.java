package org.libpetri.core.internal;

import java.util.UUID;

/**
 * The execution scope woven into every minted ν-name, {@code <transition>#<scope>:<n>}
 * (<b>NU-011</b>): the default, and the validation of a host-pinned one.
 *
 * <p>One place for both so the two executors and the detached
 * {@link org.libpetri.core.TransitionContext} fallback cannot drift apart on either.
 */
public final class ExecutionScopes {

    private ExecutionScopes() {}

    /**
     * Draws a default scope: exactly 32 lowercase hex characters — 128 bits from the
     * platform's random source ({@link UUID#randomUUID()}, dashes stripped).
     *
     * <p><b>Random, and deliberately not the execution id.</b> The execution id is a process
     * counter ([TIME-015] AC#14), so the first executor of every JVM has id {@code 0}. A
     * restore ([CORE-073]) is routinely the first thing a fresh process does — that is what a
     * durable checkpoint is for — so a default scope equal to the id re-minted, deterministically,
     * the very names sitting in the restored marking, and a [NU-020] join correlating on name
     * equality merged a restored token with an unrelated fresh one without any error. A default
     * that must not collide across processes that share nothing but a persisted snapshot has
     * nothing to derive itself from; it has to be drawn.
     *
     * <p>Randomness is confined to this default. A host that needs a reproducible name sequence
     * pins a scope (NU-011 AC#3), and within any scope — pinned or drawn — {@code <n>} is a
     * plain per-executor counter from 0.
     *
     * @return 32 lowercase hex characters
     */
    public static String random() {
        var uuid = UUID.randomUUID();
        return hex16(uuid.getMostSignificantBits()) + hex16(uuid.getLeastSignificantBits());
    }

    private static String hex16(long bits) {
        var hex = Long.toHexString(bits);
        return "0".repeat(16 - hex.length()) + hex;
    }

    /**
     * Validates a host-pinned scope. The rule is identical in every implementation: reject the
     * empty string, any {@code ':'} and any {@code '#'}.
     *
     * <p>With both separators banned from the scope a minted name parses uniquely even though
     * a transition name may itself contain either: the <b>last</b> {@code ':'} splits off the
     * counter, then the last {@code '#'} before it splits off the scope. Whitespace is
     * <b>not</b> rejected — a blank scope is ugly, not ambiguous.
     *
     * @param scope the scope a host supplied
     * @return {@code scope}
     * @throws IllegalArgumentException if {@code scope} is null, empty, or contains
     *                                  {@code ':'} or {@code '#'}
     */
    public static String requireValid(String scope) {
        if (scope == null || scope.isEmpty()) {
            throw new IllegalArgumentException("executionScope must be non-empty (NU-011)");
        }
        if (scope.indexOf(':') >= 0 || scope.indexOf('#') >= 0) {
            throw new IllegalArgumentException(
                "executionScope must not contain ':' or '#' — they separate the transition, the "
                    + "scope and the counter in <transition>#<scope>:<n>, and a scope holding "
                    + "either makes a minted name ambiguous to parse (NU-011). Got: " + scope);
        }
        return scope;
    }
}
