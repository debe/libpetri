package org.libpetri.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Collects output tokens produced by a transition action.
 *
 * <p>Thread safety is provided by returning this through {@link java.util.concurrent.CompletionStage} -
 * the happens-before relationship is implicit in how the future delivers results.
 *
 * <p><b>The {@code Out.Timeout} path.</b> When a firing times out, the executor <em>detaches</em>
 * this collector (see {@link #detach()}) and harvests a different one, so the timeout branch and
 * any still-running action write to distinct instances — they never touch the same list. A write
 * that races the detach lands in a collector nobody harvests; its only visible effect is that
 * {@link #discardedWriteCount()} may not count it.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * .action((in, out) -> {
 *     Request request = in.value(requestPlace);
 *     out.add(responsePlace, process(request));
 *     return CompletableFuture.completedFuture(out);
 * })
 * }</pre>
 *
 * @see TokenInput for reading input tokens
 */
public final class TokenOutput {

    private final List<Entry> entries = new ArrayList<>();

    /**
     * Epoch clock stamping tokens built from a raw value, or {@code null} for
     * {@link Token#of(Object)} (wall clock).
     *
     * <p>This is the <b>token-stamping boundary</b> of <b>TIME-015</b>. A transition action
     * reaches the executor's epoch clock only through here: {@link #add(Place, Object)}
     * constructs the {@link Token} itself, so there is no other interception point between
     * {@code ctx.output(place, value)} and the produced marking. Tokens the caller has
     * already built ({@link #add(Place, Token)}) carry their own timestamp and are passed
     * through untouched — the host stamped those.
     *
     * <p>Null rather than a default supplier: the standalone path then pays a predictable
     * branch instead of an indirection, per TIME-015's zero-cost-when-unused rule.
     */
    private final java.util.function.Supplier<java.time.Instant> clock;

    /** Creates a collector stamping tokens with the wall clock. */
    public TokenOutput() {
        this.clock = null;
    }

    /**
     * Creates a collector stamping tokens from a host-supplied epoch clock, without
     * changing the standalone token-creation path (<b>TIME-015</b>).
     *
     * @param clock the epoch clock; must not be null
     */
    public TokenOutput(java.util.function.Supplier<java.time.Instant> clock) {
        this.clock = java.util.Objects.requireNonNull(clock, "clock");
    }

    /**
     * Once true, further writes are rejected and counted instead of appended.
     *
     * <p>Volatile so the abandoned action's thread observes the flag promptly. The executor
     * stops harvesting this collector at the same moment it detaches, so the flag is a
     * best-effort courtesy — it turns an abandoned write into a counted no-op rather than a
     * silent one — not a correctness barrier.
     */
    private volatile boolean detached = false;

    /**
     * Best-effort count of writes rejected since {@link #detach()}. Written only after
     * {@code detached}, i.e. never on the hot path; a plain volatile increment, so concurrent
     * abandoned writers may under-count.
     */
    private volatile int discardedWrites = 0;

    /**
     * A fresh, empty collector stamping through the <b>same</b> epoch clock as this one.
     *
     * <p>Exists for {@link TransitionContext#detachForTimeout()}, which replaces the harvested
     * collector when an action times out. Building a bare {@code new TokenOutput()} there
     * silently drops the clock, so every recovery token would carry wall time under an injected
     * clock — at precisely the moment [TIME-015] AC#13 is under test. The timeout path is the
     * one place tokens are minted somewhere other than the collector the executor handed the
     * action, which is what makes it easy to miss.
     *
     * @return an empty collector with this one's clock
     */
    public TokenOutput freshWithSameClock() {
        return clock == null ? new TokenOutput() : new TokenOutput(clock);
    }

    /**
     * Add a token to an output place.
     *
     * @param place the output place
     * @param value the token value
     * @return this for chaining
     */
    public <T> TokenOutput add(Place<T> place, T value) {
        if (detached) { discardedWrites++; return this; }
        entries.add(new Entry(place, clock == null ? Token.of(value) : new Token<>(value, clock.get())));
        return this;
    }

    /**
     * Add a token to an output place.
     *
     * @param place the output place
     * @param token the token
     * @return this for chaining
     */
    public <T> TokenOutput add(Place<T> place, Token<T> token) {
        if (detached) { discardedWrites++; return this; }
        entries.add(new Entry(place, token));
        return this;
    }

    /**
     * Severs this collector: subsequent {@link #add} calls are counted and dropped.
     *
     * <p>Called by the executor (via {@link TransitionContext#detachForTimeout()}) when a
     * firing times out, so that the action it has stopped waiting for can no longer reach the
     * marking. Package-private — this is executor machinery, not part of the action-facing
     * surface. Irreversible.
     */
    void detach() {
        detached = true;
    }

    /**
     * Number of writes rejected since {@link #detach()}.
     *
     * <p>A non-zero value means a timed-out action was still running and still producing
     * output after the executor gave up on it — useful for spotting actions that overrun
     * their declared budget. Package-private; surfaced to the runtime via
     * {@link TransitionContext#discardedWriteCount()}.
     */
    int discardedWriteCount() {
        return discardedWrites;
    }

    /**
     * Returns all collected outputs.
     */
    public List<Entry> entries() {
        return entries;
    }

    /**
     * Check if any outputs were produced.
     */
    public boolean isEmpty() {
        return entries.isEmpty();
    }

    /**
     * Clears all collected outputs for reuse.
     */
    public void clear() {
        entries.clear();
    }

    /**
     * Returns the set of places that received tokens.
     * Used by the executor for output validation.
     */
    public Set<Place<?>> placesWithTokens() {
        var set = new HashSet<Place<?>>(entries.size() * 2);
        for (var entry : entries) set.add(entry.place());
        return set;
    }

    /**
     * An output entry: place + token pair.
     */
    public record Entry(Place<?> place, Token<?> token) {}

}
