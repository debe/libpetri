package org.libpetri.core;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;

/**
 * Context provided to transition actions.
 *
 * <p>Provides filtered access based on structure:
 * <ul>
 *   <li>Input places (consumed tokens)</li>
 *   <li>Read places (context tokens, not consumed)</li>
 *   <li>Output places (where to produce tokens)</li>
 * </ul>
 *
 * <p>Inhibitor and Reset arcs are handled by executor, not exposed to action.
 *
 * <p>This enforces the structure contract - actions can only access places
 * declared in the transition's structure, not arbitrary places.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * TransitionAction action = ctx -> {
 *     var input = ctx.input(INPUT_PLACE);       // consumed
 *     var config = ctx.read(CONFIG_PLACE);      // not consumed (context)
 *     ctx.output(OUTPUT_PLACE, process(input, config));
 *     return CompletableFuture.completedFuture(null);
 * };
 * }</pre>
 */
public final class TransitionContext {

    /**
     * ScopedValue carrying the current TransitionContext during action execution.
     * Allows framework code (logging interceptors, middleware) to access the
     * active transition context without explicit parameter threading.
     *
     * <pre>{@code
     * // Inside a logging adapter or framework interceptor:
     * TransitionContext ctx = TransitionContext.current();
     * if (ctx != null) {
     *     String transition = ctx.transitionName();
     * }
     * }</pre>
     */
    private static final ScopedValue<TransitionContext> CURRENT = ScopedValue.newInstance();

    /**
     * Returns the TransitionContext bound to the current thread, or null if
     * not executing within a transition action.
     */
    public static TransitionContext current() {
        return CURRENT.isBound() ? CURRENT.get() : null;
    }

    /**
     * Returns the ScopedValue carrier for binding during action execution.
     * Used by executors to bind the context before invoking the action.
     *
     * @deprecated This puts {@link ScopedValue} — final only since JDK 25 — in the published
     *     signature, binary-locking the artifact's JDK floor. It is expected to be replaced by
     *     a libpetri-owned carrier that binds the context without exposing {@code ScopedValue},
     *     at which point this becomes removable. To <em>read</em> the ambient context from an
     *     interceptor use {@link #current()}; that does not replace this method, which is what
     *     <em>establishes</em> the binding, so no {@code forRemoval} is declared yet.
     */
    @Deprecated(since = "2.13")
    public static ScopedValue<TransitionContext> scopedValue() {
        return CURRENT;
    }

    /**
     * Process-global fallback counter for {@link #freshName()} when no
     * executor-installed minter is present (e.g. a context built directly in a
     * unit test). Guarantees uniqueness; the executor installs a deterministic
     * per-run minter for replay-stable names.
     */
    private static final AtomicLong GLOBAL_FRESH_NAME_COUNTER = new AtomicLong();

    private Transition transition;
    private TokenInput rawInput;

    /**
     * What the executor harvests. Identical to {@link #writeTarget} until
     * {@link #detachForTimeout()} replaces it with a fresh collector the action cannot reach.
     */
    private TokenOutput rawOutput;

    /**
     * What the action writes to. Never reassigned, so an action already inside
     * {@code output(...)} cannot be redirected mid-write; severance happens by detaching this
     * collector, not by swapping it.
     */
    private TokenOutput writeTarget;
    private Set<Place<?>> allowedInputs;
    private Set<Place<?>> allowedReads;
    private Set<Place<?>> allowedOutputs;
    private Map<Place<?>, Place<?>> placeAlias;
    private Map<Class<?>, Object> executionContext;
    private Supplier<NameId> freshNameSupplier;

    public TransitionContext(Transition transition, TokenInput rawInput, TokenOutput rawOutput) {
        this(transition, rawInput, rawOutput, Map.of());
    }

    public TransitionContext(Transition transition, TokenInput rawInput, TokenOutput rawOutput,
                             Map<Class<?>, Object> executionContext) {
        this.transition = transition;
        this.rawInput = rawInput;
        this.rawOutput = rawOutput;
        this.writeTarget = rawOutput;
        this.allowedInputs = transition.inputPlaces();
        this.allowedReads = transition.readPlaces();
        this.allowedOutputs = transition.outputPlaces();
        this.placeAlias = transition.placeAlias();
        this.executionContext = Map.copyOf(executionContext);
    }

    /**
     * Resolves a place key through the transition's declared&rarr;actual place
     * correspondence (per <b>MOD-031</b>). For a hand-written or
     * directly-composed transition the correspondence is the identity, so this
     * returns {@code place} unchanged; after instancing / port binding it maps a
     * <i>declared</i> place constant the action hardcodes to the <i>actual</i>
     * composed place. The result feeds both the declared-set check and the token
     * store access, so {@code inputPlaces()}/{@code outputPlaces()} discovery is
     * unaffected.
     */
    @SuppressWarnings("unchecked")
    private <T> Place<T> resolve(Place<T> place) {
        return (Place<T>) placeAlias.getOrDefault(place, place);
    }

    /**
     * Updates the execution context for reuse. Input/output must be cleared separately
     * by the caller before re-populating.
     *
     * @param executionContext new execution context map
     */
    public void resetExecutionContext(Map<Class<?>, Object> executionContext) {
        this.executionContext = executionContext.isEmpty() ? Map.of() : Map.copyOf(executionContext);
    }

    // ==================== Input Access (consumed) ====================

    /**
     * Get single consumed input value - throws if place not declared as input.
     *
     * <p>For batched inputs (In.Exactly, In.All, In.AtLeast), use {@link #inputs(Place)} instead.
     *
     * @param place the input place to read from
     * @return the token value
     * @throws IllegalArgumentException if place not declared as input in structure
     * @throws IllegalStateException if multiple tokens were consumed (use inputs() instead)
     */
    public <T> T input(Place<T> place) {
        var actual = resolve(place);
        requireInput(actual);
        return rawInput.value(actual);
    }

    /**
     * Get all consumed input values for a place.
     *
     * @param place the input place to read from
     * @return list of token values
     * @throws IllegalArgumentException if place not declared as input in structure
     */
    public <T> List<T> inputs(Place<T> place) {
        var actual = resolve(place);
        requireInput(actual);
        return rawInput.values(actual);
    }

    /**
     * Get consumed input token with metadata.
     *
     * @param place the input place to read from
     * @return the token with metadata
     * @throws IllegalArgumentException if place not declared as input in structure
     */
    public <T> Token<T> inputToken(Place<T> place) {
        var actual = resolve(place);
        requireInput(actual);
        return rawInput.get(actual);
    }

    /**
     * Returns declared input places (consumed).
     * Useful for structure-aware actions like fork().
     */
    public Set<Place<?>> inputPlaces() {
        return allowedInputs;
    }

    private void requireInput(Place<?> place) {
        if (!allowedInputs.contains(place)) {
            throw new IllegalArgumentException(
                "Place '" + place.name() + "' not in declared inputs: " +
                allowedInputs.stream().map(Place::name).toList()
            );
        }
    }

    // ==================== Read Access (not consumed) ====================

    /**
     * Get read-only context value - throws if place not declared as read.
     *
     * @param place the read place to access
     * @return the token value
     * @throws IllegalArgumentException if place not declared as read in structure
     */
    public <T> T read(Place<T> place) {
        var actual = resolve(place);
        requireRead(actual);
        return rawInput.value(actual);
    }

    /**
     * Get all read-only context values for a place.
     *
     * @param place the read place to access
     * @return list of token values
     * @throws IllegalArgumentException if place not declared as read in structure
     */
    public <T> List<T> reads(Place<T> place) {
        var actual = resolve(place);
        requireRead(actual);
        return rawInput.values(actual);
    }

    /**
     * Returns declared read places (context, not consumed).
     * Useful for structure-aware actions.
     */
    public Set<Place<?>> readPlaces() {
        return allowedReads;
    }

    private void requireRead(Place<?> place) {
        if (!allowedReads.contains(place)) {
            throw new IllegalArgumentException(
                "Place '" + place.name() + "' not in declared reads: " +
                allowedReads.stream().map(Place::name).toList()
            );
        }
    }

    // ==================== Output Access ====================

    /**
     * Add output value - throws if place not declared as output.
     *
     * @param place the output place to write to
     * @param value the value to produce
     * @return this context for chaining
     * @throws IllegalArgumentException if place not declared as output in structure
     */
    public <T> TransitionContext output(Place<T> place, T value) {
        var actual = resolve(place);
        requireOutput(actual);
        writeTarget.add(actual, value);
        return this;
    }

    /**
     * Add output token with metadata.
     *
     * @param place the output place to write to
     * @param token the token to produce
     * @return this context for chaining
     * @throws IllegalArgumentException if place not declared as output in structure
     */
    public <T> TransitionContext output(Place<T> place, Token<T> token) {
        var actual = resolve(place);
        requireOutput(actual);
        writeTarget.add(actual, token);
        return this;
    }

    /**
     * Add multiple output values to the same place in a single call.
     *
     * <p>Equivalent to calling {@link #output(Place, Object)} once per value,
     * but validates the place once up front and uses a tight loop over the
     * underlying collector instead of re-dispatching per element. An empty
     * varargs is a no-op.
     *
     * <h3>Example</h3>
     * <pre>{@code
     * ctx.output(OUTPUT_PLACE, "a", "b", "c");
     * }</pre>
     *
     * @param place  the output place to write to
     * @param values the values to produce
     * @return this context for chaining
     * @throws IllegalArgumentException if place not declared as output in structure
     */
    @SafeVarargs
    public final <T> TransitionContext output(Place<T> place, T... values) {
        var actual = resolve(place);
        requireOutput(actual);
        for (T value : values) {
            writeTarget.add(actual, value);
        }
        return this;
    }

    /**
     * Add multiple output values to the same place in a single call, from an {@link Iterable}.
     *
     * <p>Equivalent to calling {@link #output(Place, Object)} once per value,
     * but validates the place once up front. Accepts any {@code Iterable},
     * including {@code List}, {@code Set}, and streams materialised via
     * {@code ::iterator}.
     *
     * <h3>Example</h3>
     * <pre>{@code
     * List<Integer> counts = computeCounts();
     * ctx.output(COUNTS_PLACE, counts);
     * }</pre>
     *
     * @param place  the output place to write to
     * @param values the values to produce
     * @return this context for chaining
     * @throws IllegalArgumentException if place not declared as output in structure
     */
    public <T> TransitionContext output(Place<T> place, Iterable<? extends T> values) {
        var actual = resolve(place);
        requireOutput(actual);
        for (T value : values) {
            writeTarget.add(actual, value);
        }
        return this;
    }

    /**
     * Severs the action's output from the marking, for use when a firing times out.
     *
     * <p>After this call the action's {@code output(...)} writes are counted and dropped, and
     * the executor harvests a fresh collector the action holds no reference to. Anything the
     * action wrote <em>before</em> the timeout is discarded with it: a partial result merged
     * with the timeout branch would violate the transition's own output spec.
     *
     * <p>This is the only isolation available. libpetri does not own the thread the action
     * runs on, so it cannot stop the work — only stop the result from landing.
     *
     * <p>Must be called by the executor, never by an action.
     */
    public void detachForTimeout() {
        writeTarget.detach();
        rawOutput = new TokenOutput();
    }

    /**
     * Number of action writes rejected since {@link #detachForTimeout()}.
     *
     * <p>Non-zero means the timed-out action was still producing output after the executor
     * gave up on it.
     */
    public int discardedWriteCount() {
        return writeTarget.discardedWriteCount();
    }

    /**
     * Produces into the executor's harvest collector rather than the action's write target.
     *
     * <p>Identical to {@link #output(Place, Object)} before {@link #detachForTimeout()}; after
     * it, this is the only route that still reaches the marking. Used by the executor to
     * deposit the timeout branch.
     *
     * <p>Executor machinery — must be called by the executor, never by an action, like
     * {@link #detachForTimeout()}.
     *
     * @param place the output place to write to
     * @param value the value to produce
     * @return this context for chaining
     * @throws IllegalArgumentException if place not declared as output in structure
     */
    public <T> TransitionContext outputToHarvest(Place<T> place, T value) {
        var actual = resolve(place);
        requireOutput(actual);
        rawOutput.add(actual, value);
        return this;
    }

    /**
     * Returns declared output places.
     * Useful for structure-aware actions like fork().
     */
    public Set<Place<?>> outputPlaces() {
        return allowedOutputs;
    }

    private void requireOutput(Place<?> place) {
        if (!allowedOutputs.contains(place)) {
            throw new IllegalArgumentException(
                "Place '" + place.name() + "' not in declared outputs: " +
                allowedOutputs.stream().map(Place::name).toList()
            );
        }
    }

    // ==================== ν-name minting (NU-010) ====================

    /**
     * Installs the ν-name minter. Wired by the executor at firing time so names
     * minted by {@link #freshName()} are monotonic across the run and
     * instance-prefixed (spec NU-010, NU-030).
     *
     * <p><b>Internal API</b> — the executor is the only legitimate caller.
     *
     * @param supplier the minter
     */
    public void setFreshNameSupplier(Supplier<NameId> supplier) {
        this.freshNameSupplier = supplier;
    }

    /**
     * Mints a fresh ν-name (the ν-binder primitive — spec NU-010).
     *
     * <p>An action calls this on the fork side to create a correlation id, then
     * writes it into the sibling output payloads; a later join correlates those
     * siblings via a {@link MatchSpec}. Uses the executor-installed minter when
     * present; otherwise falls back to a process-global counter prefixed by the
     * transition name (still unique, but not replay-stable across processes).
     *
     * @return a fresh correlation name
     */
    public NameId freshName() {
        if (freshNameSupplier != null) {
            return freshNameSupplier.get();
        }
        return new NameId(transition.name() + "#" + GLOBAL_FRESH_NAME_COUNTER.getAndIncrement());
    }

    // ==================== Structure Info ====================

    /**
     * Returns the transition name.
     */
    public String transitionName() {
        return transition.name();
    }

    // ==================== Execution Context ====================

    /**
     * Retrieves an execution context object by type.
     *
     * <p>Execution context allows external systems (like tracing) to pass
     * data into transition actions without coupling the CTPN module to
     * those systems.
     *
     * @param <T> the context type
     * @param contextType the class of the context object to retrieve
     * @return the context object, or null if not present
     */
    public <T> T executionContext(Class<T> contextType) {
        return contextType.cast(executionContext.get(contextType));
    }

    /**
     * Checks if an execution context object of the given type is present.
     *
     * @param contextType the class of the context object to check
     * @return true if the context is present
     */
    public boolean hasExecutionContext(Class<?> contextType) {
        return executionContext.containsKey(contextType);
    }

    // ==================== Internal ====================

    /**
     * Returns underlying input container for the executor.
     *
     * <p><b>Internal API:</b> This method is intended for use by {@code NetExecutor}
     * to access or reset the raw token input. Application code should
     * use {@link #input(Place)} instead.
     *
     * @return the raw token input container
     */
    public TokenInput rawInput() {
        return rawInput;
    }

    /**
     * Returns underlying output collector for the executor.
     *
     * <p><b>Internal API:</b> This method is intended for use by {@code NetExecutor}
     * to retrieve produced tokens after action completion. Application code should
     * use {@link #output(Place, Object)} instead.
     *
     * <p>Made public to allow cross-package access from {@code runtime.NetExecutor}.
     *
     * @return the raw token output collector
     */
    public TokenOutput rawOutput() {
        return rawOutput;
    }
}
