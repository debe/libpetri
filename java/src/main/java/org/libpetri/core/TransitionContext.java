package org.libpetri.core;

import java.util.List;
import java.util.Map;
import java.util.Set;

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
     */
    public static ScopedValue<TransitionContext> scopedValue() {
        return CURRENT;
    }

    private Transition transition;
    private TokenInput rawInput;
    private TokenOutput rawOutput;
    private Set<Place<?>> allowedInputs;
    private Set<Place<?>> allowedReads;
    private Set<Place<?>> allowedOutputs;
    private Map<Class<?>, Object> executionContext;

    public TransitionContext(Transition transition, TokenInput rawInput, TokenOutput rawOutput) {
        this(transition, rawInput, rawOutput, Map.of());
    }

    public TransitionContext(Transition transition, TokenInput rawInput, TokenOutput rawOutput,
                             Map<Class<?>, Object> executionContext) {
        this.transition = transition;
        this.rawInput = rawInput;
        this.rawOutput = rawOutput;
        this.allowedInputs = transition.inputPlaces();
        this.allowedReads = transition.readPlaces();
        this.allowedOutputs = transition.outputPlaces();
        this.executionContext = Map.copyOf(executionContext);
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
        requireInput(place);
        return rawInput.value(place);
    }

    /**
     * Get all consumed input values for a place.
     *
     * @param place the input place to read from
     * @return list of token values
     * @throws IllegalArgumentException if place not declared as input in structure
     */
    public <T> List<T> inputs(Place<T> place) {
        requireInput(place);
        return rawInput.values(place);
    }

    /**
     * Get consumed input token with metadata.
     *
     * @param place the input place to read from
     * @return the token with metadata
     * @throws IllegalArgumentException if place not declared as input in structure
     */
    public <T> Token<T> inputToken(Place<T> place) {
        requireInput(place);
        return rawInput.get(place);
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
        requireRead(place);
        return rawInput.value(place);
    }

    /**
     * Get all read-only context values for a place.
     *
     * @param place the read place to access
     * @return list of token values
     * @throws IllegalArgumentException if place not declared as read in structure
     */
    public <T> List<T> reads(Place<T> place) {
        requireRead(place);
        return rawInput.values(place);
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
        requireOutput(place);
        rawOutput.add(place, value);
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
        requireOutput(place);
        rawOutput.add(place, token);
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
