package org.libpetri.analysis;

/**
 * Analysis mode for environment places in state class graph construction.
 *
 * <p>Environment places model the boundary between the controlled Petri net
 * and its external environment. Different analysis modes control how the
 * analyzer treats tokens in these places.
 *
 * <h2>Modes</h2>
 * <ul>
 *   <li>{@link #alwaysAvailable()} - Assumes environment places always have
 *       sufficient tokens. Useful for checking if the net can handle continuous input.</li>
 *   <li>{@link #bounded(int)} - Analyzes with a bounded number of tokens (0 to k).
 *       Creates a finite state space for bounded analysis.</li>
 *   <li>{@link #ignore()} - Treats environment places as regular places.
 *       Useful for analyzing net structure without environment interaction.</li>
 * </ul>
 *
 * <h2>Example</h2>
 * <pre>{@code
 * var result = TimePetriNetAnalyzer.forNet(net)
 *     .initialMarking(MarkingState.empty())
 *     .goalPlaces(output)
 *     .environmentPlaces(inputEnv)
 *     .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
 *     .build()
 *     .analyze();
 * }</pre>
 *
 * @see TimePetriNetAnalyzer
 * @see StateClassGraph
 */
public sealed interface EnvironmentAnalysisMode {

    /**
     * Assumes environment places always have sufficient tokens.
     *
     * <p>In this mode, any transition with inputs only from environment places
     * is considered enabled (regardless of actual token count). This is useful
     * for analyzing liveness assuming the environment cooperates.
     *
     * <p><b>Warning:</b> This may lead to infinite state spaces if the net
     * produces unbounded tokens based on environment input.
     *
     * @return always-available mode
     */
    static EnvironmentAnalysisMode alwaysAvailable() {
        return AlwaysAvailable.INSTANCE;
    }

    /**
     * Analyzes with a bounded number of tokens in environment places.
     *
     * <p>The analyzer considers states with 0, 1, ..., k tokens in each
     * environment place. This creates a finite state space suitable for
     * complete reachability analysis.
     *
     * @param maxTokens maximum number of tokens to consider (k)
     * @return bounded mode with specified limit
     * @throws IllegalArgumentException if maxTokens is negative
     */
    static EnvironmentAnalysisMode bounded(int maxTokens) {
        if (maxTokens < 0) {
            throw new IllegalArgumentException("maxTokens must be non-negative");
        }
        return new Bounded(maxTokens);
    }

    /**
     * Treats environment places as regular places.
     *
     * <p>Standard Petri net semantics apply - transitions are only enabled
     * when their input places (including environment places) have tokens.
     * Use this for structural analysis without environment modeling.
     *
     * @return ignore mode
     */
    static EnvironmentAnalysisMode ignore() {
        return Ignore.INSTANCE;
    }

    /**
     * Always-available mode: environment places are assumed to always have tokens.
     */
    record AlwaysAvailable() implements EnvironmentAnalysisMode {
        static final AlwaysAvailable INSTANCE = new AlwaysAvailable();
    }

    /**
     * Bounded mode: environment places are analyzed up to k tokens.
     *
     * @param maxTokens maximum tokens to consider per environment place
     */
    record Bounded(int maxTokens) implements EnvironmentAnalysisMode {}

    /**
     * Ignore mode: environment places are treated as regular places.
     */
    record Ignore() implements EnvironmentAnalysisMode {
        static final Ignore INSTANCE = new Ignore();
    }
}
