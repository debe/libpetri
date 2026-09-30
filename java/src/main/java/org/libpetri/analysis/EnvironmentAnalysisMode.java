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
 *   <li>{@link #bounded(int)} - At most k tokens <b>resident</b> in each environment place
 *       at a time: injection refills the place up to k, forever ([VER-006]).</li>
 *   <li>{@link #arrivals(int)} - At most k tokens injected into each environment place
 *       <b>in total</b>, over the whole run ([VER-006]); a net rewrite {@code SmtVerifier}
 *       applies before any route.</li>
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
     * At most {@code maxTokens} tokens <b>resident</b> in each environment place at a time
     * ([VER-006]): injection refills the place up to {@code maxTokens}, forever, so a
     * transition takes at most {@code maxTokens} from it per firing, but the total injected
     * over a run is unbounded. For a bound on the total, use {@link #arrivals(int)}.
     *
     * <p>The model is the executor only when no transition deposits into an environment place
     * and the initial marking holds at most {@code maxTokens} on each one ([VER-006] AC3).
     * {@code SmtVerifier} checks both and answers Unknown, naming the place, when either fails.
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
     * At most {@code maxTokens} tokens injected into each environment place <b>in total</b>,
     * over the whole run ([VER-006]).
     *
     * <p>A net rewrite, not an encoding: before any route runs, {@code SmtVerifier} closes the
     * net as [VER-022] closes an optional arrival group ({@code min = 0}, {@code max = k}) — the
     * {@code i}-th registered environment place {@code P} gets a source place
     * {@code env:optional[i]} holding {@code maxTokens} tokens, an injection transition
     * {@code env:arrive?[i]:P} moving one token onto {@code P}, and a transition
     * {@code env:decline[i]} with no output that discards one. Every arrival is optional, so a
     * run may rest after any number of them from 0 to {@code maxTokens}: "at most" holds for
     * quiescence properties as well as for safety. The rewritten net has no environment places,
     * so enumeration, P-invariants and quiescence apply as on any closed net; counterexample
     * traces name the injection transitions (one firing per arrival) and the declines.
     * {@code arrivals(0)} injects nothing: the environment places are ordinary places.
     *
     * <p>Only {@code SmtVerifier} (and {@code SubnetDef.verify}, which uses it) applies the
     * rewrite. The state-class graph and the flattener refuse this mode for a net that still
     * has environment places: close the net first.
     *
     * @param maxTokens the most tokens injected into each environment place over a run
     * @return arrivals mode with the specified total
     * @throws IllegalArgumentException if maxTokens is negative
     */
    static EnvironmentAnalysisMode arrivals(int maxTokens) {
        if (maxTokens < 0) {
            throw new IllegalArgumentException("maxTokens must be non-negative");
        }
        return new Arrivals(0, maxTokens);
    }

    /**
     * Between {@code minTokens} and {@code maxTokens} tokens injected into each environment
     * place <b>in total</b>, over the whole run ([VER-006]). {@code arrivals(k)} is
     * {@code arrivals(0, k)}; {@code arrivals(k, k)} injects exactly {@code k}.
     *
     * <p>The same rewrite as {@link #arrivals(int)}, mapped 1:1 onto a [VER-022] arrival group
     * with these bounds: the {@code i}-th registered environment place {@code P} gets a
     * mandatory source {@code env:arrivals[i]} holding {@code minTokens} with an injection
     * transition {@code env:arrive[i]:P}, and an optional source {@code env:optional[i]} holding
     * {@code maxTokens − minTokens} with {@code env:arrive?[i]:P} and {@code env:decline[i]}. A
     * source whose count is {@code 0} is omitted with its transitions. A run is quiescent only
     * once every mandatory arrival has been injected, so exact accounting ("{@code k} inputs
     * arrive ⇒ {@code k} outcomes at quiescence") is provable under {@code arrivals(k, k)},
     * where {@code arrivals(k)} is always violated by a run that declines.
     *
     * @param minTokens the fewest tokens injected into each environment place over a run
     * @param maxTokens the most tokens injected into each environment place over a run
     * @return arrivals mode with the specified bounds
     * @throws IllegalArgumentException if minTokens is negative or maxTokens is less than minTokens
     */
    static EnvironmentAnalysisMode arrivals(int minTokens, int maxTokens) {
        if (minTokens < 0) {
            throw new IllegalArgumentException("minTokens must be non-negative");
        }
        if (maxTokens < minTokens) {
            throw new IllegalArgumentException(
                "maxTokens must be at least minTokens, got " + minTokens + ".." + maxTokens);
        }
        return new Arrivals(minTokens, maxTokens);
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
     * Arrivals mode: between {@code minTokens} and {@code maxTokens} tokens injected into each
     * environment place over a run.
     *
     * @param minTokens the mandatory part of the total per environment place
     * @param maxTokens the most tokens per environment place
     */
    record Arrivals(int minTokens, int maxTokens) implements EnvironmentAnalysisMode {
        /** Refuses {@code minTokens < 0} and {@code maxTokens < minTokens}. */
        public Arrivals {
            if (minTokens < 0 || maxTokens < minTokens) {
                throw new IllegalArgumentException(
                    "arrivals needs 0 <= minTokens <= maxTokens, got " + minTokens + ".." + maxTokens);
            }
        }

        /** {@code arrivals(maxTokens)}: at most {@code maxTokens}, none mandatory. */
        public Arrivals(int maxTokens) {
            this(0, maxTokens);
        }

        /** The refusal of an analysis that would have to model injection itself. */
        public static IllegalArgumentException notModelled(String where) {
            return new IllegalArgumentException(where + ": EnvironmentAnalysisMode.arrivals(k) is a net "
                + "rewrite applied by SmtVerifier (VER-006); close the net first and analyse it without "
                + "environment places");
        }
    }

    /**
     * Ignore mode: environment places are treated as regular places.
     */
    record Ignore() implements EnvironmentAnalysisMode {
        static final Ignore INSTANCE = new Ignore();
    }
}
