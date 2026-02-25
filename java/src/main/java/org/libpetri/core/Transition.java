package org.libpetri.core;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.ListMultimap;

import java.time.Duration;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static java.lang.System.Logger.Level;

/**
 * A transition in the Time Petri Net that transforms tokens.
 * <p>
 * Transitions are the "actions" of the net. When enabled and fired, they:
 * <ol>
 *   <li>Consume tokens from input places</li>
 *   <li>Execute their action (sync or async)</li>
 *   <li>Produce tokens to output places</li>
 * </ol>
 *
 * <h3>Enablement</h3>
 * A transition is enabled when:
 * <ul>
 *   <li>All input places have required tokens (matching guards if specified)</li>
 *   <li>All read places have required tokens</li>
 *   <li>No inhibitor places have tokens</li>
 * </ul>
 *
 * <h3>Time Semantics</h3>
 * Each transition has a {@link FiringInterval} [earliest, deadline]:
 * <ul>
 *   <li>Cannot fire before earliest time after becoming enabled</li>
 *   <li>Must fire (or be disabled) before deadline</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var process = Transition.builder("ProcessRequest")
 *     .input(requestPlace)
 *     .read(configPlace)          // read config without consuming
 *     .inhibitor(pausedPlace)     // don't process if paused
 *     .output(responsePlace)
 *     .deadline(Duration.ofSeconds(30))
 *     .priority(10)               // higher priority fires first
 *     .action((in, out) -> {
 *         var request = in.value(requestPlace);
 *         var config = in.value(configPlace);
 *         return service.process(request, config)
 *             .thenAccept(response -> out.add(responsePlace, response));
 *     })
 *     .build();
 * }</pre>
 *
 * <h3>Identity</h3>
 * Uses identity-based equality (each instance is unique regardless of name).
 * The name is purely a label for display/debugging/export.
 */
public final class Transition {
    private static final System.Logger LOG = System.getLogger(Transition.class.getName());

    private final String name;

    // NEW: Typed input/output specs with cardinality and split semantics
    private final List<In> inputSpecs;
    private final Out outputSpec;

    // Legacy fields (kept for backward compatibility during migration)
    @Deprecated(forRemoval = true)
    private final ListMultimap<Place<?>, Arc.Input<?>> inputs;
    @Deprecated(forRemoval = true)
    private final List<Arc.Output<?>> outputs;

    private final List<Arc.Inhibitor<?>> inhibitors;
    private final List<Arc.Read<?>> reads;
    private final List<Arc.Reset<?>> resets;
    private final FiringInterval interval;
    private final Timing timing;
    private final Out.Timeout actionTimeout;  // Cached from outputSpec at build time, null if no timeout
    private final TransitionAction action;
    private final int priority;

    private Transition(
        String name,
        List<In> inputSpecs,
        Out outputSpec,
        ListMultimap<Place<?>, Arc.Input<?>> inputs,
        List<Arc.Output<?>> outputs,
        List<Arc.Inhibitor<?>> inhibitors,
        List<Arc.Read<?>> reads,
        List<Arc.Reset<?>> resets,
        FiringInterval interval,
        Timing timing,
        TransitionAction action,
        int priority
    ) {
        this.name = name;
        this.inputSpecs = List.copyOf(inputSpecs);
        this.outputSpec = outputSpec;
        this.inputs = ImmutableListMultimap.copyOf(inputs);
        this.outputs = List.copyOf(outputs);
        this.inhibitors = List.copyOf(inhibitors);
        this.reads = List.copyOf(reads);
        this.resets = List.copyOf(resets);
        this.interval = interval;
        this.timing = timing;
        this.actionTimeout = findTimeout(outputSpec);  // Cached at build time
        this.action = action;
        this.priority = priority;
    }

    /**
     * Recursively searches the output spec for a Timeout node.
     * Used at build time to cache timeout for O(1) runtime lookup.
     *
     * <p><b>Note:</b> If multiple Timeout nodes exist in the structure (e.g., in a XOR),
     * only the first one found is returned. This is typically acceptable since XOR
     * branches represent mutually exclusive outcomes, and multiple timeouts would
     * be redundant. If you need multiple timeout durations, structure them in
     * separate XOR branches.
     *
     * @param out the output specification to search
     * @return the first Timeout found, or null if none exists
     */
    private static Out.Timeout findTimeout(Out out) {
        return switch (out) {
            case null -> null;
            case Out.Timeout t -> t;
            case Out.And a -> a.children().stream()
                .map(Transition::findTimeout)
                .filter(Objects::nonNull)
                .findFirst().orElse(null);
            case Out.Xor x -> x.children().stream()
                .map(Transition::findTimeout)
                .filter(Objects::nonNull)
                .findFirst().orElse(null);
            case Out.Place _ -> null;
            case Out.ForwardInput _ -> null;
        };
    }

    /** Label for display/debugging/export. Not used for identity. */
    public String name() { return name; }

    // ==================== NEW: Typed Input/Output Specs ====================

    /**
     * Returns the input specifications with cardinality.
     * Use this for enablement checks and token consumption.
     */
    public List<In> inputSpecs() { return inputSpecs; }

    /**
     * Returns the output specification (composite AND/XOR structure).
     * Use this for output validation.
     */
    public Out outputSpec() { return outputSpec; }

    // ==================== Legacy Accessors (deprecated) ====================

    /**
     * Returns the input arcs grouped by place (multimap).
     * @deprecated Use {@link #inputSpecs()} instead
     */
    @Deprecated(forRemoval = true)
    public ListMultimap<Place<?>, Arc.Input<?>> inputs() { return inputs; }

    /**
     * @deprecated Use {@link #outputSpec()} instead
     */
    @Deprecated(forRemoval = true)
    public List<Arc.Output<?>> outputs() { return outputs; }

    public List<Arc.Inhibitor<?>> inhibitors() { return inhibitors; }
    public List<Arc.Read<?>> reads() { return reads; }
    public List<Arc.Reset<?>> resets() { return resets; }

    /**
     * Returns the firing interval.
     * @deprecated Use {@link #timing()} instead
     */
    @Deprecated(forRemoval = true)
    public FiringInterval interval() { return interval; }

    /**
     * Returns the timing specification for when this transition can/must fire.
     */
    public Timing timing() { return timing; }

    /**
     * Returns true if this transition has an action timeout specified in the output spec.
     */
    public boolean hasActionTimeout() { return actionTimeout != null; }

    /**
     * Returns the action timeout if present, or null if no timeout is specified.
     */
    public Out.Timeout actionTimeout() { return actionTimeout; }

    public TransitionAction action() { return action; }
    public int priority() { return priority; }

    // ==================== Place Sets for TransitionContext ====================

    /**
     * Returns set of input places - consumed tokens.
     * Used by TransitionContext to enforce structure constraints.
     * Merges both new inputSpecs and legacy inputs.
     */
    public Set<Place<?>> inputPlaces() {
        var places = new HashSet<Place<?>>();
        // New style
        for (var in : inputSpecs) {
            places.add(in.place());
        }
        // Legacy style (for backward compatibility)
        places.addAll(inputs.keySet());
        return Set.copyOf(places);
    }

    /**
     * Returns set of read places - context tokens, not consumed.
     * Used by TransitionContext to enforce structure constraints.
     */
    public Set<Place<?>> readPlaces() {
        return reads.stream()
            .map(Arc.Read::place)
            .collect(Collectors.toUnmodifiableSet());
    }

    /**
     * Returns set of output places - where tokens are produced.
     * Used by TransitionContext to enforce structure constraints.
     * Merges both new outputSpec and legacy outputs.
     */
    public Set<Place<?>> outputPlaces() {
        var places = new HashSet<Place<?>>();
        // New style
        if (outputSpec != null) {
            places.addAll(outputSpec.allPlaces());
        }
        // Legacy style (for backward compatibility)
        for (var arc : outputs) {
            places.add(arc.place());
        }
        return Set.copyOf(places);
    }

    // Uses Object.equals/hashCode (identity-based) - no override needed

    @Override
    public String toString() {
        return "Transition[" + name + "]";
    }

    public static Builder builder(String name) {
        return new Builder(name);
    }

    public static class Builder {
        private final String name;

        // NEW: Typed input/output specs
        private final ArrayList<In> inputSpecs = new ArrayList<>();
        private Out outputSpec = null;

        // Legacy fields (for backward compatibility)
        private final ArrayListMultimap<Place<?>, Arc.Input<?>> inputs = ArrayListMultimap.create();
        private final ArrayList<Arc.Output<?>> outputs = new ArrayList<>();

        private final ArrayList<Arc.Inhibitor<?>> inhibitors = new ArrayList<>();
        private final ArrayList<Arc.Read<?>> reads = new ArrayList<>();
        private final ArrayList<Arc.Reset<?>> resets = new ArrayList<>();
        private FiringInterval interval = FiringInterval.unconstrained();
        private Timing timing = Timing.unconstrained();
        private TransitionAction action = TransitionAction.passthrough();
        private int priority = 0;

        private Builder(String name) {
            this.name = name;
        }

        // ==================== NEW: Typed Input/Output Methods ====================

        /**
         * Add input specifications with cardinality.
         *
         * <p>Example:
         * <pre>{@code
         * .inputs(In.one(headerPlace), In.atLeast(1, lineItemPlace))
         * }</pre>
         *
         * @param specs input specifications
         * @return this builder
         */
        public Builder inputs(In... specs) {
            inputSpecs.addAll(List.of(specs));
            return this;
        }

        /**
         * Set the output specification (composite AND/XOR structure).
         *
         * <p>Example:
         * <pre>{@code
         * .outputs(Out.xor(successPlace, errorPlace))
         * .outputs(Out.and(p1, p2, p3))
         * .outputs(Out.xor(Out.and(a, b), Out.and(c, d)))
         * }</pre>
         *
         * @param spec output specification
         * @return this builder
         */
        public Builder outputs(Out spec) {
            this.outputSpec = spec;
            return this;
        }

        // ==================== Legacy Methods (deprecated) ====================

        /**
         * @deprecated Use {@code inputs(In.one(place))} instead
         */
        @Deprecated(forRemoval = true)
        public <T> Builder input(Place<T> place) {
            inputs.put(place, new Arc.Input<>(place));
            return this;
        }

        /**
         * Add an existing input arc (preserves guards).
         * Used primarily for rebuilding transitions with different actions.
         * @deprecated Use {@code inputs(In.one(place))} instead
         */
        @Deprecated(forRemoval = true)
        public Builder inputArc(Arc.Input<?> arc) {
            inputs.put(arc.place(), arc);
            return this;
        }

        /**
         * Add an input arc with a guard predicate (colored Petri net semantics).
         * The transition only enables when a token matching the predicate exists.
         *
         * <p>Example - only accept ProductsFound tokens from a SearchResult place:
         * <pre>{@code
         * .inputWhen(searchResult, r -> r instanceof ProductsFound)
         * }</pre>
         *
         * @param place The input place
         * @param guard Predicate that tokens must satisfy to enable this transition
         * @deprecated Guards on inputs should use multiple transitions for CPN compliance
         */
        @Deprecated(forRemoval = true)
        public <T> Builder inputWhen(Place<T> place, Predicate<T> guard) {
            var arc = new Arc.Input<>(place, guard);
            inputs.put(place, arc);
            return this;
        }

        /**
         * Add input places (legacy vararg version).
         * @deprecated Use {@code inputs(In.one(p1), In.one(p2), ...)} instead
         */
        @Deprecated(forRemoval = true)
        public Builder inputs(Place<?>... places) {
            for (var place : places) inputs.put(place, new Arc.Input<>(place));
            return this;
        }

        /**
         * Add output places (legacy vararg version).
         * @deprecated Use {@code outputs(Out.and(p1, p2, ...))} instead
         */
        @Deprecated(forRemoval = true)
        public Builder outputs(Place<?>... places) {
            for (var place : places) outputs.add(new Arc.Output<>(place));
            return this;
        }

        /**
         * @deprecated Use {@code outputs(Out.and(place))} instead
         */
        @Deprecated(forRemoval = true)
        public <T> Builder output(Place<T> place) {
            outputs.add(new Arc.Output<>(place));
            return this;
        }

        /**
         * Add an existing output arc.
         * @deprecated Use {@code outputs(Out.and(place))} instead
         */
        @Deprecated(forRemoval = true)
        public Builder outputArc(Arc.Output<?> arc) {
            outputs.add(arc);
            return this;
        }

        public <T> Builder inhibitor(Place<T> place) {
            inhibitors.add(new Arc.Inhibitor<>(place));
            return this;
        }

        /** Add an existing inhibitor arc. */
        public Builder inhibitorArc(Arc.Inhibitor<?> arc) {
            inhibitors.add(arc);
            return this;
        }

        public Builder inhibitors(Place<?>... places) {
            for (var place : places) inhibitors.add(new Arc.Inhibitor<>(place));
            return this;
        }

        public <T> Builder read(Place<T> place) {
            reads.add(new Arc.Read<>(place));
            return this;
        }

        /** Add an existing read arc. */
        public Builder readArc(Arc.Read<?> arc) {
            reads.add(arc);
            return this;
        }

        public Builder reads(Place<?>... places) {
            for (var place : places) reads.add(new Arc.Read<>(place));
            return this;
        }

        public <T> Builder reset(Place<T> place) {
            resets.add(new Arc.Reset<>(place));
            return this;
        }

        /** Add an existing reset arc. */
        public Builder resetArc(Arc.Reset<?> arc) {
            resets.add(arc);
            return this;
        }

        public Builder resets(Place<?>... places) {
            for (var place : places) resets.add(new Arc.Reset<>(place));
            return this;
        }

        /**
         * Sets the firing interval (legacy).
         * @deprecated Use {@link #timing(Timing)} instead
         */
        @Deprecated(forRemoval = true)
        public Builder interval(FiringInterval interval) {
            this.interval = interval;
            // Also update timing for forward compatibility
            this.timing = Timing.window(interval.earliest(), interval.latest());
            return this;
        }

        /**
         * Sets the timing specification for when this transition can/must fire.
         *
         * <p>Example:
         * <pre>{@code
         * .timing(Timing.window(Duration.ofMillis(500), Duration.ofSeconds(10)))
         * .timing(Timing.delayed(Duration.ofMillis(100)))
         * }</pre>
         *
         * @param timing the timing specification
         * @return this builder
         */
        public Builder timing(Timing timing) {
            this.timing = timing;
            // Also update interval for backward compatibility
            this.interval = timing.toInterval();
            return this;
        }

        /**
         * Shorthand for immediate firing with a deadline.
         * @deprecated Use {@link #timing(Timing)} with {@link Timing#deadline(Duration)} instead
         */
        @Deprecated(forRemoval = true)
        public Builder deadline(java.time.Duration deadline) {
            this.interval = FiringInterval.immediate(deadline);
            this.timing = Timing.deadline(deadline);
            return this;
        }

        /**
         * Shorthand for immediate firing with a deadline in milliseconds.
         * @deprecated Use {@link #timing(Timing)} with {@link Timing#deadline(Duration)} instead
         */
        @Deprecated(forRemoval = true)
        public Builder deadline(long millis) {
            var duration = java.time.Duration.ofMillis(millis);
            this.interval = FiringInterval.immediate(duration);
            // Handle deadline(0) as immediate firing (for backward compatibility)
            this.timing = millis <= 0 ? Timing.immediate() : Timing.deadline(duration);
            return this;
        }

        public Builder action(TransitionAction action) {
            this.action = action;
            return this;
        }

        public Builder priority(int priority) {
            this.priority = priority;
            return this;
        }

        public Transition build() {
            var transition = new Transition(name, inputSpecs, outputSpec, inputs, outputs, inhibitors, reads, resets, interval, timing, action, priority);

            // Warn if a place appears in both new and legacy input APIs
            var newApiPlaces = inputSpecs.stream().map(In::place).collect(Collectors.toSet());
            var legacyApiPlaces = inputs.keySet();
            var duplicates = new HashSet<>(newApiPlaces);
            duplicates.retainAll(legacyApiPlaces);
            if (!duplicates.isEmpty()) {
                LOG.log(Level.WARNING,
                    "Transition ''{0}'' has places in both new and legacy input APIs: {1}. " +
                    "This may cause double token consumption.",
                    name, duplicates.stream().map(Place::name).collect(Collectors.joining(", ")));
            }

            // Validate ForwardInput references valid input places and type compatibility
            if (outputSpec != null) {
                var inputPlaces = transition.inputPlaces();
                for (var forwardInput : findForwardInputs(outputSpec)) {
                    if (!inputPlaces.contains(forwardInput.from())) {
                        throw new IllegalArgumentException(
                            "Transition '%s': ForwardInput references non-input place '%s'"
                                .formatted(name, forwardInput.from().name()));
                    }
                    // Validate type compatibility: from's tokenType must be assignable to to's tokenType
                    if (!forwardInput.to().tokenType().isAssignableFrom(forwardInput.from().tokenType())) {
                        throw new IllegalArgumentException(
                            "Transition '%s': ForwardInput type mismatch - cannot forward %s tokens from '%s' to '%s' which expects %s"
                                .formatted(name,
                                    forwardInput.from().tokenType().getSimpleName(),
                                    forwardInput.from().name(),
                                    forwardInput.to().name(),
                                    forwardInput.to().tokenType().getSimpleName()));
                    }
                }
            }

            return transition;
        }

        /**
         * Recursively finds all ForwardInput nodes in the output spec.
         */
        private static List<Out.ForwardInput> findForwardInputs(Out out) {
            return switch (out) {
                case null -> List.of();
                case Out.ForwardInput f -> List.of(f);
                case Out.And a -> a.children().stream()
                    .flatMap(c -> findForwardInputs(c).stream())
                    .toList();
                case Out.Xor x -> x.children().stream()
                    .flatMap(c -> findForwardInputs(c).stream())
                    .toList();
                case Out.Timeout t -> findForwardInputs(t.child());
                case Out.Place _ -> List.of();
            };
        }
    }
}
