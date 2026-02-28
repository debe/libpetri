package org.libpetri.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

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
 *   <li>All input places have required tokens (per cardinality specs)</li>
 *   <li>All read places have required tokens</li>
 *   <li>No inhibitor places have tokens</li>
 * </ul>
 *
 * <h3>Time Semantics</h3>
 * Each transition has a {@link Timing} specification:
 * <ul>
 *   <li>Cannot fire before earliest time after becoming enabled</li>
 *   <li>Must fire (or be disabled) before deadline</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var process = Transition.builder("ProcessRequest")
 *     .inputs(Arc.In.one(requestPlace))
 *     .read(configPlace)              // read config without consuming
 *     .inhibitor(pausedPlace)         // don't process if paused
 *     .outputs(Arc.Out.and(responsePlace))
 *     .timing(Timing.deadline(Duration.ofSeconds(30)))
 *     .priority(10)                   // higher priority fires first
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

    private final String name;
    private final List<Arc.In> inputSpecs;
    private final Arc.Out outputSpec;
    private final List<Arc.Inhibitor<?>> inhibitors;
    private final List<Arc.Read<?>> reads;
    private final List<Arc.Reset<?>> resets;
    private final Timing timing;
    private final Arc.Out.Timeout actionTimeout;
    private final TransitionAction action;
    private final int priority;

    private Transition(
        String name,
        List<Arc.In> inputSpecs,
        Arc.Out outputSpec,
        List<Arc.Inhibitor<?>> inhibitors,
        List<Arc.Read<?>> reads,
        List<Arc.Reset<?>> resets,
        Timing timing,
        TransitionAction action,
        int priority
    ) {
        this.name = name;
        this.inputSpecs = List.copyOf(inputSpecs);
        this.outputSpec = outputSpec;
        this.inhibitors = List.copyOf(inhibitors);
        this.reads = List.copyOf(reads);
        this.resets = List.copyOf(resets);
        this.timing = timing;
        this.actionTimeout = findTimeout(outputSpec);
        this.action = action;
        this.priority = priority;
    }

    /**
     * Recursively searches the output spec for a Timeout node.
     * Used at build time to cache timeout for O(1) runtime lookup.
     *
     * @param out the output specification to search
     * @return the first Timeout found, or null if none exists
     */
    private static Arc.Out.Timeout findTimeout(Arc.Out out) {
        return switch (out) {
            case null -> null;
            case Arc.Out.Timeout t -> t;
            case Arc.Out.And a -> a.children().stream()
                .map(Transition::findTimeout)
                .filter(Objects::nonNull)
                .findFirst().orElse(null);
            case Arc.Out.Xor x -> x.children().stream()
                .map(Transition::findTimeout)
                .filter(Objects::nonNull)
                .findFirst().orElse(null);
            case Arc.Out.Place _ -> null;
            case Arc.Out.ForwardInput _ -> null;
        };
    }

    /** Label for display/debugging/export. Not used for identity. */
    public String name() { return name; }

    /**
     * Returns the input specifications with cardinality.
     * Use this for enablement checks and token consumption.
     */
    public List<Arc.In> inputSpecs() { return inputSpecs; }

    /**
     * Returns the output specification (composite AND/XOR structure).
     * Use this for output validation.
     */
    public Arc.Out outputSpec() { return outputSpec; }

    public List<Arc.Inhibitor<?>> inhibitors() { return inhibitors; }
    public List<Arc.Read<?>> reads() { return reads; }
    public List<Arc.Reset<?>> resets() { return resets; }

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
    public Arc.Out.Timeout actionTimeout() { return actionTimeout; }

    public TransitionAction action() { return action; }
    public int priority() { return priority; }

    // ==================== Place Sets for TransitionContext ====================

    /**
     * Returns set of input places - consumed tokens.
     * Used by TransitionContext to enforce structure constraints.
     */
    public Set<Place<?>> inputPlaces() {
        return inputSpecs.stream()
            .map(Arc.In::place)
            .collect(Collectors.toUnmodifiableSet());
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
     */
    public Set<Place<?>> outputPlaces() {
        if (outputSpec == null) return Set.of();
        return outputSpec.allPlaces();
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
        private final ArrayList<Arc.In> inputSpecs = new ArrayList<>();
        private Arc.Out outputSpec = null;
        private final ArrayList<Arc.Inhibitor<?>> inhibitors = new ArrayList<>();
        private final ArrayList<Arc.Read<?>> reads = new ArrayList<>();
        private final ArrayList<Arc.Reset<?>> resets = new ArrayList<>();
        private Timing timing = Timing.immediate();
        private TransitionAction action = TransitionAction.passthrough();
        private int priority = 0;

        private Builder(String name) {
            this.name = name;
        }

        /**
         * Add input specifications with cardinality.
         *
         * <p>Example:
         * <pre>{@code
         * .inputs(Arc.In.one(headerPlace), Arc.In.atLeast(1, lineItemPlace))
         * }</pre>
         *
         * @param specs input specifications
         * @return this builder
         */
        public Builder inputs(Arc.In... specs) {
            inputSpecs.addAll(List.of(specs));
            return this;
        }

        /**
         * Set the output specification (composite AND/XOR structure).
         *
         * <p>Example:
         * <pre>{@code
         * .outputs(Arc.Out.xor(successPlace, errorPlace))
         * .outputs(Arc.Out.and(p1, p2, p3))
         * .outputs(Arc.Out.xor(Arc.Out.and(a, b), Arc.Out.and(c, d)))
         * }</pre>
         *
         * @param spec output specification
         * @return this builder
         */
        public Builder outputs(Arc.Out spec) {
            this.outputSpec = spec;
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
            var transition = new Transition(name, inputSpecs, outputSpec, inhibitors, reads, resets, timing, action, priority);

            // Validate ForwardInput references valid input places and type compatibility
            if (outputSpec != null) {
                var inputPlaces = transition.inputPlaces();
                for (var forwardInput : findForwardInputs(outputSpec)) {
                    if (!inputPlaces.contains(forwardInput.from())) {
                        throw new IllegalArgumentException(
                            "Transition '%s': ForwardInput references non-input place '%s'"
                                .formatted(name, forwardInput.from().name()));
                    }
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
        private static List<Arc.Out.ForwardInput> findForwardInputs(Arc.Out out) {
            return switch (out) {
                case null -> List.of();
                case Arc.Out.ForwardInput f -> List.of(f);
                case Arc.Out.And a -> a.children().stream()
                    .flatMap(c -> findForwardInputs(c).stream())
                    .toList();
                case Arc.Out.Xor x -> x.children().stream()
                    .flatMap(c -> findForwardInputs(c).stream())
                    .toList();
                case Arc.Out.Timeout t -> findForwardInputs(t.child());
                case Arc.Out.Place _ -> List.of();
            };
        }
    }
}
