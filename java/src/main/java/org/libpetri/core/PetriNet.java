package org.libpetri.core;

import java.util.*;
import java.util.function.Function;

/**
 * Immutable definition of a Time Petri Net structure.
 * <p>
 * A PetriNet is a reusable definition that can be executed multiple times
 * with different initial markings. It consists of:
 * <ul>
 *   <li>{@link Place Places} - typed containers for tokens</li>
 *   <li>{@link Transition Transitions} - actions that consume and produce tokens</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var net = PetriNet.builder("RequestProcessor")
 *     .transitions(
 *         receiveRequest,
 *         validateRequest,
 *         processRequest,
 *         sendResponse
 *     )
 *     .build();
 *
 * // Places are auto-collected from transition arcs
 * // Execute with NetExecutor (see runtime package)
 * }</pre>
 *
 * <h3>Thread Safety</h3>
 * PetriNet is immutable and thread-safe. Multiple executors can run the
 * same net definition concurrently with different markings.
 *
 * @see org.libpetri.runtime.NetExecutor NetExecutor for execution
 */
public final class PetriNet {
    private final String name;
    private final Set<Place<?>> places;
    private final Set<Transition> transitions;

    private PetriNet(String name, Set<Place<?>> places, Set<Transition> transitions) {
        this.name = name;
        this.places = Set.copyOf(places);
        this.transitions = Set.copyOf(transitions);
    }

    public String name() { return name; }
    public Set<Place<?>> places() { return places; }
    public Set<Transition> transitions() { return transitions; }

    /**
     * Creates a new PetriNet with actions bound to transitions.
     *
     * <p>This method is designed for separating static net structure from
     * runtime behavior. Define the net structure once (places, arcs, intervals),
     * then bind CDI-injected actions at runtime.
     *
     * <h3>Example</h3>
     * <pre>{@code
     * // Static structure defined at compile time
     * public static final PetriNet STRUCTURE = PetriNet.builder("Workflow")
     *     .transitions(
     *         Transition.builder("Validate").input(REQUEST).output(RESULT).build(),
     *         Transition.builder("Process").input(RESULT).output(RESPONSE).build()
     *     )
     *     .build();
     *
     * // Runtime binding with CDI services
     * @Produces
     * public PetriNet workflow(ValidationService vs, ProcessingService ps) {
     *     return STRUCTURE.bindActions(Map.of(
     *         "Validate", (in, out) -> vs.validate(in.value(REQUEST))
     *             .thenAccept(r -> out.add(RESULT, r)),
     *         "Process", (in, out) -> ps.process(in.value(RESULT))
     *             .thenAccept(r -> out.add(RESPONSE, r))
     *     ));
     * }
     * }</pre>
     *
     * @param actionBindings map from transition name to action
     * @return new PetriNet with bound actions
     * @throws IllegalArgumentException if a transition name is not found
     */
    public PetriNet bindActions(Map<String, TransitionAction> actionBindings) {
        return bindActions(name -> actionBindings.getOrDefault(name, TransitionAction.passthrough()));
    }

    /**
     * Creates a new PetriNet with actions bound via a resolver function.
     *
     * <p>The resolver is called for each transition with the transition name,
     * and should return the action to use. This allows for flexible binding
     * strategies (e.g., CDI lookup, method references).
     *
     * @param actionResolver function that resolves transition name to action
     * @return new PetriNet with bound actions
     */
    public PetriNet bindActions(Function<String, TransitionAction> actionResolver) {
        var boundTransitions = new LinkedHashSet<Transition>();
        for (var t : transitions) {
            var action = actionResolver.apply(t.name());
            if (action != null && action != t.action()) {
                boundTransitions.add(rebuildWithAction(t, action));
            } else {
                boundTransitions.add(t);
            }
        }
        return new PetriNet(name, places, boundTransitions);
    }

    /**
     * Creates a new transition with a different action while preserving all arc specifications.
     *
     * <p>This method handles both the new typed API ({@link In}/{@link Out} specs) and
     * the legacy arc-based API for backward compatibility. Both are copied independently.
     *
     * <p><b>New API fields copied:</b>
     * <ul>
     *   <li>{@code inputSpecs} - typed input specifications (In.one, In.exactly, etc.)</li>
     *   <li>{@code outputSpec} - composite output specification (Out.and, Out.xor, etc.)</li>
     * </ul>
     *
     * <p><b>Legacy API fields copied:</b>
     * <ul>
     *   <li>{@code inputs} - arc-based input definitions</li>
     *   <li>{@code outputs} - arc-based output definitions</li>
     *   <li>{@code inhibitors}, {@code reads}, {@code resets} - control arcs</li>
     * </ul>
     *
     * @param t the original transition
     * @param action the new action to bind
     * @return a new transition with the given action and all original specifications
     */
    private static Transition rebuildWithAction(Transition t, TransitionAction action) {
        var builder = Transition.builder(t.name())
            .timing(t.timing())
            .priority(t.priority())
            .action(action);

        // NEW API: Copy inputSpecs and outputSpec
        if (!t.inputSpecs().isEmpty()) {
            builder.inputs(t.inputSpecs().toArray(new In[0]));
        }
        if (t.outputSpec() != null) {
            builder.outputs(t.outputSpec());
        }

        // LEGACY API: Copy for backward compatibility
        t.inputs().values().forEach(builder::inputArc);
        t.outputs().forEach(builder::outputArc);

        // Other arc types
        t.inhibitors().forEach(builder::inhibitorArc);
        t.reads().forEach(builder::readArc);
        t.resets().forEach(builder::resetArc);

        return builder.build();
    }

    public static Builder builder(String name) {
        return new Builder(name);
    }

    public static class Builder {
        private final String name;
        private final HashSet<Place<?>> places = new HashSet<>();
        private final HashSet<Transition> transitions = new HashSet<>();

        private Builder(String name) {
            this.name = name;
        }

        public <T> Builder place(Place<T> place) {
            places.add(place);
            return this;
        }

        public Builder places(Place<?>... places) {
            this.places.addAll(List.of(places));
            return this;
        }

        public Builder transition(Transition transition) {
            transitions.add(transition);
            // Auto-add places from transition arcs
            places.addAll(transition.inputs().keySet());
            transition.outputs().forEach(arc -> places.add(arc.place()));
            transition.inhibitors().forEach(arc -> places.add(arc.place()));
            transition.reads().forEach(arc -> places.add(arc.place()));
            return this;
        }

        public Builder transitions(Transition... transitions) {
            for (var t : transitions) {
                transition(t);
            }
            return this;
        }

        public PetriNet build() {
            return new PetriNet(name, places, transitions);
        }
    }
}
