package org.libpetri.runtime;

import java.util.*;

import org.libpetri.core.*;

/**
 * Shared static helpers used by both {@link NetExecutor} and {@link BitmapNetExecutor}.
 */
final class ExecutorSupport {

    private ExecutorSupport() {}

    /**
     * Recursively validates that a transition's output satisfies its declared {@link Arc.Out} spec.
     *
     * @param tName transition name for error messages
     * @param spec the output specification to validate
     * @param produced set of places that received tokens
     * @return the set of claimed places, or empty if not satisfied
     * @throws OutViolationException if a structural violation is detected
     */
    static Optional<Set<Place<?>>> validateOutSpec(String tName, Arc.Out spec, Set<Place<?>> produced) {
        return switch (spec) {
            case Arc.Out.Place p -> produced.contains(p.place())
                ? Optional.of(Set.of(p.place()))
                : Optional.empty();

            case Arc.Out.And and -> {
                var claimed = new HashSet<Place<?>>();
                for (Arc.Out child : and.children()) {
                    var result = validateOutSpec(tName, child, produced);
                    if (result.isEmpty()) yield Optional.<Set<Place<?>>>empty();
                    claimed.addAll(result.get());
                }
                yield Optional.of(claimed);
            }

            case Arc.Out.Xor xor -> {
                var satisfied = xor.children().stream()
                    .flatMap(child -> validateOutSpec(tName, child, produced).stream())
                    .toList();

                yield switch (satisfied.size()) {
                    case 0 -> throw new OutViolationException(
                        "'%s': XOR violation - no branch produced (exactly 1 required)".formatted(tName));
                    case 1 -> Optional.of(satisfied.getFirst());
                    default -> {
                        // When one branch subsumes all others (e.g., AND(A,B,C) vs AND(A,B)),
                        // select the most specific match.
                        var subsuming = satisfied.stream()
                            .filter(candidate -> satisfied.stream()
                                .allMatch(other -> other == candidate || candidate.containsAll(other)))
                            .toList();
                        if (subsuming.size() == 1) {
                            yield Optional.of(subsuming.getFirst());
                        }
                        throw new OutViolationException(
                            "'%s': XOR violation - multiple branches produced".formatted(tName));
                    }
                };
            }

            case Arc.Out.Timeout timeout -> validateOutSpec(tName, timeout.child(), produced);

            case Arc.Out.ForwardInput f -> produced.contains(f.to())
                ? Optional.of(Set.of(f.to()))
                : Optional.empty();
        };
    }

    /**
     * Produces tokens to the timeout branch output places.
     */
    @SuppressWarnings("unchecked")
    static void produceTimeoutOutput(TransitionContext context, Arc.Out timeoutChild) {
        produceTimeoutOutputRecursive(context, timeoutChild);
    }

    @SuppressWarnings("unchecked")
    private static void produceTimeoutOutputRecursive(TransitionContext context, Arc.Out out) {
        switch (out) {
            case Arc.Out.Place p ->
                context.output((Place<Object>) p.place(), Token.unit().value());
            case Arc.Out.ForwardInput f -> {
                Object value = context.input(f.from());
                context.output((Place<Object>) f.to(), value);
            }
            case Arc.Out.And a ->
                a.children().forEach(c -> produceTimeoutOutputRecursive(context, c));
            case Arc.Out.Xor _ ->
                throw new IllegalStateException("XOR not allowed in timeout child");
            case Arc.Out.Timeout _ ->
                throw new IllegalStateException("Nested Timeout not allowed");
        }
    }

    /**
     * Drains pending external events, completing each with {@code false}.
     */
    static void drainPendingExternalEvents(Queue<ExternalEvent<?>> queue) {
        ExternalEvent<?> event;
        while ((event = queue.poll()) != null) {
            event.resultFuture().complete(false);
        }
    }
}
