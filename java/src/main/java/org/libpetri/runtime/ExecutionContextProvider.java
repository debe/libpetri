package org.libpetri.runtime;

import java.util.List;
import java.util.Map;

import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionContext;

/**
 * Provider for creating execution context objects passed to transition actions.
 *
 * <p>Execution context allows external systems (like tracing) to inject data
 * into the {@link TransitionContext} without coupling the TCPN module to those systems.
 *
 * <p>The provider is called once per transition firing, receiving the transition
 * and consumed tokens. It returns a map of context objects keyed by their class.
 *
 * <h2>Example: Tracing Integration</h2>
 * <pre>{@code
 * ExecutionContextProvider provider = (transition, consumed) -> {
 *     Span span = tracer.spanBuilder(transition.name()).startSpan();
 *     return Map.of(SpanContext.class, new OpenTelemetrySpanContext(span));
 * };
 * }</pre>
 *
 * @see TransitionContext#executionContext(Class)
 * @see NetExecutor.Builder#executionContextProvider(ExecutionContextProvider)
 */
@FunctionalInterface
public interface ExecutionContextProvider {
    /**
     * A no-op provider that returns an empty context map.
     */
    ExecutionContextProvider NOOP = (transition, consumed) -> Map.of();

    /**
     * Creates execution context for a transition firing.
     *
     * @param transition the transition about to fire
     * @param consumedTokens tokens consumed from input places
     * @return map of context objects keyed by their class
     */
    Map<Class<?>, Object> createContext(Transition transition, List<Token<?>> consumedTokens);
}
