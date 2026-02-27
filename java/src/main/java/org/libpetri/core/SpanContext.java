package org.libpetri.core;

/**
 * Decoupled abstraction for tracing span context.
 *
 * <p>This interface provides a framework-agnostic way for transition actions
 * to interact with tracing spans without coupling the CTPN module to specific
 * tracing implementations (like OpenTelemetry or Langfuse).
 *
 * <p>Implementations can wrap OpenTelemetry spans, allowing actions to:
 * <ul>
 *   <li>Make the span current for the executing thread</li>
 *   <li>Add attributes for Langfuse visibility</li>
 *   <li>Record exceptions that occur during action execution</li>
 *   <li>Add named events to mark significant points in execution</li>
 * </ul>
 *
 * <h2>Usage in Actions</h2>
 * <pre>{@code
 * public CompletionStage<Void> execute(TransitionContext ctx) {
 *     SpanContext spanContext = ctx.executionContext(SpanContext.class);
 *     if (spanContext != null) {
 *         spanContext.makeCurrent();
 *         spanContext.setAttribute("langfuse.event.id", eventId);
 *     }
 *     // ... action logic ...
 * }
 * }</pre>
 *
 * @see TransitionContext#executionContext(Class)
 */
public interface SpanContext {

    /**
     * Makes this span the current span for the executing thread.
     *
     * <p>This allows OpenTelemetry's {@code Span.current()} to return
     * the appropriate span for this transition's execution context.
     */
    void makeCurrent();

    /**
     * Sets a string attribute on the span.
     *
     * @param key the attribute key
     * @param value the attribute value
     */
    void setAttribute(String key, String value);

    /**
     * Sets a long attribute on the span.
     *
     * @param key the attribute key
     * @param value the attribute value
     */
    void setAttribute(String key, long value);

    /**
     * Records an exception on the span.
     *
     * <p>This marks the span with error information that will be
     * visible in trace visualizations.
     *
     * @param exception the exception to record
     */
    void recordException(Throwable exception);

    /**
     * Adds a named event to the span.
     *
     * <p>Events mark significant points during span execution and
     * are visible in trace timelines.
     *
     * @param name the event name
     */
    void addEvent(String name);

    /**
     * Closes the current scope if one was opened via {@link #makeCurrent()}.
     *
     * <p>Call this when the transition action completes to restore the previous
     * span context. This is essential for proper span nesting - without closing
     * the scope, child spans created in async contexts will not be properly
     * parented under the transition span.
     *
     * <p>Actions should always call this in a finally block:
     * <pre>{@code
     * SpanContext spanContext = ctx.executionContext(SpanContext.class);
     * if (spanContext != null) {
     *     spanContext.makeCurrent();
     * }
     * try {
     *     // ... action logic ...
     * } finally {
     *     if (spanContext != null) {
     *         spanContext.closeScope();
     *     }
     * }
     * }</pre>
     */
    void closeScope();
}
