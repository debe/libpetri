package org.libpetri.debug;

import java.util.concurrent.Callable;
import java.util.function.Consumer;

import org.libpetri.event.NetEvent;

/**
 * Scope manager for log capture using {@link ScopedValue}.
 *
 * <p>Any logging framework adapter (e.g., Logback Appender) reads the current sink
 * from {@link #current()} to determine whether log messages should be captured.
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * LogCaptureScope.run("myTransition", eventStore::append, () -> {
 *     // log.info() calls within this block will be captured
 * });
 * }</pre>
 *
 * @see LogSink
 */
public final class LogCaptureScope {

    /**
     * Mutable carrier for the log sink.
     *
     * <p>The reentry flag is single-thread-safe because {@link ScopedValue} is
     * bound per-thread — no {@link ThreadLocal} needed.
     */
    public static final class LogSink {
        private final String transitionName;
        private final Consumer<NetEvent.LogMessage> sink;
        private boolean capturing;

        public LogSink(String transitionName, Consumer<NetEvent.LogMessage> sink) {
            this.transitionName = transitionName;
            this.sink = sink;
        }

        public String transitionName() { return transitionName; }

        /**
         * Attempts to enter capture mode. Returns false if already capturing (reentry).
         */
        public boolean tryEnter() {
            if (capturing) return false;
            capturing = true;
            return true;
        }

        public void exit() { capturing = false; }

        public void accept(NetEvent.LogMessage msg) { sink.accept(msg); }

        /**
         * Creates a copy with the same transition name and sink callback but an
         * independent reentry guard — safe to use on a different thread.
         */
        public LogSink copy() {
            return new LogSink(transitionName, sink);
        }
    }

    private static final ScopedValue<LogSink> CURRENT = ScopedValue.newInstance();

    private LogCaptureScope() {}

    /**
     * Returns the currently active log sink for this thread, or null if none.
     *
     * @return the active sink, or null
     */
    public static LogSink current() {
        return CURRENT.isBound() ? CURRENT.get() : null;
    }

    /**
     * Wraps a {@link Runnable} so that the current thread's {@link LogSink} is
     * re-bound via {@link ScopedValue} when the runnable executes on another thread.
     *
     * <p>If no sink is currently bound, the runnable is returned as-is.
     *
     * @param op the operation to wrap
     * @return wrapped runnable that propagates the log capture scope
     */
    public static Runnable wrapRunnable(Runnable op) {
        LogSink sink = current();
        if (sink == null) return op;
        LogSink copy = sink.copy();
        return () -> ScopedValue.where(CURRENT, copy).run(op);
    }

    /**
     * Wraps a {@link Callable} so that the current thread's {@link LogSink} is
     * re-bound via {@link ScopedValue} when the callable executes on another thread.
     *
     * <p>If no sink is currently bound, the callable is returned as-is.
     *
     * @param <T> the return type
     * @param op the operation to wrap
     * @return wrapped callable that propagates the log capture scope
     */
    public static <T> Callable<T> wrapCallable(Callable<T> op) {
        LogSink sink = current();
        if (sink == null) return op;
        LogSink copy = sink.copy();
        return () -> ScopedValue.where(CURRENT, copy).call(op::call);
    }

    /**
     * Runs the given operation with a log capture sink bound via {@link ScopedValue}.
     *
     * @param transitionName the transition whose action is being executed
     * @param sink callback to receive captured log messages (e.g., {@code eventStore::append})
     * @param op the operation to run within the scope
     */
    public static void run(String transitionName, Consumer<NetEvent.LogMessage> sink, Runnable op) {
        ScopedValue.where(CURRENT, new LogSink(transitionName, sink)).run(op);
    }

    /**
     * Calls the given operation with a log capture sink bound via {@link ScopedValue}.
     *
     * <p>Value-returning variant of {@link #run(String, Consumer, Runnable)}.
     *
     * @param <T> the return type
     * @param <X> the exception type
     * @param transitionName the transition whose action is being executed
     * @param sink callback to receive captured log messages
     * @param op the operation to call within the scope
     * @return the result of the operation
     * @throws X if the operation throws
     */
    public static <T, X extends Throwable> T call(
            String transitionName,
            Consumer<NetEvent.LogMessage> sink,
            ScopedValue.CallableOp<T, X> op) throws X {
        return ScopedValue.where(CURRENT, new LogSink(transitionName, sink)).call(op);
    }
}
