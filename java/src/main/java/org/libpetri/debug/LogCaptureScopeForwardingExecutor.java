package org.libpetri.debug;

import java.util.Collection;
import java.util.List;
import java.util.concurrent.*;

/**
 * Executor wrapper that propagates the {@link LogCaptureScope} across thread boundaries.
 *
 * <p>Follows the same pattern as {@code MDCForwardingExecutorServiceWrapper}: tasks submitted
 * to this executor have the current thread's {@link LogCaptureScope.LogSink} captured at
 * submission time and re-bound via {@link ScopedValue} on the executing thread.
 */
public class LogCaptureScopeForwardingExecutor implements ExecutorService {

    private final ExecutorService delegate;

    public LogCaptureScopeForwardingExecutor(ExecutorService delegate) {
        this.delegate = delegate;
    }

    public static ExecutorService wrap(ExecutorService delegate) {
        return new LogCaptureScopeForwardingExecutor(delegate);
    }

    private Runnable wrap(Runnable command) {
        return LogCaptureScope.wrapRunnable(command);
    }

    private <T> Callable<T> wrap(Callable<T> task) {
        return LogCaptureScope.wrapCallable(task);
    }

    @Override
    public <T> Future<T> submit(Callable<T> task) {
        return delegate.submit(wrap(task));
    }

    @Override
    public <T> Future<T> submit(Runnable task, T result) {
        return delegate.submit(wrap(task), result);
    }

    @Override
    public Future<?> submit(Runnable task) {
        return delegate.submit(wrap(task));
    }

    @Override
    public <T> List<Future<T>> invokeAll(Collection<? extends Callable<T>> tasks) throws InterruptedException {
        return delegate.invokeAll(tasks.stream().map(this::wrap).toList());
    }

    @Override
    public <T> List<Future<T>> invokeAll(Collection<? extends Callable<T>> tasks,
                                         long timeout,
                                         TimeUnit unit) throws InterruptedException {
        return delegate.invokeAll(tasks.stream().map(this::wrap).toList(), timeout, unit);
    }

    @Override
    public <T> T invokeAny(Collection<? extends Callable<T>> tasks) throws
                                                                    InterruptedException,
                                                                    ExecutionException {
        return delegate.invokeAny(tasks.stream().map(this::wrap).toList());
    }

    @Override
    public <T> T invokeAny(Collection<? extends Callable<T>> tasks,
                           long timeout,
                           TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
        return delegate.invokeAny(tasks.stream().map(this::wrap).toList(), timeout, unit);
    }

    @Override
    public void execute(Runnable command) {
        delegate.execute(wrap(command));
    }

    // Methods forwarded unchanged

    @Override
    public void shutdown() {
        delegate.shutdown();
    }

    @Override
    public List<Runnable> shutdownNow() {
        return delegate.shutdownNow();
    }

    @Override
    public boolean isShutdown() {
        return delegate.isShutdown();
    }

    @Override
    public boolean isTerminated() {
        return delegate.isTerminated();
    }

    @Override
    public boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException {
        return delegate.awaitTermination(timeout, unit);
    }

    @Override
    public void close() {
        delegate.close();
    }
}
