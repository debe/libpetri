package org.libpetri.runtime;

import java.time.Instant;
import java.util.function.BooleanSupplier;

/**
 * Host-supplied time source and cooperative wait for an executor, per <b>TIME-015</b>.
 *
 * <p>The seam is <b>per executor</b>, never per net: a {@link org.libpetri.core.PetriNet} is
 * immutable and shared across composition ([MOD-010]), so a clock attached to one would have
 * to be merged at every {@code compose}, and a host running two executors in one process —
 * comparing an engine against a reference, or testing one net under virtual time while
 * another runs live — needs them on independent clocks.
 *
 * <h2>Two time bases, not one</h2>
 * <p>An executor reads time from two unrelated sources and a single injected {@code now}
 * cannot serve both:
 * <ul>
 *   <li>{@link #nanoTime()} — the <b>firing clock</b>. Enablement stamps ([TIME-010]),
 *       elapsed-time decisions ([TIME-004], [TIME-005], [TIME-006]), deadline enforcement
 *       ([TIME-013]) and the wake-up interval are computed from it.</li>
 *   <li>{@link #now()} — the <b>epoch clock</b>. Stamps token creation ([CORE-011]) and the
 *       timestamps events carry.</li>
 * </ul>
 * <p>Their origins are unrelated and must not be conflated. A host may derive both from one
 * logical source, and should when it needs the two to agree across a replay.
 *
 * <h2>Contract</h2>
 * <p>All of these hold, none is an error condition today, and <b>each is silent when
 * violated</b> — which is why they are stated rather than checked:
 * <ol>
 *   <li><b>Non-decreasing.</b> {@link #nanoTime()} must not go backwards. Elapsed time is a
 *       difference from an enablement stamp, so a backwards step yields a negative elapsed
 *       value, which re-opens the earliest bound of an already-due transition and can stall
 *       the net indefinitely with no error surfaced. Note <i>non-decreasing</i>, not strictly
 *       increasing: a host clock derived from a coarse source (milliseconds, say) returns the
 *       <b>same value</b> across many cycles, and that is normal rather than a fault. libpetri
 *       does not assume a tick between two reads.</li>
 *   <li><b>Suspend or advance — and where there is no boundary, suspend.</b> Given a
 *       <i>finite</i> {@code delayNanos}, {@link #awaitWork} must either suspend until that
 *       boundary or advance the clock to it; a host clock that advances only on demand, paired
 *       with a wait that does neither, spins forever with elapsed time never reaching the bound.
 *
 *       <p>{@link Long#MAX_VALUE} is <b>not</b> a boundary and neither disjunct applies to it.
 *       The executor passes it whenever nothing timed is pending — which is most of the time:
 *       parked on an in-flight action, or waiting for an external event. There is no instant to
 *       advance to, so the wait MUST <b>suspend until woken</b>. Returning immediately is
 *       non-conforming: the executor re-enters the wait at once and the loop becomes a spin.
 *       This is the case a first reading misses; test your implementation against
 *       {@code Long.MAX_VALUE} explicitly.</li>
 *   <li><b>Spurious completion permitted.</b> {@link #awaitWork} may return early and for no
 *       reason. The executor re-checks its boundary conditions and never treats "the wait
 *       returned" as "the boundary is reached".</li>
 *   <li><b>Abort completes, not fails.</b> When the executor is shutting down ([ENV-013])
 *       {@link #awaitWork} must return normally rather than throwing. Shutdown is precisely
 *       the path on which a failing wait is most likely to escape unobserved.</li>
 *   <li><b>The readiness predicate is time-free.</b> The {@code ready} supplier passed to
 *       {@link #awaitWork} may be called repeatedly; it must be cheap, repeatable and
 *       side-effect free, and must never itself consult a clock — a time-based predicate
 *       reintroduces the real clock behind the seam.</li>
 * </ol>
 *
 * <h2>Admission from inside the wait</h2>
 * <p>A cooperative host has no foreign thread: it is <i>inside</i> {@link #awaitWork} when an
 * external result arrives. Calling {@link PetriNetExecutor#inject} from there is <b>legal</b>.
 * Injection is queue-only — it does not mutate the marking at the point of call — so the
 * event is admitted in the executor's own external-events phase on the next cycle, in the
 * executor's own order. A host must not otherwise re-enter the executor from the wait.
 *
 * <p><b>Inject and return — never await admission.</b> The
 * {@link java.util.concurrent.CompletableFuture} that {@code inject} returns is completed by
 * the <i>orchestrator</i> when the event reaches its phase, and inside this call the
 * orchestrator is the caller. Awaiting it therefore blocks the only thing that could complete
 * it: the executor deadlocks against itself, with no error, no timeout from the executor's own
 * machinery, and nothing to indicate what happened. Use
 * {@link PetriNetExecutor#injectAsync}, which returns {@code void} and so cannot be awaited;
 * the tokens arrive on a following cycle either way.
 *
 * <h2>Scope limit: action timeouts are not virtualized</h2>
 *
 * <p>One kind of net-declared timing stays on real time. The {@code timeout(after, recovery)}
 * branch of an output spec ([IO-013]) is enforced by a <b>per-action</b> wait, while this seam
 * owns the executor's single orchestrator wait — so under an injected clock the recovery
 * tokens are stamped from {@link #now()} ([TIME-015] AC#13), but the {@code after} interval
 * itself still elapses in real time. A net declaring {@code timeout(…)} is therefore
 * <b>not fully virtualizable</b>: a host replaying one waits the real interval, even though its
 * {@code delayed}, {@code window}, {@code deadline} and {@code exact} timings do not.
 *
 * <p>Stated explicitly because the rest of this seam would otherwise imply the opposite, and
 * the mix is easy to hit — a host that compiles its own sleeps to {@code delayed(…)} and its
 * step timeouts to {@code Out.Timeout} gets one virtualized and one not. It is a boundary, not
 * an oversight: bringing action timeouts under the seam would mean the clock mediating every
 * in-flight action's wait rather than one orchestrator wait. And the tempting half-fix is
 * <b>forbidden</b> — routing the timeout interval through the clock while the action's own
 * wait stays on real time would fire the recovery branch at a virtual instant the action never
 * reached, producing a recovery for work that is still running.
 *
 * <h2>Host-minted tokens</h2>
 * <p>This seam stamps tokens the <b>executor</b> produces. Tokens a host mints in its own
 * code — notably an executor's <b>initial marking</b>, which is built before any executor or
 * environment exists — are outside it and no seam can reach them. Use
 * {@link org.libpetri.core.Token#Token(Object, Instant)} for those;
 * {@link org.libpetri.core.Token#of(Object)} stamps wall-clock and is therefore
 * non-deterministic under a host clock.
 *
 * <h2>Default cost</h2>
 * <p>Absent an environment the executor calls {@link System#nanoTime()} and
 * {@link Instant#now()} directly, behind a null check on a {@code final} field. No executor
 * allocates a default implementation of this interface, so the unused path pays a predictable
 * branch rather than an interface dispatch.
 *
 * @see PetriNetExecutor
 */
public interface ExecutionEnvironment {

    /**
     * The firing clock: monotonic logical elapsed time in <b>nanoseconds</b>.
     *
     * <p>Only differences between two readings are meaningful — the origin is arbitrary, as
     * with {@link System#nanoTime()}. Must be non-decreasing; equal successive readings are
     * permitted.
     *
     * @return logical nanoseconds, non-decreasing across calls
     */
    long nanoTime();

    /**
     * The epoch clock: the logical timestamp stamped onto executor-produced tokens and the
     * events the executor emits.
     *
     * @return the logical wall-clock instant
     */
    Instant now();

    /**
     * Suspends cooperatively until {@code ready} reports work, or until {@code delayNanos}
     * of logical time has passed — <b>whichever comes first</b>.
     *
     * <p>The wait is "signal or timeout", never a bare sleep. {@code ready} is the signal
     * half: it reports a completing action, an injected external event, or a close, any of
     * which must wake the wait without the interval being waited out. {@code delayNanos} is
     * the timeout half. A host that honours only the interval stalls the net on the first
     * completion that arrives early; one that honours only {@code ready} never reaches a
     * timing boundary.
     *
     * <p>A host may OR its own conditions into the wait alongside {@code ready}.
     *
     * <p>Returning immediately is always permitted (contract point 3), and is <b>required</b>
     * when {@code ready} already reports true or {@code delayNanos} is non-positive — a
     * boundary already due must let the next cycle act on it rather than being waited out
     * ([EXEC-001], [CONC-010]).
     *
     * <p><b>Interrupts.</b> This method cannot throw {@link InterruptedException}. The
     * executor always calls it with the thread's interrupt flag <b>clear</b>, and reads the
     * flag when it returns: set on return means an interrupt arrived during the wait, which
     * ends the run {@link TerminationReason#INTERRUPTED} ([EXEC-041]). A host that blocks
     * interruptibly should therefore catch the exception, restore the flag
     * ({@code Thread.currentThread().interrupt()}) and return; one that swallows it makes the
     * run uninterruptible while it waits, and one that sets the flag for reasons of its own
     * ends the run.
     *
     * @param ready      readiness predicate; cheap, repeatable, side-effect free and never
     *                   time-based. May be called any number of times, including zero.
     * @param delayNanos logical nanoseconds until the next timing boundary, or
     *                   {@link Long#MAX_VALUE} when there is no timer to wait for. Never
     *                   negative.
     */
    void awaitWork(BooleanSupplier ready, long delayNanos);
}
