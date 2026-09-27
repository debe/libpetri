package org.libpetri.core.internal;

/**
 * When one {@code SmtVerifier.verify()} call must stop ([VER-013]): its optional total wall-clock
 * budget has run out, or the caller <b>cancelled</b> it by interrupting the verifying thread.
 * One stop mechanism for both, so everything that polls the deadline sees a cancellation at the
 * same points.
 *
 * <p>The verifier binds a deadline for the duration of every call — an unlimited one when no
 * total budget is set, which still sees cancellation. Everything it runs on that thread reads it
 * from here rather than through a parameter threaded down every signature: the z3 transport
 * clamps each process to what is left ({@code Z3Solver.run}) and kills a running process when
 * the thread is interrupted ({@code Z3Process.run}), and the solver-free graph builds and long
 * pure loops call {@link #checkpoint()} as they go. Nothing is bound outside such a call, so
 * every other caller of those loops — the executors, the analysis API, open-net verification's
 * own graph — pays one {@link ScopedValue#isBound()} per checkpoint and nothing else.
 *
 * <p>Cancellation is Java's own idiom, thread interruption. A poll reads the thread's interrupt
 * status <b>without clearing it</b>, so the caller still sees the flag when {@code verify()}
 * returns.
 *
 * <p>When the call must stop, the checkpoint throws {@link Stopped} — {@link Cancelled} or
 * {@link Exhausted} — which unwinds to {@code verify()} and becomes the {@code Unknown} verdict
 * naming the reason and the phase that was running. {@code ProgrammingError} re-throws it, so the
 * catches that degrade a failure into a weaker result let it through.
 *
 * <p>Internal API: not part of the public contract.
 */
public final class VerificationDeadline {

    private static final ScopedValue<VerificationDeadline> CURRENT = ScopedValue.newInstance();

    /** {@code -1} when no total budget is set. */
    private final long budgetMs;
    private final long deadlineNanos;
    private volatile String phase = "net preparation";

    /** A deadline {@code budgetMs} from now. */
    public VerificationDeadline(long budgetMs) {
        this.budgetMs = Math.max(0, budgetMs);
        long now = System.nanoTime();
        long nanos;
        try {
            nanos = Math.multiplyExact(this.budgetMs, 1_000_000L);
        } catch (ArithmeticException _) {
            nanos = Long.MAX_VALUE / 2;
        }
        this.deadlineNanos = now + nanos;
    }

    private VerificationDeadline(String phase) {
        this.budgetMs = -1;
        this.deadlineNanos = 0;
        this.phase = phase;
    }

    /** A deadline with no total budget: it stops only on cancellation. */
    public static VerificationDeadline unlimited() {
        return new VerificationDeadline("net preparation");
    }

    /**
     * A deadline with no total budget whose running step is {@code phase} from the start: for a
     * caller whose whole work is that one step, so a cancellation before it starts names it.
     */
    public static VerificationDeadline unlimited(String phase) {
        return new VerificationDeadline(phase);
    }

    /** The carrier {@code verify()} binds for the duration of the call. */
    public static ScopedValue<VerificationDeadline> carrier() {
        return CURRENT;
    }

    /** The deadline bound on this thread, or {@code null} outside a {@code verify()} call. */
    public static VerificationDeadline current() {
        return CURRENT.isBound() ? CURRENT.get() : null;
    }

    /** Throws {@link Stopped} when a bound deadline says stop; a no-op otherwise. */
    public static void checkpoint() {
        if (CURRENT.isBound()) {
            CURRENT.get().check();
        }
    }

    /** Whether a total budget is set. */
    public boolean limited() {
        return budgetMs >= 0;
    }

    /** The budget as the caller set it, in milliseconds; {@code -1} when none is set. */
    public long budgetMs() {
        return budgetMs;
    }

    /** Milliseconds left, {@code <= 0} once the deadline has passed; {@link Long#MAX_VALUE} unlimited. */
    public long remainingMs() {
        if (!limited()) {
            return Long.MAX_VALUE;
        }
        return Math.floorDiv(deadlineNanos - System.nanoTime(), 1_000_000L);
    }

    /** Whether the total budget has run out (never, when none is set). */
    public boolean expired() {
        return limited() && System.nanoTime() - deadlineNanos >= 0;
    }

    /** Whether the verifying thread — this one — has been interrupted. Does not clear the flag. */
    public static boolean cancelled() {
        return Thread.currentThread().isInterrupted();
    }

    /**
     * Starts the step {@code phase}: throws {@link Stopped} when the call must already stop, so the
     * step never starts, and otherwise names it for the {@code Unknown} reason of a later stop.
     * The check comes first, so a stop always names the step that was running when the budget
     * ran out ([VER-013]), never the one about to start.
     */
    public void enter(String phase) {
        check();
        this.phase = phase;
    }

    /** The step last {@linkplain #enter entered}. */
    public String phase() {
        return phase;
    }

    /**
     * Throws {@link Cancelled} when the thread has been interrupted, else {@link Exhausted} when
     * the budget has run out. Cancellation wins when both hold at one poll.
     */
    public void check() {
        if (cancelled()) {
            throw new Cancelled(this);
        }
        if (expired()) {
            throw new Exhausted(this);
        }
    }

    /** The exhaustion reason: {@code total verification budget of <N> ms exhausted during <phase>}. */
    public String reason() {
        return "total verification budget of " + budgetMs + " ms exhausted during " + phase;
    }

    /** The cancellation reason: {@code verification cancelled during <phase>}. */
    public String cancelledReason() {
        return "verification cancelled during " + phase;
    }

    /**
     * The call must stop. Unwinds to {@code verify()}; never a verdict of the step it cut off,
     * and never a class-budget truncation (a {@code StateSpaceCache} build that throws leaves
     * its entry as it found it).
     */
    public abstract static sealed class Stopped extends RuntimeException permits Exhausted, Cancelled {
        private final transient VerificationDeadline deadline;

        Stopped(VerificationDeadline deadline, String message) {
            super(message, null, false, false);
            this.deadline = deadline;
        }

        /** The deadline that stopped the call. */
        public VerificationDeadline deadline() {
            return deadline;
        }

        /** The {@code Unknown} reason, naming the phase that was running. */
        public abstract String reason();
    }

    /** The total budget ran out. */
    public static final class Exhausted extends Stopped {
        public Exhausted(VerificationDeadline deadline) {
            super(deadline, deadline.reason());
        }

        @Override
        public String reason() {
            return deadline().reason();
        }
    }

    /** The verifying thread was interrupted. */
    public static final class Cancelled extends Stopped {
        public Cancelled(VerificationDeadline deadline) {
            super(deadline, deadline.cancelledReason());
        }

        @Override
        public String reason() {
            return deadline().cancelledReason();
        }
    }
}
