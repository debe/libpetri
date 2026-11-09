package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An earliest bound past {@link Timing#MAX_DURATION}, the finite stand-in for "no latest bound",
 * would make {@code [earliest, MAX_DURATION]} empty, and a state-class graph would read a
 * transition that can fire as one that never can. Construction rejects it, as it rejects the
 * other invalid bounds.
 */
class TimingBoundsTest {

    private static final Duration PAST = Timing.MAX_DURATION.plusMillis(1);

    @Test
    void delayedRejectsAnEarliestBoundPastTheOpenEnd() {
        assertThrows(IllegalArgumentException.class, () -> Timing.delayed(PAST));
    }

    @Test
    void windowRejectsAnEarliestBoundPastTheOpenEnd() {
        assertThrows(IllegalArgumentException.class, () -> Timing.window(PAST, PAST.plusMillis(1)));
    }

    /** [TIME-001] AC4, [TIME-003]: a deadline past the open end is one no run reaches. */
    @Test
    void deadlineRejectsABoundPastTheOpenEnd() {
        var e = assertThrows(IllegalArgumentException.class, () -> Timing.deadline(PAST));
        assertEquals("Deadline must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
    }

    /** [TIME-001] AC4: the positivity rule comes first, so a zero deadline keeps its message. */
    @Test
    void deadlinePositivityIsCheckedFirst() {
        var e = assertThrows(IllegalArgumentException.class, () -> Timing.deadline(Duration.ZERO));
        assertEquals("Deadline must be positive: PT0S", e.getMessage());
    }

    /** [TIME-001] AC4, [TIME-005]: a window whose latest bound is past the open end is one no run reaches. */
    @Test
    void windowRejectsALatestBoundPastTheOpenEnd() {
        var e = assertThrows(IllegalArgumentException.class, () -> Timing.window(Timing.MAX_DURATION, PAST));
        assertEquals("Latest must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
        e = assertThrows(IllegalArgumentException.class, () -> Timing.window(Duration.ZERO, PAST));
        assertEquals("Latest must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
    }

    /** [TIME-001] AC4, [TIME-005]: the earliest bound is checked first, then the ordering, then latest. */
    @Test
    void windowEarliestBoundIsCheckedFirst() {
        var e = assertThrows(IllegalArgumentException.class, () -> Timing.window(PAST, PAST.plusMillis(1)));
        assertEquals("Earliest must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
    }

    @Test
    void exactRejectsATimePastTheOpenEnd() {
        assertThrows(IllegalArgumentException.class, () -> Timing.exact(PAST));
    }

    /**
     * TIME-001 AC5: the checks live in the records' compact constructors, so a timing written
     * out directly, without a factory, is checked too. Rust and TypeScript, whose variants
     * bypass the factories, re-run them in the transition builder instead.
     */
    @Test
    void aRecordWrittenOutDirectlyIsCheckedToo() {
        assertThrows(IllegalArgumentException.class, () -> new Timing.Delayed(PAST));
        assertThrows(IllegalArgumentException.class, () -> new Timing.Window(PAST, PAST.plusMillis(1)));
        assertThrows(IllegalArgumentException.class,
                () -> new Timing.Window(Duration.ofMillis(5), Duration.ofMillis(3)));
        assertThrows(IllegalArgumentException.class, () -> new Timing.Exact(PAST));
        assertThrows(IllegalArgumentException.class, () -> new Timing.Deadline(Duration.ZERO));
        var e = assertThrows(IllegalArgumentException.class, () -> new Timing.Deadline(PAST));
        assertEquals("Deadline must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
        // The transition builder takes the record as built, so it cannot hold an invalid deadline.
        assertThrows(IllegalArgumentException.class,
                () -> Transition.builder("t").timing(new Timing.Deadline(PAST)).build());
        e = assertThrows(IllegalArgumentException.class, () -> new Timing.Window(Timing.MAX_DURATION, PAST));
        assertEquals("Latest must be at most MAX_DURATION (PT876000H): " + PAST, e.getMessage());
        // Likewise for a window: the builder cannot hold one whose latest bound is past the open end.
        assertThrows(IllegalArgumentException.class,
                () -> Transition.builder("t").timing(new Timing.Window(Duration.ZERO, PAST)).build());
    }

    @Test
    void theOpenEndItselfIsAccepted() {
        assertEquals(Timing.MAX_DURATION, Timing.delayed(Timing.MAX_DURATION).earliest());
        // [TIME-001] AC4, [TIME-005]: window(MAX_DURATION, MAX_DURATION) and window(0, MAX_DURATION) are accepted.
        var window = Timing.window(Timing.MAX_DURATION, Timing.MAX_DURATION);
        assertEquals(Timing.MAX_DURATION, window.earliest());
        assertEquals(Timing.MAX_DURATION, window.latest());
        assertEquals(Timing.MAX_DURATION, Timing.window(Duration.ZERO, Timing.MAX_DURATION).latest());
        assertEquals(Timing.MAX_DURATION, Timing.exact(Timing.MAX_DURATION).earliest());
        // [TIME-001] AC4, [TIME-003]: deadline(MAX_DURATION) is accepted and stays reapable.
        var deadline = Timing.deadline(Timing.MAX_DURATION);
        assertEquals(Timing.MAX_DURATION, deadline.latest());
        assertEquals(true, deadline.hasDeadline());
    }
}
