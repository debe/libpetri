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
    }

    @Test
    void theOpenEndItselfIsAccepted() {
        assertEquals(Timing.MAX_DURATION, Timing.delayed(Timing.MAX_DURATION).earliest());
        assertEquals(Timing.MAX_DURATION, Timing.window(Timing.MAX_DURATION, PAST).earliest());
        assertEquals(Timing.MAX_DURATION, Timing.exact(Timing.MAX_DURATION).earliest());
    }
}
