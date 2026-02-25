package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link FiringInterval}.
 */
class FiringIntervalTest {

    @Test
    void constructor_withValidInterval_succeeds() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertEquals(Duration.ofMillis(100), interval.earliest());
        assertEquals(Duration.ofMillis(500), interval.latest());
    }

    @Test
    void constructor_withNegativeEarliest_throwsException() {
        assertThrows(IllegalArgumentException.class, () ->
            new FiringInterval(Duration.ofMillis(-1), Duration.ofMillis(500))
        );
    }

    @Test
    void constructor_withLatestBeforeEarliest_throwsException() {
        assertThrows(IllegalArgumentException.class, () ->
            new FiringInterval(Duration.ofMillis(500), Duration.ofMillis(100))
        );
    }

    @Test
    void immediate_createsZeroToDeadlineInterval() {
        var interval = FiringInterval.immediate(Duration.ofMillis(1000));

        assertEquals(Duration.ZERO, interval.earliest());
        assertEquals(Duration.ofMillis(1000), interval.deadline());
    }

    @Test
    void exact_createsEqualEarliestAndLatest() {
        var interval = FiringInterval.exact(Duration.ofMillis(500));

        assertEquals(Duration.ofMillis(500), interval.earliest());
        assertEquals(Duration.ofMillis(500), interval.latest());
    }

    @Test
    void unconstrained_hasZeroEarliestAndHugeLatest() {
        var interval = FiringInterval.unconstrained();

        assertEquals(Duration.ZERO, interval.earliest());
        assertTrue(interval.latest().toDays() > 1000);
        assertFalse(interval.hasFiniteDeadline());
    }

    @Test
    void canFire_beforeEarliest_returnsFalse() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertFalse(interval.canFire(Duration.ofMillis(50)));
        assertFalse(interval.canFire(Duration.ofMillis(99)));
    }

    @Test
    void canFire_atEarliest_returnsTrue() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertTrue(interval.canFire(Duration.ofMillis(100)));
    }

    @Test
    void canFire_afterEarliest_returnsTrue() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertTrue(interval.canFire(Duration.ofMillis(200)));
        assertTrue(interval.canFire(Duration.ofMillis(500)));
        assertTrue(interval.canFire(Duration.ofMillis(1000)));
    }

    @Test
    void mustFire_beforeLatest_returnsFalse() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertFalse(interval.mustFire(Duration.ofMillis(200)));
        assertFalse(interval.mustFire(Duration.ofMillis(499)));
    }

    @Test
    void mustFire_atLatest_returnsTrue() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertTrue(interval.mustFire(Duration.ofMillis(500)));
    }

    @Test
    void mustFire_afterLatest_returnsTrue() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertTrue(interval.mustFire(Duration.ofMillis(600)));
        assertTrue(interval.mustFire(Duration.ofMillis(1000)));
    }

    @Test
    void deadline_returnsLatest() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertEquals(Duration.ofMillis(500), interval.deadline());
    }

    @Test
    void hasFiniteDeadline_forFiniteInterval_returnsTrue() {
        var interval = new FiringInterval(Duration.ofMillis(0), Duration.ofMillis(5000));

        assertTrue(interval.hasFiniteDeadline());
    }

    @Test
    void hasFiniteDeadline_forUnconstrainedInterval_returnsFalse() {
        var interval = FiringInterval.unconstrained();

        assertFalse(interval.hasFiniteDeadline());
    }

    @Test
    void hasFiniteDeadline_forVeryLongInterval_returnsFalse() {
        var interval = new FiringInterval(Duration.ZERO, Duration.ofDays(365 * 100));

        assertFalse(interval.hasFiniteDeadline());
    }

    @Test
    void equality_sameIntervals_areEqual() {
        var i1 = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));
        var i2 = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));

        assertEquals(i1, i2);
        assertEquals(i1.hashCode(), i2.hashCode());
    }

    @Test
    void equality_differentIntervals_notEqual() {
        var i1 = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));
        var i2 = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(600));

        assertNotEquals(i1, i2);
    }
}
