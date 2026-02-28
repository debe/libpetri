package org.libpetri.core;

import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link Arc} types.
 */
class ArcTest {

    record TestValue(String data) {}
    record OtherValue(int count) {}

    @Nested
    class InArcTests {

        @Test
        void inOne_storesPlace() {
            var place = Place.of("Input", TestValue.class);
            var spec = Arc.In.one(place);

            assertSame(place, spec.place());
            assertInstanceOf(Arc.In.One.class, spec);
        }

        @Test
        void inExactly_storesPlaceAndCount() {
            var place = Place.of("Input", TestValue.class);
            var spec = Arc.In.exactly(3, place);

            assertSame(place, spec.place());
            assertInstanceOf(Arc.In.Exactly.class, spec);
            assertEquals(3, ((Arc.In.Exactly) spec).count());
        }

        @Test
        void inAll_storesPlace() {
            var place = Place.of("Input", TestValue.class);
            var spec = Arc.In.all(place);

            assertSame(place, spec.place());
            assertInstanceOf(Arc.In.All.class, spec);
        }

        @Test
        void inAtLeast_storesPlaceAndMinimum() {
            var place = Place.of("Input", TestValue.class);
            var spec = Arc.In.atLeast(5, place);

            assertSame(place, spec.place());
            assertInstanceOf(Arc.In.AtLeast.class, spec);
            assertEquals(5, ((Arc.In.AtLeast) spec).minimum());
        }

        @Test
        void inExactly_rejectsZeroCount() {
            var place = Place.of("Input", TestValue.class);
            assertThrows(IllegalArgumentException.class, () -> Arc.In.exactly(0, place));
        }

        @Test
        void inAtLeast_rejectsZeroMinimum() {
            var place = Place.of("Input", TestValue.class);
            assertThrows(IllegalArgumentException.class, () -> Arc.In.atLeast(0, place));
        }

        @Test
        void requiredCount_returnsCorrectValues() {
            var place = Place.of("P", TestValue.class);

            assertEquals(1, Arc.In.one(place).requiredCount());
            assertEquals(3, Arc.In.exactly(3, place).requiredCount());
            assertEquals(1, Arc.In.all(place).requiredCount());
            assertEquals(5, Arc.In.atLeast(5, place).requiredCount());
        }
    }

    @Nested
    class OutArcTests {

        @Test
        void outPlace_storesPlace() {
            var place = Place.of("Output", TestValue.class);
            var spec = Arc.Out.place(place);

            assertEquals(place, spec.place());
        }

        @Test
        void outAnd_storesChildren() {
            var p1 = Place.of("P1", TestValue.class);
            var p2 = Place.of("P2", TestValue.class);
            var spec = Arc.Out.and(p1, p2);

            assertEquals(2, spec.children().size());
        }

        @Test
        void outXor_storesChildren() {
            var p1 = Place.of("P1", TestValue.class);
            var p2 = Place.of("P2", TestValue.class);
            var spec = Arc.Out.xor(p1, p2);

            assertEquals(2, spec.children().size());
        }

        @Test
        void outXor_rejectsLessThanTwoChildren() {
            var p1 = Place.of("P1", TestValue.class);
            assertThrows(IllegalArgumentException.class, () ->
                Arc.Out.xor(Arc.Out.place(p1)));
        }
    }

    @Nested
    class InhibitorArcTests {

        @Test
        void inhibitor_matchesTokenOfCorrectType() {
            var place = Place.of("Blocker", TestValue.class);
            var arc = new Arc.Inhibitor<>(place);

            var matching = Token.of(new TestValue("block"));
            var wrongType = Token.of(new OtherValue(1));

            assertTrue(arc.matches(matching));
            assertFalse(arc.matches(wrongType));
        }

        @Test
        void inhibitor_matchesNullValue() {
            var place = Place.of("Blocker", TestValue.class);
            var arc = new Arc.Inhibitor<>(place);

            Token<TestValue> nullToken = new Token<>(null, java.time.Instant.now());

            assertTrue(arc.matches(nullToken));
        }
    }

    @Nested
    class ReadArcTests {

        @Test
        void read_matchesTokenOfCorrectType() {
            var place = Place.of("Context", TestValue.class);
            var arc = new Arc.Read<>(place);

            var matching = Token.of(new TestValue("context"));
            var wrongType = Token.of(new OtherValue(1));

            assertTrue(arc.matches(matching));
            assertFalse(arc.matches(wrongType));
        }
    }

    @Nested
    class ResetArcTests {

        @Test
        void reset_storesPlace() {
            var place = Place.of("Buffer", TestValue.class);
            var arc = new Arc.Reset<>(place);

            assertSame(place, arc.place());
        }
    }

    @Nested
    class SealedHierarchyTests {

        @Test
        void arc_isSealed_withFourPermittedTypes() {
            assertTrue(Arc.class.isSealed());

            var permitted = Arc.class.getPermittedSubclasses();
            assertEquals(4, permitted.length);
        }

        @Test
        void patternMatching_worksForAllArcTypes() {
            var place = Place.of("Test", String.class);

            Arc in = Arc.In.one(place);
            Arc inhibitor = new Arc.Inhibitor<>(place);
            Arc read = new Arc.Read<>(place);
            Arc reset = new Arc.Reset<>(place);

            assertEquals("in", describeArc(in));
            assertEquals("inhibitor", describeArc(inhibitor));
            assertEquals("read", describeArc(read));
            assertEquals("reset", describeArc(reset));
        }

        private String describeArc(Arc arc) {
            return switch (arc) {
                case Arc.In _ -> "in";
                case Arc.Inhibitor<?> _ -> "inhibitor";
                case Arc.Read<?> _ -> "read";
                case Arc.Reset<?> _ -> "reset";
            };
        }
    }
}
