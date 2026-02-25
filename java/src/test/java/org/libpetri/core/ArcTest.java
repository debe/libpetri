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
    class InputArcTests {

        @Test
        void input_withoutGuard_matchesAnyTokenOfType() {
            var place = Place.of("Input", TestValue.class);
            var arc = new Arc.Input<>(place);

            var matching = Token.of(new TestValue("data"));
            var wrongType = Token.of(new OtherValue(42));

            assertTrue(arc.matches(matching));
            assertFalse(arc.matches(wrongType));
        }

        @Test
        void input_withGuard_onlyMatchesWhenGuardPasses() {
            var place = Place.of("Numbers", Integer.class);
            var arc = new Arc.Input<>(place, n -> n > 10);

            assertTrue(arc.matches(Token.of(15)));
            assertFalse(arc.matches(Token.of(5)));
        }

        @Test
        void hasGuard_withGuard_returnsTrue() {
            var place = Place.of("Input", String.class);
            var arc = new Arc.Input<>(place, s -> s.length() > 0);

            assertTrue(arc.hasGuard());
        }

        @Test
        void hasGuard_withoutGuard_returnsFalse() {
            var place = Place.of("Input", String.class);
            var arc = new Arc.Input<>(place);

            assertFalse(arc.hasGuard());
        }

        @Test
        void place_returnsConnectedPlace() {
            var place = Place.of("Input", String.class);
            var arc = new Arc.Input<>(place);

            assertSame(place, arc.place());
        }
    }

    @Nested
    class OutputArcTests {

        @Test
        void output_storesPlace() {
            var place = Place.of("Output", TestValue.class);
            var arc = new Arc.Output<>(place);

            assertSame(place, arc.place());
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
        void arc_isSealed_withFivePermittedTypes() {
            assertTrue(Arc.class.isSealed());

            var permitted = Arc.class.getPermittedSubclasses();
            assertEquals(5, permitted.length);
        }

        @Test
        void patternMatching_worksForAllArcTypes() {
            var place = Place.of("Test", String.class);

            Arc input = new Arc.Input<>(place);
            Arc output = new Arc.Output<>(place);
            Arc inhibitor = new Arc.Inhibitor<>(place);
            Arc read = new Arc.Read<>(place);
            Arc reset = new Arc.Reset<>(place);

            assertEquals("input", describeArc(input));
            assertEquals("output", describeArc(output));
            assertEquals("inhibitor", describeArc(inhibitor));
            assertEquals("read", describeArc(read));
            assertEquals("reset", describeArc(reset));
        }

        private String describeArc(Arc arc) {
            return switch (arc) {
                case Arc.Input<?> _ -> "input";
                case Arc.Output<?> _ -> "output";
                case Arc.Inhibitor<?> _ -> "inhibitor";
                case Arc.Read<?> _ -> "read";
                case Arc.Reset<?> _ -> "reset";
            };
        }
    }
}
