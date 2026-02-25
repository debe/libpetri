package org.libpetri.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link Place}.
 */
class PlaceTest {

    record TestValue(String data) {}
    record OtherValue(int count) {}

    @Test
    void of_createsPlaceWithNameAndType() {
        var place = Place.of("MyPlace", TestValue.class);

        assertEquals("MyPlace", place.name());
        assertEquals(TestValue.class, place.tokenType());
    }

    @Test
    void accepts_tokenWithMatchingType_returnsTrue() {
        var place = Place.of("Input", TestValue.class);
        var token = Token.of(new TestValue("data"));

        assertTrue(place.accepts(token));
    }

    @Test
    void accepts_tokenWithWrongType_returnsFalse() {
        var place = Place.of("Input", TestValue.class);
        var token = Token.of(new OtherValue(42));

        assertFalse(place.accepts(token));
    }

    @Test
    void accepts_tokenWithNullValue_returnsTrue() {
        var place = Place.of("Input", TestValue.class);
        Token<TestValue> token = new Token<>(null, java.time.Instant.now());

        assertTrue(place.accepts(token));
    }

    @Test
    void accepts_unitToken_returnsTrue() {
        var place = Place.of("Control", String.class);
        var token = Token.unit();

        assertTrue(place.accepts(token));
    }

    @Test
    void accepts_subtypeToken_returnsTrue() {
        var place = Place.of("Numbers", Number.class);
        var intToken = Token.of(Integer.valueOf(42));
        var doubleToken = Token.of(Double.valueOf(3.14));

        assertTrue(place.accepts(intToken));
        assertTrue(place.accepts(doubleToken));
    }

    @Test
    void equality_samePlaces_areEqual() {
        var place1 = Place.of("Input", String.class);
        var place2 = Place.of("Input", String.class);

        assertEquals(place1, place2);
        assertEquals(place1.hashCode(), place2.hashCode());
    }

    @Test
    void equality_differentNames_notEqual() {
        var place1 = Place.of("Input", String.class);
        var place2 = Place.of("Output", String.class);

        assertNotEquals(place1, place2);
    }

    @Test
    void equality_differentTypes_notEqual() {
        var place1 = Place.of("Data", String.class);
        var place2 = Place.of("Data", Integer.class);

        assertNotEquals(place1, place2);
    }
}
