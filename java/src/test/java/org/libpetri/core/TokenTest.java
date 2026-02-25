package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.time.Instant;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link Token}.
 */
class TokenTest {

    record TestValue(String data) {}
    record OtherValue(int count) {}

    @Test
    void of_createsTokenWithValueAndTimestamp() {
        var before = Instant.now();
        var token = Token.of(new TestValue("hello"));
        var after = Instant.now();

        assertNotNull(token.value());
        assertEquals("hello", token.value().data());
        assertFalse(token.createdAt().isBefore(before));
        assertFalse(token.createdAt().isAfter(after));
    }

    @Test
    void of_withNullValue_createsToken() {
        var token = Token.of((String) null);

        assertNull(token.value());
        assertNotNull(token.createdAt());
    }

    @Test
    void unit_returnsSingletonInstance() {
        Token<String> unit1 = Token.unit();
        Token<Integer> unit2 = Token.unit();

        assertSame(unit1, unit2);
        assertNull(unit1.value());
        assertTrue(unit1.isUnit());
    }

    @Test
    void unit_hasEpochTimestamp() {
        var unit = Token.unit();

        assertEquals(Instant.EPOCH, unit.createdAt());
    }

    @Test
    void isUnit_forRegularToken_returnsFalse() {
        var token = Token.of("regular");

        assertFalse(token.isUnit());
    }

    @Test
    void isUnit_forUnitToken_returnsTrue() {
        var unit = Token.unit();

        assertTrue(unit.isUnit());
    }

    @Test
    void isType_withMatchingType_returnsTrue() {
        var token = Token.of(new TestValue("data"));

        assertTrue(token.isType(TestValue.class));
    }

    @Test
    void isType_withSupertype_returnsTrue() {
        var token = Token.of(Integer.valueOf(42));

        assertTrue(token.isType(Number.class));
        assertTrue(token.isType(Object.class));
    }

    @Test
    void isType_withWrongType_returnsFalse() {
        var token = Token.of(new TestValue("data"));

        assertFalse(token.isType(OtherValue.class));
        assertFalse(token.isType(String.class));
    }

    @Test
    void isType_withNullValue_returnsFalse() {
        var token = Token.of((String) null);

        assertFalse(token.isType(String.class));
    }

    @Test
    void isType_forUnitToken_returnsFalse() {
        var unit = Token.unit();

        assertFalse(unit.isType(Object.class));
        assertFalse(unit.isType(Void.class));
    }

    @Test
    void equality_sameValueAndTimestamp_areEqual() {
        var timestamp = Instant.now();
        var token1 = new Token<>("hello", timestamp);
        var token2 = new Token<>("hello", timestamp);

        assertEquals(token1, token2);
        assertEquals(token1.hashCode(), token2.hashCode());
    }

    @Test
    void equality_differentValue_notEqual() {
        var timestamp = Instant.now();
        var token1 = new Token<>("hello", timestamp);
        var token2 = new Token<>("world", timestamp);

        assertNotEquals(token1, token2);
    }

    @Test
    void equality_differentTimestamp_notEqual() {
        var token1 = new Token<>("hello", Instant.now());
        var token2 = new Token<>("hello", Instant.now().plusSeconds(1));

        assertNotEquals(token1, token2);
    }
}
