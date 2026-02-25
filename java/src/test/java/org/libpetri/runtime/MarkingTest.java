package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.*;

import org.libpetri.core.Arc;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.Test;

class MarkingTest {

    record Value(String data) {}

    @Test
    void removeFirst_fromEmptyPlace_returnsNull() {
        var place = Place.of("empty", Value.class);
        var marking = Marking.empty();

        assertNull(marking.removeFirst(place), "removeFirst on empty place should return null");
    }

    @Test
    void peekTokens_fromEmptyPlace_returnsEmpty() {
        var place = Place.of("empty", Value.class);
        var marking = Marking.empty();

        var tokens = marking.peekTokens(place);
        assertTrue(tokens.isEmpty(), "peekTokens on empty place should return empty collection");
    }

    @Test
    void removeFirstMatching_noGuard_emptyQueue_returnsNull() {
        var place = Place.of("p", Value.class);
        var arc = new Arc.Input<>(place); // no guard
        var marking = Marking.empty();

        assertNull(marking.removeFirstMatching(arc));
    }

    @Test
    void removeFirstMatching_withGuard_noMatch_returnsNull() {
        var place = Place.of("p", Value.class);
        var arc = new Arc.Input<>(place, v -> v.data().equals("target"));
        var marking = Marking.from(Map.of(
            place, List.of(
                Token.of(new Value("no")),
                Token.of(new Value("miss"))
            )
        ));

        // Guard matches neither token - iterator exhausts, returns null
        assertNull(marking.removeFirstMatching(arc));
        // Both tokens should still be there
        assertEquals(2, marking.tokenCount(place));
    }

    @Test
    void hasMatchingToken_noGuard_withTokens_returnsTrue() {
        var place = Place.of("p", Value.class);
        var arc = new Arc.Input<>(place); // no guard
        var marking = Marking.from(Map.of(
            place, List.of(Token.of(new Value("any")))
        ));

        assertTrue(marking.hasMatchingToken(arc));
    }

    @Test
    void hasMatchingToken_emptyPlace_returnsFalse() {
        var place = Place.of("p", Value.class);
        var arc = new Arc.Input<>(place);
        var marking = Marking.empty();

        assertFalse(marking.hasMatchingToken(arc));
    }

    @Test
    void removeAll_fromEmptyPlace_returnsEmptyList() {
        var place = Place.of("p", Value.class);
        var marking = Marking.empty();

        var result = marking.removeAll(place);
        assertTrue(result.isEmpty());
    }

    @Test
    void removeFirst_existingQueueButEmpty_returnsNull() {
        // Create a marking with a place, add and then remove the token
        // so the queue exists but is empty
        var place = Place.of("p", Value.class);
        var marking = Marking.from(Map.of(
            place, List.of(Token.of(new Value("only")))
        ));
        // Remove the only token
        marking.removeFirst(place);
        // Now queue exists but is empty
        assertNull(marking.removeFirst(place));
    }

    @Test
    void inspect_withNullTokenValue_showsNull() {
        var place = Place.of("p", Value.class);
        var marking = Marking.empty();
        // Add a unit token (null value)
        marking.addToken(place, Token.unit());

        var inspected = marking.inspect();
        assertTrue(inspected.contains("null"), "inspect should show 'null' for null-valued token");
    }
}
