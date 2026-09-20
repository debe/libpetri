package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.libpetri.core.*;

import java.time.Instant;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * <b>CORE-073</b>: the structured snapshot form, and restore through it.
 *
 * <p>The form is normative precisely because it was not before: four implementations invented
 * four shapes, or none. These pin the shape itself — place <b>name</b> to an ordered sequence of
 * tokens — and the four criteria that a naive round-trip test cannot reach.
 */
class MarkingSnapshotTest {

    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);

    private static final Instant T1 = Instant.parse("2020-01-01T00:00:00Z");
    private static final Instant T2 = Instant.parse("2021-06-15T12:30:00Z");

    @Test
    void roundTripPreservesValueAndCreatedAt_AC1() {
        var marking = Marking.from(Map.of(A, List.of(new Token<>("x", T1))));

        var snapshot = marking.snapshot();
        assertEquals(List.of("a"), List.copyOf(snapshot.keySet()), "keyed by place NAME");

        var restored = Marking.fromSnapshot(snapshot, List.of(A));
        assertEquals("x", restored.peekFirst(A).value());
        assertEquals(T1, restored.peekFirst(A).createdAt(),
            "CORE-073 AC#1: created_at round-trips unchanged — restore is the one path where "
                + "the engine hands back a timestamp it did not choose");
    }

    @Test
    void fifoOrderSurvives_AC6() {
        var marking = Marking.empty();
        marking.addToken(A, new Token<>("A", T1));
        marking.addToken(A, new Token<>("B", T1));
        marking.addToken(A, new Token<>("C", T1));

        var restored = Marking.fromSnapshot(marking.snapshot(), List.of(A));

        assertEquals(List.of("A", "B", "C"),
            restored.peekTokens(A).stream().map(Token::value).toList(),
            "CORE-073 AC#6: order is part of the data — it decides which token a firing "
                + "consumes, so a snapshot that loses it is not a restore");
        assertEquals("A", restored.removeFirst(A).value(),
            "the first consumption takes A, not whichever the map happened to yield");
    }

    @Test
    void emptyAndOmittedPlacesRestoreIdentically_AC7() {
        // Capture never emits an empty sequence, so only a hand-built or foreign snapshot
        // reaches this path — which is why it is tested directly rather than by round-trip.
        var omitted  = Marking.fromSnapshot(Map.of(), List.of(A));
        var explicit = Marking.fromSnapshot(Map.of("a", List.of()), List.of(A));

        assertEquals(0, omitted.tokenCount(A));
        assertEquals(0, explicit.tokenCount(A));
        assertEquals(omitted.snapshot(), explicit.snapshot(),
            "CORE-073 AC#7: a place present-but-empty and a place omitted must restore "
                + "identically. A round-trip test can never exercise this, because capture "
                + "omits empty places in every implementation.");
    }

    @Test
    void unknownPlaceNameIsRetainedNotDropped_AC7() {
        // A snapshot taken from a net that has since lost a place.
        var snapshot = Map.<String, List<Token<?>>>of("goneAway", List.of(new Token<>("v", T2)));

        var restored = Marking.fromSnapshot(snapshot, List.of(A));

        assertEquals(snapshot, restored.snapshot(),
            "CORE-073 AC#7 / CORE-072: a place name the receiving net does not declare is "
                + "retained rather than dropped, so a snapshot survives a round-trip through a "
                + "net that has since gained or lost a place");
    }

    /** A value no built-in codec can encode. */
    private record Unserializable(Runnable closure, Object nativeHandle) {}

    @Test
    void noCodecIsImposedOnValues_AC8() {
        Place<Unserializable> opaque = Place.of("opaque", Unserializable.class);
        var value = new Unserializable(() -> { }, new Object());
        var marking = Marking.from(Map.of(opaque, List.of(new Token<>(value, T1))));

        var restored = Marking.fromSnapshot(marking.snapshot(), List.of(opaque));

        assertSame(value, restored.peekFirst(opaque).value(),
            "CORE-073 AC#8: the form is structural, not serialized. The engine must not impose "
                + "a codec nor require values to be serializable — the host owns that, because "
                + "only the host knows what its values are. The same instance comes back.");
    }

    @Test
    void snapshotPlaceOrderIsDeterministic_AC12() {
        var marking = Marking.empty();
        for (var name : List.of("zeta", "alpha", "mid")) {
            marking.addToken(Place.of(name, String.class), new Token<>("v", T1));
        }
        assertEquals(List.of("alpha", "mid", "zeta"), List.copyOf(marking.snapshot().keySet()),
            "CORE-073 AC#12: sorted by place name. Inserted zeta/alpha/mid deliberately — "
                + "comparing two snapshots of one marking would pass against an implementation "
                + "that merely preserved insertion order, which is what this criterion rules "
                + "out. Only the per-place sequence is normatively ordered, but a stable key "
                + "order keeps a serialized snapshot diffable, hashable and content-addressable.");
    }

    @Test
    void placeOrderIsCodePointNotUtf16CodeUnit_AC12() {
        // U+1F600 (astral, leading surrogate 0xD83D) against U+E000 (private use, BMP).
        //   code point: U+E000 (57344) < U+1F600 (128512)   -> privateUse first
        //   code unit : 0xD83D (55357) < 0xE000 (57344)     -> astral first
        // The two orders disagree, which an all-ASCII test can never reveal.
        String astral     = "\uD83D\uDE00";
        String privateUse = "\uE000";

        var marking = Marking.empty();
        marking.addToken(Place.of(astral, String.class), new Token<>("v", T1));
        marking.addToken(Place.of(privateUse, String.class), new Token<>("v", T1));

        assertEquals(List.of(privateUse, astral), List.copyOf(marking.snapshot().keySet()),
            "CORE-073 AC#12: ascending CODE-POINT order, not Java's natural String.compareTo, "
                + "which is UTF-16 code-unit order. A place name above U+FFFF is enough to make "
                + "Java disagree with Rust and TypeScript about the same marking — and the point "
                + "of one normative form is that a snapshot compares equal byte for byte across "
                + "languages, which is what lets a cross-language conformance check be a byte "
                + "comparison rather than a normalise-then-compare.");

        // Sanity: the natural order really is the other one, so this test discriminates.
        assertTrue(astral.compareTo(privateUse) < 0,
            "String.compareTo puts the astral name first — the order this test rules out");
    }

    @Test
    void theMarkingSnapshotEventCanonicalisesOrderToo_AC12_EVT014() {
        // Built from a deliberately UNORDERED input, not from Marking.snapshot(): asserting on
        // an already-sorted input would pass against an event that merely preserved what it was
        // given, which is what this has to rule out.
        String astral     = "\uD83D\uDE00";
        String privateUse = "\uE000";
        var unordered = new java.util.LinkedHashMap<String, List<Token<?>>>();
        unordered.put("zeta",      List.of(new Token<>("v", T1)));
        unordered.put(astral,      List.of(new Token<>("v", T1)));
        unordered.put("alpha",     List.of(new Token<>("v", T1)));
        unordered.put(privateUse,  List.of(new Token<>("v", T1)));

        var event = new org.libpetri.event.NetEvent.MarkingSnapshot(Instant.EPOCH, unordered);

        assertEquals(List.of("alpha", "zeta", privateUse, astral),
            List.copyOf(event.marking().keySet()),
            "CORE-073 / EVT-014: the canonical order follows the form into the event. It used to "
                + "collect into Collectors.toUnmodifiableMap, whose Map.ofEntries backing "
                + "randomises iteration order with a per-JVM salt — so the same marking produced "
                + "a different key order on every run, and an archive written twice from "
                + "identical data differed. Canonicalising the returned snapshot but not the "
                + "event would fix the case nobody persists and leave the case everyone does.");

        // Same input again: order is a function of the content, not of when it was built.
        assertEquals(List.copyOf(event.marking().keySet()),
            List.copyOf(new org.libpetri.event.NetEvent.MarkingSnapshot(Instant.EPOCH, unordered)
                .marking().keySet()),
            "reproducible across constructions — [EVT-025] makes event bodies per-language and "
                + "explicitly not byte-compatible, so cross-language equality is not claimed; "
                + "reproducibility across runs of THIS implementation is what is required");
    }

    @Test
    void restoreIsUnaffectedByThePresentedPlaceOrder_AC12() {
        // The second half of AC#12, and the half that matters more in Java than elsewhere:
        // restore resolves names against the receiving net, so there is a lookup step where an
        // order dependency could hide.
        Place<String> z = Place.of("zeta", String.class);
        Place<String> m = Place.of("mid",  String.class);
        var places = List.<Place<?>>of(A, z, m);

        var forward = new java.util.LinkedHashMap<String, List<Token<?>>>();
        forward.put("a",    List.of(new Token<>("1", T1)));
        forward.put("mid",  List.of(new Token<>("2", T1)));
        forward.put("zeta", List.of(new Token<>("3", T2)));

        var reversed = new java.util.LinkedHashMap<String, List<Token<?>>>();
        List.copyOf(forward.keySet()).reversed().forEach(k -> reversed.put(k, forward.get(k)));

        assertEquals(List.of("a", "mid", "zeta"), List.copyOf(forward.keySet()));
        assertEquals(List.of("zeta", "mid", "a"), List.copyOf(reversed.keySet()),
            "the two really are presented in different orders");

        assertEquals(
            Marking.fromSnapshot(forward, places).snapshot(),
            Marking.fromSnapshot(reversed, places).snapshot(),
            "CORE-073 AC#12: a restore is unaffected by the order the places are presented in");
    }

    // Restore THROUGH AN EXECUTOR (AC#9, AC#10, AC#11, and AC#7 retention end to end) lives in
    // AbstractExecutorSnapshotTest, which runs every case against both executors: they share
    // neither the restore path nor the in-flight bookkeeping.

    // ============================================================
    //  MOD-024 — two places, one name (Java only)
    // ============================================================

    private static final Place<String>  X_STRING  = Place.of("x", String.class);
    private static final Place<Integer> X_INTEGER = Place.of("x", Integer.class);

    @Test
    void restoreRejectsTwoPlacesWithOneName_MOD024() {
        var snapshot = Map.<String, List<Token<?>>>of("x", List.of(new Token<>("s", T1)));

        var ex = assertThrows(IllegalArgumentException.class,
            () -> Marking.fromSnapshot(snapshot, List.of(X_STRING, X_INTEGER)),
            "Java tells the two apart by token type; the snapshot form knows only 'x'. Which "
                + "place the tokens belong to is not recoverable, and resolving to whichever "
                + "the collection offered last landed them on the wrong place or the right one "
                + "by luck.");
        assertTrue(ex.getMessage().contains("'x'") && ex.getMessage().contains("MOD-024"),
            "names the place and the requirement. Got: " + ex.getMessage());

        assertThrows(IllegalArgumentException.class,
            () -> Marking.resolveSnapshot(Map.of(), List.of(X_STRING, X_INTEGER)),
            "rejected on the NET, not on the collision: the outcome must not depend on what one "
                + "particular snapshot happened to hold");
        assertDoesNotThrow(() -> Marking.fromSnapshot(snapshot, List.of(X_STRING, X_STRING, A)),
            "the same place twice is not two places");
    }

    @Test
    void snapshotOfTwoMarkedPlacesWithOneNameNeverThrowsAndLosesNothing_MOD024() {
        var marking = Marking.empty();
        marking.addToken(X_STRING, new Token<>("s", T1));
        marking.addToken(X_INTEGER, new Token<>(1, T2));

        // The executors call this on the orchestrator thread to emit MarkingSnapshot events; a
        // throw there aborts the run. So the loud failure is executor.snapshot()'s and
        // restore's, on the caller's thread — and this merges rather than overwrites.
        var snapshot = assertDoesNotThrow(marking::snapshot);
        assertEquals(List.of(1, "s"), snapshot.get("x").stream().map(Token::value).toList(),
            "both places' tokens, ordered by token-type name (java.lang.Integer before "
                + "java.lang.String) — a function of the content, not of HashMap order over a "
                + "hash that includes Class.hashCode(). One used to overwrite the other: "
                + snapshot);
    }
}
