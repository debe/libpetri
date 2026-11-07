package org.libpetri.core;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * The build-time output-spec checks: [IO-012] AC5 (two branches claiming one set), [IO-013] AC7
 * (at most one Timeout node), [IO-013] AC8 (no Xor inside the Timeout child) and [IO-014] AC7 (ForwardInput only inside a Timeout child), with
 * the cross-language message text and check order.
 */
class OutputSpecBuildChecksTest {

    private static final Duration D = Duration.ofSeconds(1);
    private static final Duration E = Duration.ofSeconds(2);

    private static final Place<Object> A = p("A");
    private static final Place<Object> B = p("B");
    private static final Place<Object> C = p("C");
    private static final Place<Object> P = p("P");
    private static final Place<Object> Q = p("Q");
    private static final Place<Object> IN = p("a");

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    private static Transition build(Out spec) {
        return Transition.builder("t").inputs(In.one(IN)).outputs(spec).build();
    }

    private static String rejection(Out spec) {
        return assertThrows(IllegalArgumentException.class, () -> build(spec), spec.toString()).getMessage();
    }

    private static String ambiguous(int i, int j, String places) {
        return "output spec of transition 't' is ambiguous: output branches " + i + " and " + j
            + " both claim {" + places + "}; no write can tell them apart (IO-012)";
    }

    private static String timeouts(int n) {
        return "output spec of transition 't' has " + n + " Timeout nodes; an output spec has at most one,"
            + " nested or not (IO-013)";
    }

    private static String xorInTimeout() {
        return "output spec of transition 't' has a Xor node inside the child of its Timeout node; the"
            + " timeout outcome deposits one fixed set of places (IO-013)";
    }

    private static String bareForward(String from, String to) {
        return "output spec of transition 't' uses ForwardInput('" + from + "', '" + to + "') outside the"
            + " child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)";
    }

    // ==================== IO-012 AC5 ====================

    @Test
    void io012_ac5_ambiguousSpecsAreRejectedNamingTheFirstPair() {
        var cases = Map.<Out, String>of(
            Out.xor(P, P), ambiguous(0, 1, "P"),
            Out.xor(Out.and(A, B), Out.and(B, A)), ambiguous(0, 1, "A, B"),
            Out.xor(Out.place(A), Out.xor(A, B)), ambiguous(0, 1, "A"),
            Out.and(Out.place(Q), Out.xor(P, P)), ambiguous(0, 1, "Q, P"),
            Out.xor(Out.and(Out.place(A), Out.xor(B, C)), Out.and(A, B)), ambiguous(0, 2, "A, B"),
            Out.xor(Out.place(P), Out.timeout(D, Out.place(P))), ambiguous(0, 1, "P"),
            Out.xor(Out.place(B), Out.timeout(D, Out.forwardInput(IN, B))), ambiguous(0, 1, "B"));
        cases.forEach((spec, message) -> assertEquals(message, rejection(spec), spec.toString()));
    }

    @Test
    void io012_ac5_distinctBranchesBuild() {
        assertDoesNotThrow(() -> build(Out.xor(Out.and(A, B, C), Out.and(A, B))));
        assertDoesNotThrow(() -> build(Out.xor(Out.and(P, A), Out.and(P, B))));
        assertDoesNotThrow(() -> build(Out.xor(Out.place(A), Out.timeout(D, Out.place(B)))));
    }

    @Test
    void io012_indicesFollowTheIo016Numbering() {
        // And's first child varies slowest: Xor(A, B) x Xor(P, P) = [A,P] [A,P] [B,P] [B,P].
        assertEquals(ambiguous(0, 1, "A, P"), rejection(Out.and(Out.xor(A, B), Out.xor(P, P))));
        // Xor(P, P) x Xor(A, B) = [P,A] [P,B] [P,A] [P,B]: the first repeat is branch 2.
        assertEquals(ambiguous(0, 2, "P, A"), rejection(Out.and(Out.xor(P, P), Out.xor(A, B))));
        // The repeated set of the third alternative was first claimed by the first.
        assertEquals(ambiguous(0, 3, "A, B"),
            rejection(Out.xor(Out.and(A, B), Out.place(C), Out.place(Q), Out.and(B, A))));
    }

    @Test
    void io012_reportsThePairTheOtherImplementationsReport() {
        var x = p("X");
        var y = p("Y");
        var d = p("D");
        var e = p("E");
        // Branches [X,A] [X,B] [X,A'] [Y,A] [Y,B] [Y,A'] with A' = A: (0, 2).
        assertEquals(ambiguous(0, 2, "X, A"),
            rejection(Out.and(Out.xor(x, y), Out.xor(Out.place(A), Out.place(B), Out.place(A)))));
        // A repeat in the first child shows at stride 3: (0, 3).
        assertEquals(ambiguous(0, 3, "X, A"),
            rejection(Out.and(Out.xor(x, x), Out.xor(Out.place(A), Out.place(B), Out.place(C)))));
        // A later alternative that repeats a deep branch of an earlier one: (3, 5).
        assertEquals(ambiguous(3, 5, "B, D"),
            rejection(Out.xor(Out.and(Out.xor(A, B), Out.xor(C, d)), Out.place(e), Out.and(d, B))));
    }

    @Test
    void io012_alternativesSharingOnePlaceAreComparedWithinEachOthersPlaces() {
        var left = new ArrayList<Out>();
        var right = new ArrayList<Out>();
        left.add(Out.place(P));
        right.add(Out.place(P));
        for (int k = 0; k < 40; k++) {
            left.add(Out.xor(p("x" + k), p("y" + k)));
            right.add(Out.xor(p("u" + k), p("v" + k)));
        }
        assertTimeoutPreemptively(Duration.ofSeconds(5),
            () -> build(Out.xor(new Out.And(left), new Out.And(right))));
    }

    @Test
    void io012_largeSpecsAreCheckedWithoutEnumeratingEveryBranch() {
        // An And of 64 two-way Xors has 2^64 branches, all distinct.
        var wide = new ArrayList<Out>();
        for (int k = 0; k < 64; k++) wide.add(Out.xor(p("x" + k), p("y" + k)));
        assertTimeoutPreemptively(Duration.ofSeconds(5), () -> build(new Out.And(wide)));

        // The same with a duplicate in the first child: the first repeat is branch 2^64.
        var dupFirst = new ArrayList<Out>();
        dupFirst.add(Out.xor(P, P));
        dupFirst.addAll(wide);
        var message = assertTimeoutPreemptively(Duration.ofSeconds(5), () -> rejection(new Out.And(dupFirst)));
        var names = new StringBuilder("P");
        for (int k = 0; k < 64; k++) names.append(", x").append(k);
        assertEquals("output spec of transition 't' is ambiguous: output branches 0 and 18446744073709551616"
            + " both claim {" + names + "}; no write can tell them apart (IO-012)", message);
    }

    // ==================== IO-013 AC7 ====================

    @Test
    void io013_ac7_moreThanOneTimeoutIsRejected() {
        assertEquals(timeouts(2), rejection(Out.timeout(D, Out.timeout(E, Out.place(P)))));
        assertEquals(timeouts(2), rejection(Out.xor(Out.timeout(D, Out.place(A)), Out.timeout(E, Out.place(B)))));
        assertEquals(timeouts(2), rejection(Out.and(Out.timeout(D, Out.place(A)),
            Out.xor(Out.place(B), Out.timeout(E, Out.place(C))))));
        assertEquals(timeouts(3), rejection(Out.xor(Out.timeout(D, Out.place(A)),
            Out.timeout(E, Out.timeout(D, Out.place(B))), Out.place(C))));
    }

    @Test
    void io013_ac7_oneTimeoutBuilds() {
        assertDoesNotThrow(() -> build(Out.xor(Out.place(A), Out.timeout(D, Out.place(B)))));
        assertDoesNotThrow(() -> build(Out.timeout(D, Out.and(A, B))));
    }

    // ==================== IO-013 AC8 ====================

    @Test
    void io013_ac8_xorInsideTheTimeoutChildIsRejected() {
        var d = p("D");
        assertEquals(xorInTimeout(), rejection(Out.timeout(D, Out.xor(A, B))));
        assertEquals(xorInTimeout(), rejection(
            Out.xor(Out.place(C), Out.timeout(D, Out.and(Out.place(A), Out.xor(B, d))))));
        assertEquals(xorInTimeout(), rejection(
            Out.and(Out.place(C), Out.timeout(D, Out.and(Out.place(A), Out.and(Out.xor(B, d)))))));
    }

    @Test
    void io013_ac8_xorOutsideTheTimeoutChildBuilds() {
        assertDoesNotThrow(() -> build(Out.xor(Out.place(A), Out.timeout(D, Out.place(B)))));
        assertDoesNotThrow(() -> build(Out.timeout(D, Out.and(Out.place(A), Out.forwardInput(IN, B)))));
        assertDoesNotThrow(() -> build(Out.xor(Out.and(Out.place(C), Out.timeout(D, Out.and(A, B))),
            Out.place(P))));
    }

    // ==================== IO-014 AC7 ====================

    @Test
    void io014_ac7_forwardOutsideATimeoutChildIsRejected() {
        var b = p("b");
        var c = p("c");
        var e = p("e");
        assertEquals(bareForward("a", "b"), rejection(Out.forwardInput(IN, b)));
        assertEquals(bareForward("a", "b"), rejection(Out.xor(Out.place(c), Out.forwardInput(IN, b))));
        assertEquals(bareForward("a", "b"), rejection(Out.and(Out.place(c), Out.xor(Out.place(e), Out.forwardInput(IN, b)))));
    }

    @Test
    void io014_ac7_forwardInsideATimeoutChildBuilds() {
        var b = p("b");
        var c = p("c");
        var e = p("e");
        assertDoesNotThrow(() -> build(Out.timeout(D, Out.forwardInput(IN, b))));
        assertDoesNotThrow(() -> build(Out.xor(Out.place(c), Out.timeout(D, Out.and(Out.place(e), Out.forwardInput(IN, b))))));
    }

    // ==================== Check order ====================

    @Test
    void checksRunInTheirFixedOrder() {
        var other = p("other");
        // IO-011 before IO-013.
        assertEquals("output spec of transition 't' names place 'P' twice in one AND branch; outputs are sets"
                + " (IO-015) — a weighted output is not supported, add a second place or a follow-up transition",
            rejection(Out.and(Out.place(P), Out.place(P), Out.timeout(D, Out.place(A)), Out.timeout(E, Out.place(B)))));
        // IO-011 before the IO-013 Xor-in-Timeout check.
        assertEquals("output spec of transition 't' names place 'P' twice in one AND branch; outputs are sets"
                + " (IO-015) — a weighted output is not supported, add a second place or a follow-up transition",
            rejection(Out.timeout(D, Out.and(Out.place(P), Out.xor(P, A)))));
        // IO-013 Timeout count before the IO-013 Xor-in-Timeout check.
        assertEquals(timeouts(2), rejection(Out.xor(Out.timeout(D, Out.xor(A, B)), Out.timeout(E, Out.place(C)))));
        // IO-013 before IO-014.
        assertEquals(timeouts(2), rejection(Out.xor(Out.forwardInput(IN, A),
            Out.timeout(D, Out.place(B)), Out.timeout(E, Out.place(C)))));
        // IO-013 Xor-in-Timeout before IO-014 placement.
        assertEquals(xorInTimeout(), rejection(Out.xor(Out.forwardInput(IN, A), Out.timeout(D, Out.xor(B, C)))));
        // IO-013 Xor-in-Timeout before the from-is-input check.
        assertEquals(xorInTimeout(), rejection(Out.timeout(D, Out.xor(Out.forwardInput(other, B), Out.place(C)))));
        // IO-013 Xor-in-Timeout before IO-012.
        assertEquals(xorInTimeout(), rejection(Out.xor(Out.place(B), Out.timeout(D, Out.xor(B, C)))));
        // IO-014 placement before the from-is-input check.
        assertEquals(bareForward("other", "B"), rejection(Out.and(Out.place(A), Out.forwardInput(other, B))));
        // From-is-input (IO-014 AC3) before IO-012.
        assertEquals("Transition 't': ForwardInput references non-input place 'other'",
            rejection(Out.xor(Out.place(B), Out.timeout(D, Out.forwardInput(other, B)))));
    }

    @Test
    void theChecksRunOnTheCompositionPath() {
        // MOD-020 / IO-012: two output ports in different Xor alternatives bound to one host place.
        var in = p("IN");
        var sa = p("SA");
        var sb = p("SB");
        var def = SubnetDef.builder("Split").place(in).place(sa).place(sb)
            .transition(Transition.builder("split").inputs(In.one(in)).outputs(Out.xor(sa, sb)).build())
            .inputPort("in", in).outputPort("a", sa).outputPort("b", sb)
            .build();
        var host = PetriNet.builder("host");
        var x = p("X");
        var error = assertThrows(IllegalArgumentException.class,
            () -> host.compose(def.instantiate("s"), Map.of("in", p("GO"), "a", x, "b", x)));
        assertEquals("output spec of transition 's/split' is ambiguous: output branches 0 and 1 both claim {X};"
            + " no write can tell them apart (IO-012)", error.getMessage());
    }
}
