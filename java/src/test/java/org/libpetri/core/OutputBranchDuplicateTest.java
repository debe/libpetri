package org.libpetri.core;

import java.time.Duration;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [IO-011] AC4: a place named twice in one AND branch of an output spec is rejected when the
 * transition is built; [MOD-020] AC8: two output ports bound to one host place in one AND branch
 * are rejected at compose with the port-naming message.
 */
class OutputBranchDuplicateTest {

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    private static String message(String t, String place) {
        return "output spec of transition '" + t + "' names place '" + place + "' twice in one AND branch;"
            + " outputs are sets (IO-015) — a weighted output is not supported, add a second place or a"
            + " follow-up transition";
    }

    private static Transition.Builder t(String name) {
        return Transition.builder(name).inputs(In.one(p("IN")));
    }

    @Test
    void aPlaceTwiceInOneAndBranch_isRejectedAtTransitionBuild() {
        var pp = p("P");
        var specs = new Arc.Out[] {
            Out.and(pp, pp),
            Out.and(Out.place(pp), Out.and(Out.place(p("Q")), Out.place(pp))),
            Out.xor(Out.place(p("A")), Out.and(pp, pp)),
            // A XOR child of an AND: the branch {P, P} exists.
            Out.and(Out.xor(pp, p("A")), Out.place(pp)),
            // A timeout branch is read through to its child.
            Out.xor(Out.place(p("A")), Out.timeout(Duration.ofSeconds(1), Out.and(pp, pp))),
        };
        for (var spec : specs) {
            var error = assertThrows(IllegalArgumentException.class, () -> t("fork").outputs(spec).build(),
                spec.toString());
            assertEquals(message("fork", "P"), error.getMessage());
        }
    }

    @Test
    void theSamePlaceInDifferentXorAlternatives_isAccepted() {
        var pp = p("P");
        assertDoesNotThrow(() -> t("choose").outputs(
            Out.xor(Out.and(pp, p("A")), Out.and(pp, p("B")))).build());
        assertDoesNotThrow(() -> t("choose2").outputs(Out.xor(pp, p("A"), p("B"))).build());
        assertDoesNotThrow(() -> t("fork").outputs(Out.and(pp, p("Q"))).build());
    }

    @Test
    void aForwardInputTargetCountsAsALeaf() {
        var in = p("IN");
        var error = assertThrows(IllegalArgumentException.class, () -> Transition.builder("retry")
            .inputs(In.one(in))
            .outputs(Out.and(Out.place(p("R")), Out.forwardInput(in, p("R"))))
            .build());
        assertEquals(message("retry", "R"), error.getMessage());
    }

    /** A split producing into both output ports in one AND branch, or in two XOR alternatives. */
    private static SubnetDef<Void> split(boolean and) {
        var in = p("IN");
        var a = p("A");
        var b = p("B");
        return SubnetDef.builder("Split").place(in).place(a).place(b)
            .transition(Transition.builder("split").inputs(In.one(in))
                .outputs(and ? Out.and(a, b) : Out.xor(a, b)).build())
            .inputPort("in", in).outputPort("a", a).outputPort("b", b)
            .build();
    }

    @Test
    void twoOutputPortsBoundToOneHostPlace_inOneAndBranch_isRejectedAtCompose() {
        var x = p("X");
        var b = PetriNet.builder("host");
        var error = assertThrows(IllegalArgumentException.class, () -> b.compose(
            split(true).instantiate("s"), Map.of("in", p("GO"), "a", x, "b", x)));
        assertEquals("ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition"
            + " 's/split' would produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind"
            + " them to distinct places or use one port.", error.getMessage());
    }

    @Test
    void twoOutputPortsBoundToOneHostPlace_inDifferentXorAlternatives_isAccepted() {
        var x = p("X");
        var b = PetriNet.builder("host");
        b.compose(split(false).instantiate("s"), Map.of("in", p("GO"), "a", x, "b", x));
        var net = assertDoesNotThrow(b::build);
        var s = net.transitions().stream().filter(t -> t.name().equals("s/split")).findFirst().orElseThrow();
        assertTrue(s.outputSpec().allPlaces().contains(x));
    }
}
