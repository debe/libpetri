package org.libpetri.core;

import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Build-time checks on instance composition: [MOD-027] arcs naming a port place composition
 * bound away, [MOD-020] two ports of one instance bound to one host place under a shared
 * consumer, the reset-place collection of {@link PetriNet.Builder#transition}, and
 * {@link PetriNet#subnetOf} ([MOD-040]).
 */
class ComposeBindingChecksTest {

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    /** The lab's answer subnet: IN -> start -> ANSWERING -> finish -> DRAFT, ports in / draft. */
    private static SubnetDef<Void> answer() {
        var in = p("IN");
        var busy = p("ANSWERING");
        var draft = p("DRAFT");
        return SubnetDef.builder("Answer").place(in).place(busy).place(draft)
            .transition(Transition.builder("start").inputs(In.one(in)).outputs(Out.place(busy)).build())
            .transition(Transition.builder("finish").inputs(In.one(busy)).outputs(Out.place(draft)).build())
            .inputPort("in", in).outputPort("draft", draft)
            .build();
    }

    /**
     * The lab's guard hub (research/net-metrics/lab GuardNets.turns(1, "hub")) reduced to the
     * defect: the host resets {@code answer/IN}, which compose bound to {@code A_IN}.
     */
    private static PetriNet.Builder hubHost(boolean killBeforeCompose) {
        var aIn = p("A_IN");
        var draft = p("DRAFT");
        var bad = p("VERDICT_BAD");
        var refused = p("REFUSED");
        var kill = Transition.builder("kill").inputs(In.one(bad)).inhibitor(draft)
            .reset(p("answer/IN")).reset(p("answer/ANSWERING")).outputs(Out.place(refused)).build();
        var b = PetriNet.builder("guard-hub");
        b.transition(Transition.builder("fork").inputs(In.one(p("INBOX"))).outputs(Out.and(p("G_IN"), aIn)).build());
        if (killBeforeCompose) b.transition(kill);
        b.compose(answer().instantiate("answer"), Map.of("in", aIn, "draft", draft));
        if (!killBeforeCompose) b.transition(kill);
        return b;
    }

    @Test
    void arcOnABoundAwayPort_isRejectedAtBuild_whateverTheOrder() {
        for (boolean before : new boolean[] {true, false}) {
            var builder = hubHost(before);
            var error = assertThrows(IllegalArgumentException.class, builder::build);
            assertTrue(error.getMessage().startsWith(
                    "place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN'"
                        + " at compose; reference 'A_IN' instead"),
                error.getMessage());
        }
    }

    @Test
    void referencingTheHostPlace_builds_andTheResetClearsWhatTheInstanceConsumes() {
        var aIn = p("A_IN");
        var b = PetriNet.builder("fixed");
        b.compose(answer().instantiate("answer"), Map.of("in", aIn, "draft", p("DRAFT")));
        b.transition(Transition.builder("kill").inputs(In.one(p("VERDICT_BAD"))).reset(aIn).build());
        var net = assertDoesNotThrow(b::build);
        var start = net.transitions().stream().filter(t -> t.name().equals("answer/start")).findFirst().orElseThrow();
        assertTrue(start.inputPlaces().contains(aIn), "the instance consumes from the place the reset clears");
    }

    @Test
    void anInternalPlaceOfTheInstance_isStillReferenceable() {
        // answer/ANSWERING is internal, not a port: it survives compose and a host arc on it is
        // legal (if poor encapsulation).
        var aIn = p("A_IN");
        var b = PetriNet.builder("reach-in");
        b.compose(answer().instantiate("answer"), Map.of("in", aIn, "draft", p("DRAFT")));
        b.transition(Transition.builder("peek").inputs(In.one(p("GO"))).read(p("answer/ANSWERING")).build());
        assertDoesNotThrow(b::build);
    }

    @Test
    void everyArcKindOnABoundAwayPort_isRejected() {
        var retired = p("answer/DRAFT");
        var kinds = new java.util.ArrayList<Transition>();
        kinds.add(Transition.builder("in").inputs(In.one(retired)).build());
        kinds.add(Transition.builder("out").inputs(In.one(p("GO"))).outputs(Out.xor(p("OTHER"), retired)).build());
        kinds.add(Transition.builder("read").inputs(In.one(p("GO"))).read(retired).build());
        kinds.add(Transition.builder("inh").inputs(In.one(p("GO"))).inhibitor(retired).build());
        for (var t : kinds) {
            var b = PetriNet.builder("kinds");
            b.compose(answer().instantiate("answer"), Map.of("in", p("A_IN"), "draft", p("DRAFT")));
            b.transition(t);
            var error = assertThrows(IllegalArgumentException.class, b::build, t.name());
            assertTrue(error.getMessage().contains("is port 'draft' of instance 'answer'"), error.getMessage());
        }
    }

    @Test
    void aPortBoundToAPlaceOfTheSameIdentity_isNotRetired() {
        var b = PetriNet.builder("identity");
        b.compose(answer().instantiate("answer"), Map.of("in", p("answer/IN"), "draft", p("DRAFT")));
        b.transition(Transition.builder("feed").inputs(In.one(p("GO"))).outputs(Out.place(p("answer/IN"))).build());
        assertDoesNotThrow(b::build);
    }

    /** A join consuming from two ports. */
    private static SubnetDef<Void> join() {
        var a = p("A");
        var bb = p("B");
        return SubnetDef.builder("Join").place(a).place(bb).place(p("OUT"))
            .transition(Transition.builder("join").inputs(In.one(a), In.one(bb)).outputs(Out.place(p("OUT"))).build())
            .inputPort("a", a).inputPort("b", bb).outputPort("out", p("OUT"))
            .build();
    }

    @Test
    void twoPortsOnOneHostPlaceUnderOneConsumer_areRejectedAtCompose() {
        var x = p("X");
        var b = PetriNet.builder("collide");
        var error = assertThrows(IllegalArgumentException.class,
            () -> b.compose(join().instantiate("s"), Map.of("a", x, "b", x, "out", p("DONE"))));
        assertTrue(error.getMessage().startsWith(
                "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join'"
                    + " would consume from 'X' through two input arcs. Bind them to distinct places or"
                    + " use one port."),
            error.getMessage());
    }

    @Test
    void builderCollectsResetPlaces() {
        var net = PetriNet.builder("resets")
            .transition(Transition.builder("t").inputs(In.one(p("a"))).reset(p("scratch")).build())
            .build();
        assertTrue(net.places().contains(p("scratch")), net.places().toString());
    }

    @Test
    void subnetOf_readsMembershipThenInstancePrefix() {
        var guard = SubnetDef.builder("Guard").place(p("IN")).place(p("OK"))
            .transition(Transition.builder("check").inputs(In.one(p("IN"))).outputs(Out.place(p("OK"))).build())
            .build();
        var b = PetriNet.builder("host");
        b.compose(guard);                                                            // direct: membership
        b.compose(answer().instantiate("answer"), Map.of("in", p("A_IN"), "draft", p("DRAFT")));
        b.transition(Transition.builder("top").inputs(In.one(p("DRAFT"))).outputs(Out.place(p("x/y"))).build());
        var net = b.build();

        assertEquals(Optional.of("Guard"), net.subnetOf("check"));
        assertEquals(Optional.of("Guard"), net.subnetOf("IN"));
        assertEquals(Optional.of("answer"), net.subnetOf("answer/start"));
        assertEquals(Optional.of("answer"), net.subnetOf("answer/ANSWERING"));
        assertEquals(Optional.empty(), net.subnetOf("A_IN"), "a host place");
        assertEquals(Optional.empty(), net.subnetOf("top"), "a host transition");
        assertEquals(Optional.empty(), net.subnetOf("x/y"), "no transition under x/: not an instance");
        assertEquals(Optional.empty(), net.subnetOf("answer/IN"), "bound away: not in the net");
        assertEquals(Optional.empty(), net.subnetOf("nope/thing"), "not in the net");
        assertTrue(net.subnetMembership().keySet().stream().noneMatch(k -> k.startsWith("answer/")),
            "MOD-026 rule 4: instance composition records no membership");
    }

    @Test
    void subnetOf_walksUpToAPrefixThatCarriesATransition() {
        var b = PetriNet.builder("walk");
        b.transition(Transition.builder("s1/t").inputs(In.one(p("s1/IN"))).outputs(Out.place(p("s1/obs/TURN"))).build());
        b.transition(Transition.builder("outer/inner/t").inputs(In.one(p("outer/inner/p"))).outputs(Out.place(p("outer/q"))).build());
        b.compose(SubnetDef.builder("Owner").place(p("m/a/b"))
            .transition(Transition.builder("m/t").inputs(In.one(p("m/a/b"))).build())
            .build());
        var net = b.build();

        assertEquals(Optional.of("s1"), net.subnetOf("s1/obs/TURN"), "s1/obs carries no transition");
        assertEquals(Optional.of("s1"), net.subnetOf("s1/t"));
        assertEquals(Optional.of("outer/inner"), net.subnetOf("outer/inner/p"), "nested instance");
        assertEquals(Optional.of("outer/inner"), net.subnetOf("outer/inner/t"));
        assertEquals(Optional.of("outer"), net.subnetOf("outer/q"), "outer/inner/t is under outer/");
        assertEquals(Optional.of("Owner"), net.subnetOf("m/a/b"), "membership wins");
        assertEquals(Optional.of("Owner"), net.subnetOf("m/t"), "membership wins");
    }

    /** A leading '/' is not a prefix boundary: {@code /x/t} belongs to {@code /x} ([MOD-040]). */
    @Test
    void subnetOf_skipsALeadingSlash() {
        var net = PetriNet.builder("rooted")
            .transition(Transition.builder("/x/t").inputs(In.one(p("/x/IN"))).outputs(Out.place(p("/OUT"))).build())
            .build();

        assertEquals(Optional.of("/x"), net.subnetOf("/x/t"));
        assertEquals(Optional.of("/x"), net.subnetOf("/x/IN"));
        assertEquals(Optional.empty(), net.subnetOf("/OUT"), "'' is no instance");
        assertEquals(Optional.empty(), net.subnetOf("/x/absent"), "not in the net");
        assertEquals(Optional.empty(), net.subnetOf(null));
    }
}
