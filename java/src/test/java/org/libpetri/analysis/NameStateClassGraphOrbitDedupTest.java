package org.libpetri.analysis;

import java.time.Duration;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-012] orbit dedup: a join (and the EXTENDED consume role) emits one successor per distinct
 * signature among its enabling symbols, not one per symbol. The class set is unchanged — only
 * parallel identical edges disappear — and join-heavy graphs stop being quadratic in their class
 * count.
 */
class NameStateClassGraphOrbitDedupTest {

    private static final Place<String> CLERK = Place.of("clerk", String.class);
    private static final Place<String> ORDER = Place.of("order", String.class);
    private static final Place<String> ORDER_CLERK = Place.of("order_clerk", String.class);
    private static final Place<String> SEND_DONE = Place.of("send_done", String.class);

    /** PNID Fig. 11(b) (research/net-metrics/validation/pnid, {@code res11b}); two clerks. */
    private static PetriNet fig11b() {
        var match = MatchSpec.builder()
            .key(ORDER, (String v) -> NameId.of(v))
            .key(ORDER_CLERK, (String v) -> NameId.of(v))
            .build();
        return StructureOnly.bind(PetriNet.builder("P-Fig11b-not-exclusive").transitions(
            Transition.builder("create_order").read(CLERK).outputs(Out.and(ORDER, ORDER_CLERK)).build(),
            Transition.builder("send_order").inputs(In.one(ORDER), In.one(ORDER_CLERK)).match(match)
                .outputs(Out.place(SEND_DONE)).build()).build());
    }

    private static NameStateClassGraph build(PetriNet net, int maxClasses) {
        var fragment = NameFragment.classify(net, FragmentMode.BASE, Set.of(), AllMints.of(net));
        return NameStateClassGraph.build(net, MarkingState.builder().tokens(CLERK, 2).build(), fragment,
            maxClasses, Set.of(), EnvironmentAnalysisMode.ignore(), PrioritySemantics.NONE);
    }

    @Test
    @Timeout(value = 120, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void fig11b_anEightThousandClassBuild_isFast() {
        var net = fig11b();
        build(net, 500); // warm-up
        var timings = new ArrayList<String>();
        long last = 0;
        for (int cap : new int[] {2_000, 4_000, 8_000}) {
            long t0 = System.nanoTime();
            var graph = build(net, cap);
            last = (System.nanoTime() - t0) / 1_000_000;
            assertFalse(graph.isComplete(), "Fig. 11(b) mints without bound");
            assertEquals(cap, graph.classCount(), "the build stops at its class budget");
            timings.add(cap + " classes: " + last + " ms");
        }
        System.out.println("[VER-012 orbit dedup] Fig. 11(b) Route B build: " + String.join(", ", timings));
        // Generous: measured at about a second after the dedup, and 14 s before it (quadratic:
        // every join emitted one successor per live order, each copied and keyed).
        assertTrue(last < 6_000, "8 000 classes took " + last + " ms");
    }

    @Test
    void fig11b_theJoinEmitsOneSuccessorPerSignature_notPerSymbol() {
        var graph = build(fig11b(), 200);
        // A class with n live orders, each on order and order_clerk once: every one has the same
        // signature, so send_order leaves it by one edge, not n.
        for (int i = 0; i < graph.expandedCount(); i++) {
            long sends = graph.successorLabelsOf(i).stream().filter("send_order"::equals).count();
            assertTrue(sends <= 1, "class " + i + " has " + sends + " send_order edges");
        }
        // No two edges out of one class share a label and a target.
        for (int i = 0; i < graph.expandedCount(); i++) {
            var seen = new HashSet<String>();
            var succ = graph.successorsOf(i);
            var labels = graph.successorLabelsOf(i);
            for (int k = 0; k < succ.size(); k++) {
                assertTrue(seen.add(labels.get(k) + ">" + succ.get(k)), "parallel identical edge out of " + i);
            }
        }
    }

    /**
     * Different signatures stay apart: a join whose enabling symbols differ in how often they
     * occur elsewhere yields one successor per signature. {@code mk: S -> A, B, C} mints a name
     * onto {@code A}, {@code B} and the extra coloured place {@code C}; {@code mk2: T -> A, B}
     * mints one onto {@code A} and {@code B} only. The join on {@code A, B} then has two
     * signatures — and two distinct successor classes.
     */
    @Test
    void distinctSignatures_keepDistinctSuccessors() {
        var s = Place.of("S", String.class);
        var t = Place.of("T", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var c = Place.of("C", String.class);
        var d = Place.of("D", String.class);
        var done = Place.of("DONE", String.class);
        var matchAB = MatchSpec.builder().key(a, (String v) -> NameId.of(v)).key(b, (String v) -> NameId.of(v)).build();
        var matchCD = MatchSpec.builder().key(c, (String v) -> NameId.of(v)).key(d, (String v) -> NameId.of(v)).build();
        var net = StructureOnly.bind(PetriNet.builder("signatures").transitions(
            Transition.builder("mk").inputs(In.one(s)).outputs(Out.and(a, b, c)).build(),
            Transition.builder("mk2").inputs(In.one(t)).outputs(Out.and(a, b)).build(),
            Transition.builder("join").inputs(In.one(a), In.one(b)).match(matchAB).outputs(Out.place(done)).build(),
            // Makes C a coloured place (a key) without ever firing: D is never marked.
            Transition.builder("never").inputs(In.one(c), In.one(d)).match(matchCD).outputs(Out.place(done)).build())
            .build());
        var fragment = NameFragment.classify(net, FragmentMode.BASE, Set.of(), AllMints.of(net));
        var graph = NameStateClassGraph.build(net, MarkingState.builder().tokens(s, 1).tokens(t, 1).build(), fragment,
            1_000, Set.of(), EnvironmentAnalysisMode.ignore(), PrioritySemantics.NONE);
        assertTrue(graph.isComplete());
        // The class after mk and mk2 holds two names with different signatures on A and B.
        int both = -1;
        for (int i = 0; i < graph.classCount(); i++) {
            var m = graph.markingOf(i);
            if (m.tokens(a) == 2 && m.tokens(b) == 2 && m.tokens(c) == 1) both = i;
        }
        assertTrue(both >= 0, "the class holding both names");
        List<Integer> joinTargets = new ArrayList<>();
        for (int k = 0; k < graph.successorsOf(both).size(); k++) {
            if (graph.successorLabelsOf(both).get(k).equals("join")) joinTargets.add(graph.successorsOf(both).get(k));
        }
        assertEquals(2, joinTargets.size(), "one successor per signature");
        assertEquals(2, new HashSet<>(joinTargets).size(), "and they are different classes");
    }

    /**
     * NU-054: a relaying join adds back the symbol it removed. Signatures are read on the
     * PRE-step layer, where a transposition of two equal-signature symbols fixes the layer; the
     * relay step is equivariant (it adds exactly the symbol it removed), so that transposition
     * maps one successor onto the other and their canonical keys are equal. The dedup therefore
     * still emits one successor per signature — here for a correlated self-loop, whose relay
     * target {@code Y} is also a key.
     */
    @Test
    void relayJoin_equalSignatureSymbolsGiveEqualKeys() {
        var s = Place.of("S", String.class);
        var p = Place.of("p", String.class);
        var y = Place.of("Y", String.class);
        var q = Place.of("q", String.class);
        var done = Place.of("done", String.class);
        var net = StructureOnly.bind(PetriNet.builder("relay-self-loop").transitions(
            Transition.builder("A").inputs(In.one(s)).outputs(Out.and(p, y)).build(),
            Transition.builder("B").inputs(In.one(p), In.one(y))
                .match(MatchSpec.builder().key(p, (String v) -> NameId.of(v)).key(y, (String v) -> NameId.of(v))
                    .relayTo(y, (String v) -> NameId.of(v)).relayTo(q, (String v) -> NameId.of(v)).build())
                .outputs(Out.and(y, q)).build(),
            Transition.builder("D").inputs(In.one(q), In.one(y))
                .match(MatchSpec.builder().key(q, (String v) -> NameId.of(v)).key(y, (String v) -> NameId.of(v)).build())
                .outputs(Out.place(done)).build())
            .build());
        var fragment = NameFragment.classify(net, FragmentMode.EXTENDED, Set.of(), AllMints.of(net));
        var role = fragment.role("B");
        assertTrue(role instanceof NameFragment.Role.Join j && j.relayTo().equals(Set.of("Y", "q")), role.toString());

        // Symbols 1 and 2 have equal signatures (p=1, Y=1); symbol 3 also sits on q.
        var names = new NameMarking();
        for (int sym : new int[] {1, 2, 3}) {
            names.add("p", sym, 1);
            names.add("Y", sym, 1);
        }
        names.add("q", 3, 1);
        Set<Place<?>> outs = Set.of(y, q);
        var succ = NameStateClassGraph.nameSuccessors(role, names, outs, fragment, new int[] {10})
            .stream().map(NameStateClassGraph.NameStep::after).toList();
        assertEquals(2, succ.size(), "one successor per signature: {1,2} and {3}");

        // Firing on the dropped symbol 2 by hand gives the key of the kept symbol 1's successor.
        var by2 = names.copy();
        by2.remove("p", 2, 1);
        by2.remove("Y", 2, 1);
        by2.add("Y", 2, 1);
        by2.add("q", 2, 1);
        assertEquals(succ.get(0).canonicalKey(fragment.colouredOrder), by2.canonicalKey(fragment.colouredOrder));
        assertEquals(1, succ.get(0).countOf("Y", 1), "the self-loop keeps the name on its key");
        assertEquals(1, succ.get(0).countOf("q", 1), "and relays it to q");
        assertEquals(0, succ.get(0).countOf("p", 1));
    }
}
