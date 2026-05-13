package org.libpetri.core.internal;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.time.Duration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link SubnetRewriter} — the structural rewrite primitive
 * shared between {@code SubnetDef.instantiate(...)} and (later)
 * {@code PetriNet.Builder.compose(...)} per <b>MOD-020</b>.
 *
 * <p>Coverage:
 * <ul>
 *   <li>Exhaustive {@code Arc.In} variants (One, Exactly, All, AtLeast).</li>
 *   <li>Exhaustive {@code Arc.Out} variants (Place, And, Xor, Timeout, ForwardInput),
 *       including a recursive {@code And/Xor} tree to verify tree-walking.</li>
 *   <li>Coverage of {@code Inhibitor}, {@code Read}, {@code Reset}.</li>
 *   <li>Identity behaviour on places not present in the remap (partial-remap
 *       semantics — the future {@code compose} caller depends on this).</li>
 *   <li>{@code renameNet} end-to-end check on a small body.</li>
 * </ul>
 */
class SubnetRewriterTest {

    // ============================================================
    //  Helpers
    // ============================================================

    private static <T> Place<T> p(String name, Class<T> type) {
        return Place.of(name, type);
    }

    /** Builds a single-entry remap: orig -> renamed (same tokenType). */
    private static <T> Map<Place<?>, Place<?>> remap(Place<T> orig, String prefix) {
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(orig, SubnetRewriter.renamePlace(orig, prefix));
        return m;
    }

    private static Place<?> renamed(Map<Place<?>, Place<?>> m, Place<?> orig) {
        return m.get(orig);
    }

    // ============================================================
    //  Arc.In rewrite — exhaustive variant coverage
    // ============================================================

    @Test
    void rewriteIn_one_remapsPlace() {
        Place<String> orig = p("input", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteIn(new Arc.In.One(orig), m);

        assertInstanceOf(Arc.In.One.class, rewritten);
        assertEquals("r1/input", rewritten.place().name());
        assertEquals(String.class, rewritten.place().tokenType());
    }

    @Test
    void rewriteIn_exactly_remapsPlace_preservesCount() {
        Place<String> orig = p("batch", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteIn(new Arc.In.Exactly(orig, 7), m);

        assertInstanceOf(Arc.In.Exactly.class, rewritten);
        var ex = (Arc.In.Exactly) rewritten;
        assertEquals("r1/batch", ex.place().name());
        assertEquals(7, ex.count());
    }

    @Test
    void rewriteIn_all_remapsPlace() {
        Place<String> orig = p("queue", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteIn(new Arc.In.All(orig), m);

        assertInstanceOf(Arc.In.All.class, rewritten);
        assertEquals("r1/queue", rewritten.place().name());
    }

    @Test
    void rewriteIn_atLeast_remapsPlace_preservesMinimum() {
        Place<String> orig = p("buf", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteIn(new Arc.In.AtLeast(orig, 3), m);

        assertInstanceOf(Arc.In.AtLeast.class, rewritten);
        var al = (Arc.In.AtLeast) rewritten;
        assertEquals("r1/buf", al.place().name());
        assertEquals(3, al.minimum());
    }

    // ============================================================
    //  Arc.Out rewrite — exhaustive variant coverage + recursion
    // ============================================================

    @Test
    void rewriteOut_place_remapsPlace() {
        Place<String> orig = p("out", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteOut(new Arc.Out.Place(orig), m);

        assertInstanceOf(Arc.Out.Place.class, rewritten);
        assertEquals("r1/out", ((Arc.Out.Place) rewritten).place().name());
    }

    @Test
    void rewriteOut_and_remapsAllChildren() {
        Place<String> a = p("a", String.class);
        Place<String> b = p("b", String.class);
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(a, SubnetRewriter.renamePlace(a, "r1"));
        m.put(b, SubnetRewriter.renamePlace(b, "r1"));

        var and = new Arc.Out.And(List.of(new Arc.Out.Place(a), new Arc.Out.Place(b)));
        var rewritten = (Arc.Out.And) SubnetRewriter.rewriteOut(and, m);

        assertEquals(2, rewritten.children().size());
        var c0 = (Arc.Out.Place) rewritten.children().get(0);
        var c1 = (Arc.Out.Place) rewritten.children().get(1);
        assertEquals("r1/a", c0.place().name());
        assertEquals("r1/b", c1.place().name());
    }

    @Test
    void rewriteOut_xor_remapsAllChildren() {
        Place<String> a = p("a", String.class);
        Place<String> b = p("b", String.class);
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(a, SubnetRewriter.renamePlace(a, "r1"));
        m.put(b, SubnetRewriter.renamePlace(b, "r1"));

        var xor = new Arc.Out.Xor(List.of(new Arc.Out.Place(a), new Arc.Out.Place(b)));
        var rewritten = (Arc.Out.Xor) SubnetRewriter.rewriteOut(xor, m);

        assertEquals(2, rewritten.children().size());
        assertEquals("r1/a", ((Arc.Out.Place) rewritten.children().get(0)).place().name());
        assertEquals("r1/b", ((Arc.Out.Place) rewritten.children().get(1)).place().name());
    }

    @Test
    void rewriteOut_andOfXor_recursivelyRewrites() {
        Place<String> a = p("a", String.class);
        Place<String> b = p("b", String.class);
        Place<String> c = p("c", String.class);
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(a, SubnetRewriter.renamePlace(a, "r1"));
        m.put(b, SubnetRewriter.renamePlace(b, "r1"));
        m.put(c, SubnetRewriter.renamePlace(c, "r1"));

        // AND( XOR(a,b), Place(c) )
        var tree = new Arc.Out.And(List.of(
            new Arc.Out.Xor(List.of(new Arc.Out.Place(a), new Arc.Out.Place(b))),
            new Arc.Out.Place(c)
        ));

        var rewritten = (Arc.Out.And) SubnetRewriter.rewriteOut(tree, m);

        // Outer And shape preserved.
        assertEquals(2, rewritten.children().size());

        // First child must still be an Xor, with both leaves remapped.
        var innerXor = (Arc.Out.Xor) rewritten.children().get(0);
        assertEquals(2, innerXor.children().size());
        assertEquals("r1/a", ((Arc.Out.Place) innerXor.children().get(0)).place().name());
        assertEquals("r1/b", ((Arc.Out.Place) innerXor.children().get(1)).place().name());

        // Second child is a leaf Place, remapped.
        assertEquals("r1/c", ((Arc.Out.Place) rewritten.children().get(1)).place().name());
    }

    @Test
    void rewriteOut_xorOfAnd_recursivelyRewrites() {
        Place<String> a = p("a", String.class);
        Place<String> b = p("b", String.class);
        Place<String> c = p("c", String.class);
        Place<String> d = p("d", String.class);
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(a, SubnetRewriter.renamePlace(a, "r1"));
        m.put(b, SubnetRewriter.renamePlace(b, "r1"));
        m.put(c, SubnetRewriter.renamePlace(c, "r1"));
        m.put(d, SubnetRewriter.renamePlace(d, "r1"));

        // XOR( AND(a,b), AND(c,d) )
        var tree = new Arc.Out.Xor(List.of(
            new Arc.Out.And(List.of(new Arc.Out.Place(a), new Arc.Out.Place(b))),
            new Arc.Out.And(List.of(new Arc.Out.Place(c), new Arc.Out.Place(d)))
        ));

        var rewritten = (Arc.Out.Xor) SubnetRewriter.rewriteOut(tree, m);
        assertEquals(2, rewritten.children().size());

        var leftAnd  = (Arc.Out.And) rewritten.children().get(0);
        var rightAnd = (Arc.Out.And) rewritten.children().get(1);

        assertEquals("r1/a", ((Arc.Out.Place) leftAnd.children().get(0)).place().name());
        assertEquals("r1/b", ((Arc.Out.Place) leftAnd.children().get(1)).place().name());
        assertEquals("r1/c", ((Arc.Out.Place) rightAnd.children().get(0)).place().name());
        assertEquals("r1/d", ((Arc.Out.Place) rightAnd.children().get(1)).place().name());
    }

    @Test
    void rewriteOut_timeout_recursesIntoChild_preservesDuration() {
        Place<String> orig = p("late", String.class);
        var m = remap(orig, "r1");

        var t = new Arc.Out.Timeout(Duration.ofMillis(250), new Arc.Out.Place(orig));
        var rewritten = (Arc.Out.Timeout) SubnetRewriter.rewriteOut(t, m);

        assertEquals(Duration.ofMillis(250), rewritten.after());
        assertEquals("r1/late", ((Arc.Out.Place) rewritten.child()).place().name());
    }

    @Test
    void rewriteOut_forwardInput_remapsBothEnds() {
        Place<String> from = p("query", String.class);
        Place<String> to   = p("retry", String.class);
        var m = new HashMap<Place<?>, Place<?>>();
        m.put(from, SubnetRewriter.renamePlace(from, "r1"));
        m.put(to,   SubnetRewriter.renamePlace(to, "r1"));

        var fi = new Arc.Out.ForwardInput(from, to);
        var rewritten = (Arc.Out.ForwardInput) SubnetRewriter.rewriteOut(fi, m);

        assertEquals("r1/query", rewritten.from().name());
        assertEquals("r1/retry", rewritten.to().name());
    }

    // ============================================================
    //  Inhibitor / Read / Reset
    // ============================================================

    @Test
    void rewriteInhibitor_remapsPlace_preservesGenericType() {
        Place<String> orig = p("paused", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteInhibitor(new Arc.Inhibitor<>(orig), m);
        assertEquals("r1/paused", rewritten.place().name());
        assertEquals(String.class, rewritten.place().tokenType());
    }

    @Test
    void rewriteRead_remapsPlace() {
        Place<String> orig = p("ctx", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteRead(new Arc.Read<>(orig), m);
        assertEquals("r1/ctx", rewritten.place().name());
    }

    @Test
    void rewriteReset_remapsPlace() {
        Place<String> orig = p("buf", String.class);
        var m = remap(orig, "r1");

        var rewritten = SubnetRewriter.rewriteReset(new Arc.Reset<>(orig), m);
        assertEquals("r1/buf", rewritten.place().name());
    }

    // ============================================================
    //  Partial remap (identity on unmapped places)
    // ============================================================

    @Test
    void rewriteIn_partialRemap_unmappedPlaceIsIdentity() {
        // Critical for compose(...): the future caller will pass a partial
        // remap (only the bound port places). Unmapped places must stay put.
        Place<String> mapped   = p("mapped", String.class);
        Place<String> unmapped = p("unmapped", String.class);
        var m = remap(mapped, "r1");
        // 'unmapped' is intentionally absent from m.

        var rA = SubnetRewriter.rewriteIn(new Arc.In.One(mapped), m);
        assertEquals("r1/mapped", rA.place().name(), "mapped place is rewritten");

        var rB = SubnetRewriter.rewriteIn(new Arc.In.One(unmapped), m);
        assertSame(unmapped, rB.place(), "unmapped place is identity (not renamed)");
    }

    @Test
    void rewriteOut_partialRemap_unmappedLeafIsIdentity() {
        Place<String> mapped   = p("mapped", String.class);
        Place<String> unmapped = p("unmapped", String.class);
        var m = remap(mapped, "r1");

        var tree = new Arc.Out.And(List.of(
            new Arc.Out.Place(mapped),
            new Arc.Out.Place(unmapped)
        ));
        var rewritten = (Arc.Out.And) SubnetRewriter.rewriteOut(tree, m);
        assertEquals("r1/mapped", ((Arc.Out.Place) rewritten.children().get(0)).place().name());
        assertSame(unmapped, ((Arc.Out.Place) rewritten.children().get(1)).place());
    }

    // ============================================================
    //  renameNet end-to-end
    // ============================================================

    @Test
    void renameNet_endToEnd_renamesEverythingAndFillsMaps() {
        Place<String> in = p("in", String.class);
        Place<String> out = p("out", String.class);
        Transition t = Transition.builder("forward")
            .inputs(Arc.In.one(in))
            .outputs(Arc.Out.and(out))
            .build();
        PetriNet body = PetriNet.builder("Body").transition(t).build();

        var placeRemap = new HashMap<Place<?>, Place<?>>();
        var transitionRemap = new HashMap<Transition, Transition>();

        PetriNet renamed = SubnetRewriter.renameNet(body, "i1", placeRemap, transitionRemap);

        // Net name itself prefixed.
        assertEquals("i1/Body", renamed.name());

        // Every place renamed.
        assertEquals(2, renamed.places().size());
        for (var p : renamed.places()) {
            assertTrue(p.name().startsWith("i1/"), "place: " + p.name());
        }

        // The remap holds old → new bindings.
        assertEquals("i1/in",  placeRemap.get(in).name());
        assertEquals("i1/out", placeRemap.get(out).name());

        // The single transition is also renamed and recorded in the remap.
        assertEquals(1, renamed.transitions().size());
        var renamedT = renamed.transitions().iterator().next();
        assertEquals("i1/forward", renamedT.name());
        assertSame(renamedT, transitionRemap.get(t));

        // Arcs in the renamed transition reference the renamed places (not originals).
        assertEquals(1, renamedT.inputSpecs().size());
        assertEquals("i1/in", renamedT.inputSpecs().get(0).place().name());
    }

    @Test
    void renameNet_clearsRemapMaps_onEntry() {
        Place<String> p1 = p("p1", String.class);
        Transition t = Transition.builder("t").read(p1).build();
        PetriNet body = PetriNet.builder("B").transition(t).build();

        var placeRemap = new HashMap<Place<?>, Place<?>>();
        placeRemap.put(p("garbage", String.class), p("more-garbage", String.class));
        var transitionRemap = new HashMap<Transition, Transition>();
        transitionRemap.put(t, t); // garbage stale entry

        SubnetRewriter.renameNet(body, "x", placeRemap, transitionRemap);

        // Garbage entries must be wiped out — only the freshly-renamed entries remain.
        assertFalse(placeRemap.containsKey(p("garbage", String.class)),
            "renameNet must clear the placeRemap on entry");
        assertEquals(1, placeRemap.size());
        assertTrue(placeRemap.containsKey(p1));

        assertEquals(1, transitionRemap.size());
        // The fresh entry has the renamed transition, not the original.
        assertEquals("x/t", transitionRemap.get(t).name());
    }

    @Test
    void rewriteTransition_preservesTimingPriorityActionByReference() {
        Place<String> in = p("in", String.class);
        // Use a non-passthrough action so we can compare references.
        org.libpetri.core.TransitionAction sharedAction =
            ctx -> java.util.concurrent.CompletableFuture.completedFuture(null);

        Transition orig = Transition.builder("t")
            .inputs(Arc.In.one(in))
            .timing(org.libpetri.core.Timing.delayed(Duration.ofMillis(50)))
            .priority(7)
            .action(sharedAction)
            .build();

        var m = remap(in, "z");
        var rewritten = SubnetRewriter.rewriteTransition(orig, "z", m);

        assertEquals("z/t", rewritten.name());
        assertEquals(7, rewritten.priority());
        assertSame(sharedAction, rewritten.action(), "MOD-030: action shared by reference");
        assertEquals(orig.timing(), rewritten.timing());
    }

    // ============================================================
    //  Convenience factories
    // ============================================================

    @Test
    void newPlaceRemap_returnsEmptyMutableMap() {
        Map<Place<?>, Place<?>> m = SubnetRewriter.newPlaceRemap();
        assertTrue(m.isEmpty());
        m.put(p("x", String.class), p("y", String.class));
        assertEquals(1, m.size());
    }

    @Test
    void newTransitionRemap_returnsEmptyMutableMap() {
        Map<Transition, Transition> m = SubnetRewriter.newTransitionRemap();
        assertTrue(m.isEmpty());
        Transition t = Transition.builder("t").read(p("p", String.class)).build();
        m.put(t, t);
        assertEquals(1, m.size());
    }

}
