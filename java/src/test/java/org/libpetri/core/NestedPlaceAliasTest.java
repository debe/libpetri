package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.runtime.ActionFailureHandler;
import org.libpetri.runtime.BitmapNetExecutor;
import org.libpetri.runtime.Marking;
import org.libpetri.runtime.PrecompiledNetExecutor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.place;

/**
 * Regression tests for the <b>MOD-031</b> declared&rarr;actual place
 * correspondence across <i>multiple</i> rewrite passes — AC#8 (identity
 * round-trip) and AC#9 (all-identity wholesale drop).
 *
 * <h2>What broke</h2>
 * <p>The correspondence's key set must stay the complete set of author-original
 * places through every pass. The chained pass deliberately does <b>not</b> walk
 * the arcs — their names are intermediate-pass names the author never declared —
 * which makes the map the <i>only</i> carrier of that key set. Dropping an entry
 * because it momentarily resolved to its own declared name therefore loses it for
 * good: a later pass renames the place, the chained path has nothing to carry
 * forward, and the action resolves against a place no longer in the composed net.
 *
 * <p>The failure is not a build error. The transition enables, fires, consumes its
 * inputs, and only then throws its declared-place check — so under [EXEC-031] (no
 * rollback) the tokens are gone. That is why these tests assert on an executor run
 * rather than on the correspondence's shape, and install an
 * {@link ActionFailureHandler}: without one the executor swallows the cause and the
 * only symptom is a silently empty sink.
 *
 * <p>Both executors are exercised: {@link BitmapNetExecutor} is the reference
 * semantics and {@link PrecompiledNetExecutor} must stay behaviorally identical.
 */
class NestedPlaceAliasTest {

    /**
     * MOD-031 AC#8 — the mixed case. One declared place round-trips to its own
     * name at an intermediate pass while another is renamed at that same pass;
     * a later pass renames both.
     *
     * <p>The mix is what makes this unrecoverable. If <i>every</i> entry had gone
     * identity the map would be dropped wholesale and the next pass would rebuild
     * the key set from the arcs (AC#9, below); because {@code input} stays
     * non-identity the map survives non-empty, the next pass takes the chained
     * branch, and the lost {@code output} key is never re-derived.
     *
     * <pre>
     *   pass 1  instantiate("inner")   input  &rarr; inner/input        output &rarr; inner/output
     *   pass 2  bindPort into middle   input  &rarr; inner/input        output &rarr; output        &lt;-- IDENTITY
     *   pass 3  instantiate("outer")   input  &rarr; outer/inner/input  output &rarr; outer/output
     *   pass 4  bindPort into host     input  &rarr; outer/inner/input  output &rarr; sink
     * </pre>
     */
    @Test
    void declaredPortReturningToItsOwnName_survivesALaterRename_MOD031_AC8() {
        Place<String> input  = Place.of("input",  String.class);
        Place<String> output = Place.of("output", String.class);

        // The action hardcodes its DECLARED constants — it never discovers places.
        SubnetDef<Void> def = SubnetDef.builder("move")
            .inputPort("input", input)
            .outputPort("output", output)
            .transition(Transition.builder("move")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build())
            .build();

        var inner = def.instantiate("inner");

        // The identity step: the middle level rebinds the inner "output" port to a
        // place ALREADY NAMED "output". Java's Place is a record with structural
        // equality on (name, tokenType), so this is the very same key as the inner
        // declared constant and pass 2 maps output -> output. The "input" port is
        // left unbound, which is what keeps the map non-empty.
        PetriNet middleNet = PetriNet.builder("middle")
            .compose(inner, Map.of("output", output))
            .build();

        var middle = SubnetDef.fromNet(middleNet, Interface.builder()
                .inputPort("input", inner.port("input", String.class))
                .outputPort("output", output)
                .build())
            .instantiate("outer");

        Place<String> sink = Place.of("sink", String.class);
        PetriNet net = PetriNet.builder("host")
            .compose(middle, Map.of("output", sink))
            .build();

        Place<String> hostInput = middle.port("input", String.class);

        assertResolvesOnBothExecutors(net, hostInput, sink, "ok",
            "MOD-031 AC#8: the hardcoded declared 'output' constant must resolve to the host 'sink'");

        // Secondary: pin the correspondence itself, so a regression also names the
        // lost key rather than only the resolution failure it causes.
        Transition composed = findTransition(net, "outer/inner/move");
        assertEquals(Map.of(input, hostInput, output, sink), composed.placeAlias(),
            "MOD-031 AC#8: a key whose actual side round-trips to its declared name at an "
                + "intermediate pass must still be carried forward — the chained pass never "
                + "re-reads the arcs, so dropping it loses the author-original key for good");
    }

    /**
     * MOD-031 AC#9 — the all-identity variant must also pass. Here <i>every</i>
     * declared place round-trips at pass 2, so the correspondence is dropped
     * wholesale; the next pass then rebuilds the key set from the arcs, whose
     * names are still author-original at that point. This is the branch that keeps
     * the wholesale drop legitimate, and it is the one an over-eager "never drop
     * anything" fix would leave untested.
     */
    @Test
    void allIdentityCorrespondence_isDroppedWholesaleAndSelfHeals_MOD031_AC9() {
        Place<String> input  = Place.of("input",  String.class);
        Place<String> output = Place.of("output", String.class);

        SubnetDef<Void> def = SubnetDef.builder("move")
            .inputPort("input", input)
            .outputPort("output", output)
            .transition(Transition.builder("move")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build())
            .build();

        // BOTH ports rebound to places of their own declared names.
        PetriNet middleNet = PetriNet.builder("middle")
            .compose(def.instantiate("inner"), Map.of("input", input, "output", output))
            .build();

        Transition afterIdentityPass = findTransition(middleNet, "inner/move");
        assertTrue(afterIdentityPass.placeAlias().isEmpty(),
            "MOD-031 AC#9: an all-identity correspondence may be dropped as a whole — the next "
                + "pass rebuilds the key set from arcs that are still author-original");

        var outer = SubnetDef.fromNet(middleNet, Interface.builder()
                .inputPort("input", input)
                .outputPort("output", output)
                .build())
            .instantiate("outer");

        Place<String> src  = Place.of("src",  String.class);
        Place<String> sink = Place.of("sink", String.class);
        PetriNet net = PetriNet.builder("host")
            .compose(outer, Map.of("input", src, "output", sink))
            .build();

        assertResolvesOnBothExecutors(net, src, sink, "ok",
            "MOD-031 AC#9: after the wholesale drop the arc walk must re-derive both "
                + "author-original keys, so the action still resolves them");
    }

    // ============================================================
    //  Helpers
    // ============================================================

    /**
     * Runs {@code net} with one token on {@code source} on <b>both</b> executors and
     * asserts the action resolved its declared places and produced on {@code sink}.
     *
     * <p>Both are exercised because {@link PrecompiledNetExecutor} must stay
     * behaviorally identical to the {@link BitmapNetExecutor} reference; they build
     * their declared-place sets by different routes.
     *
     * <p>An {@link ActionFailureHandler} is installed because a failing action is
     * <i>reported</i>, not propagated: without one the declared-place error is
     * swallowed and the only symptom is a silently empty sink — which is exactly the
     * silent token loss this test exists to catch.
     */
    private static void assertResolvesOnBothExecutors(
        PetriNet net,
        Place<String> source,
        Place<String> sink,
        String value,
        String because
    ) {
        Map<Place<?>, List<Token<?>>> initial = Map.of(source, List.of(Token.of(value)));

        var bitmapFailures = new ArrayList<Throwable>();
        try (var exec = BitmapNetExecutor.builder(net, initial)
                .uncaughtActionHandler((t, cause) -> bitmapFailures.add(cause))
                .build()) {
            assertProduced("BitmapNetExecutor", exec.run(), bitmapFailures, sink, value, because);
        }

        var precompiledFailures = new ArrayList<Throwable>();
        try (var exec = PrecompiledNetExecutor.builder(net, initial)
                .uncaughtActionHandler((t, cause) -> precompiledFailures.add(cause))
                .build()) {
            assertProduced("PrecompiledNetExecutor", exec.run(), precompiledFailures, sink, value, because);
        }
    }

    private static void assertProduced(
        String executorName,
        Marking marking,
        List<Throwable> failures,
        Place<String> sink,
        String value,
        String because
    ) {
        assertTrue(failures.isEmpty(),
            executorName + ": " + because + " — instead the action failed its declared-place "
                + "check. It had already consumed its inputs (EXEC-031: no rollback), so the "
                + "tokens are lost. Cause: " + failures);
        assertTrue(marking.hasTokens(sink),
            executorName + ": " + because + ". Marking: " + marking);
        assertEquals(value, marking.peekFirst(sink).value(), executorName + ": " + because);
    }

    private static Transition findTransition(PetriNet net, String name) {
        for (var t : net.transitions()) {
            if (t.name().equals(name)) return t;
        }
        throw new AssertionError("no transition named '" + name + "' in net '" + net.name()
            + "'. Transitions: " + net.transitions());
    }
}
