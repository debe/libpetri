package org.libpetri.analysis;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [IO-007] regression tests: the state class graph must consume tokens exactly as the
 * executor does.
 *
 * <p>{@code In.All} and {@code In.AtLeast} drain their input place at runtime
 * ({@code BitmapNetExecutor} consumes {@code marking.tokenCount(place)} for both).
 * The analysis previously consumed a <em>minimum</em> instead (1 for {@code All},
 * {@code minimum()} for {@code AtLeast}), leaving residual tokens the real net never
 * holds. Those phantom tokens keep inhibitor arcs unsatisfied and suppress successors,
 * so a reachable marking gets reported unreachable — a false {@code Verdict.Proven}
 * on the {@code NuScgVerifier} safety path.
 */
class StateClassGraphConsumptionTest {

    @Test
    @DisplayName("In.all drains its place, so an inhibitor-gated successor is reachable")
    void allInputDrainsPlaceSoInhibitedSuccessorIsReachable() {
        var p = Place.of("p", Integer.class);
        var g = Place.of("g", Integer.class);
        var out = Place.of("out", Integer.class);
        var bad = Place.of("bad", Integer.class);

        // t consumes ALL of p plus the single guard token in g, so it fires exactly once
        // and p is either drained completely or untouched — never left with a residue.
        var t = Transition.builder("t")
            .inputs(In.all(p), In.one(g))
            .outputs(Out.place(out))
            .action(TransitionAction.fork())
            .build();

        // u is gated on p being empty. It only becomes enabled once t has drained p.
        var u = Transition.builder("u")
            .inputs(In.one(out))
            .inhibitors(p)
            .outputs(Out.place(bad))
            .action(TransitionAction.fork())
            .build();

        var net = PetriNet.builder("AllDrains").transitions(t, u).build();

        var scg = StateClassGraph.build(
            net,
            MarkingState.builder().tokens(p, 3).tokens(g, 1).build(),
            1_000
        );

        boolean badReachable = scg.stateClasses().stream()
            .anyMatch(sc -> sc.marking().tokens(bad) > 0);

        assertTrue(badReachable,
            "`bad` is reachable in the real net: t consumes all 3 tokens from p, which "
                + "satisfies u's inhibitor. Consuming a minimum leaves a residue in p that "
                + "blocks u forever and makes the analysis under-approximate reachability. "
                + "Markings found: " + markingsOf(scg, p, g, out, bad));
    }

    @Test
    @DisplayName("In.atLeast drains its place — p is only ever 5 or 0, never a residue")
    void atLeastInputDrainsPlaceLeavingNoResidue() {
        var p = Place.of("p", Integer.class);
        var out = Place.of("out", Integer.class);

        // atLeast(2, p) enables at 2+ tokens but consumes every token present.
        var t = Transition.builder("t")
            .inputs(In.atLeast(2, p))
            .outputs(Out.place(out))
            .action(TransitionAction.fork())
            .build();

        var net = PetriNet.builder("AtLeastDrains").transitions(t).build();

        var scg = StateClassGraph.build(
            net,
            MarkingState.builder().tokens(p, 5).build(),
            1_000
        );

        var counts = scg.stateClasses().stream()
            .map(sc -> sc.marking().tokens(p))
            .collect(Collectors.toSet());

        assertEquals(Set.of(5, 0), counts,
            "p must be 5 (initial) or 0 (drained by the single firing). Any other value is a "
                + "residue the executor never produces — consuming `minimum` instead of all "
                + "would leave 3. Observed p counts: " + counts);
    }

    private static String markingsOf(StateClassGraph scg, Place<?>... places) {
        return scg.stateClasses().stream()
            .map(sc -> {
                var sb = new StringBuilder("{");
                for (var pl : places) {
                    sb.append(pl.name()).append('=').append(sc.marking().tokens(pl)).append(' ');
                }
                return sb.append('}').toString();
            })
            .collect(Collectors.joining(", "));
    }
}
