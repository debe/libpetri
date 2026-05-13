package org.libpetri.export;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

/**
 * Cross-language DOT byte-parity fixture: builds a net that exercises both
 * XOR-junction and AND-junction synthesis (per EXP-012) in a single
 * transition's output tree. The transition fires from one input place to a
 * combined output spec {@code AND(XOR(a, b), c)} — yielding one AND junction
 * and one nested XOR junction.
 *
 * <p>Consumed by {@code scripts/cross-lang-dot-parity.sh}.
 *
 * <p>Mirrors {@code typescript/scripts/cross-lang-junctions-dot.ts} and
 * {@code rust/libpetri/tests/cross_lang_junctions_dot.rs}.
 */
public class CrossLangJunctionsDot {

    /** Default output path, relative to the {@code java/} module root. */
    public static final String DEFAULT_OUT = "target/cross-lang-junctions-dot/java.dot";

    @Test
    void emitsJunctionsComplexDot() throws IOException {
        // Net layout — every junction-target place is "pre-seeded" into the
        // mapper's place-analysis map by an earlier source transition so the
        // junction-emitting transition's unordered Out.allPlaces() traversal
        // does NOT determine the place declaration order in the final DOT.
        // This works around an arc-iteration-order divergence in Java's
        // Out.allPlaces() (HashSet-backed, JVM-randomised).
        Place<String> srcA = Place.of("srcA", String.class);
        Place<String> srcB = Place.of("srcB", String.class);
        Place<String> srcC = Place.of("srcC", String.class);
        Place<String> srcD = Place.of("srcD", String.class);
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);
        Place<String> c = Place.of("c", String.class);
        Place<String> d = Place.of("d", String.class);
        Place<String> srcXor = Place.of("srcXor", String.class);
        Place<String> srcAnd = Place.of("srcAnd", String.class);

        // Seed transitions: register each leaf place into the analysis map
        // in pre-order before any junction-bearing transition is examined.
        Transition seedA = Transition.builder("seedA")
            .inputs(In.one(srcA)).outputs(Out.place(a)).build();
        Transition seedB = Transition.builder("seedB")
            .inputs(In.one(srcB)).outputs(Out.place(b)).build();
        Transition seedC = Transition.builder("seedC")
            .inputs(In.one(srcC)).outputs(Out.place(c)).build();
        Transition seedD = Transition.builder("seedD")
            .inputs(In.one(srcD)).outputs(Out.place(d)).build();

        // The junction transitions — these are what actually exercise EXP-012.
        Transition tXor = Transition.builder("routeXor")
            .inputs(In.one(srcXor))
            .outputs(Out.xor(a, b))
            .build();

        Transition tAnd = Transition.builder("routeAnd")
            .inputs(In.one(srcAnd))
            .outputs(Out.and(c, d))
            .build();

        var net = PetriNet.builder("junctions")
            .transition(seedA)
            .transition(seedB)
            .transition(seedC)
            .transition(seedD)
            .transition(tXor)
            .transition(tAnd)
            .build();

        String dot = DotExporter.export(net);

        String outPath = System.getProperty("libpetri.crossLang.outFile", DEFAULT_OUT);
        Path target = Path.of(outPath);
        if (target.getParent() != null) {
            Files.createDirectories(target.getParent());
        }
        Files.writeString(target, dot);
    }
}
