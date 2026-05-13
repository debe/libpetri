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
 * Cross-language DOT byte-parity fixture: builds a plain non-composed
 * {@link PetriNet} (no subnet composition, no clusters in the rendered DOT)
 * and emits the resulting DOT to the path named by the
 * {@code libpetri.crossLang.outFile} system property (or to
 * {@code target/cross-lang-flat-dot/java.dot} by default).
 *
 * <p>Consumed by {@code scripts/cross-lang-dot-parity.sh} together with its
 * TypeScript and Rust siblings to assert the renderer produces identical DOT
 * across languages even when the input contains no composition metadata.
 *
 * <p>Mirrors {@code typescript/scripts/cross-lang-flat-dot.ts} and
 * {@code rust/libpetri/tests/cross_lang_flat_dot.rs}.
 */
public class CrossLangFlatDot {

    /** Default output path, relative to the {@code java/} module root. */
    public static final String DEFAULT_OUT = "target/cross-lang-flat-dot/java.dot";

    @Test
    void emitsFlatNonComposedDot() throws IOException {
        Place<String> p1 = Place.of("p1", String.class);
        Place<String> p2 = Place.of("p2", String.class);

        Transition t1 = Transition.builder("t1")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();

        var net = PetriNet.builder("flat")
            .place(p1)
            .place(p2)
            .transition(t1)
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
