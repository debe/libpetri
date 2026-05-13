package org.libpetri.export;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

/**
 * Cross-language DOT byte-parity fixture: builds a net where a transition
 * both outputs to a place and resets the same place — the renderer must
 * collapse the two arcs into a single combined edge per EXP-013.
 *
 * <p>Consumed by {@code scripts/cross-lang-dot-parity.sh}.
 *
 * <p>Mirrors {@code typescript/scripts/cross-lang-reset-output-dot.ts} and
 * {@code rust/libpetri/tests/cross_lang_reset_output_dot.rs}.
 */
public class CrossLangResetOutputDot {

    /** Default output path, relative to the {@code java/} module root. */
    public static final String DEFAULT_OUT = "target/cross-lang-reset-output-dot/java.dot";

    @Test
    void emitsResetOutputCollapseDot() throws IOException {
        Place<String> cache = Place.of("cache", String.class);

        // refresh: outputs to cache AND resets cache -> single combined edge.
        Transition refresh = Transition.builder("refresh")
            .outputs(Out.place(cache))
            .reset(cache)
            .build();

        var net = PetriNet.builder("reset_collapse")
            .place(cache)
            .transition(refresh)
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
