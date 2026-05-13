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
 * Cross-language DOT byte-parity fixture: builds a net with at least one
 * Read arc and one Inhibitor arc on the same transition to verify the
 * renderer styles each distinctly and produces byte-identical DOT across
 * languages.
 *
 * <p>Consumed by {@code scripts/cross-lang-dot-parity.sh}.
 *
 * <p>Mirrors {@code typescript/scripts/cross-lang-inhibitor-read-dot.ts} and
 * {@code rust/libpetri/tests/cross_lang_inhibitor_read_dot.rs}.
 */
public class CrossLangInhibitorReadDot {

    /** Default output path, relative to the {@code java/} module root. */
    public static final String DEFAULT_OUT = "target/cross-lang-inhibitor-read-dot/java.dot";

    @Test
    void emitsInhibitorReadStylingDot() throws IOException {
        Place<String> req = Place.of("req", String.class);
        Place<String> done = Place.of("done", String.class);
        Place<String> lock = Place.of("lock", String.class);
        Place<String> paused = Place.of("paused", String.class);

        Transition process = Transition.builder("process")
            .inputs(In.one(req))
            .read(lock)
            .inhibitor(paused)
            .outputs(Out.place(done))
            .build();

        // Place ordering matches the renderer's place-analysis traversal
        // (inputs -> outputs -> inhibitors -> reads), required for byte-parity
        // because some language backends ignore the builder's place list and
        // re-derive ordering from arc iteration.
        var net = PetriNet.builder("inh_read")
            .place(req)
            .place(done)
            .place(paused)
            .place(lock)
            .transition(process)
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
