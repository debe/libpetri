package org.libpetri.export;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.fixtures.SubnetFixtures;

/**
 * Cross-language DOT byte-parity fixture: builds the canonical
 * producer / bounded-buffer / consumer pipeline composed via
 * {@link PetriNet.Builder#compose} and emits the resulting DOT to the path
 * named by the {@code libpetri.crossLang.outFile} system property (or to
 * {@code target/cross-lang-pipeline-dot/java.dot} by default).
 *
 * <p>The output is consumed by {@code scripts/cross-lang-dot-parity.sh},
 * which builds the same pipeline in TypeScript and Rust and asserts the
 * three DOT outputs are byte-identical.
 *
 * <p>Implemented as a JUnit test (rather than a {@code main} class) so
 * regular {@code ./mvnw test} runs verify the pipeline at least executes
 * end-to-end. The parity script invokes this single test with
 * {@code -Dtest=CrossLangPipelineDot}.
 */
public class CrossLangPipelineDot {

    /** Default output path, relative to the {@code java/} module root. */
    public static final String DEFAULT_OUT = "target/cross-lang-pipeline-dot/java.dot";

    @Test
    void emitsCanonicalPipelineDot() throws IOException {
        var producerDef = SubnetFixtures.producer();
        var bufferDef = SubnetFixtures.boundedBuffer(2);
        var consumerDef = SubnetFixtures.consumer();

        var prod = producerDef.instantiate("prod");
        var buf = bufferDef.instantiate("buf");
        var cons = consumerDef.instantiate("cons");

        Place<String> producerToBuffer = Place.of("producerToBuffer", String.class);
        Place<String> bufferToConsumer = Place.of("bufferToConsumer", String.class);

        var net = PetriNet.builder("pipeline")
            .compose(prod, b -> b.bindPort("output", producerToBuffer))
            .compose(buf, b -> b.bindPort("put", producerToBuffer)
                                .bindPort("get", bufferToConsumer))
            .compose(cons, b -> b.bindPort("input", bufferToConsumer))
            .build();

        String dot = DotExporter.export(net);

        String outPath = System.getProperty("libpetri.crossLang.outFile", DEFAULT_OUT);
        Path target = Path.of(outPath);
        if (target.getParent() != null) {
            Files.createDirectories(target.getParent());
        }
        Files.writeString(target, dot);
        // Echo to stdout so the parity script can also pipe-capture if it
        // prefers (when -Dlibpetri.crossLang.echo=true is set).
        if (Boolean.getBoolean("libpetri.crossLang.echo")) {
            System.out.print(dot);
        }
    }
}
