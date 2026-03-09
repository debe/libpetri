package org.libpetri.examples.parser;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Stress test: parse a synthetic ~100K-line Java source file.
 */
class SyntheticLargeFileTest {

    static PetriNetParser parser;

    @BeforeAll
    static void compileGrammar() {
        parser = PetriNetParser.forJava25();
    }

    @Test
    void parseLargeGeneratedFile() {
        var source = SyntheticJavaSource.generateForStressTest();
        long lines = source.lines().count();
        System.out.println("Generated source: " + lines + " lines, " + source.length() + " chars");

        long start = System.nanoTime();
        var result = parser.parse(source);
        long elapsed = System.nanoTime() - start;

        double seconds = elapsed / 1_000_000_000.0;
        double linesPerSec = lines / seconds;
        System.out.printf("Parsed in %.2f s (%.0f lines/sec)%n", seconds, linesPerSec);

        assertTrue(result.success(),
            result.errorMessage() != null ? result.errorMessage() : "Unknown error");
    }
}
