package org.libpetri.examples.parser;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Parses the entire libpetri core library (~85 files, ~17K lines)
 * through the Petri net parser. All files parse successfully.
 */
class LibpetriSelfParseTest {

    static PetriNetParser parser;

    @BeforeAll
    static void compileGrammar() {
        parser = PetriNetParser.forJava25();
    }

    static Stream<Path> libpetriSourceFiles() throws IOException {
        var root = Path.of("../../java/src/main/java/org/libpetri");
        return Files.walk(root)
            .filter(p -> p.toString().endsWith(".java"))
            .filter(p -> !p.toString().endsWith("package-info.java"))
            .sorted();
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("libpetriSourceFiles")
    void parseLibpetriSource(Path sourceFile) throws IOException {
        var fileName = sourceFile.getFileName().toString();
        var source = Files.readString(sourceFile);
        var result = parser.parse(source);

        assertTrue(result.success(),
            fileName + ": " +
            (result.errorMessage() != null ? result.errorMessage() : "Unknown error"));
    }

    @Test
    void summaryStatistics() throws IOException {
        var files = libpetriSourceFiles().toList();
        long totalLines = 0;
        long totalChars = 0;
        int successes = 0;
        int failures = 0;
        long totalNanos = 0;

        for (var file : files) {
            var source = Files.readString(file);
            totalChars += source.length();
            totalLines += source.lines().count();
            long start = System.nanoTime();
            var result = parser.parse(source);
            totalNanos += System.nanoTime() - start;
            if (result.success()) {
                successes++;
            } else {
                failures++;
                System.err.println("FAIL: " + file.getFileName() + ": " + result.errorMessage());
            }
        }

        long elapsedMs = totalNanos / 1_000_000;
        System.out.printf("=== libpetri Self-Parse Summary ===%n");
        System.out.printf("  Files: %d (%d passed, %d failed)%n", files.size(), successes, failures);
        System.out.printf("  Total: %,d lines, %,d chars%n", totalLines, totalChars);
        System.out.printf("  Parsed in %,d ms (%,d lines/sec)%n",
            elapsedMs, elapsedMs > 0 ? totalLines * 1000 / elapsedMs : 0);

        assertTrue(successes == files.size(),
            "Expected all " + files.size() + " files to parse, but " + failures + " failed");
    }
}
