package org.libpetri.examples.parser;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Parses all of the parser's own source files through the Petri net parser.
 */
class SelfParseTest {

    static PetriNetParser parser;

    @BeforeAll
    static void compileGrammar() {
        parser = PetriNetParser.forJava25();
    }

    static Stream<Path> sourceFiles() throws IOException {
        var root = Path.of("src/main/java/org/libpetri/examples/parser");
        return Files.walk(root)
            .filter(p -> p.toString().endsWith(".java"))
            .sorted();
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("sourceFiles")
    void selfParse(Path sourceFile) throws IOException {
        var source = Files.readString(sourceFile);
        var result = parser.parse(source);
        assertTrue(result.success(),
            sourceFile.getFileName() + ": " +
            (result.errorMessage() != null ? result.errorMessage() : "Unknown error"));
    }
}
