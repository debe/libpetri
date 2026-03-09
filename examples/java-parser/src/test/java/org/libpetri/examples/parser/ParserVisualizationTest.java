package org.libpetri.examples.parser;

import org.junit.jupiter.api.Test;
import org.libpetri.examples.parser.compiler.GrammarNetCompiler;
import org.libpetri.examples.parser.grammar.Grammar;
import org.libpetri.examples.parser.grammar.Production;
import org.libpetri.export.DotExporter;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.examples.parser.grammar.GrammarElement.*;

/**
 * Tests DOT export and verifies compiled net structure.
 */
class ParserVisualizationTest {

    @Test
    void exportsTinyGrammarToDot() {
        var grammar = Grammar.of("S",
            new Production("S", choice(terminal("a"), terminal("b")))
        );
        var compiled = GrammarNetCompiler.compile(grammar);
        var dot = DotExporter.export(compiled.net());

        assertNotNull(dot);
        assertFalse(dot.isEmpty());
        assertTrue(dot.contains("digraph"), "Should be a digraph");
        assertTrue(dot.contains("JavaParser"), "Should contain net name");
        System.out.println("Tiny grammar DOT (" + dot.length() + " chars):\n" + dot.substring(0, Math.min(dot.length(), 500)));
    }

    @Test
    void exportsSimpleGrammarWithNonTerminals() {
        var grammar = Grammar.of("S",
            new Production("S", seq(terminal("class"), nonTerminal("Name"), terminal("{"), terminal("}"))),
            new Production("Name", tokenMatch(org.libpetri.examples.parser.lexer.TokenType.IDENTIFIER))
        );
        var compiled = GrammarNetCompiler.compile(grammar);
        var dot = DotExporter.export(compiled.net());

        assertNotNull(dot);
        assertTrue(dot.length() > 100, "Should have substantial content");
        System.out.println("Simple grammar: places=" + compiled.placeCount() +
                         ", transitions=" + compiled.transitionCount());
    }

    @Test
    void exportsJava25GrammarToDot() {
        var parser = PetriNetParser.forJava25();
        var compiled = parser.compiledNet();

        System.out.println("=== Java 25 Parser Net Statistics ===");
        System.out.println("  Productions: " + compiled.productionCount());
        System.out.println("  Places: " + compiled.placeCount());
        System.out.println("  Transitions: " + compiled.transitionCount());
        System.out.println("  Net name: " + compiled.net().name());

        var dot = parser.exportDot();
        assertNotNull(dot);
        assertTrue(dot.length() > 1000, "Full grammar DOT should be substantial: " + dot.length());

        // Verify net has expected components
        assertTrue(compiled.placeCount() >= 100, "Expected >= 100 places");
        assertTrue(compiled.transitionCount() >= 100, "Expected >= 100 transitions");
        assertTrue(compiled.productionCount() >= 100, "Expected >= 100 productions");

        System.out.println("  DOT output: " + dot.length() + " chars");
    }

    @Test
    void productionStartEndPlacesExist() {
        var parser = PetriNetParser.forJava25();
        var compiled = parser.compiledNet();

        // Verify some key productions have start/end places
        assertNotNull(compiled.productionStartPlaces().get("CompilationUnit"));
        assertNotNull(compiled.productionEndPlaces().get("CompilationUnit"));
        assertNotNull(compiled.productionStartPlaces().get("ClassDeclaration"));
        assertNotNull(compiled.productionStartPlaces().get("Expression"));
        assertNotNull(compiled.productionStartPlaces().get("Statement"));
    }

    @Test
    void generateFullGrammarSvg() throws IOException, InterruptedException {
        var parser = PetriNetParser.forJava25();
        var dot = parser.exportDot();

        var svg = renderSvg("sfdp", dot, "-Goverlap=prism");
        if (svg == null) {
            System.out.println("sfdp not available, skipping SVG generation");
            return;
        }

        var docsDir = Path.of("").toAbsolutePath().resolve("../../docs").normalize();
        Files.createDirectories(docsDir);
        Files.writeString(docsDir.resolve("example-java-parser.svg"), svg);
        System.out.println("Wrote full grammar SVG: " + svg.length() + " chars");
    }

    @Test
    void generateGrammarFragmentSvg() throws IOException, InterruptedException {
        // Small 3-production grammar to show hierarchical structure
        var grammar = Grammar.of("S",
            new Production("S", seq(terminal("class"), nonTerminal("Name"), terminal("{"),
                optional(nonTerminal("Member")), terminal("}"))),
            new Production("Name", tokenMatch(org.libpetri.examples.parser.lexer.TokenType.IDENTIFIER)),
            new Production("Member", seq(nonTerminal("Name"), terminal("("), terminal(")"),
                terminal("{"), terminal("}")))
        );
        var compiled = GrammarNetCompiler.compile(grammar);
        var dot = DotExporter.export(compiled.net());

        System.out.println("Fragment: places=" + compiled.placeCount() +
                         ", transitions=" + compiled.transitionCount());

        var svg = renderSvg("dot", dot);
        if (svg == null) {
            System.out.println("dot not available, skipping SVG generation");
            return;
        }

        var docsDir = Path.of("").toAbsolutePath().resolve("../../docs").normalize();
        Files.createDirectories(docsDir);
        Files.writeString(docsDir.resolve("example-parser-grammar-fragment.svg"), svg);
        System.out.println("Wrote fragment SVG: " + svg.length() + " chars");
    }

    private String renderSvg(String engine, String dot, String... extraArgs) throws IOException, InterruptedException {
        var cmd = new java.util.ArrayList<>(java.util.List.of(engine, "-Tsvg"));
        cmd.addAll(java.util.List.of(extraArgs));
        var process = new ProcessBuilder(cmd)
                .redirectErrorStream(true)
                .start();
        process.getOutputStream().write(dot.getBytes(StandardCharsets.UTF_8));
        process.getOutputStream().close();

        var svg = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);

        if (!process.waitFor(10, TimeUnit.MINUTES)) {
            process.destroyForcibly();
            System.err.println(engine + " timed out");
            return null;
        }

        if (process.exitValue() != 0) {
            System.err.println(engine + " exited with code " + process.exitValue() + ": " + svg);
            return null;
        }

        // Strip XML prolog/DOCTYPE
        int svgStart = svg.indexOf("<svg");
        if (svgStart > 0) svg = svg.substring(svgStart);

        // Strip explicit width/height so SVG scales via viewBox
        svg = svg.replaceFirst("\\s+width=\"[^\"]*\"", "");
        svg = svg.replaceFirst("\\s+height=\"[^\"]*\"", "");

        return svg;
    }
}
