package org.libpetri.examples.parser;

import org.junit.jupiter.api.Test;
import org.libpetri.examples.parser.compiler.GrammarNetCompiler;
import org.libpetri.examples.parser.grammar.Grammar;
import org.libpetri.examples.parser.grammar.Production;
import org.libpetri.export.DotExporter;

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
}
