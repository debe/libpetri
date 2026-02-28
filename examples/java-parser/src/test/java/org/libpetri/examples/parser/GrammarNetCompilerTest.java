package org.libpetri.examples.parser;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Token;
import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.compiler.CompiledParserNet;
import org.libpetri.examples.parser.compiler.GrammarNetCompiler;
import org.libpetri.examples.parser.compiler.ParseState;
import org.libpetri.examples.parser.grammar.Grammar;
import org.libpetri.examples.parser.grammar.GrammarElement;
import org.libpetri.examples.parser.grammar.Production;
import org.libpetri.examples.parser.lexer.JavaLexer;
import org.libpetri.examples.parser.lexer.LexToken;
import org.libpetri.examples.parser.lexer.TokenType;
import org.libpetri.runtime.BitmapNetExecutor;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.examples.parser.grammar.GrammarElement.*;

/**
 * Tests each compilation pattern in isolation with tiny grammars.
 */
class GrammarNetCompilerTest {

    @Test
    void compilesTerminalPattern() {
        // Grammar: S → 'class'
        var grammar = Grammar.of("S", new Production("S", terminal("class")));
        var result = runParse(grammar, "class");
        assertTrue(result.success(), "Should parse 'class' successfully");
    }

    @Test
    void terminalPatternRejectsWrongToken() {
        // Grammar: S → 'class'
        var grammar = Grammar.of("S", new Production("S", terminal("class")));
        var result = runParse(grammar, "interface");
        assertFalse(result.success(), "Should reject 'interface' when expecting 'class'");
    }

    @Test
    void compilesTokenMatchPattern() {
        // Grammar: S → IDENTIFIER
        var grammar = Grammar.of("S", new Production("S", tokenMatch(TokenType.IDENTIFIER)));
        var result = runParse(grammar, "foo");
        assertTrue(result.success(), "Should parse identifier");
    }

    @Test
    void compilesSequencePattern() {
        // Grammar: S → 'class' IDENTIFIER
        var grammar = Grammar.of("S",
            new Production("S", seq(terminal("class"), tokenMatch(TokenType.IDENTIFIER)))
        );
        var result = runParse(grammar, "class Foo");
        assertTrue(result.success(), "Should parse 'class Foo'");
    }

    @Test
    void compilesChoicePattern() {
        // Grammar: S → 'class' | 'interface'
        var grammar = Grammar.of("S",
            new Production("S", choice(terminal("class"), terminal("interface")))
        );

        assertTrue(runParse(grammar, "class").success(), "Should parse 'class'");
        assertTrue(runParse(grammar, "interface").success(), "Should parse 'interface'");
    }

    @Test
    void compilesRepetitionPattern() {
        // Grammar: S → 'a' {',' 'a'}
        // Note: this is a simplification — using terminal 'a' as keyword
        var grammar = Grammar.of("S",
            new Production("S", seq(
                tokenMatch(TokenType.IDENTIFIER),
                repeat(seq(terminal(","), tokenMatch(TokenType.IDENTIFIER)))
            ))
        );

        assertTrue(runParse(grammar, "a").success(), "Should parse single element");
        assertTrue(runParse(grammar, "a , b").success(), "Should parse two elements");
        assertTrue(runParse(grammar, "a , b , c").success(), "Should parse three elements");
    }

    @Test
    void compilesOptionalPattern() {
        // Grammar: S → 'class' [IDENTIFIER]
        var grammar = Grammar.of("S",
            new Production("S", seq(
                terminal("class"),
                optional(tokenMatch(TokenType.IDENTIFIER))
            ))
        );

        assertTrue(runParse(grammar, "class Foo").success(), "Should parse with optional present");
        assertTrue(runParse(grammar, "class").success(), "Should parse without optional");
    }

    @Test
    void compilesNonTerminalCallReturn() {
        // Grammar: S → A
        //          A → 'class'
        var grammar = Grammar.of("S",
            new Production("S", nonTerminal("A")),
            new Production("A", terminal("class"))
        );

        assertTrue(runParse(grammar, "class").success(), "Should parse via non-terminal call");
    }

    @Test
    void compilesMultipleNonTerminalCallSites() {
        // Grammar: S → A ';' A
        //          A → IDENTIFIER
        var grammar = Grammar.of("S",
            new Production("S", seq(
                nonTerminal("A"), terminal(";"), nonTerminal("A")
            )),
            new Production("A", tokenMatch(TokenType.IDENTIFIER))
        );

        assertTrue(runParse(grammar, "foo ; bar").success(),
            "Should parse with multiple call sites to same production");
    }

    @Test
    void compilesNestedNonTerminals() {
        // Grammar: S → A
        //          A → B
        //          B → IDENTIFIER
        var grammar = Grammar.of("S",
            new Production("S", nonTerminal("A")),
            new Production("A", nonTerminal("B")),
            new Production("B", tokenMatch(TokenType.IDENTIFIER))
        );

        assertTrue(runParse(grammar, "foo").success(), "Should parse through nested non-terminals");
    }

    @Test
    void compilesChoiceWithDifferentTokenTypes() {
        // Grammar: S → INT_LITERAL | STRING_LITERAL | IDENTIFIER
        var grammar = Grammar.of("S",
            new Production("S", choice(
                tokenMatch(TokenType.INT_LITERAL),
                tokenMatch(TokenType.STRING_LITERAL),
                tokenMatch(TokenType.IDENTIFIER)
            ))
        );

        assertTrue(runParse(grammar, "42").success(), "Should parse int literal");
        assertTrue(runParse(grammar, "\"hello\"").success(), "Should parse string literal");
        assertTrue(runParse(grammar, "foo").success(), "Should parse identifier");
    }

    @Test
    void netHasExpectedStructure() {
        // Grammar: S → 'a' | 'b'
        var grammar = Grammar.of("S",
            new Production("S", choice(terminal("a"), terminal("b")))
        );
        var compiled = GrammarNetCompiler.compile(grammar);

        assertTrue(compiled.placeCount() > 0, "Should have places");
        assertTrue(compiled.transitionCount() > 0, "Should have transitions");
        assertEquals(1, compiled.productionCount(), "Should have 1 production");
        assertNotNull(compiled.startPlace(), "Should have start place");
        assertNotNull(compiled.endPlace(), "Should have end place");
        assertNotNull(compiled.errorPlace(), "Should have error place");
    }

    @Test
    void compilesComplexGrammar() {
        // Grammar mimicking simple class declaration:
        // S → 'class' IDENTIFIER '{' {Member} '}'
        // Member → Type IDENTIFIER ';'
        // Type → 'int' | 'double'
        var grammar = Grammar.of("S",
            new Production("S", seq(
                terminal("class"), tokenMatch(TokenType.IDENTIFIER),
                terminal("{"),
                repeat(nonTerminal("Member")),
                terminal("}")
            )),
            new Production("Member", seq(
                nonTerminal("Type"), tokenMatch(TokenType.IDENTIFIER), terminal(";")
            )),
            new Production("Type", choice(terminal("int"), terminal("double")))
        );

        var compiled = GrammarNetCompiler.compile(grammar);
        assertTrue(compiled.placeCount() > 10, "Complex grammar should have many places: " + compiled.placeCount());
        assertTrue(compiled.transitionCount() > 10, "Complex grammar should have many transitions: " + compiled.transitionCount());

        // Parse a simple class
        assertTrue(runParse(grammar, "class Foo { }").success(), "Should parse empty class");
        assertTrue(runParse(grammar, "class Foo { int x ; }").success(), "Should parse class with field");
        assertTrue(runParse(grammar, "class Foo { int x ; double y ; }").success(), "Should parse class with two fields");
    }

    @Test
    void leftRecursionElimination() {
        // Grammar with left recursion: Expr → Expr '+' Term | Term
        // Should be rewritten to: Expr → Term {'+' Term}
        var grammar = Grammar.of("Expr",
            new Production("Expr", choice(
                seq(nonTerminal("Expr"), terminal("+"), nonTerminal("Term")),
                nonTerminal("Term")
            )),
            new Production("Term", tokenMatch(TokenType.IDENTIFIER))
        );

        var eliminated = grammar.eliminateLeftRecursion();
        // The eliminated grammar should compile without stack overflow
        var compiled = GrammarNetCompiler.compile(eliminated);
        assertNotNull(compiled);
    }

    @Test
    void grammarFirstSetComputation() {
        var grammar = Grammar.of("S",
            new Production("S", choice(terminal("class"), terminal("interface"))),
            new Production("A", nonTerminal("S"))
        );

        var first = grammar.firstSet(nonTerminal("S"));
        assertTrue(first.contains("T:class"));
        assertTrue(first.contains("T:interface"));

        // FIRST(A) should include FIRST(S) through non-terminal
        var firstA = grammar.firstSet(nonTerminal("A"));
        assertTrue(firstA.contains("T:class"));
        assertTrue(firstA.contains("T:interface"));
    }

    @Test
    void grammarFirstPredicate() {
        var grammar = Grammar.of("S",
            new Production("S", choice(
                terminal("class"),
                tokenMatch(TokenType.IDENTIFIER)
            ))
        );

        var pred = grammar.firstPredicate("S");
        assertTrue(pred.test(new LexToken(TokenType.KEYWORD, "class", 1, 1)));
        assertTrue(pred.test(new LexToken(TokenType.IDENTIFIER, "foo", 1, 1)));
        assertFalse(pred.test(new LexToken(TokenType.INT_LITERAL, "42", 1, 1)));
    }

    // ==================== Helpers ====================

    private PetriNetParser.ParseResult runParse(Grammar grammar, String source) {
        var parser = PetriNetParser.forGrammar(grammar);
        return parser.parse(source);
    }
}
