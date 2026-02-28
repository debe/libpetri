package org.libpetri.examples.parser;

import org.libpetri.core.Token;
import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.compiler.CompiledParserNet;
import org.libpetri.examples.parser.compiler.GrammarNetCompiler;
import org.libpetri.examples.parser.compiler.ParseState;
import org.libpetri.examples.parser.grammar.Grammar;
import org.libpetri.examples.parser.grammar.Java25Grammar;
import org.libpetri.examples.parser.lexer.JavaLexer;
import org.libpetri.examples.parser.lexer.LexToken;
import org.libpetri.runtime.BitmapNetExecutor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Facade that ties together lexer, grammar, compiler, and executor
 * to parse Java 25 source code via a Petri net.
 *
 * <p>Usage:
 * <pre>{@code
 * var parser = PetriNetParser.forJava25();
 * AstNode ast = parser.parse("class Foo {}");
 * String dot = parser.exportDot();
 * }</pre>
 */
public final class PetriNetParser {

    private final CompiledParserNet compiledNet;
    private final Grammar grammar;

    private PetriNetParser(Grammar grammar, CompiledParserNet compiledNet) {
        this.grammar = grammar;
        this.compiledNet = compiledNet;
    }

    /**
     * Create a parser for the full Java 25 grammar.
     * Compiles the grammar into a Petri net (one-time cost).
     */
    public static PetriNetParser forJava25() {
        var grammar = Java25Grammar.create();
        var compiled = GrammarNetCompiler.compile(grammar);
        return new PetriNetParser(grammar, compiled);
    }

    /**
     * Create a parser for a custom grammar.
     */
    public static PetriNetParser forGrammar(Grammar grammar) {
        var compiled = GrammarNetCompiler.compile(grammar);
        return new PetriNetParser(grammar, compiled);
    }

    /**
     * Parse a single source string into an AST.
     */
    public ParseResult parse(String source) {
        var tokens = JavaLexer.tokenize(source);
        return executeNet(tokens);
    }

    /**
     * Parse multiple source strings through the same compiled net.
     * Each source gets its own ParseState token flowing through the net independently.
     */
    public List<ParseResult> parseAll(String... sources) {
        var results = new ArrayList<ParseResult>(sources.length);
        for (var source : sources) {
            results.add(parse(source));
        }
        return results;
    }

    /**
     * Get the compiled parser net for inspection.
     */
    public CompiledParserNet compiledNet() {
        return compiledNet;
    }

    /**
     * Export the parser net structure to DOT format.
     */
    public String exportDot() {
        return org.libpetri.export.DotExporter.export(compiledNet.net());
    }

    /**
     * Get statistics about the compiled net.
     */
    public String statistics() {
        return compiledNet.statistics();
    }

    private ParseResult executeNet(List<LexToken> tokenList) {
        var tokens = tokenList.toArray(LexToken[]::new);
        var initialState = ParseState.initial(tokens);

        var executor = BitmapNetExecutor.create(
            compiledNet.net(),
            Map.of(compiledNet.startPlace(), List.of(new Token<>(initialState, ParseState.EPOCH)))
        );

        var marking = executor.run();

        // Check end place for result
        var endTokens = marking.peekTokens(compiledNet.endPlace());
        if (!endTokens.isEmpty()) {
            var finalState = (ParseState) endTokens.iterator().next().value();
            var ast = finalState.astStack() != null ? finalState.peekAst() : null;
            return new ParseResult(ast, true, null, finalState);
        }

        // Check error place
        var errorTokens = marking.peekTokens(compiledNet.errorPlace());
        if (!errorTokens.isEmpty()) {
            var errorState = (ParseState) errorTokens.iterator().next().value();
            var current = errorState.current();
            var msg = "Parse error at " + current.line() + ":" + current.column() +
                      " — unexpected " + current.type() + "(" + current.value() + ")";
            return new ParseResult(null, false, msg, errorState);
        }

        return new ParseResult(null, false, "Parse stalled — no tokens at end or error places", null);
    }

    /**
     * Result of parsing a source string.
     */
    public record ParseResult(
        AstNode ast,
        boolean success,
        String errorMessage,
        ParseState finalState
    ) {}
}
