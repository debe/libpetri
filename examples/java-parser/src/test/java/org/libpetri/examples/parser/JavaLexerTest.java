package org.libpetri.examples.parser;

import org.junit.jupiter.api.Test;
import org.libpetri.examples.parser.lexer.JavaLexer;
import org.libpetri.examples.parser.lexer.LexToken;
import org.libpetri.examples.parser.lexer.TokenType;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class JavaLexerTest {

    @Test
    void tokenizesKeywords() {
        var tokens = JavaLexer.tokenize("class interface enum record sealed permits");
        assertTokenValues(tokens, "class", "interface", "enum", "record", "sealed", "permits", "");
        assertEquals(TokenType.KEYWORD, tokens.get(0).type());
        assertEquals(TokenType.KEYWORD, tokens.get(3).type()); // record
        assertEquals(TokenType.KEYWORD, tokens.get(4).type()); // sealed
    }

    @Test
    void tokenizesIdentifiers() {
        var tokens = JavaLexer.tokenize("foo bar_123 MyClass");
        assertTokenValues(tokens, "foo", "bar_123", "MyClass", "");
        assertEquals(TokenType.IDENTIFIER, tokens.get(0).type());
        assertEquals(TokenType.IDENTIFIER, tokens.get(1).type());
    }

    @Test
    void tokenizesNonSealed() {
        var tokens = JavaLexer.tokenize("non-sealed class Foo");
        assertTokenValues(tokens, "non-sealed", "class", "Foo", "");
        assertEquals(TokenType.KEYWORD, tokens.get(0).type());
    }

    @Test
    void tokenizesIntLiterals() {
        var tokens = JavaLexer.tokenize("42 0xFF 0b1010 1_000_000");
        assertEquals(TokenType.INT_LITERAL, tokens.get(0).type());
        assertEquals("42", tokens.get(0).value());
        assertEquals(TokenType.INT_LITERAL, tokens.get(1).type());
        assertEquals("0xFF", tokens.get(1).value());
        assertEquals(TokenType.INT_LITERAL, tokens.get(2).type());
        assertEquals("0b1010", tokens.get(2).value());
        assertEquals(TokenType.INT_LITERAL, tokens.get(3).type());
    }

    @Test
    void tokenizesLongLiterals() {
        var tokens = JavaLexer.tokenize("42L 0xFFL");
        assertEquals(TokenType.LONG_LITERAL, tokens.get(0).type());
        assertEquals(TokenType.LONG_LITERAL, tokens.get(1).type());
    }

    @Test
    void tokenizesFloatLiterals() {
        var tokens = JavaLexer.tokenize("3.14f 1.0F .5f");
        assertEquals(TokenType.FLOAT_LITERAL, tokens.get(0).type());
        assertEquals(TokenType.FLOAT_LITERAL, tokens.get(1).type());
        assertEquals(TokenType.FLOAT_LITERAL, tokens.get(2).type());
    }

    @Test
    void tokenizesDoubleLiterals() {
        var tokens = JavaLexer.tokenize("3.14 1.0d 1e10 2.5E-3");
        assertEquals(TokenType.DOUBLE_LITERAL, tokens.get(0).type());
        assertEquals(TokenType.DOUBLE_LITERAL, tokens.get(1).type());
        assertEquals(TokenType.DOUBLE_LITERAL, tokens.get(2).type());
        assertEquals(TokenType.DOUBLE_LITERAL, tokens.get(3).type());
    }

    @Test
    void tokenizesStringLiteral() {
        var tokens = JavaLexer.tokenize("\"hello world\" \"escaped\\\"quote\"");
        assertEquals(TokenType.STRING_LITERAL, tokens.get(0).type());
        assertEquals("\"hello world\"", tokens.get(0).value());
        assertEquals(TokenType.STRING_LITERAL, tokens.get(1).type());
    }

    @Test
    void tokenizesTextBlock() {
        var tokens = JavaLexer.tokenize("\"\"\"\n    hello\n    world\n    \"\"\"");
        assertEquals(TokenType.TEXT_BLOCK, tokens.get(0).type());
    }

    @Test
    void tokenizesCharLiteral() {
        var tokens = JavaLexer.tokenize("'a' '\\n' '\\''");
        assertEquals(TokenType.CHAR_LITERAL, tokens.get(0).type());
        assertEquals("'a'", tokens.get(0).value());
        assertEquals(TokenType.CHAR_LITERAL, tokens.get(1).type());
    }

    @Test
    void tokenizesBooleanAndNull() {
        var tokens = JavaLexer.tokenize("true false null");
        assertEquals(TokenType.BOOLEAN_LITERAL, tokens.get(0).type());
        assertEquals(TokenType.BOOLEAN_LITERAL, tokens.get(1).type());
        assertEquals(TokenType.NULL_LITERAL, tokens.get(2).type());
    }

    @Test
    void tokenizesOperators() {
        var tokens = JavaLexer.tokenize("+ - * / % == != <= >= && || ++ -- -> :: << <<=");
        assertEquals(TokenType.OPERATOR, tokens.get(0).type());
        assertEquals("+", tokens.get(0).value());
        // Find ->
        var arrow = tokens.stream().filter(t -> t.value().equals("->")).findFirst();
        assertTrue(arrow.isPresent());
        // Find ::
        var dcolon = tokens.stream().filter(t -> t.value().equals("::")).findFirst();
        assertTrue(dcolon.isPresent());
        // Find <<
        var leftShift = tokens.stream().filter(t -> t.value().equals("<<")).findFirst();
        assertTrue(leftShift.isPresent());
        // Note: >> and >>> are NOT combined — each '>' is a separate token
        // to avoid ambiguity with generics (e.g., List<Comparable<T>>)
    }

    @Test
    void tokenizesSeparators() {
        var tokens = JavaLexer.tokenize("( ) { } [ ] ; , . @ ...");
        assertTokenValues(tokens, "(", ")", "{", "}", "[", "]", ";", ",", ".", "@", "...", "");
        for (int i = 0; i < tokens.size() - 1; i++) {
            assertEquals(TokenType.SEPARATOR, tokens.get(i).type(), "token " + i);
        }
    }

    @Test
    void skipsLineComments() {
        var tokens = JavaLexer.tokenize("foo // this is a comment\nbar");
        assertTokenValues(tokens, "foo", "bar", "");
    }

    @Test
    void skipsBlockComments() {
        var tokens = JavaLexer.tokenize("foo /* block\ncomment */ bar");
        assertTokenValues(tokens, "foo", "bar", "");
    }

    @Test
    void tracksLineAndColumn() {
        var tokens = JavaLexer.tokenize("foo\nbar baz");
        assertEquals(1, tokens.get(0).line());
        assertEquals(1, tokens.get(0).column());
        assertEquals(2, tokens.get(1).line());
        assertEquals(1, tokens.get(1).column());
        assertEquals(2, tokens.get(2).line());
        assertEquals(5, tokens.get(2).column());
    }

    @Test
    void tokenizesContextualKeywords() {
        var tokens = JavaLexer.tokenize("var yield when");
        assertEquals(TokenType.KEYWORD, tokens.get(0).type());
        assertEquals(TokenType.KEYWORD, tokens.get(1).type());
        assertEquals(TokenType.KEYWORD, tokens.get(2).type());
    }

    @Test
    void tokenizesCompleteClassDeclaration() {
        var source = """
            public class Calculator {
                private int value = 0;

                public int add(int x) {
                    return value += x;
                }
            }
            """;
        var tokens = JavaLexer.tokenize(source);
        // Should not contain any line/block comment residue
        assertTrue(tokens.stream().noneMatch(t -> t.value().contains("//")));
        // Last token should be EOF
        assertEquals(TokenType.EOF, tokens.getLast().type());
        // Should have reasonable number of tokens
        assertTrue(tokens.size() > 20, "Expected >20 tokens, got " + tokens.size());
    }

    @Test
    void tokenizesRecordDeclaration() {
        var source = "record Point(double x, double y) {}";
        var tokens = JavaLexer.tokenize(source);
        assertEquals("record", tokens.get(0).value());
        assertEquals(TokenType.KEYWORD, tokens.get(0).type());
        assertEquals("Point", tokens.get(1).value());
        assertEquals(TokenType.IDENTIFIER, tokens.get(1).type());
    }

    @Test
    void tokenizesSwitchExpression() {
        var source = """
            switch (x) {
                case 1 -> "one";
                case 2 -> "two";
                default -> "other";
            }
            """;
        var tokens = JavaLexer.tokenize(source);
        assertTrue(tokens.stream().anyMatch(t -> t.value().equals("->")));
        assertTrue(tokens.stream().anyMatch(t -> t.value().equals("switch")));
        assertTrue(tokens.stream().anyMatch(t -> t.value().equals("default")));
    }

    @Test
    void tokenizesLambda() {
        var source = "(x, y) -> x + y";
        var tokens = JavaLexer.tokenize(source);
        assertTrue(tokens.stream().anyMatch(t -> t.value().equals("->")));
    }

    @Test
    void tokenizesPatternMatching() {
        var source = "obj instanceof String s";
        var tokens = JavaLexer.tokenize(source);
        assertEquals("obj", tokens.get(0).value());
        assertEquals("instanceof", tokens.get(1).value());
        assertEquals(TokenType.KEYWORD, tokens.get(1).type());
        assertEquals("String", tokens.get(2).value());
        assertEquals("s", tokens.get(3).value());
    }

    @Test
    void endsWithEof() {
        var tokens = JavaLexer.tokenize("");
        assertEquals(1, tokens.size());
        assertEquals(TokenType.EOF, tokens.getFirst().type());
    }

    private void assertTokenValues(List<LexToken> tokens, String... expected) {
        assertEquals(expected.length, tokens.size(),
            "Expected " + expected.length + " tokens but got " + tokens.size() + ": " + tokens);
        for (int i = 0; i < expected.length; i++) {
            assertEquals(expected[i], tokens.get(i).value(), "Token " + i);
        }
    }
}
