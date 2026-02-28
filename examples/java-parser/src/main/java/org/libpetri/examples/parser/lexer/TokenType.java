package org.libpetri.examples.parser.lexer;

/**
 * Token types for Java 25 lexical analysis.
 */
public enum TokenType {
    KEYWORD,
    IDENTIFIER,
    INT_LITERAL,
    LONG_LITERAL,
    FLOAT_LITERAL,
    DOUBLE_LITERAL,
    STRING_LITERAL,
    TEXT_BLOCK,
    CHAR_LITERAL,
    BOOLEAN_LITERAL,
    NULL_LITERAL,
    OPERATOR,
    SEPARATOR,
    EOF
}
