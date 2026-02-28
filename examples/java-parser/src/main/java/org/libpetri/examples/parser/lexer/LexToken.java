package org.libpetri.examples.parser.lexer;

/**
 * A lexical token produced by the Java lexer.
 */
public record LexToken(TokenType type, String value, int line, int column) {

    public LexToken {
        if (type == null) throw new IllegalArgumentException("type must not be null");
        if (value == null) throw new IllegalArgumentException("value must not be null");
    }

    public boolean is(TokenType t, String v) {
        return type == t && value.equals(v);
    }

    public boolean is(String v) {
        return value.equals(v);
    }

    public boolean isType(TokenType t) {
        return type == t;
    }

    @Override
    public String toString() {
        return type + "(" + value + ")@" + line + ":" + column;
    }
}
