package org.libpetri.examples.parser.lexer;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Hand-written single-pass lexer for Java 25.
 * char[]-backed, keyword lookup via Set, token list pre-sized by source length heuristic.
 */
public final class JavaLexer {

    private static final Set<String> KEYWORDS = Set.of(
        "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
        "class", "const", "continue", "default", "do", "double", "else", "enum",
        "extends", "final", "finally", "float", "for", "goto", "if", "implements",
        "import", "instanceof", "int", "interface", "long", "native", "new",
        "package", "private", "protected", "public", "return", "short", "static",
        "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
        "transient", "try", "void", "volatile", "while",
        // Contextual keywords treated as keywords for parsing purposes
        "var", "yield", "record", "sealed", "non-sealed", "permits", "when",
        "module", "open", "opens", "requires", "exports", "uses", "provides",
        "to", "with", "transitive"
    );

    private static final Set<String> BOOLEAN_LITERALS = Set.of("true", "false");

    private final char[] source;
    private int pos;
    private int line;
    private int column;

    private JavaLexer(String source) {
        this.source = source.toCharArray();
        this.pos = 0;
        this.line = 1;
        this.column = 1;
    }

    public static List<LexToken> tokenize(String source) {
        return new JavaLexer(source).scan();
    }

    private List<LexToken> scan() {
        var tokens = new ArrayList<LexToken>(source.length / 5);

        while (pos < source.length) {
            skipWhitespaceAndComments();
            if (pos >= source.length) break;

            int startLine = line;
            int startCol = column;
            char c = source[pos];

            LexToken token = switch (c) {
                case '"' -> scanStringOrTextBlock(startLine, startCol);
                case '\'' -> scanCharLiteral(startLine, startCol);
                case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ->
                    scanNumber(startLine, startCol);
                case '(' -> singleSep("(", startLine, startCol);
                case ')' -> singleSep(")", startLine, startCol);
                case '{' -> singleSep("{", startLine, startCol);
                case '}' -> singleSep("}", startLine, startCol);
                case '[' -> singleSep("[", startLine, startCol);
                case ']' -> singleSep("]", startLine, startCol);
                case ';' -> singleSep(";", startLine, startCol);
                case ',' -> singleSep(",", startLine, startCol);
                case '@' -> singleSep("@", startLine, startCol);
                case '.' -> scanDot(startLine, startCol);
                default -> {
                    if (Character.isJavaIdentifierStart(c)) {
                        yield scanIdentifierOrKeyword(startLine, startCol);
                    }
                    yield scanOperator(startLine, startCol);
                }
            };

            tokens.add(token);
        }

        tokens.add(new LexToken(TokenType.EOF, "", line, column));
        return tokens;
    }

    private LexToken singleSep(String value, int l, int c) {
        pos++;
        column++;
        return new LexToken(TokenType.SEPARATOR, value, l, c);
    }

    private LexToken scanDot(int l, int c) {
        if (pos + 2 < source.length && source[pos + 1] == '.' && source[pos + 2] == '.') {
            pos += 3; column += 3;
            return new LexToken(TokenType.SEPARATOR, "...", l, c);
        }
        if (pos + 1 < source.length && Character.isDigit(source[pos + 1])) {
            return scanNumber(l, c);
        }
        pos++; column++;
        return new LexToken(TokenType.SEPARATOR, ".", l, c);
    }

    private LexToken scanIdentifierOrKeyword(int l, int c) {
        int start = pos;
        pos++; column++;
        while (pos < source.length && Character.isJavaIdentifierPart(source[pos])) {
            pos++; column++;
        }

        // Handle non-sealed (special compound keyword)
        String word = new String(source, start, pos - start);
        if (word.equals("non") && pos < source.length && source[pos] == '-') {
            int savedPos = pos;
            int savedCol = column;
            pos++; column++;
            if (pos + 6 <= source.length) {
                String rest = new String(source, pos, 6);
                if (rest.equals("sealed")) {
                    pos += 6; column += 6;
                    return new LexToken(TokenType.KEYWORD, "non-sealed", l, c);
                }
            }
            pos = savedPos; column = savedCol;
        }

        if (BOOLEAN_LITERALS.contains(word)) {
            return new LexToken(TokenType.BOOLEAN_LITERAL, word, l, c);
        }
        if (word.equals("null")) {
            return new LexToken(TokenType.NULL_LITERAL, word, l, c);
        }
        if (KEYWORDS.contains(word)) {
            return new LexToken(TokenType.KEYWORD, word, l, c);
        }
        return new LexToken(TokenType.IDENTIFIER, word, l, c);
    }

    private LexToken scanStringOrTextBlock(int l, int c) {
        // Check for text block """
        if (pos + 2 < source.length && source[pos + 1] == '"' && source[pos + 2] == '"') {
            return scanTextBlock(l, c);
        }
        return scanString(l, c);
    }

    private LexToken scanString(int l, int c) {
        var sb = new StringBuilder();
        sb.append('"');
        pos++; column++; // skip opening "
        while (pos < source.length && source[pos] != '"') {
            if (source[pos] == '\\') {
                sb.append(source[pos]);
                pos++; column++;
                if (pos < source.length) {
                    sb.append(source[pos]);
                    pos++; column++;
                }
            } else {
                sb.append(source[pos]);
                pos++; column++;
            }
        }
        if (pos < source.length) {
            sb.append('"');
            pos++; column++; // skip closing "
        }
        return new LexToken(TokenType.STRING_LITERAL, sb.toString(), l, c);
    }

    private LexToken scanTextBlock(int l, int c) {
        var sb = new StringBuilder();
        sb.append("\"\"\"");
        pos += 3; column += 3; // skip opening """

        // Skip rest of line after opening """
        while (pos < source.length && source[pos] != '\n') {
            pos++; column++;
        }

        while (pos < source.length) {
            if (source[pos] == '"' && pos + 2 < source.length
                    && source[pos + 1] == '"' && source[pos + 2] == '"') {
                sb.append("\"\"\"");
                pos += 3; column += 3;
                return new LexToken(TokenType.TEXT_BLOCK, sb.toString(), l, c);
            }
            if (source[pos] == '\n') {
                sb.append('\n');
                pos++; line++; column = 1;
            } else {
                sb.append(source[pos]);
                pos++; column++;
            }
        }
        return new LexToken(TokenType.TEXT_BLOCK, sb.toString(), l, c);
    }

    private LexToken scanCharLiteral(int l, int c) {
        var sb = new StringBuilder();
        sb.append('\'');
        pos++; column++; // skip opening '
        while (pos < source.length && source[pos] != '\'') {
            if (source[pos] == '\\') {
                sb.append(source[pos]);
                pos++; column++;
                if (pos < source.length) {
                    sb.append(source[pos]);
                    pos++; column++;
                }
            } else {
                sb.append(source[pos]);
                pos++; column++;
            }
        }
        if (pos < source.length) {
            sb.append('\'');
            pos++; column++; // skip closing '
        }
        return new LexToken(TokenType.CHAR_LITERAL, sb.toString(), l, c);
    }

    private LexToken scanNumber(int l, int c) {
        int start = pos;
        boolean isFloat = false;
        boolean isLong = false;

        // Handle hex, octal, binary prefixes
        if (source[pos] == '0' && pos + 1 < source.length) {
            char next = source[pos + 1];
            if (next == 'x' || next == 'X') {
                pos += 2; column += 2;
                scanHexDigits();
                return finishNumber(start, l, c);
            }
            if (next == 'b' || next == 'B') {
                pos += 2; column += 2;
                scanBinaryDigits();
                return finishNumber(start, l, c);
            }
        }

        // Decimal digits (with underscores)
        scanDecimalDigits();

        // Fractional part
        if (pos < source.length && source[pos] == '.') {
            // Check it's not ".." (range) or method call
            if (pos + 1 < source.length && Character.isDigit(source[pos + 1])) {
                isFloat = true;
                pos++; column++;
                scanDecimalDigits();
            } else if (pos + 1 >= source.length || !Character.isJavaIdentifierStart(source[pos + 1])) {
                isFloat = true;
                pos++; column++;
                scanDecimalDigits();
            }
        }

        // Exponent
        if (pos < source.length && (source[pos] == 'e' || source[pos] == 'E')) {
            isFloat = true;
            pos++; column++;
            if (pos < source.length && (source[pos] == '+' || source[pos] == '-')) {
                pos++; column++;
            }
            scanDecimalDigits();
        }

        // Type suffix
        if (pos < source.length) {
            char suffix = source[pos];
            if (suffix == 'f' || suffix == 'F') {
                pos++; column++;
                String value = new String(source, start, pos - start);
                return new LexToken(TokenType.FLOAT_LITERAL, value, l, c);
            }
            if (suffix == 'd' || suffix == 'D') {
                pos++; column++;
                String value = new String(source, start, pos - start);
                return new LexToken(TokenType.DOUBLE_LITERAL, value, l, c);
            }
            if (suffix == 'l' || suffix == 'L') {
                isLong = true;
                pos++; column++;
            }
        }

        String value = new String(source, start, pos - start);
        if (isFloat) return new LexToken(TokenType.DOUBLE_LITERAL, value, l, c);
        if (isLong) return new LexToken(TokenType.LONG_LITERAL, value, l, c);
        return new LexToken(TokenType.INT_LITERAL, value, l, c);
    }

    private LexToken finishNumber(int start, int l, int c) {
        // Check for long suffix
        if (pos < source.length && (source[pos] == 'l' || source[pos] == 'L')) {
            pos++; column++;
            return new LexToken(TokenType.LONG_LITERAL, new String(source, start, pos - start), l, c);
        }
        return new LexToken(TokenType.INT_LITERAL, new String(source, start, pos - start), l, c);
    }

    private void scanDecimalDigits() {
        while (pos < source.length && (Character.isDigit(source[pos]) || source[pos] == '_')) {
            pos++; column++;
        }
    }

    private void scanHexDigits() {
        while (pos < source.length && (isHexDigit(source[pos]) || source[pos] == '_')) {
            pos++; column++;
        }
    }

    private void scanBinaryDigits() {
        while (pos < source.length && (source[pos] == '0' || source[pos] == '1' || source[pos] == '_')) {
            pos++; column++;
        }
    }

    private boolean isHexDigit(char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
    }

    private LexToken scanOperator(int l, int c) {
        // Multi-character operators (ordered longest-first)
        // NOTE: '>' is never combined into '>>' or '>>>' to avoid the Java
        // generics ambiguity (e.g., List<Comparable<T>>). The parser handles
        // shift operators as sequences of '>' tokens.
        String op = null;

        if (pos + 2 < source.length) {
            String three = new String(source, pos, 3);
            op = switch (three) {
                case "<<=", "..." -> three;
                default -> null;
            };
        }

        if (op == null && pos + 1 < source.length) {
            String two = new String(source, pos, 2);
            op = switch (two) {
                case "==", "!=", "<=", ">=", "&&", "||", "++", "--",
                     "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
                     "<<", "->", "::" -> two;
                default -> null;
            };
            // Handle >>= and >>>= as >= after > (let parser handle)
            // Handle >> and >>> as separate > tokens (let parser handle)
        }

        if (op == null) {
            op = String.valueOf(source[pos]);
        }

        pos += op.length();
        column += op.length();

        // Distinguish : as separator vs operator
        if (op.equals(":") || op.equals("?")) {
            return new LexToken(TokenType.OPERATOR, op, l, c);
        }

        return new LexToken(TokenType.OPERATOR, op, l, c);
    }

    private void skipWhitespaceAndComments() {
        while (pos < source.length) {
            char c = source[pos];

            if (c == ' ' || c == '\t' || c == '\r') {
                pos++; column++;
            } else if (c == '\n') {
                pos++; line++; column = 1;
            } else if (c == '/' && pos + 1 < source.length) {
                if (source[pos + 1] == '/') {
                    // Line comment
                    pos += 2; column += 2;
                    while (pos < source.length && source[pos] != '\n') {
                        pos++; column++;
                    }
                } else if (source[pos + 1] == '*') {
                    // Block comment
                    pos += 2; column += 2;
                    while (pos + 1 < source.length) {
                        if (source[pos] == '*' && source[pos + 1] == '/') {
                            pos += 2; column += 2;
                            break;
                        }
                        if (source[pos] == '\n') {
                            line++; column = 1;
                        } else {
                            column++;
                        }
                        pos++;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }
}
