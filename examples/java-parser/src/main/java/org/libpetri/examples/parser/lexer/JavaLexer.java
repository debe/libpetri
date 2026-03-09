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
        var tokens = new JavaLexer(source).scan();
        disambiguateTypeArguments(tokens);
        return tokens;
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
                case '@' -> scanAt(startLine, startCol);
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

    private LexToken scanAt(int l, int c) {
        // Check for @interface (annotation type declaration)
        // Emitted as single KEYWORD token to prevent @ being consumed as Annotation start
        int probe = pos + 1;
        while (probe < source.length && (source[probe] == ' ' || source[probe] == '\t'
            || source[probe] == '\n' || source[probe] == '\r')) {
            probe++;
        }
        if (probe + 9 <= source.length
            && new String(source, probe, 9).equals("interface")
            && (probe + 9 >= source.length || !Character.isJavaIdentifierPart(source[probe + 9]))) {
            // Consume @ + whitespace + 'interface' as single token
            pos = probe + 9;
            column += (pos - (l == line ? c : 1));
            return new LexToken(TokenType.KEYWORD, "@interface", l, c);
        }
        pos++; column++;
        return new LexToken(TokenType.SEPARATOR, "@", l, c);
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

    // ==================== Type Argument Disambiguation ====================

    /**
     * Post-processing pass that identifies {@code <...>} sequences used as type arguments
     * (not comparison operators) and reclassifies them as TYPE_OPEN / TYPE_CLOSE tokens.
     *
     * <p>Heuristic: {@code <} is a type argument opener when:
     * <ol>
     *   <li>Preceded by IDENTIFIER, {@code >} (nested close), or {@code )} </li>
     *   <li>The content between {@code <} and matching {@code >} is type-like
     *       (identifiers, wildcards, commas, dots, nested type args, dims, bounds)</li>
     *   <li>The matching {@code >} is followed by a type-continuing token:
     *       IDENTIFIER, {@code (}, {@code )}, {@code .}, {@code [}, {@code >}, {@code ,},
     *       {@code @}, {@code ;}, or keywords like {@code extends}, {@code implements}</li>
     * </ol>
     */
    private static void disambiguateTypeArguments(List<LexToken> tokens) {
        for (int i = 0; i < tokens.size(); i++) {
            var tok = tokens.get(i);
            if (!isLessThan(tok)) continue;

            // Check predecessor context
            if (i == 0) continue;
            var prev = tokens.get(i - 1);
            boolean validPredecessor = switch (prev.type()) {
                case IDENTIFIER, TYPE_CLOSE -> true;
                case SEPARATOR -> prev.value().equals(")") || prev.value().equals("{")
                    || prev.value().equals("}") || prev.value().equals(";")
                    || prev.value().equals(",") || prev.value().equals("@")
                    || prev.value().equals(".");  // Class.<Type>method explicit type args
                // Keywords like static, public, abstract precede type parameter declarations
                case KEYWORD -> true;
                default -> false;
            };
            if (!validPredecessor) continue;

            // Try to find matching '>' with balanced type argument content
            int closeIdx = findMatchingTypeClose(tokens, i + 1, 0);
            if (closeIdx < 0) continue;

            // Check what follows the closing '>'
            if (closeIdx + 1 < tokens.size()) {
                var after = tokens.get(closeIdx + 1);
                if (!isTypeFollower(after)) continue;
            }

            // Reclassify the matched pair (and any nested pairs found during matching)
            reclassifyTypeArgs(tokens, i, closeIdx);
        }
    }

    private static boolean isLessThan(LexToken tok) {
        return tok.type() == TokenType.OPERATOR && tok.value().equals("<");
    }

    private static boolean isGreaterThan(LexToken tok) {
        return tok.type() == TokenType.OPERATOR && tok.value().equals(">");
    }

    /**
     * Finds the matching '>' for a type argument list starting at index {@code start}.
     * Returns the index of the matching '>', or -1 if content is not type-like.
     */
    private static int findMatchingTypeClose(List<LexToken> tokens, int start, int depth) {
        int i = start;
        while (i < tokens.size()) {
            var tok = tokens.get(i);

            if (isGreaterThan(tok) || (tok.type() == TokenType.TYPE_CLOSE && tok.value().equals(">"))) {
                return i;
            }

            // Nested '<' — recurse
            if (isLessThan(tok) || tok.type() == TokenType.TYPE_OPEN) {
                int nested = findMatchingTypeClose(tokens, i + 1, depth + 1);
                if (nested < 0) return -1;
                i = nested + 1;
                continue;
            }

            // Check if this token is valid inside type arguments
            if (!isValidTypeContent(tok)) return -1;

            i++;
        }
        return -1; // No matching '>'
    }

    /** Checks if a token is valid inside type argument brackets. */
    private static boolean isValidTypeContent(LexToken tok) {
        return switch (tok.type()) {
            case IDENTIFIER -> true;
            case KEYWORD -> tok.value().equals("extends") || tok.value().equals("super")
                || tok.value().equals("int") || tok.value().equals("long")
                || tok.value().equals("short") || tok.value().equals("byte")
                || tok.value().equals("char") || tok.value().equals("float")
                || tok.value().equals("double") || tok.value().equals("boolean")
                || tok.value().equals("void");
            case OPERATOR -> tok.value().equals("?") || tok.value().equals("&");
            case SEPARATOR -> tok.value().equals(",") || tok.value().equals(".")
                || tok.value().equals("[") || tok.value().equals("]")
                || tok.value().equals("@");
            case TYPE_OPEN, TYPE_CLOSE -> true;
            default -> false;
        };
    }

    /** Checks if a token can follow a type argument closing '>'. */
    private static boolean isTypeFollower(LexToken tok) {
        return switch (tok.type()) {
            case IDENTIFIER -> true;
            case SEPARATOR -> tok.value().equals("(") || tok.value().equals(")")
                || tok.value().equals(".") || tok.value().equals("[")
                || tok.value().equals(",") || tok.value().equals(";")
                || tok.value().equals("@") || tok.value().equals("{")
                || tok.value().equals("]") || tok.value().equals("...");
            case OPERATOR -> tok.value().equals(">") || tok.value().equals("::")
                || tok.value().equals("&");
            case TYPE_CLOSE -> true;
            // Keywords that can follow type args: permits, throws, extends, implements, etc.
            // Exclude expression-only operators like + - * / to avoid false positives on a > b + c
            case KEYWORD -> true;
            case EOF -> true;
            default -> false;
        };
    }

    /** Reclassifies '<' at openIdx and '>' at closeIdx as TYPE_OPEN/TYPE_CLOSE. */
    private static void reclassifyTypeArgs(List<LexToken> tokens, int openIdx, int closeIdx) {
        var open = tokens.get(openIdx);
        tokens.set(openIdx, new LexToken(TokenType.TYPE_OPEN, "<", open.line(), open.column()));

        var close = tokens.get(closeIdx);
        tokens.set(closeIdx, new LexToken(TokenType.TYPE_CLOSE, ">", close.line(), close.column()));

        // Also reclassify nested pairs within this range
        for (int i = openIdx + 1; i < closeIdx; i++) {
            var tok = tokens.get(i);
            if (isLessThan(tok)) {
                // Check if preceded by IDENTIFIER or TYPE_CLOSE
                if (i > 0) {
                    var prev = tokens.get(i - 1);
                    if (prev.type() == TokenType.IDENTIFIER || prev.type() == TokenType.TYPE_CLOSE) {
                        int nested = findMatchingTypeClose(tokens, i + 1, 0);
                        if (nested > 0 && nested <= closeIdx) {
                            reclassifyTypeArgs(tokens, i, nested);
                        }
                    }
                }
            }
        }
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
