package org.libpetri.smt.z3;

import java.util.ArrayList;
import java.util.List;

/**
 * Text-level helpers shared by the transport, the Spacer runner, the certificate
 * check and the counterexample decoder (VER-013). Byte-for-byte mirrors of the Rust
 * {@code z3_process} / {@code smt_verifier} helpers.
 */
public final class SmtText {

    private SmtText() {}

    /**
     * The first trimmed stdout line that is a {@code (check-sat)} answer, or
     * {@code null}. The answer is a LINE anywhere in the reply, not the first bytes: a
     * build is free to print a warning first, and a HORN script that asks for both a
     * proof and a model always gets one {@code (error …)} line back.
     */
    public static String classifyFirstLine(String stdout) {
        return stdout.lines()
            .map(String::strip)
            .filter(l -> l.equals("sat") || l.equals("unsat") || l.equals("unknown"))
            .findFirst()
            .orElse(null);
    }

    /** True when z3's {@code -T} backstop fired: it prints the single line {@code timeout}. */
    public static boolean timeoutLine(String stdout) {
        return stdout.lines().map(String::strip).anyMatch(l -> l.equals("timeout"));
    }

    /** The first {@code (error …)} line in a z3 stream, trimmed; {@code null} if none. */
    public static String errorLine(String text) {
        return text.lines()
            .map(String::strip)
            .filter(l -> l.startsWith("(error"))
            .findFirst()
            .orElse(null);
    }

    /**
     * Returns the index one past the {@code )} matching the {@code (} at {@code start},
     * or {@code -1} when the expression is unbalanced. Paren counting skips string
     * literals ({@code "…"}, with {@code ""} escapes) and quoted symbols ({@code |…|}).
     */
    public static int sexprEnd(String s, int start) {
        int depth = 0;
        boolean inString = false;
        boolean inSymbol = false;
        for (int i = start; i < s.length(); i++) {
            char c = s.charAt(i);
            if (inString) {
                if (c == '"') {
                    inString = false;
                }
            } else if (inSymbol) {
                if (c == '|') {
                    inSymbol = false;
                }
            } else {
                switch (c) {
                    case '"' -> inString = true;
                    case '|' -> inSymbol = true;
                    case '(' -> depth++;
                    case ')' -> {
                        depth--;
                        if (depth == 0) {
                            return i + 1;
                        }
                    }
                    default -> { }
                }
            }
        }
        return -1;
    }

    /**
     * Every complete {@code (define-fun …)} s-expression in {@code output}, in order. A
     * truncated (unbalanced) definition is dropped rather than half-captured.
     */
    public static List<String> extractDefineFuns(String output) {
        var defs = new ArrayList<String>();
        int from = 0;
        while (true) {
            int pos = output.indexOf("(define-fun", from);
            if (pos < 0) {
                break;
            }
            int end = sexprEnd(output, pos);
            if (end < 0) {
                break;
            }
            defs.add(output.substring(pos, end));
            from = end;
        }
        return defs;
    }

    /**
     * The inductive invariant of a {@code sat} reply: every {@code (define-fun …)} of
     * the {@code (get-model)} block joined with newlines, or {@code null} when no model
     * was printed.
     */
    public static String extractInvariant(String output) {
        var defs = extractDefineFuns(output);
        return defs.isEmpty() ? null : String.join("\n", defs);
    }
}
