package org.libpetri.examples.parser.grammar;

import org.libpetri.examples.parser.lexer.TokenType;

import java.util.List;

/**
 * Sealed hierarchy representing EBNF grammar elements.
 * Each variant maps to a specific Petri net compilation pattern.
 */
public sealed interface GrammarElement {

    /** Match a specific keyword, operator, or separator by exact string value. */
    record Terminal(String value) implements GrammarElement {
        public Terminal {
            if (value == null || value.isEmpty()) throw new IllegalArgumentException("Terminal value must not be empty");
        }
    }

    /** Match any token of a given type (e.g., IDENTIFIER, INT_LITERAL). */
    record TokenMatch(TokenType type) implements GrammarElement {
        public TokenMatch {
            if (type == null) throw new IllegalArgumentException("TokenMatch type must not be null");
        }
    }

    /** Reference to another production by name. */
    record NonTerminal(String name) implements GrammarElement {
        public NonTerminal {
            if (name == null || name.isEmpty()) throw new IllegalArgumentException("NonTerminal name must not be empty");
        }
    }

    /** Ordered sequence: A B C — all elements must match in order. */
    record Sequence(List<GrammarElement> elements) implements GrammarElement {
        public Sequence {
            if (elements == null || elements.size() < 2) throw new IllegalArgumentException("Sequence needs at least 2 elements");
            elements = List.copyOf(elements);
        }
    }

    /** Alternation: A | B | C — exactly one branch matches. */
    record Choice(List<GrammarElement> alternatives) implements GrammarElement {
        public Choice {
            if (alternatives == null || alternatives.size() < 2) throw new IllegalArgumentException("Choice needs at least 2 alternatives");
            alternatives = List.copyOf(alternatives);
        }
    }

    /** Zero-or-more repetition: {A} — body matches zero or more times. */
    record Repetition(GrammarElement body) implements GrammarElement {
        public Repetition {
            if (body == null) throw new IllegalArgumentException("Repetition body must not be null");
        }
    }

    /** Optional element: [A] — body matches zero or one time. */
    record Optional(GrammarElement body) implements GrammarElement {
        public Optional {
            if (body == null) throw new IllegalArgumentException("Optional body must not be null");
        }
    }

    // ==================== Factory Methods ====================

    static Terminal terminal(String value) { return new Terminal(value); }
    static TokenMatch tokenMatch(TokenType type) { return new TokenMatch(type); }
    static NonTerminal nonTerminal(String name) { return new NonTerminal(name); }

    static GrammarElement seq(GrammarElement... elements) {
        if (elements.length == 1) return elements[0];
        return new Sequence(List.of(elements));
    }

    static GrammarElement choice(GrammarElement... alternatives) {
        if (alternatives.length == 1) return alternatives[0];
        return new Choice(List.of(alternatives));
    }

    static Repetition repeat(GrammarElement body) { return new Repetition(body); }
    static Optional optional(GrammarElement body) { return new Optional(body); }
}
