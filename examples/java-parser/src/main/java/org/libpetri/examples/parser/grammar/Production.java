package org.libpetri.examples.parser.grammar;

/**
 * A named grammar production: name → body.
 */
public record Production(String name, GrammarElement body) {
    public Production {
        if (name == null || name.isEmpty()) throw new IllegalArgumentException("Production name must not be empty");
        if (body == null) throw new IllegalArgumentException("Production body must not be null");
    }
}
