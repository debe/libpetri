package org.libpetri.examples.parser.grammar;

import org.libpetri.examples.parser.lexer.LexToken;
import org.libpetri.examples.parser.lexer.TokenType;

import java.util.*;
import java.util.function.Predicate;

/**
 * A complete grammar: ordered list of productions with FIRST set computation
 * and left-recursion elimination.
 */
public final class Grammar {

    private final List<Production> productions;
    private final Map<String, Production> byName;
    private final String startProduction;

    // Cached FIRST sets: production name → set of (terminal value | token type name)
    private Map<String, Set<String>> firstSets;

    // Cached FIRST predicates: production name → predicate on LexToken
    private Map<String, Predicate<LexToken>> firstPredicates;

    private Grammar(List<Production> productions, String startProduction) {
        this.productions = List.copyOf(productions);
        this.startProduction = startProduction;

        var map = new LinkedHashMap<String, Production>();
        for (var p : this.productions) {
            if (map.containsKey(p.name())) {
                throw new IllegalArgumentException("Duplicate production: " + p.name());
            }
            map.put(p.name(), p);
        }
        this.byName = Collections.unmodifiableMap(map);
    }

    public static Grammar of(String startProduction, Production... productions) {
        return new Grammar(List.of(productions), startProduction);
    }

    public static Grammar of(String startProduction, List<Production> productions) {
        return new Grammar(productions, startProduction);
    }

    public List<Production> productions() { return productions; }
    public String startProduction() { return startProduction; }

    public Production get(String name) {
        var p = byName.get(name);
        if (p == null) throw new IllegalArgumentException("Unknown production: " + name);
        return p;
    }

    public boolean has(String name) { return byName.containsKey(name); }
    public Set<String> productionNames() { return byName.keySet(); }

    /**
     * Compute FIRST set for a grammar element.
     * Returns set of string keys: terminal values prefixed with "T:" and token type names prefixed with "TT:".
     */
    public Set<String> firstSet(GrammarElement element) {
        ensureFirstSets();
        return computeFirst(element, new HashSet<>());
    }

    /**
     * Get a pre-built predicate that checks if a LexToken is in the FIRST set of a production.
     */
    public Predicate<LexToken> firstPredicate(String productionName) {
        ensureFirstPredicates();
        var pred = firstPredicates.get(productionName);
        if (pred == null) throw new IllegalArgumentException("Unknown production: " + productionName);
        return pred;
    }

    /**
     * Get a pre-built predicate for a grammar element's FIRST set.
     */
    public Predicate<LexToken> firstPredicate(GrammarElement element) {
        var first = firstSet(element);
        return buildPredicate(first);
    }

    /**
     * Eliminate direct left recursion from all productions.
     * Rewrites A → A α | β to A → β {α}
     */
    public Grammar eliminateLeftRecursion() {
        var newProductions = new ArrayList<Production>();

        for (var prod : productions) {
            var leftRecursive = new ArrayList<GrammarElement>();
            var nonLeftRecursive = new ArrayList<GrammarElement>();

            var alternatives = flattenChoice(prod.body());

            for (var alt : alternatives) {
                if (isLeftRecursive(prod.name(), alt)) {
                    leftRecursive.add(stripLeftRecursion(prod.name(), alt));
                } else {
                    nonLeftRecursive.add(alt);
                }
            }

            if (leftRecursive.isEmpty()) {
                newProductions.add(prod);
            } else {
                // A → β A'
                // A' → α A' | ε
                // Rewritten as: A → β {α}
                var tailName = prod.name() + "_tail";

                // Build tail body: choice of left-recursive suffixes
                GrammarElement tailBody;
                if (leftRecursive.size() == 1) {
                    tailBody = leftRecursive.getFirst();
                } else {
                    tailBody = new GrammarElement.Choice(leftRecursive);
                }

                // Build base: choice of non-left-recursive alternatives
                GrammarElement base;
                if (nonLeftRecursive.size() == 1) {
                    base = nonLeftRecursive.getFirst();
                } else if (nonLeftRecursive.isEmpty()) {
                    throw new IllegalStateException("Production " + prod.name() + " is entirely left-recursive");
                } else {
                    base = new GrammarElement.Choice(nonLeftRecursive);
                }

                // New production: base followed by optional repetition of tail
                var newBody = GrammarElement.seq(base, GrammarElement.repeat(tailBody));
                newProductions.add(new Production(prod.name(), newBody));
            }
        }

        return new Grammar(newProductions, startProduction);
    }

    // ==================== Internal ====================

    private void ensureFirstSets() {
        if (firstSets != null) return;

        firstSets = new HashMap<>();
        for (var name : byName.keySet()) {
            firstSets.put(name, new HashSet<>());
        }

        // Fixed-point iteration
        boolean changed = true;
        while (changed) {
            changed = false;
            for (var prod : productions) {
                var current = firstSets.get(prod.name());
                var computed = computeFirst(prod.body(), new HashSet<>());
                if (current.addAll(computed)) {
                    changed = true;
                }
            }
        }
    }

    private void ensureFirstPredicates() {
        if (firstPredicates != null) return;
        ensureFirstSets();

        firstPredicates = new HashMap<>();
        for (var entry : firstSets.entrySet()) {
            firstPredicates.put(entry.getKey(), buildPredicate(entry.getValue()));
        }
    }

    private Set<String> computeFirst(GrammarElement element, Set<String> visited) {
        return switch (element) {
            case GrammarElement.Terminal t -> Set.of("T:" + t.value());
            case GrammarElement.TokenMatch t -> Set.of("TT:" + t.type().name());
            case GrammarElement.NonTerminal nt -> {
                if (visited.contains(nt.name())) yield Set.of();
                visited.add(nt.name());
                if (firstSets != null && firstSets.containsKey(nt.name())) {
                    yield firstSets.get(nt.name());
                }
                var prod = byName.get(nt.name());
                yield prod != null ? computeFirst(prod.body(), visited) : Set.of();
            }
            case GrammarElement.Sequence seq -> {
                // FIRST(A B C) = FIRST(A) ∪ (if A nullable: FIRST(B)) ∪ (if A,B nullable: FIRST(C))
                var result = new HashSet<String>();
                for (var elem : seq.elements()) {
                    result.addAll(computeFirst(elem, visited));
                    if (!canBeEmpty(elem, visited)) break;
                }
                yield result;
            }
            case GrammarElement.Choice ch -> {
                var result = new HashSet<String>();
                for (var alt : ch.alternatives()) {
                    result.addAll(computeFirst(alt, visited));
                }
                yield result;
            }
            case GrammarElement.Repetition rep -> computeFirst(rep.body(), visited);
            case GrammarElement.Optional opt -> computeFirst(opt.body(), visited);
        };
    }

    /** Check if a grammar element can derive the empty string. */
    private boolean canBeEmpty(GrammarElement element, Set<String> visited) {
        return switch (element) {
            case GrammarElement.Terminal _ -> false;
            case GrammarElement.TokenMatch _ -> false;
            case GrammarElement.NonTerminal nt -> {
                if (visited.contains(nt.name())) yield false;
                visited.add(nt.name());
                var prod = byName.get(nt.name());
                yield prod != null && canBeEmpty(prod.body(), visited);
            }
            case GrammarElement.Sequence seq ->
                seq.elements().stream().allMatch(e -> canBeEmpty(e, visited));
            case GrammarElement.Choice ch ->
                ch.alternatives().stream().anyMatch(a -> canBeEmpty(a, visited));
            case GrammarElement.Repetition _ -> true;
            case GrammarElement.Optional _ -> true;
        };
    }

    private Predicate<LexToken> buildPredicate(Set<String> firstSet) {
        // Pre-compute terminal values and token types for O(1) lookup
        var terminalValues = new HashSet<String>();
        var tokenTypes = EnumSet.noneOf(TokenType.class);

        for (var key : firstSet) {
            if (key.startsWith("T:")) {
                terminalValues.add(key.substring(2));
            } else if (key.startsWith("TT:")) {
                tokenTypes.add(TokenType.valueOf(key.substring(3)));
            }
        }

        return token -> {
            // Token type match (e.g., tokenMatch(TYPE_OPEN))
            if (tokenTypes.contains(token.type())) return true;
            // Terminal value match — but TYPE_OPEN/TYPE_CLOSE should only match via tokenTypes
            if (terminalValues.contains(token.value())) {
                // Don't let terminal("<") match TYPE_OPEN, or terminal(">") match TYPE_CLOSE
                if (token.type() == TokenType.TYPE_OPEN || token.type() == TokenType.TYPE_CLOSE) {
                    return false;
                }
                return true;
            }
            return false;
        };
    }

    private List<GrammarElement> flattenChoice(GrammarElement element) {
        if (element instanceof GrammarElement.Choice ch) {
            return ch.alternatives();
        }
        return List.of(element);
    }

    private boolean isLeftRecursive(String name, GrammarElement element) {
        return switch (element) {
            case GrammarElement.NonTerminal nt -> nt.name().equals(name);
            case GrammarElement.Sequence seq -> {
                var first = seq.elements().getFirst();
                yield first instanceof GrammarElement.NonTerminal nt && nt.name().equals(name);
            }
            default -> false;
        };
    }

    private GrammarElement stripLeftRecursion(String name, GrammarElement element) {
        if (element instanceof GrammarElement.Sequence seq) {
            var rest = seq.elements().subList(1, seq.elements().size());
            if (rest.size() == 1) return rest.getFirst();
            return new GrammarElement.Sequence(rest);
        }
        // Shouldn't happen — left-recursive without suffix
        throw new IllegalStateException("Cannot strip left recursion from: " + element);
    }
}
