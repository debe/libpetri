package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.core.internal.CodePointOrder;
import org.libpetri.smt.GraphDecision;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.SmtProperty;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

/**
 * The contract's guarantee at one quiescent marking ([VER-022]): which clauses it breaks and
 * which places it strands.
 *
 * <p>The stranding half is the rest set of [VER-014], read through {@link RestSet}, the class
 * every {@code DeadlockFree} route reads. The clause places, the rest places and the
 * environment's own places are sinks, and each designed terminal is a conditional sink. That
 * is what lets the SMT route ask for it with {@code deadlockFree()} and mean the same thing.
 *
 * <p>The rest declaration, the waiver markers and the stranding attribution are derived here
 * only, so the two routes cannot judge different sets. Every place is resolved through
 * {@link ClosedNet#canonical} first, so a contract place and the closed net's place of that name
 * are one place, as in the name-keyed reference.
 */
final class QuiescencePredicate {

    private QuiescencePredicate() {}

    /**
     * The contract's rest set in [VER-014] form.
     *
     * @param sinks       clause places, then rest places, then the environment's own places,
     *                    each once by name
     * @param conditional each designed terminal, marker and excused places
     */
    record RestDeclaration(List<Place<?>> sinks, List<RestSet.ConditionalSinks> conditional) {
        RestDeclaration {
            sinks = List.copyOf(sinks);
            conditional = List.copyOf(conditional);
        }
    }

    /** One thing a quiescent marking breaks. */
    sealed interface Finding {
        /** The finding's subject: its clause's name or its place's name. */
        String subject();

        ContractViolation.Kind kind();

        /** The finding in words. */
        String describe();
    }

    /** A clause's count out of bounds: {@code count} tokens across its places. */
    record ClauseFinding(OpenNetContract.CountClause clause, long count, GraphDecision.CountBound bound)
            implements Finding {
        @Override
        public String subject() {
            return clause.name();
        }

        @Override
        public ContractViolation.Kind kind() {
            return ContractViolation.Kind.CLAUSE;
        }

        @Override
        public String describe() {
            String expected = SmtProperty.countAcross(clause.min(), clause.max(), clause.places());
            return bound == GraphDecision.CountBound.UPPER
                ? expected + " at quiescence, found " + count + " (an upper bound holds under a terminal too)"
                : expected + " at quiescence, found " + count;
        }
    }

    /** {@code count} tokens resting on {@code place}, which nothing in the contract excuses. */
    record StrandedFinding(String place, int count) implements Finding {
        @Override
        public String subject() {
            return place;
        }

        @Override
        public ContractViolation.Kind kind() {
            return ContractViolation.Kind.STRANDED;
        }

        @Override
        public String describe() {
            return place + " holds " + count
                + " at quiescence, and nothing in the contract lets a token rest there";
        }
    }

    /** Clause places, rest places and the environment's own places as sinks; each designed terminal as a conditional sink. */
    static RestDeclaration restDeclarationOf(OpenNetContract contract, ClosedNet closed) {
        var sinks = new LinkedHashMap<String, Place<?>>();
        for (var c : contract.clauses()) {
            for (var p : c.places()) {
                sinks.putIfAbsent(p.name(), closed.canonical(p));
            }
        }
        for (var p : contract.rest()) {
            sinks.putIfAbsent(p.name(), closed.canonical(p));
        }
        for (var p : closed.environmentPlaces()) {
            sinks.putIfAbsent(p.name(), closed.canonical(p));
        }
        var conditional = new ArrayList<RestSet.ConditionalSinks>(contract.terminals().size());
        for (var t : contract.terminals()) {
            conditional.add(new RestSet.ConditionalSinks(
                closed.canonical(t.marker()), new LinkedHashSet<>(closed.canonical(t.excused()))));
        }
        return new RestDeclaration(new ArrayList<>(sinks.values()), conditional);
    }

    /**
     * The clause lower bounds' waivers: every designed terminal's marker ([VER-002]).
     *
     * <p>Both routes must waive by the same set in the same order — the graph route reads it
     * through {@link GraphDecision#countViolation} and the encoder through its index order — so
     * it is derived here once rather than at each call site.
     */
    static List<Place<?>> waiverMarkers(OpenNetContract contract, ClosedNet closed) {
        var markers = new ArrayList<Place<?>>(contract.terminals().size());
        for (var t : contract.terminals()) {
            markers.add(closed.canonical(t.marker()));
        }
        return markers;
    }

    /**
     * The places {@code m} strands, marked <b>and</b> unexcused ([VER-014]), by name in
     * {@link CodePointOrder}: the one attribution both routes use ({@link RestSet#strandedPlaces}).
     */
    static List<Place<?>> strandedNames(MarkingState m, RestDeclaration rest) {
        return RestSet.strandedPlaces(m, rest.sinks(), rest.conditional());
    }

    /** The clause's places as the closed net resolves them. */
    static List<Place<?>> clausePlaces(OpenNetContract.CountClause clause, ClosedNet closed) {
        return closed.canonical(clause.places());
    }

    /**
     * What the quiescent marking {@code m} breaks: clauses in contract order, then stranded
     * places by name. Empty when {@code m} meets the contract.
     */
    static List<Finding> quiescenceFindings(
            MarkingState m, OpenNetContract contract, ClosedNet closed, RestDeclaration rest
    ) {
        var findings = new ArrayList<Finding>();
        // The clause is a QuiescentCount with every terminal marker as a waiver ([VER-002]),
        // read through the same predicate the graph routes use for that property.
        var markers = waiverMarkers(contract, closed);
        for (var clause : contract.clauses()) {
            var places = clausePlaces(clause, closed);
            var bound = GraphDecision.countViolation(m, places, clause.min(), clause.max(), markers);
            if (bound != null) {
                findings.add(new ClauseFinding(clause, GraphDecision.tokensAcross(m, places), bound));
            }
        }
        for (var place : strandedNames(m, rest)) {
            findings.add(new StrandedFinding(place.name(), m.tokens(place)));
        }
        return findings;
    }
}
