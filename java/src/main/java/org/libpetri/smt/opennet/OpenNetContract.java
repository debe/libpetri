package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.function.Consumer;

/**
 * A subnet's contract: the environment it assumes and what it guarantees at quiescence
 * ([VER-022]). Build one with {@link #builder()}; check it with
 * {@link OpenNetVerifier#verifyOpenNet}.
 *
 * <p>The <b>assumption</b> half says what the environment does: which tokens the subnet
 * holds before anything arrives, and the arrival groups, each delivering between
 * {@code min} and {@code max} tokens onto its places at any point of the run. Every bound is
 * finite. A bound is both the runtime cap and the width of the claim, so an environment that
 * delivers without limit is not something a contract can assume.
 *
 * <p>The <b>guarantee</b> half says what every quiescent marking holds: the count clauses,
 * the rest places, and the designed terminals under which a run may stop short. A place the
 * contract does not name is internal to the subnet and must be empty at quiescence. Every
 * run must also come to rest, unless {@link Builder#requireTermination} is turned off.
 *
 * <pre>{@code
 * var contract = OpenNetContract.builder()
 *     .initialTokens(idle, 1)
 *     .initialTokens(budget, k)
 *     .arrive(1, inData, inEmpty)          // exactly one arrival on the input edge
 *     .arriveAtMost(1, halt)               // never or once
 *     .expect("e3", 1, e3Data, e3Empty)    // one of data / empty per outgoing edge, once it runs
 *     .expect("idle", 1, idle)
 *     .expect("budget", k, budget)
 *     .expect("history", 1, done, skipped)
 *     .terminal(halt, inData, inEmpty)     // a halted run leaves the arrival where it was delivered
 *     .terminal(skipped)                   // a skipped run writes no output edge at all
 *     .build();
 * }</pre>
 *
 * <p><b>A node that can skip needs its edge clauses conditional.</b> {@code expect("e3", 1, …)}
 * alone says every quiescent marking writes that edge exactly once, which a node that
 * legitimately skips does not: it comes to rest having written the edge zero times, and the
 * clause reports it. Whether that is a defect or a design is the contract's to say, so name
 * the place that marks a skip as a {@link Builder#terminal terminal}. That waives the clauses'
 * lower bounds while it is marked and leaves every upper bound in force, so a run that writes
 * an edge twice is still caught.
 *
 * <p><b>A subnet that asks something of its neighbours needs an environment.</b> Verified
 * alone, a node that dispatches a request and waits has nobody to answer it: it quiesces with
 * the request outstanding, which is correct for an open net whose environment does nothing
 * and rarely what was meant. Give the contract the transitions the neighbours would fire
 * ({@link Builder#environment}), and their own places stay theirs — never counted as the
 * subnet stranding a token. An environment transition is never executed, so it needs no
 * action.
 *
 * <p><b>Places are keyed by name</b>, as the TypeScript reference keys them. Java's
 * {@link Place} equality is structural on name <em>and</em> token type, so two places with
 * one name and different token types are one place to the contract, and the closure resolves
 * each to the net's own place of that name ({@link OpenNetClosure#closeOpenNet}).
 */
public final class OpenNetContract {

    /**
     * The environment delivers between {@code min} and {@code max} tokens in total, each onto
     * one of {@code places}, each at any point of the run.
     *
     * @param places the places a token may arrive on, distinct by name, in declaration order
     * @param min    the tokens the environment must deliver
     * @param max    the tokens it may deliver at most; never below {@code min}, at least 1
     */
    public record ArrivalGroup(List<Place<?>> places, int min, int max) {
        public ArrivalGroup {
            places = List.copyOf(places);
        }
    }

    /**
     * At every quiescent marking the tokens across {@code places} number between {@code min}
     * and {@code max} (empty is unbounded). A marked designed terminal waives {@code min},
     * never {@code max}: a halt stops progress, it does not license a token too many.
     *
     * @param name   the clause's name, unique within the contract; a violation's subject
     * @param places the places the count is taken across, distinct by name
     * @param min    the least count, waived while a terminal marker is marked
     * @param max    the most, never waived; empty when unbounded
     */
    public record CountClause(String name, List<Place<?>> places, int min, OptionalInt max) {
        public CountClause {
            places = List.copyOf(places);
        }
    }

    /**
     * While {@code marker} holds a token, the clauses' lower bounds are waived and tokens may
     * rest on {@code excused}: the places where the work the marker interrupted was delivered.
     * The marker itself may always rest, as a conditional-sink marker may ([VER-014]).
     *
     * @param marker  the designed-terminal marker
     * @param excused the places a token may rest on while the marker is marked, distinct by name
     */
    public record DesignedTerminal(Place<?> marker, List<Place<?>> excused) {
        public DesignedTerminal {
            excused = List.copyOf(excused);
        }
    }

    /**
     * The initial marking's places with their counts, in the order they were first named and
     * distinct by name. {@link #places()} reports first-mention order and the port trace lists
     * changes in it. A {@link MarkingState} keeps that order too, but tells two places with one
     * name and different token types apart, where the reference's marking keeps one.
     */
    private final List<Map.Entry<Place<?>, Integer>> initialTokens;
    private final MarkingState initialMarking;
    private final List<ArrivalGroup> arrivals;
    private final List<CountClause> clauses;
    private final List<Place<?>> rest;
    private final List<DesignedTerminal> terminals;
    private final List<Transition> environment;
    private final boolean requiresTermination;

    private OpenNetContract(Builder b) {
        this.initialTokens = List.copyOf(b.initialTokens.values());
        var marking = MarkingState.builder();
        for (var entry : initialTokens) {
            marking.tokens(entry.getKey(), entry.getValue());
        }
        this.initialMarking = marking.build();
        this.arrivals = List.copyOf(b.arrivals);
        this.clauses = List.copyOf(b.clauses);
        this.rest = List.copyOf(b.rest.values());
        var terminals = new ArrayList<DesignedTerminal>(b.terminals.size());
        for (var t : b.terminals.values()) {
            terminals.add(new DesignedTerminal(t.marker, new ArrayList<>(t.excused.values())));
        }
        this.terminals = List.copyOf(terminals);
        this.environment = List.copyOf(b.environment);
        this.requiresTermination = b.requiresTermination;
    }

    public static Builder builder() {
        return new Builder();
    }

    /**
     * This contract with each of {@code markers} merged in as a designed terminal excusing
     * {@code excused}: the form a net-declared terminal place takes here ([EXEC-042],
     * [VER-014]). A marker the contract already names keeps its position and gains the excuses.
     */
    OpenNetContract withDesignedTerminals(Collection<? extends Place<?>> markers,
                                          Collection<? extends Place<?>> excused) {
        var b = new Builder();
        b.initialTokens.putAll(copyOfInitial());
        b.arrivals.addAll(arrivals);
        b.clauses.addAll(clauses);
        for (var p : rest) {
            b.rest.put(p.name(), p);
        }
        for (var t : terminals) {
            b.terminal(t.marker(), t.excused().toArray(new Place<?>[0]));
        }
        // One rebuild for every marker: O(markers × excused), not a rebuild per marker.
        var excusedArray = excused.toArray(new Place<?>[0]);
        for (var marker : markers) {
            b.terminal(marker, excusedArray);
        }
        b.environment.addAll(environment);
        b.requiresTermination = requiresTermination;
        return new OpenNetContract(b);
    }

    private Map<String, Map.Entry<Place<?>, Integer>> copyOfInitial() {
        var out = new LinkedHashMap<String, Map.Entry<Place<?>, Integer>>();
        for (var e : initialTokens) {
            out.put(e.getKey().name(), e);
        }
        return out;
    }

    /** Tokens the subnet holds before anything arrives: its own resources and any shared pool it borrows from. */
    public MarkingState initialMarking() {
        return initialMarking;
    }

    public List<ArrivalGroup> arrivals() {
        return arrivals;
    }

    public List<CountClause> clauses() {
        return clauses;
    }

    /** Places that may hold any number of tokens at quiescence. */
    public List<Place<?>> rest() {
        return rest;
    }

    public List<DesignedTerminal> terminals() {
        return terminals;
    }

    /** Transitions the environment fires: neighbours that react to what the subnet sends. */
    public List<Transition> environment() {
        return environment;
    }

    /** Whether every run must come to rest. */
    public boolean requiresTermination() {
        return requiresTermination;
    }

    /**
     * Every place the initial marking, an arrival group, a clause, the rest set or a terminal
     * marker names, then every place an environment transition touches, in first-mention
     * order and distinct by name. A violation's port trace reports the token changes on these
     * places.
     *
     * <p>A terminal's <em>excused</em> places are <b>not</b> included, so a place that only
     * ever appears as an excuse is absent here; {@link OpenNetClosure#closeOpenNet} adds those
     * separately, because every place the contract names has to join the closed net for both
     * routes to resolve it.
     */
    public List<Place<?>> places() {
        var seen = new LinkedHashMap<String, Place<?>>();
        for (var entry : initialTokens) {
            seen.putIfAbsent(entry.getKey().name(), entry.getKey());
        }
        for (var g : arrivals) {
            addAll(seen, g.places());
        }
        for (var c : clauses) {
            addAll(seen, c.places());
        }
        addAll(seen, rest);
        for (var t : terminals) {
            seen.putIfAbsent(t.marker().name(), t.marker());
        }
        for (var t : environment) {
            addAll(seen, transitionPlaces(t));
        }
        return List.copyOf(seen.values());
    }

    /** The contract as the report prints it, one line per part. */
    public List<String> describe() {
        var lines = new ArrayList<String>();
        lines.add("  Initial marking: " + Report.markingText(initialMarking));
        if (arrivals.isEmpty()) {
            lines.add("  Arrivals: none");
        } else {
            var groups = new ArrayList<String>(arrivals.size());
            for (var g : arrivals) {
                groups.add(SmtProperty.countPhrase(g.min(), OptionalInt.of(g.max()))
                    + " onto {" + names(g.places()) + "}");
            }
            lines.add("  Arrivals: " + String.join("; ", groups));
        }
        if (clauses.isEmpty()) {
            lines.add("  At quiescence: no count clauses");
        } else {
            var parts = new ArrayList<String>(clauses.size());
            for (var c : clauses) {
                parts.add(c.name() + " = " + SmtProperty.countAcross(c.min(), c.max(), c.places()));
            }
            lines.add("  At quiescence: " + String.join("; ", parts));
        }
        if (!rest.isEmpty()) {
            lines.add("  Rest: " + names(rest));
        }
        for (var t : terminals) {
            lines.add(t.excused().isEmpty()
                ? "  Terminal: when " + t.marker().name()
                : "  Terminal: when " + t.marker().name() + ": " + names(t.excused()));
        }
        if (!environment.isEmpty()) {
            var transitionNames = new ArrayList<String>(environment.size());
            for (var t : environment) {
                transitionNames.add(t.name());
            }
            lines.add("  Environment transitions: " + String.join(", ", transitionNames));
        }
        lines.add("  Termination: " + (requiresTermination ? "every run comes to rest" : "not required"));
        return List.copyOf(lines);
    }

    /**
     * Every place an arc of {@code t} touches: inputs, reads, inhibitors, resets, then
     * outputs in the order the output spec names them.
     *
     * <p>The order reaches the report through {@link #places()}, so the outputs are read off
     * the spec tree rather than {@link Transition#outputPlaces()}, a set with no order.
     */
    static List<Place<?>> transitionPlaces(Transition t) {
        var places = new ArrayList<Place<?>>();
        for (var in : t.inputSpecs()) {
            places.add(in.place());
        }
        for (var r : t.reads()) {
            places.add(r.place());
        }
        for (var i : t.inhibitors()) {
            places.add(i.place());
        }
        for (var r : t.resets()) {
            places.add(r.place());
        }
        if (t.outputSpec() != null) {
            var outputs = new LinkedHashSet<Place<?>>();
            collectOutputPlaces(t.outputSpec(), outputs);
            places.addAll(outputs);
        }
        return places;
    }

    private static void collectOutputPlaces(Arc.Out out, LinkedHashSet<Place<?>> into) {
        switch (out) {
            case Arc.Out.Place p -> into.add(p.place());
            case Arc.Out.ForwardInput f -> into.add(f.to());
            case Arc.Out.And a -> a.children().forEach(child -> collectOutputPlaces(child, into));
            case Arc.Out.Xor x -> x.children().forEach(child -> collectOutputPlaces(child, into));
            case Arc.Out.Timeout t -> collectOutputPlaces(t.child(), into);
        }
    }

    private static void addAll(Map<String, Place<?>> seen, Collection<? extends Place<?>> places) {
        for (var p : places) {
            seen.putIfAbsent(p.name(), p);
        }
    }

    private static String names(Collection<? extends Place<?>> places) {
        var out = new ArrayList<String>(places.size());
        for (var p : places) {
            out.add(p.name());
        }
        return String.join(", ", out);
    }

    /**
     * Builds an {@link OpenNetContract}. Every method validates as it goes and throws
     * {@link IllegalArgumentException} on a contract that cannot mean anything, with the
     * message the TypeScript reference throws: a malformed contract is the caller's error,
     * reported where it is built rather than as a verdict about the net.
     */
    public static final class Builder {
        private final LinkedHashMap<String, Map.Entry<Place<?>, Integer>> initialTokens = new LinkedHashMap<>();
        private final List<ArrivalGroup> arrivals = new ArrayList<>();
        private final List<CountClause> clauses = new ArrayList<>();
        private final LinkedHashMap<String, Place<?>> rest = new LinkedHashMap<>();
        private final LinkedHashMap<String, TerminalEntry> terminals = new LinkedHashMap<>();
        private final List<Transition> environment = new ArrayList<>();
        private boolean requiresTermination = true;

        private static final class TerminalEntry {
            final Place<?> marker;
            final LinkedHashMap<String, Place<?>> excused = new LinkedHashMap<>();

            TerminalEntry(Place<?> marker) {
                this.marker = marker;
            }
        }

        private Builder() {}

        /**
         * Replaces the tokens the subnet holds before anything arrives with {@code marking}.
         *
         * <p>Its places are taken in the order its builder first saw them
         * ({@link MarkingState#placesWithTokens()}), as the TypeScript reference takes them, and
         * that order reaches the port trace.
         */
        public Builder initialMarking(MarkingState marking) {
            initialTokens.clear();
            for (var p : marking.placesWithTokens()) {
                initialTokens(p, marking.tokens(p));
            }
            return this;
        }

        /** {@link #initialMarking(MarkingState)} for the marking {@code configurator} builds. */
        public Builder initialMarking(Consumer<MarkingState.Builder> configurator) {
            var builder = MarkingState.builder();
            configurator.accept(builder);
            return initialMarking(builder.build());
        }

        /**
         * Sets the tokens {@code place} holds before anything arrives; {@code 0} removes it. A
         * place set again keeps the position it was first named at, as the reference's marking
         * builder does, so the order of these calls is the port trace's order.
         *
         * @throws IllegalArgumentException when {@code count} is negative
         */
        public Builder initialTokens(Place<?> place, int count) {
            if (count < 0) {
                throw new IllegalArgumentException("Token count cannot be negative: " + count);
            }
            if (count == 0) {
                initialTokens.remove(place.name());
            } else {
                initialTokens.put(place.name(), Map.entry(place, count));
            }
            return this;
        }

        /** The environment delivers exactly {@code count} tokens, each onto one of {@code places}, at any point of the run. */
        public Builder arrive(int count, Place<?>... places) {
            return arriveBetween(count, count, places);
        }

        /** The environment delivers at most {@code max} tokens, possibly none. {@code arriveAtMost(1, halt)} is "never or once". */
        public Builder arriveAtMost(int max, Place<?>... places) {
            return arriveBetween(0, max, places);
        }

        /**
         * The environment delivers between {@code min} and {@code max} tokens in total, each
         * onto one of {@code places}, at any point of the run.
         *
         * @throws IllegalArgumentException when {@code min} is negative, {@code max < min},
         *     {@code max} is {@code 0}, or {@code places} is empty
         */
        public Builder arriveBetween(int min, int max, Place<?>... places) {
            if (min < 0 || max < min || max < 1) {
                throw new IllegalArgumentException(
                    "OpenNetContract: an arrival group needs whole bounds with 0 <= min <= max and max >= 1, "
                    + "got " + min + ".." + max + ". A bound is both the runtime cap and the width of the claim, "
                    + "so it is finite.");
            }
            arrivals.add(new ArrivalGroup(distinct(places, "an arrival group"), min, max));
            return this;
        }

        /** At every quiescent marking, exactly {@code count} tokens across {@code places}. */
        public Builder expect(String name, int count, Place<?>... places) {
            return expectBetween(name, count, OptionalInt.of(count), places);
        }

        /** At every quiescent marking, between {@code min} and {@code max} tokens across {@code places}. */
        public Builder expectBetween(String name, int min, int max, Place<?>... places) {
            return expectBetween(name, min, OptionalInt.of(max), places);
        }

        /**
         * At every quiescent marking, between {@code min} and {@code max} tokens across
         * {@code places}; an empty {@code max} is unbounded.
         *
         * @throws IllegalArgumentException when {@code name} is empty or already taken, when
         *     {@code min} is negative or {@code max < min}, or when {@code places} is empty
         */
        public Builder expectBetween(String name, int min, OptionalInt max, Place<?>... places) {
            if (name.isEmpty()) {
                throw new IllegalArgumentException("OpenNetContract: a clause needs a name");
            }
            for (var c : clauses) {
                if (c.name().equals(name)) {
                    throw new IllegalArgumentException("OpenNetContract: duplicate clause name '" + name + "'");
                }
            }
            if (min < 0 || (max.isPresent() && max.getAsInt() < min)) {
                throw new IllegalArgumentException("OpenNetContract: clause '" + name
                    + "' needs whole bounds with 0 <= min <= max, got " + min + ".."
                    // The reference's unbounded max is `Infinity`, and the message prints it.
                    + (max.isPresent() ? Integer.toString(max.getAsInt()) : "Infinity"));
            }
            clauses.add(new CountClause(name, distinct(places, "clause '" + name + "'"), min, max));
            return this;
        }

        /** Places that may hold any number of tokens at quiescence. */
        public Builder rest(Place<?>... places) {
            for (var p : places) {
                rest.putIfAbsent(p.name(), p);
            }
            return this;
        }

        /**
         * A designed terminal: while {@code marker} holds a token, lower bounds are waived and
         * tokens may rest on {@code excused}. Repeated calls for one marker accumulate.
         */
        public Builder terminal(Place<?> marker, Place<?>... excused) {
            var entry = terminals.computeIfAbsent(marker.name(), _ -> new TerminalEntry(marker));
            for (var p : excused) {
                entry.excused.putIfAbsent(p.name(), p);
            }
            return this;
        }

        /**
         * Transitions the environment fires: a neighbour that reacts to what the subnet sends,
         * such as a tool that answers a request, or a loop body that sends an item back at most
         * as often as a budget of its own allows. An arrival group cannot say that, because its
         * tokens do not wait for a request.
         *
         * <p>They join the closed net unchanged but for their arcs, which resolve to the net's
         * places by name as every contract place does, and their firings are marked as
         * environment steps in the port trace. A place only they touch belongs to the
         * environment: it may hold tokens at quiescence, and the internal-place check never
         * reports it. A place they share with the subnet is a port and is judged like any other.
         * Their actions never run, so one that declares outputs may keep {@code passthrough()}.
         *
         * @throws IllegalArgumentException when a transition's name is already one of the
         *     contract's environment transitions
         */
        public Builder environment(Transition... transitions) {
            for (var t : transitions) {
                for (var e : environment) {
                    if (e.name().equals(t.name())) {
                        throw new IllegalArgumentException(
                            "OpenNetContract: duplicate environment transition '" + t.name() + "'");
                    }
                }
                environment.add(t);
            }
            return this;
        }

        /** Whether every run must come to rest (default {@code true}). */
        public Builder requireTermination(boolean required) {
            this.requiresTermination = required;
            return this;
        }

        public OpenNetContract build() {
            return new OpenNetContract(this);
        }

        /**
         * {@code places} without repeats by name, in the order given.
         *
         * @throws IllegalArgumentException when {@code places} is empty: a group or clause over
         *     nothing is a contract that says nothing
         */
        private static List<Place<?>> distinct(Place<?>[] places, String what) {
            if (places.length == 0) {
                throw new IllegalArgumentException("OpenNetContract: " + what + " names no place");
            }
            var byName = new LinkedHashMap<String, Place<?>>();
            for (var p : places) {
                byName.putIfAbsent(p.name(), p);
            }
            return List.copyOf(byName.values());
        }
    }
}
