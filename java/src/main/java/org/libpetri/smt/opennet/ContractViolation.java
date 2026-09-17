package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.OptionalInt;

/**
 * One broken part of the contract, with a firing sequence that breaks it ([VER-022]).
 *
 * @param kind        which part of the contract is broken
 * @param subject     the clause's name, a stranded place's name, or {@code termination}. The two
 *                    routes attribute a stranding differently: the graph route reports one
 *                    violation per stranded place, the SMT route one violation for the whole
 *                    query, naming every place its witness strands as a comma-separated list
 * @param detail      what was found, in words
 * @param transitions the firing sequence from the initial marking, environment transitions included
 * @param markings    the marking before the first firing and after each one, when the route has
 *                    them in order
 * @param cycleStart  for {@link Kind#TERMINATION}, the index into {@code transitions} where the
 *                    repeating cycle starts; empty otherwise
 * @param portTrace   the firings of {@code transitions} that touch the boundary
 * @param confirmed   whether {@code transitions} is a real firing sequence in order. Always on
 *                    the graph route; on the SMT route it is the counterexample replay's outcome
 *                    ([VER-003])
 */
public record ContractViolation(
    Kind kind,
    String subject,
    String detail,
    List<String> transitions,
    List<MarkingState> markings,
    OptionalInt cycleStart,
    List<PortStep> portTrace,
    boolean confirmed
) {

    public ContractViolation {
        transitions = List.copyOf(transitions);
        markings = List.copyOf(markings);
        portTrace = List.copyOf(portTrace);
    }

    /** Which part of the contract a violation breaks. */
    public enum Kind {
        /** A count clause: too few tokens across its places at quiescence with no terminal marked, or too many. */
        CLAUSE("clause"),
        /** A token rests where the contract lets none rest: on an internal place, or on one only an unmarked terminal excuses. */
        STRANDED("stranded"),
        /** A run that never comes to rest: a reachable cycle. */
        TERMINATION("termination");

        private final String label;

        Kind(String label) {
            this.label = label;
        }

        /** {@code clause}, {@code stranded} or {@code termination}, as the report prints it. */
        public String label() {
            return label;
        }
    }

    /**
     * A token-count change on one contract place.
     *
     * @param place the place's name
     * @param delta tokens after the firing minus tokens before; never {@code 0}
     */
    public record PortChange(String place, int delta) {}

    /**
     * A firing that touches the subnet's boundary: an environment step, or a change on a
     * contract place.
     *
     * @param step        the firing's position in {@link ContractViolation#transitions()},
     *                    counting from 1
     * @param transition  the firing's transition name
     * @param environment set when the environment fired it: {@code ARRIVAL} or {@code DECLINE}
     *                    for an arrival group, {@code TRANSITION} for one of the contract's
     *                    environment transitions; {@code null} for the subnet
     * @param changes     token changes on the contract's places, in the contract's order
     */
    public record PortStep(int step, String transition, EnvironmentStep.Kind environment, List<PortChange> changes) {
        public PortStep {
            changes = List.copyOf(changes);
        }
    }

    /** A violation as a route finds it, before its port trace is read off. */
    record Witness(
        Kind kind,
        String subject,
        String detail,
        List<String> transitions,
        List<MarkingState> markings,
        OptionalInt cycleStart,
        boolean confirmed
    ) {}

    /**
     * A violation with its port trace, read off consecutive markings of the witness. Without
     * one marking per firing plus the initial one there is nothing to read the changes off, so
     * the trace is empty rather than guessed.
     *
     * @param tracedPlaces the places whose changes the trace reports, as the closed net
     *                     resolves them ({@link ClosedNet#canonical})
     */
    static ContractViolation of(ClosedNet closed, List<Place<?>> tracedPlaces, Witness w) {
        var portTrace = new ArrayList<PortStep>();
        var transitions = w.transitions();
        var markings = w.markings();
        if (markings.size() == transitions.size() + 1) {
            for (int i = 0; i < transitions.size(); i++) {
                var before = markings.get(i);
                var after = markings.get(i + 1);
                var changes = new ArrayList<PortChange>();
                for (var p : tracedPlaces) {
                    int delta = after.tokens(p) - before.tokens(p);
                    if (delta != 0) {
                        changes.add(new PortChange(p.name(), delta));
                    }
                }
                var env = closed.environment().get(transitions.get(i));
                if (!changes.isEmpty() || env != null) {
                    portTrace.add(new PortStep(i + 1, transitions.get(i), env == null ? null : env.kind(), changes));
                }
            }
        }
        return new ContractViolation(
            w.kind(), w.subject(), w.detail(), transitions, markings, w.cycleStart(), portTrace, w.confirmed());
    }
}
