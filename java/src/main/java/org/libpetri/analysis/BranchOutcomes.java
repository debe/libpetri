package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.ToIntFunction;

/**
 * What one firing of a transition can deposit, for every analysis that expands a transition's
 * output spec: the flattener behind the SMT routes, the state-class graph (the enumeration
 * route, [VER-017]), the &nu; name-partition graph (Route B) and everything built on those.
 *
 * <p>A firing ends one of two ways, and they deposit differently:
 * <ul>
 *   <li><b>The action completes</b> and writes a branch of the spec ([IO-015]). A branch is a
 *       set of places and the analyses model one token per place of it ([IO-016]); a
 *       {@code ForwardInput} leaf is then an ordinary claim on its {@code to} place.</li>
 *   <li><b>The action's {@code Timeout} fires</b> ([IO-013]). The marking receives the timeout
 *       child's tokens <em>and nothing else</em> — no sibling of the {@code Timeout} — and a
 *       {@code ForwardInput(from, to)} leaf deposits one token in {@code to} <b>per token the
 *       firing consumed from {@code from}</b> ([IO-014]): {@code n} for {@code Exactly(n)}, the
 *       whole drained batch for {@code All} / {@code AtLeast}.</li>
 * </ul>
 *
 * <p>Every analysis used to read the timeout child as if the action had written it: one token
 * per named place, siblings included. On {@code exactly(2, a) -> xor(c, timeout(50,
 * forwardInput(a, b)))} that deposits one token in {@code b} where the executor deposits two,
 * and {@code placeBound(b, 1)} was proven by the structural and the enumeration routes alike.
 *
 * <p>{@link #outcomes} lists the action outcomes first, in {@link Arc.Out#enumerateBranches()}
 * order — so a flat transition keeps its {@code _b<i>} name and a graph edge its branch index —
 * then the timeout outcome when it differs from every action outcome. It differs exactly when
 * the child forwards a batch that is not one token, or the {@code Timeout} has a sibling in its
 * branch; on every other spec the list is the one the analyses always used.
 *
 * <p>A forward of an {@code All} / {@code AtLeast} input deposits a marking-dependent count
 * ({@link Deposit.Drained}) — a transfer. The graphs resolve it from the marking they fire in,
 * so the state-space enumeration ([VER-017]), the timed state-class graph and Route B decide
 * such a net exactly; the flat encodings cannot express it, so the verifier refuses it on the
 * linear routes only ({@link #drainedForward}).
 */
public final class BranchOutcomes {

    private BranchOutcomes() {}

    /** Tokens one outcome deposits into one place. */
    public sealed interface Deposit {
        /**
         * A fixed count: 1 for a place an action writes ([IO-016]) or a timeout mints,
         * {@code n} for a timeout forward from a {@code One} / {@code Exactly(n)} input
         * ([IO-014]).
         *
         * @param count the tokens deposited
         */
        record Tokens(int count) implements Deposit {}

        /**
         * A timeout forward from an {@code All} / {@code AtLeast} input: every token the firing
         * drained from {@code from} ([IO-014]), which depends on the marking it fires in.
         *
         * @param from the drained input place
         */
        record Drained(Place<?> from) implements Deposit {}
    }

    /**
     * One way a firing of a transition can end: the places it deposits into, each once, in the
     * order the spec declares them. Equality ignores that order.
     *
     * @param deposits each place this outcome deposits into, with how many tokens (read-only)
     */
    public record Outcome(Map<Place<?>, Deposit> deposits) {

        /** The outcome of a transition with no output spec: nothing is deposited. */
        public static final Outcome EMPTY = new Outcome(Map.of());

        /**
         * The places this outcome deposits into, in declaration order: the &nu; name layer reads
         * which places receive a token, and rejects from its fragment a coloured place that
         * receives any count but one.
         *
         * @return the places (read-only)
         */
        public Set<Place<?>> places() {
            return deposits.keySet();
        }

        /**
         * The count this outcome deposits into {@code place}, with a {@code Drained} forward
         * resolved by {@code drained}.
         *
         * @param deposit the deposit to resolve
         * @param drained the tokens drained from a place
         * @return the tokens deposited
         */
        public static int resolve(Deposit deposit, ToIntFunction<Place<?>> drained) {
            return switch (deposit) {
                case Deposit.Tokens t -> t.count();
                case Deposit.Drained d -> drained.applyAsInt(d.from());
            };
        }
    }

    /**
     * The ways one firing of {@code t} can deposit (class docs). Never empty: a transition with
     * no output spec has the one empty outcome.
     *
     * @param t the transition
     * @return the outcomes, action branches first
     */
    public static List<Outcome> outcomes(Transition t) {
        var out = t.outputSpec();
        if (out == null) {
            return List.of(Outcome.EMPTY);
        }
        var result = new ArrayList<Outcome>();
        for (var branch : out.enumerateBranches()) {
            var deposits = new LinkedHashMap<Place<?>, Deposit>();
            for (var p : branch) {
                deposits.put(p, new Deposit.Tokens(1));
            }
            result.add(outcome(deposits));
        }
        if (result.isEmpty()) {
            result.add(Outcome.EMPTY);
        }
        // The executor takes the first Timeout of the spec ([IO-013]), and so do we.
        var timeout = t.actionTimeout();
        if (timeout != null) {
            for (var deposits : timeoutDeposits(timeout.child(), t)) {
                var o = outcome(deposits);
                if (!result.contains(o)) {
                    result.add(o);
                }
            }
        }
        return List.copyOf(result);
    }

    /**
     * Where a token the executor writes on timeout comes from ([IO-013], [IO-014]). The action
     * writes nothing on that path, so the value is fixed by the spec alone.
     *
     * @param to   the place written
     * @param from the input a {@code ForwardInput} leaf copies (values unchanged, so each token
     *             keeps the name it had there), or {@code null} for an {@code Out.Place} leaf, whose
     *             unit token has no value and so no ν name
     */
    public record TimeoutWrite(String to, String from) {}

    /**
     * Every place the first {@code Timeout} of {@code t}'s output spec writes into, with where
     * the token comes from. Empty when the spec has no {@code Timeout}. The ν analyses read this
     * to tell a timeout deposit, which the executor makes by copying or by writing a unit token,
     * from an action write, which the ν contracts cover ([NU-010], [NU-051]).
     *
     * @param t the transition
     * @return the timeout writes, in spec order
     */
    public static List<TimeoutWrite> timeoutWrites(Transition t) {
        var timeout = t.actionTimeout();
        var acc = new ArrayList<TimeoutWrite>();
        if (timeout != null) {
            collectTimeoutWrites(timeout.child(), acc);
        }
        return List.copyOf(acc);
    }

    private static void collectTimeoutWrites(Arc.Out out, List<TimeoutWrite> acc) {
        switch (out) {
            case Arc.Out.Place p -> acc.add(new TimeoutWrite(p.place().name(), null));
            case Arc.Out.ForwardInput f -> acc.add(new TimeoutWrite(f.to().name(), f.from().name()));
            case Arc.Out.Timeout inner -> collectTimeoutWrites(inner.child(), acc);
            case Arc.Out.Xor x -> x.children().forEach(c -> collectTimeoutWrites(c, acc));
            case Arc.Out.And a -> a.children().forEach(c -> collectTimeoutWrites(c, acc));
        }
    }

    private static Outcome outcome(LinkedHashMap<Place<?>, Deposit> deposits) {
        return new Outcome(Collections.unmodifiableMap(deposits));
    }

    /**
     * The deposits of a {@code Timeout} child, one map per branch of it. The executors reject a
     * {@code Xor} under a {@code Timeout} when it fires; reading it as alternatives here keeps
     * the enumeration total.
     */
    private static List<LinkedHashMap<Place<?>, Deposit>> timeoutDeposits(Arc.Out out, Transition t) {
        return switch (out) {
            case Arc.Out.Place p -> {
                var m = new LinkedHashMap<Place<?>, Deposit>();
                m.put(p.place(), new Deposit.Tokens(1));
                yield List.of(m);
            }
            case Arc.Out.ForwardInput f -> {
                var m = new LinkedHashMap<Place<?>, Deposit>();
                var deposit = forwardDeposit(t, f.from());
                if (!deposit.equals(new Deposit.Tokens(0))) {
                    m.put(f.to(), deposit);
                }
                yield List.of(m);
            }
            case Arc.Out.Timeout inner -> timeoutDeposits(inner.child(), t);
            case Arc.Out.Xor x -> {
                var all = new ArrayList<LinkedHashMap<Place<?>, Deposit>>();
                for (var c : x.children()) {
                    all.addAll(timeoutDeposits(c, t));
                }
                yield all;
            }
            case Arc.Out.And a -> {
                List<LinkedHashMap<Place<?>, Deposit>> acc = List.of(new LinkedHashMap<>());
                for (var child : a.children()) {
                    var next = timeoutDeposits(child, t);
                    var merged = new ArrayList<LinkedHashMap<Place<?>, Deposit>>();
                    for (var left : acc) {
                        for (var right : next) {
                            var m = new LinkedHashMap<>(left);
                            for (var e : right.entrySet()) {
                                // A place twice in one branch is rejected at build ([IO-011]);
                                // summing keeps this total regardless.
                                m.merge(e.getKey(), e.getValue(), (x, y) ->
                                    x instanceof Deposit.Tokens(int xa) && y instanceof Deposit.Tokens(int ya)
                                        ? new Deposit.Tokens(xa + ya) : y);
                            }
                            merged.add(m);
                        }
                    }
                    acc = merged;
                }
                yield acc;
            }
        };
    }

    /**
     * What a timeout forward from {@code from} deposits ([IO-014]): one token per token the
     * firing consumed from {@code from}. A place that is not an input of {@code t} (the builder
     * rejects it) consumes nothing and forwards nothing.
     */
    private static Deposit forwardDeposit(Transition t, Place<?> from) {
        for (var in : t.inputSpecs()) {
            if (!in.place().name().equals(from.name())) continue;
            return switch (in) {
                case Arc.In.One _, Arc.In.Exactly _ -> new Deposit.Tokens(in.requiredCount());
                case Arc.In.All _, Arc.In.AtLeast _ -> new Deposit.Drained(in.place());
            };
        }
        return new Deposit.Tokens(0);
    }

    /**
     * A timeout forward whose count the flat encodings cannot express ({@link #drainedForward}).
     *
     * @param transition the transition declaring it
     * @param from       the drained input place ({@code All} / {@code AtLeast})
     * @param to         the place it forwards to
     */
    public record DrainedForward(String transition, String from, String to) {
        /**
         * The {@code Unknown} reason the verifier gives for this net ([VER-003]).
         *
         * @return the reason
         */
        public String reason() {
            return "transition '" + transition + "' forwards its All/AtLeast input '" + from
                + "' to '" + to + "' on timeout, which deposits one token per token drained "
                + "(IO-014), a marking-dependent count the flat encodings cannot express; "
                + "refusing to certify on the linear routes (the state-space graphs decide it "
                + "exactly: VER-017 enumeration, Route B)";
        }
    }

    /**
     * The first timeout forward, in transition order, from an {@code All} / {@code AtLeast}
     * input: its deposit is the drained batch ({@link Deposit.Drained}), a transfer the
     * incidence-matrix analyses (P-invariants, the linear bound, the state equation, the firing
     * bound, the CHC transition rule, Route A) have no column for. The verifier lets the graph
     * routes decide such a net and refuses it before the first linear route.
     *
     * @param net the net
     * @return the first drained forward, if any
     */
    public static Optional<DrainedForward> drainedForward(PetriNet net) {
        for (var t : net.transitions()) {
            for (var o : outcomes(t)) {
                for (var e : o.deposits().entrySet()) {
                    if (e.getValue() instanceof Deposit.Drained d) {
                        return Optional.of(new DrainedForward(t.name(), d.from().name(), e.getKey().name()));
                    }
                }
            }
        }
        return Optional.empty();
    }
}
