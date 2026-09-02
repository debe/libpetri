package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Decodes z3's refutation output into replayable counterexample material.
 *
 * <p>There is exactly one decoder: {@link #decodeStateSet}, which collects the ground
 * {@code Reachable} facts of a {@code :produce-proofs} refutation into a SET. The
 * ordered trace a caller sees is reconstructed from that set by
 * {@link AbstractReplayer}; the proof printer's traversal order is not a firing order
 * and was never safe to read as one.
 *
 * <p>Applications with non-ground arguments (rule bodies quantify {@code Reachable}
 * over variables) or the wrong arity are skipped; a malformed proof simply yields a
 * smaller (possibly empty) set, never an exception. Byte-for-byte mirror of the Rust
 * {@code counterexample::decode_state_set}.
 */
public final class CounterexampleDecoder {

    private CounterexampleDecoder() {}

    /**
     * Result of counterexample decoding.
     *
     * @param states the ground {@code Reachable} markings of the proof as an order-free
     *               set (text order preserved for display), what
     *               {@link AbstractReplayer} chains into a firing order
     * @param note   why nothing was decoded ({@code null} when {@code states} is non-empty)
     */
    public record DecodedStates(Set<MarkingState> states, String note) {}

    /** Decodes the states of a z3 reply; a note says so when none were found. */
    public static DecodedStates decode(String answer, FlatNet flatNet) {
        var states = decodeStateSet(answer, flatNet);
        String note = states.isEmpty()
            ? "no ground Reachable states in the z3 proof"
            : null;
        return new DecodedStates(states, note);
    }

    /**
     * Collects the ground {@code Reachable(...)} applications from a z3 refutation
     * proof into a state set, in text order.
     */
    public static Set<MarkingState> decodeStateSet(String answer, FlatNet flatNet) {
        var set = new LinkedHashSet<MarkingState>();
        if (answer == null) {
            return Collections.unmodifiableSet(set);
        }
        int P = flatNet.placeCount();
        for (String head : new String[] {"(Reachable", "(|Reachable|"}) {
            int from = 0;
            while (true) {
                int pos = answer.indexOf(head, from);
                if (pos < 0) {
                    break;
                }
                int start = pos;
                from = start + head.length();
                // Word boundary: "(Reachable" must not match "(ReachableFoo …".
                if (head.equals("(Reachable")) {
                    if (from >= answer.length()) {
                        continue;
                    }
                    char next = answer.charAt(from);
                    if (!Character.isWhitespace(next) && next != ')') {
                        continue;
                    }
                }
                int end = SmtText.sexprEnd(answer, start);
                if (end < 0) {
                    break;
                }
                String inner = answer.substring(start + head.length(), end - 1);
                long[] args = parseGroundIntArgs(inner);
                if (args != null && args.length == P) {
                    set.add(toMarking(args, flatNet));
                }
            }
        }
        return Collections.unmodifiableSet(set);
    }

    private static MarkingState toMarking(long[] args, FlatNet flatNet) {
        var builder = MarkingState.builder();
        for (int i = 0; i < args.length; i++) {
            if (args[i] > 0) {
                builder.tokens(flatNet.places().get(i), (int) Math.min(args[i], Integer.MAX_VALUE));
            }
        }
        return builder.build();
    }

    /**
     * Parses an application's argument text into integers, accepting only GROUND
     * arguments: bare integer literals ({@code 3}, {@code -1}) and the SMT-LIB negation
     * form {@code (- 3)}. Any other token (a bound variable, a nested expression) makes
     * the application non-ground: returns {@code null}.
     */
    static long[] parseGroundIntArgs(String inner) {
        var args = new ArrayList<Long>();
        String rest = inner.stripLeading();
        while (!rest.isEmpty()) {
            if (rest.startsWith("(")) {
                String stripped = rest.substring(1);
                int close = stripped.indexOf(')');
                if (close < 0) {
                    return null;
                }
                String body = stripped.substring(0, close);
                if (body.contains("(")) {
                    return null;
                }
                String trimmed = body.strip();
                if (!trimmed.startsWith("-")) {
                    return null;
                }
                String negated = trimmed.substring(1).strip();
                Long n = parseLong(negated);
                if (n == null) {
                    return null;
                }
                args.add(-n);
                rest = stripped.substring(close + 1).stripLeading();
            } else {
                int tokenEnd = rest.length();
                for (int i = 0; i < rest.length(); i++) {
                    char c = rest.charAt(i);
                    if (Character.isWhitespace(c) || c == '(' || c == ')') {
                        tokenEnd = i;
                        break;
                    }
                }
                Long n = parseLong(rest.substring(0, tokenEnd));
                if (n == null) {
                    return null;
                }
                args.add(n);
                rest = rest.substring(tokenEnd).stripLeading();
            }
        }
        long[] out = new long[args.size()];
        for (int i = 0; i < out.length; i++) {
            out[i] = args.get(i);
        }
        return out;
    }

    private static Long parseLong(String token) {
        try {
            return Long.parseLong(token);
        } catch (NumberFormatException _) {
            return null;
        }
    }

    /** The decoded states as a list, in text order (a report convenience). */
    public static List<MarkingState> asList(Set<MarkingState> states) {
        return List.copyOf(states);
    }
}
