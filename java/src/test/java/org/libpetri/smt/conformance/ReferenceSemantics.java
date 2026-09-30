package org.libpetri.smt.conformance;

import org.libpetri.smt.conformance.ConformanceNet.InSpec;
import org.libpetri.smt.conformance.ConformanceNet.OutSpec;
import org.libpetri.smt.conformance.ConformanceNet.PropSpec;
import org.libpetri.smt.conformance.ConformanceNet.TSpec;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Pattern;

/**
 * The corpus README's reference firing rule, written here from the spec and sharing no code with
 * the verifier: it replays a language's counterexample (conformance rule 3).
 *
 * <p>Untimed and priority-blind ([VER-004]). A firing consumes its inputs ([IO-001]..[IO-004]:
 * {@code all} / {@code atLeast} drain the place), clears its reset places ([CORE-034]), then
 * deposits one of its outcomes:
 * <ul>
 *   <li><b>the action completes</b>: one claim of the output tree ([IO-015]) — {@code and} the
 *       product of its children, {@code xor} their union, {@code timeout} its child's claim, a
 *       {@code forward} claims {@code to} — with one token per claimed place ([IO-016]);</li>
 *   <li><b>a {@code timeout} fires</b> ([IO-013] AC5): that timeout's child and nothing else, a
 *       {@code forward} depositing one token per token consumed from {@code from} ([IO-014]).</li>
 * </ul>
 * This is the rule of {@code rust/libpetri-verification/tests/route_agreement.rs}.
 *
 * <p>A marking is a sorted map holding only its marked places, so equal markings are equal maps.
 */
public final class ReferenceSemantics {

    private ReferenceSemantics() {}

    private static final Pattern BRANCH_SUFFIX = Pattern.compile("^(.*)_b\\d+$");

    static Map<String, Integer> normalise(Map<String, Integer> m) {
        var out = new TreeMap<String, Integer>();
        m.forEach((k, v) -> {
            if (v != null && v > 0) {
                out.put(k, v);
            }
        });
        return out;
    }

    static int count(Map<String, Integer> m, String place) {
        return m.getOrDefault(place, 0);
    }

    static boolean enabled(TSpec t, Map<String, Integer> m) {
        for (InSpec in : t.inputs()) {
            if (count(m, in.place()) < in.required()) {
                return false;
            }
        }
        for (String r : t.reads()) {
            if (count(m, r) < 1) {
                return false;
            }
        }
        for (String i : t.inhibitors()) {
            if (count(m, i) != 0) {
                return false;
            }
        }
        return true;
    }

    /** One leaf of an output alternative: a place, or a forward carrying its multiplicity. */
    private record Leaf(String place, String forwardFrom) {}

    /**
     * The claims of {@code o}. {@code timedOut} selects the timeout outcome's deposit, where a
     * forward carries the consumed multiplicity; otherwise a forward is one token in {@code to}.
     */
    private static List<List<Leaf>> alternatives(OutSpec o, boolean timedOut) {
        return switch (o) {
            case null -> List.of(List.of());
            case OutSpec.PlaceOut p -> List.of(List.of(new Leaf(p.place(), null)));
            case OutSpec.ForwardOut f -> List.of(List.of(new Leaf(f.to(), timedOut ? f.from() : null)));
            case OutSpec.TimeoutOut t -> alternatives(t.child(), timedOut);
            case OutSpec.XorOut x -> {
                var acc = new ArrayList<List<Leaf>>();
                x.children().forEach(c -> acc.addAll(alternatives(c, timedOut)));
                yield acc;
            }
            case OutSpec.AndOut a -> {
                List<List<Leaf>> acc = List.of(List.of());
                for (OutSpec c : a.children()) {
                    var next = new ArrayList<List<Leaf>>();
                    for (var left : acc) {
                        for (var right : alternatives(c, timedOut)) {
                            var joined = new ArrayList<>(left);
                            joined.addAll(right);
                            next.add(joined);
                        }
                    }
                    acc = next;
                }
                yield acc;
            }
        };
    }

    /** Every {@code timeout} node of an output tree, outermost first. */
    private static void timeouts(OutSpec o, List<OutSpec.TimeoutOut> acc) {
        switch (o) {
            case null -> { }
            case OutSpec.TimeoutOut t -> {
                acc.add(t);
                timeouts(t.child(), acc);
            }
            case OutSpec.AndOut a -> a.children().forEach(c -> timeouts(c, acc));
            case OutSpec.XorOut x -> x.children().forEach(c -> timeouts(c, acc));
            case OutSpec.PlaceOut p -> { }
            case OutSpec.ForwardOut f -> { }
        }
    }

    /** What one firing can deposit: every completion claim, then every timeout outcome. */
    private static List<List<Leaf>> outcomes(OutSpec o) {
        var acc = new ArrayList<>(alternatives(o, false));
        var ts = new ArrayList<OutSpec.TimeoutOut>();
        timeouts(o, ts);
        ts.forEach(t -> acc.addAll(alternatives(t.child(), true)));
        return acc;
    }

    /** Every marking one firing of an enabled {@code t} can produce. */
    static Set<Map<String, Integer>> fire(TSpec t, Map<String, Integer> m) {
        var base = new HashMap<>(m);
        var consumed = new HashMap<String, Integer>();
        for (InSpec in : t.inputs()) {
            int have = count(base, in.place());
            int n = switch (in.kind()) {
                case "one" -> 1;
                case "exactly" -> in.n();
                default -> have; // all, atLeast: drain
            };
            base.put(in.place(), have - n);
            consumed.put(in.place(), n);
        }
        for (String r : t.resets()) {
            base.put(r, 0);
        }
        var out = new LinkedHashSet<Map<String, Integer>>();
        for (var alt : outcomes(t.output())) {
            var next = new HashMap<>(base);
            for (Leaf leaf : alt) {
                int add = leaf.forwardFrom() == null ? 1 : consumed.getOrDefault(leaf.forwardFrom(), 0);
                next.merge(leaf.place(), add, Integer::sum);
            }
            out.add(normalise(next));
        }
        return out;
    }

    /** Reap-quiescent ([VER-002], [TIME-013]): every enabled transition is reapable. */
    static boolean quiescent(ConformanceNet net, Map<String, Integer> m) {
        return net.transitions().stream().noneMatch(t -> !t.reapable() && enabled(t, m));
    }

    /** The property's bad-state predicate ([VER-002]). */
    static boolean bad(ConformanceNet net, PropSpec p, Map<String, Integer> m) {
        return switch (p.type()) {
            case "deadlock-free" -> quiescent(net, m)
                && m.entrySet().stream().anyMatch(e -> e.getValue() > 0 && !p.sinks().contains(e.getKey()));
            case "terminates-at-sink" -> quiescent(net, m) && p.sinks().stream().noneMatch(s -> count(m, s) > 0);
            case "place-bound" -> count(m, p.place()) > p.bound();
            case "mutual-exclusion" -> p.places().stream().filter(s -> count(m, s) > 0).count() >= 2;
            case "unreachable" -> p.places().stream().allMatch(s -> count(m, s) > 0);
            case "quiescent-count" -> {
                if (!quiescent(net, m)) {
                    yield false;
                }
                int sum = new LinkedHashSet<>(p.places()).stream().mapToInt(s -> count(m, s)).sum();
                yield sum < p.min() || (p.max() != null && sum > p.max());
            }
            default -> throw new IllegalStateException(p.type());
        };
    }

    /**
     * A language's transition name with a flattener branch suffix ({@code t_b1}) removed, but
     * only when the net has no transition by the full name and does have one by the stripped name.
     */
    static String strip(ConformanceNet net, String name) {
        if (find(net, name) != null) {
            return name;
        }
        var m = BRANCH_SUFFIX.matcher(name);
        if (m.matches() && find(net, m.group(1)) != null) {
            return m.group(1);
        }
        return name;
    }

    private static TSpec find(ConformanceNet net, String name) {
        for (TSpec t : net.transitions()) {
            if (t.name().equals(name)) {
                return t;
            }
        }
        return null;
    }

    /**
     * Replays a firing sequence from the initial marking. Every step must be enabled in some
     * state the prefix can reach; the sequence replays iff some final state violates {@code p}.
     *
     * @return empty when the trace replays, else why not
     */
    static Optional<String> replay(ConformanceNet net, PropSpec p, List<String> names) {
        Set<Map<String, Integer>> states = Set.of(normalise(net.marking()));
        for (int step = 0; step < names.size(); step++) {
            String name = strip(net, names.get(step));
            TSpec t = find(net, name);
            if (t == null) {
                return Optional.of("step " + step + ": unknown transition '" + names.get(step) + "'");
            }
            var next = new LinkedHashSet<Map<String, Integer>>();
            for (var s : states) {
                if (enabled(t, s)) {
                    next.addAll(fire(t, s));
                }
            }
            if (next.isEmpty()) {
                return Optional.of("step " + step + ": '" + name + "' is not enabled in " + states);
            }
            states = next;
        }
        for (var s : states) {
            if (bad(net, p, s)) {
                return Optional.empty();
            }
        }
        return Optional.of("no final state of " + names + " violates " + p.id() + " (" + p.type()
            + "); final states " + states);
    }
}
