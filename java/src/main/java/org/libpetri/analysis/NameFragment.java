package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Name-correlation fragment classifier for the &nu;-aware state class graph
 * (NU-050, Route B).
 *
 * <p>Identifies the <b>coloured</b> places (the correlated inputs of &nu;-joins)
 * and the role of each transition in the supported mint &rarr; matched-join
 * fragment: a <i>mint</i> produces a freshly-named token into a coloured place,
 * a <i>join</i> consumes one shared name from every correlated input, and
 * everything else is <i>ordinary</i>. {@link #classify} returns {@code null} when
 * the net is not a &nu;-net or falls outside the fragment (a non-match transition
 * consuming a coloured place, or a join re-minting into one); the verifier then
 * falls back to the SMT / Route A path.
 */
public final class NameFragment {

    /** A transition's role w.r.t. the coloured places. */
    public sealed interface Role {
        record Ordinary() implements Role {}
        record Mint() implements Role {}
        /** Correlated inputs (place name &rarr; required per-firing count), sorted by name. */
        record Join(List<Map.Entry<String, Integer>> colouredIn) implements Role {}
    }

    final List<String> colouredOrder;
    private final Set<String> coloured;
    private final Map<String, Role> roles;

    private NameFragment(List<String> colouredOrder, Set<String> coloured, Map<String, Role> roles) {
        this.colouredOrder = colouredOrder;
        this.coloured = coloured;
        this.roles = roles;
    }

    public boolean isColoured(String place) {
        return coloured.contains(place);
    }

    Role role(String transition) {
        return roles.getOrDefault(transition, new Role.Ordinary());
    }

    /**
     * Classifies {@code net}. Returns {@code null} when it is not a &nu;-net or
     * falls outside the supported mint&rarr;matched-join fragment.
     */
    public static NameFragment classify(PetriNet net) {
        var coloured = new TreeSet<String>();
        boolean anyMatch = false;
        for (var t : net.transitions()) {
            if (t.matchSpec() != null) {
                anyMatch = true;
                for (var key : t.matchSpec().keys()) {
                    coloured.add(key.place().name());
                }
            }
        }
        if (!anyMatch || coloured.isEmpty()) {
            return null;
        }

        var roles = new HashMap<String, Role>();
        for (var t : net.transitions()) {
            boolean consumesColoured =
                t.inputSpecs().stream().anyMatch(in -> coloured.contains(in.place().name()));
            boolean producesColoured = false;
            if (t.outputSpec() != null) {
                for (var branch : t.outputSpec().enumerateBranches()) {
                    for (var p : branch) {
                        if (coloured.contains(p.name())) {
                            producesColoured = true;
                        }
                    }
                }
            }

            Role role;
            if (t.matchSpec() != null) {
                if (producesColoured) {
                    return null; // re-mint onto a coloured place — out of fragment
                }
                var colouredIn = new ArrayList<Map.Entry<String, Integer>>();
                for (var key : t.matchSpec().keys()) {
                    var place = key.place().name();
                    // One/Exactly consume a fixed count of the matched name, which
                    // the SCG step removes faithfully. All/AtLeast consume ALL
                    // matching tokens at runtime — the fixed-count step would
                    // under-consume — so drop those to the sound over-approximation.
                    Integer required = fixedRequiredCount(t, place);
                    if (required == null) {
                        return null;
                    }
                    colouredIn.add(Map.entry(place, required));
                }
                colouredIn.sort(Map.Entry.comparingByKey());
                role = new Role.Join(colouredIn);
            } else if (producesColoured) {
                if (consumesColoured) {
                    return null;
                }
                role = new Role.Mint();
            } else {
                if (consumesColoured) {
                    return null;
                }
                role = new Role.Ordinary();
            }
            roles.put(t.name(), role);
        }

        return new NameFragment(new ArrayList<>(coloured), coloured, roles);
    }

    /**
     * The fixed per-firing consumption of the matched name for {@code t}'s input
     * on {@code placeName}, or {@code null} when the cardinality consumes ALL
     * matching tokens (All/AtLeast) or no such input exists — neither of which the
     * fixed-count SCG step can model faithfully.
     */
    private static Integer fixedRequiredCount(Transition t, String placeName) {
        for (var in : t.inputSpecs()) {
            if (in.place().name().equals(placeName)) {
                return switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.All _ -> null;
                    case Arc.In.AtLeast _ -> null;
                };
            }
        }
        return null;
    }
}
