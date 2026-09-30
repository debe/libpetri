package org.libpetri.smt.encoding;

import org.libpetri.analysis.BranchOutcomes;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;
import org.libpetri.smt.Reaping;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Flattens a {@link PetriNet} into a {@link FlatNet} suitable for SMT encoding.
 *
 * <p>Flattening involves:
 * <ol>
 *   <li>Assigning each place a stable integer index (sorted by name)</li>
 *   <li>Expanding every way a firing can end ({@link BranchOutcomes#outcomes}: each XOR
 *       branch, and a timeout that deposits differently) into its own flat transition</li>
 *   <li>Building pre/post vectors from input/output specs</li>
 *   <li>Recording inhibitor, read, and reset arcs</li>
 *   <li>Setting environment bounds for bounded analysis mode</li>
 * </ol>
 */
public final class NetFlattener {

    private NetFlattener() {}

    /**
     * Every place the net mentions, in a stable insertion order: {@link PetriNet#places()}
     * plus the places declared only by an arc — the builder auto-adds input, output,
     * inhibitor and read places, but a reset arc's place reaches the net only through the
     * transition, so {@code net.places()} alone under-reports.
     *
     * <p>This is the set {@link #flatten} indexes, exposed so a caller that has not
     * flattened yet can ask whether a place resolves in the net — {@code SmtVerifier}
     * reads it to refuse a property over an undeclared place before it picks a route.
     *
     * @param net the net to read
     * @return every declared place, insertion-ordered
     */
    public static LinkedHashSet<Place<?>> declaredPlaces(PetriNet net) {
        var allPlaces = new LinkedHashSet<Place<?>>(net.places());
        for (var t : net.transitions()) {
            for (var in : t.inputSpecs()) {
                allPlaces.add(in.place());
            }
            if (t.outputSpec() != null) {
                allPlaces.addAll(t.outputSpec().allPlaces());
            }
            t.inhibitors().forEach(arc -> allPlaces.add(arc.place()));
            t.reads().forEach(arc -> allPlaces.add(arc.place()));
            t.resets().forEach(arc -> allPlaces.add(arc.place()));
        }
        return allPlaces;
    }

    /**
     * Flattens a PetriNet into a FlatNet.
     *
     * @param net              the Petri net to flatten
     * @param environmentPlaces environment places for reactive analysis
     * @param environmentMode  how to treat environment places
     * @return the flattened net
     */
    public static FlatNet flatten(
            PetriNet net,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        return flatten(net, environmentPlaces, environmentMode, t -> Reaping.isReapable(t.timing()));
    }

    /**
     * {@link #flatten(PetriNet, Set, EnvironmentAnalysisMode)} with the caller deciding which
     * source transitions are reapable ([TIME-013]): none under {@code assumeNoReaping}, or a set
     * named before a rewrite dropped the timing. The three-argument form marks a transition
     * reapable exactly when its timing is {@code deadline} or {@code window}.
     *
     * @param net              the Petri net to flatten
     * @param environmentPlaces environment places for reactive analysis
     * @param environmentMode  how to treat environment places
     * @param reapable         whether a source transition can be reaped
     * @return the flattened net
     */
    public static FlatNet flatten(
            PetriNet net,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            java.util.function.Predicate<Transition> reapable
    ) {
        // 1. Collect ALL places (net.places() may miss new-API-declared places)
        var allPlaces = declaredPlaces(net);

        // Sort by name for stable indexing. Unicode code-point order, not UTF-16
        // code-unit order, so the index agrees with the Rust and TypeScript
        // flatteners on every name and the emitted scripts stay byte-identical
        // (VER-013).
        var places = allPlaces.stream()
            .sorted(Comparator.comparing(Place::name, CodePointOrder.COMPARATOR))
            .collect(Collectors.toList());

        var placeIndex = new LinkedHashMap<Place<?>, Integer>();
        for (int i = 0; i < places.size(); i++) {
            placeIndex.put(places.get(i), i);
        }

        // 2. Compute environment bounds (legacy post-cap) and the injection map.
        //    The injection map (VER-006) drives the encoder's env-injection rule and
        //    the incidence-matrix injector columns; a null value means unbounded
        //    (AlwaysAvailable), an integer caps injection (Bounded). HashMap is used
        //    deliberately so null values are permitted (Map.copyOf rejects them).
        //    Below the injection guard the post-cap bites only when a transition
        //    deposits into an environment place or M0 holds more than k there, and
        //    there it removes executor steps: SmtVerifier refuses both (VER-006 AC3).
        var environmentBounds = new HashMap<Place<?>, Integer>();
        var environmentInjection = new HashMap<Place<?>, Integer>();
        switch (environmentMode) {
            case EnvironmentAnalysisMode.AlwaysAvailable _ -> {
                for (var ep : environmentPlaces) {
                    environmentInjection.put(ep.place(), null);
                }
            }
            case EnvironmentAnalysisMode.Bounded bounded -> {
                for (var ep : environmentPlaces) {
                    environmentBounds.put(ep.place(), bounded.maxTokens());
                    environmentInjection.put(ep.place(), bounded.maxTokens());
                }
            }
            case EnvironmentAnalysisMode.Ignore _ -> {
                // Not modeled: env places stay ordinary (frozen at their initial count).
            }
            case EnvironmentAnalysisMode.Arrivals _ -> {
                if (!environmentPlaces.isEmpty()) {
                    throw EnvironmentAnalysisMode.Arrivals.notModelled("NetFlattener");
                }
            }
        }

        // 3. Expand transitions
        int n = places.size();
        var flatTransitions = new ArrayList<FlatTransition>();

        for (var transition : net.transitions()) {
            // One flat transition per way a firing can end (BranchOutcomes): each branch the
            // action may write, one token per place ([IO-016]), then the timeout outcome when
            // it deposits differently — only the timeout child's places, a forward depositing
            // one token per consumed token ([IO-013] AC5, [IO-014]).
            var branches = BranchOutcomes.outcomes(transition);

            for (int branchIdx = 0; branchIdx < branches.size(); branchIdx++) {
                var outcome = branches.get(branchIdx);
                String name = branches.size() > 1
                    ? transition.name() + "_b" + branchIdx
                    : transition.name();

                // Build pre-vector and consumeAll flags
                int[] preVector = new int[n];
                boolean[] consumeAll = new boolean[n];

                // Build pre-vector from inputSpecs
                for (var in : transition.inputSpecs()) {
                    int idx = placeIndex.getOrDefault(in.place(), -1);
                    if (idx < 0) continue;

                    switch (in) {
                        case Arc.In.One _ -> preVector[idx] = 1;
                        case Arc.In.Exactly e -> preVector[idx] = e.count();
                        case Arc.In.All _ -> {
                            preVector[idx] = 1;
                            consumeAll[idx] = true;
                        }
                        case Arc.In.AtLeast a -> {
                            preVector[idx] = a.minimum();
                            consumeAll[idx] = true;
                        }
                    }
                }

                // Build post-vector from the outcome's deposits. A forward of an All /
                // AtLeast input deposits the drained batch, which no post vector can hold; its
                // minimum stands in, and the verifier refuses the net before any flat route
                // reads it (BranchOutcomes.drainedForward); the graph routes, which count the
                // batch, decide it first.
                int[] postVector = new int[n];
                for (var e : outcome.deposits().entrySet()) {
                    int idx = placeIndex.getOrDefault(e.getKey(), -1);
                    if (idx >= 0) {
                        postVector[idx] += BranchOutcomes.Outcome.resolve(e.getValue(),
                            from -> minimum(transition, from));
                    }
                }

                // Inhibitor places
                int[] inhibitorPlaces = transition.inhibitors().stream()
                    .map(arc -> placeIndex.getOrDefault(arc.place(), -1))
                    .filter(idx -> idx >= 0)
                    .mapToInt(Integer::intValue)
                    .toArray();

                // Read places
                int[] readPlaces = transition.reads().stream()
                    .map(arc -> placeIndex.getOrDefault(arc.place(), -1))
                    .filter(idx -> idx >= 0)
                    .mapToInt(Integer::intValue)
                    .toArray();

                // Reset places
                int[] resetPlaces = transition.resets().stream()
                    .map(arc -> placeIndex.getOrDefault(arc.place(), -1))
                    .filter(idx -> idx >= 0)
                    .mapToInt(Integer::intValue)
                    .toArray();

                flatTransitions.add(new FlatTransition(
                    name, transition,
                    branches.size() > 1 ? branchIdx : -1,
                    preVector, postVector,
                    inhibitorPlaces, readPlaces, resetPlaces,
                    consumeAll,
                    reapable.test(transition)
                ));
            }
        }

        return new FlatNet(
            List.copyOf(places),
            Map.copyOf(placeIndex),
            List.copyOf(flatTransitions),
            Map.copyOf(environmentBounds),
            // unmodifiableMap (not Map.copyOf): preserves null values for AlwaysAvailable.
            Collections.unmodifiableMap(new HashMap<>(environmentInjection))
        );
    }

    /** The tokens {@code t} requires from {@code from}: 0 when it is not an input. */
    private static int minimum(Transition t, Place<?> from) {
        for (var in : t.inputSpecs()) {
            if (in.place().name().equals(from.name())) {
                return in.requiredCount();
            }
        }
        return 0;
    }
}
