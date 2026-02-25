package org.libpetri.smt.encoding;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.In;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Flattens a {@link PetriNet} into a {@link FlatNet} suitable for SMT encoding.
 *
 * <p>Flattening involves:
 * <ol>
 *   <li>Assigning each place a stable integer index (sorted by name)</li>
 *   <li>Expanding XOR outputs into separate flat transitions (one per branch)</li>
 *   <li>Building pre/post vectors from input/output specs</li>
 *   <li>Recording inhibitor, read, and reset arcs</li>
 *   <li>Setting environment bounds for bounded analysis mode</li>
 * </ol>
 */
public final class NetFlattener {

    private NetFlattener() {}

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
        // 1. Collect ALL places (net.places() may miss new-API-declared places)
        var allPlaces = new LinkedHashSet<>(net.places());
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

        // Sort by name for stable indexing
        var places = allPlaces.stream()
            .sorted(Comparator.comparing(Place::name))
            .collect(Collectors.toList());

        var placeIndex = new LinkedHashMap<Place<?>, Integer>();
        for (int i = 0; i < places.size(); i++) {
            placeIndex.put(places.get(i), i);
        }

        // 2. Compute environment bounds
        var envPlaceSet = environmentPlaces.stream()
            .map(EnvironmentPlace::place)
            .collect(Collectors.toSet());

        var environmentBounds = new HashMap<Place<?>, Integer>();
        if (environmentMode instanceof EnvironmentAnalysisMode.Bounded bounded) {
            for (var ep : environmentPlaces) {
                environmentBounds.put(ep.place(), bounded.maxTokens());
            }
        }

        // 3. Expand transitions
        int n = places.size();
        var flatTransitions = new ArrayList<FlatTransition>();

        for (var transition : net.transitions()) {
            var branches = enumerateOutputBranches(transition);

            for (int branchIdx = 0; branchIdx < branches.size(); branchIdx++) {
                var branchPlaces = branches.get(branchIdx);
                String name = branches.size() > 1
                    ? transition.name() + "_b" + branchIdx
                    : transition.name();

                // Build pre-vector and consumeAll flags
                int[] preVector = new int[n];
                boolean[] consumeAll = new boolean[n];

                // New API: inputSpecs
                for (var in : transition.inputSpecs()) {
                    int idx = placeIndex.getOrDefault(in.place(), -1);
                    if (idx < 0) continue;

                    switch (in) {
                        case In.One _ -> preVector[idx] = 1;
                        case In.Exactly e -> preVector[idx] = e.count();
                        case In.All _ -> {
                            preVector[idx] = 1;
                            consumeAll[idx] = true;
                        }
                        case In.AtLeast a -> {
                            preVector[idx] = a.minimum();
                            consumeAll[idx] = true;
                        }
                    }
                }

                // Legacy API: inputs() multimap (backward compatibility)
                for (var place : transition.inputs().keySet()) {
                    int idx = placeIndex.getOrDefault(place, -1);
                    if (idx < 0 || preVector[idx] > 0) continue; // skip if already set by inputSpecs
                    preVector[idx] = transition.inputs().get(place).size();
                }

                // Build post-vector from branch output places
                int[] postVector = new int[n];
                for (var place : branchPlaces) {
                    int idx = placeIndex.getOrDefault(place, -1);
                    if (idx >= 0) {
                        postVector[idx] = 1;
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
                    consumeAll
                ));
            }
        }

        return new FlatNet(
            List.copyOf(places),
            Map.copyOf(placeIndex),
            List.copyOf(flatTransitions),
            Map.copyOf(environmentBounds)
        );
    }

    /**
     * Enumerates output branches for a transition.
     * Returns list of place-sets (one per XOR branch).
     */
    private static List<Set<Place<?>>> enumerateOutputBranches(Transition t) {
        if (t.outputSpec() != null) {
            return t.outputSpec().enumerateBranches();
        }

        // Legacy: single branch with all output places
        if (!t.outputs().isEmpty()) {
            Set<Place<?>> places = t.outputs().stream()
                .map(arc -> (Place<?>) arc.place())
                .collect(Collectors.toUnmodifiableSet());
            return List.of(places);
        }

        // No outputs (sink transition)
        return List.of(Set.of());
    }
}
