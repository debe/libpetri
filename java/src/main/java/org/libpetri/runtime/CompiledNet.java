package org.libpetri.runtime;

import java.util.*;

import org.libpetri.core.*;

/**
 * Integer-indexed, precomputed representation of a {@link PetriNet} for bitmap-based execution.
 *
 * <p>Constructed once from a symbolic PetriNet and is immutable after construction.
 * Uses {@link BitSet} masks for O(1) enablement checks via bitwise operations.
 *
 * <h2>ID Assignment</h2>
 * <p>Places and transitions are assigned stable integer IDs (0-based) during construction.
 * These IDs index into all arrays and bitmaps used by {@link BitmapNetExecutor}.
 *
 * <h2>Precomputed Masks</h2>
 * <p>For each transition, the following read-only BitSet masks are precomputed:
 * <ul>
 *   <li>{@code needsMask[tid]} — input places + read places (all must be marked)</li>
 *   <li>{@code inhibitorMask[tid]} — inhibitor places (none may be marked)</li>
 *   <li>{@code resetMask[tid]} — reset arc places (cleared during firing)</li>
 * </ul>
 *
 * <h2>Reverse Index</h2>
 * <p>{@code placeToTransitions[pid]} maps each place to the transitions affected by
 * token changes at that place. Used for event-driven dirty-set updates.
 *
 * @see BitmapNetExecutor
 * @see PetriNet
 */
public final class CompiledNet {
    /** Number of bits to shift for word index (2^6 = 64 bits per long). */
    static final int WORD_SHIFT = 6;
    /** Mask for bit position within a word (0x3F = 63). */
    static final int BIT_MASK = 63;

    private final PetriNet net;
    private final int placeCount;
    private final int transitionCount;
    private final int wordCount;

    // ID mappings
    private final Place<?>[] placesById;
    private final Transition[] transitionsById;
    // HashMap: Place is a record, so structural equals is correct and needed
    private final Map<Place<?>, Integer> placeIndex;
    // IdentityHashMap: Transition has no structural equals; identity comparison is faster
    private final IdentityHashMap<Transition, Integer> transitionIndex;

    // Precomputed masks per transition (read-only after construction)
    private final BitSet[] needsMask;
    private final BitSet[] inhibitorMask;
    private final BitSet[] resetMask;

    // Cached long[] representations of masks (avoids allocation on hot path)
    private final long[][] needsMaskWords;
    private final long[][] inhibitorMaskWords;

    // Reverse index: place → affected transitions
    private final int[][] placeToTransitions;

    // Precomputed consumption place IDs per transition (input + reset places)
    private final int[][] consumptionPlaceIds;

    // Cardinality and guard flags
    private final CardinalityCheck[] cardinalityChecks;
    private final boolean[] hasGuards;

    /**
     * Cardinality check for transitions with non-trivial input requirements.
     * Only allocated for transitions that have In.Exactly, In.All, In.AtLeast,
     * or legacy multi-arc inputs.
     */
    record CardinalityCheck(int[] placeIds, int[] requiredCounts) {}

    /**
     * Compiles a PetriNet into an integer-indexed structure.
     *
     * @param net the symbolic Petri net to compile
     * @return compiled net ready for bitmap execution
     */
    public static CompiledNet compile(PetriNet net) {
        return new CompiledNet(net);
    }

    private CompiledNet(PetriNet net) {
        this.net = net;

        // Collect all places from transitions (same as PetriNet.Builder does)
        var allPlaces = new LinkedHashSet<Place<?>>();
        for (var t : net.transitions()) {
            for (var in : t.inputSpecs()) allPlaces.add(in.place());
            allPlaces.addAll(t.inputs().keySet());
            for (var arc : t.reads()) allPlaces.add(arc.place());
            for (var arc : t.inhibitors()) allPlaces.add(arc.place());
            for (var arc : t.resets()) allPlaces.add(arc.place());
            if (t.outputSpec() != null) allPlaces.addAll(t.outputSpec().allPlaces());
            for (var arc : t.outputs()) allPlaces.add(arc.place());
        }
        // Also include places declared on the net itself
        allPlaces.addAll(net.places());

        this.placeCount = allPlaces.size();
        this.wordCount = (placeCount + BIT_MASK) >>> WORD_SHIFT; // ceil(placeCount / 64)

        // Assign place IDs
        this.placesById = allPlaces.toArray(new Place<?>[0]);
        this.placeIndex = new HashMap<>(placeCount * 2);
        for (int i = 0; i < placesById.length; i++) {
            placeIndex.put(placesById[i], i);
        }

        // Assign transition IDs (use LinkedHashSet for deterministic ordering)
        var allTransitions = new ArrayList<>(net.transitions());
        this.transitionCount = allTransitions.size();
        this.transitionsById = allTransitions.toArray(new Transition[0]);
        this.transitionIndex = new IdentityHashMap<>(transitionCount * 2);
        for (int i = 0; i < transitionsById.length; i++) {
            transitionIndex.put(transitionsById[i], i);
        }

        // Precompute masks
        this.needsMask = new BitSet[transitionCount];
        this.inhibitorMask = new BitSet[transitionCount];
        this.resetMask = new BitSet[transitionCount];
        this.consumptionPlaceIds = new int[transitionCount][];
        this.cardinalityChecks = new CardinalityCheck[transitionCount];
        this.hasGuards = new boolean[transitionCount];

        // Track which transitions are affected by each place
        @SuppressWarnings("unchecked")
        var placeToTransitionsList = (List<Integer>[]) new List[placeCount];
        for (int i = 0; i < placeCount; i++) {
            placeToTransitionsList[i] = new ArrayList<>();
        }

        for (int tid = 0; tid < transitionCount; tid++) {
            var t = transitionsById[tid];
            var needs = new BitSet(placeCount);
            var inhibitors = new BitSet(placeCount);
            var resets = new BitSet(placeCount);

            // Pass 1: Determine if cardinality check is needed
            boolean needsCardinality = false;
            int inputCount = t.inputSpecs().size();
            var inputEntries = t.inputs().asMap().entrySet();
            int legacyCount = inputEntries.size();

            for (var in : t.inputSpecs()) {
                int pid = placeIndex.get(in.place());
                needs.set(pid);
                placeToTransitionsList[pid].add(tid);

                int required = in.requiredCount();
                if (required > 1 || in instanceof In.All || in instanceof In.AtLeast) {
                    needsCardinality = true;
                }
            }

            for (var entry : inputEntries) {
                int pid = placeIndex.get(entry.getKey());
                needs.set(pid);
                placeToTransitionsList[pid].add(tid);

                if (entry.getValue().size() > 1) {
                    needsCardinality = true;
                }

                for (var arc : entry.getValue()) {
                    if (arc.hasGuard()) {
                        hasGuards[tid] = true;
                    }
                }
            }

            // Pass 2: Build cardinality arrays only when needed
            if (needsCardinality) {
                int[] cPids = new int[inputCount + legacyCount];
                int[] cReqs = new int[inputCount + legacyCount];
                int ci = 0;
                for (var in : t.inputSpecs()) {
                    cPids[ci] = placeIndex.get(in.place());
                    cReqs[ci] = in.requiredCount();
                    ci++;
                }
                for (var entry : inputEntries) {
                    cPids[ci] = placeIndex.get(entry.getKey());
                    cReqs[ci] = entry.getValue().size();
                    ci++;
                }
                cardinalityChecks[tid] = new CardinalityCheck(cPids, cReqs);
            }

            // Read arcs
            for (var arc : t.reads()) {
                int pid = placeIndex.get(arc.place());
                needs.set(pid);
                placeToTransitionsList[pid].add(tid);
            }

            // Inhibitor arcs
            for (var arc : t.inhibitors()) {
                int pid = placeIndex.get(arc.place());
                inhibitors.set(pid);
                placeToTransitionsList[pid].add(tid);
            }

            // Reset arcs
            for (var arc : t.resets()) {
                int pid = placeIndex.get(arc.place());
                resets.set(pid);
                placeToTransitionsList[pid].add(tid);
            }

            // Precompute consumption place IDs (deduplicated via BitSet)
            var consumptionBits = new BitSet(placeCount);
            for (var in : t.inputSpecs()) consumptionBits.set(placeIndex.get(in.place()));
            for (var key : t.inputs().keySet()) consumptionBits.set(placeIndex.get(key));
            for (var arc : t.resets()) consumptionBits.set(placeIndex.get(arc.place()));
            int[] cpIds = new int[consumptionBits.cardinality()];
            for (int i = 0, b = consumptionBits.nextSetBit(0); b >= 0; b = consumptionBits.nextSetBit(b + 1), i++) {
                cpIds[i] = b;
            }
            consumptionPlaceIds[tid] = cpIds;

            needsMask[tid] = needs;
            inhibitorMask[tid] = inhibitors;
            resetMask[tid] = resets;
        }

        // Cache long[] representations of masks for hot-path methods
        this.needsMaskWords = new long[transitionCount][];
        this.inhibitorMaskWords = new long[transitionCount][];
        for (int tid = 0; tid < transitionCount; tid++) {
            needsMaskWords[tid] = needsMask[tid].toLongArray();
            inhibitorMaskWords[tid] = inhibitorMask[tid].toLongArray();
        }

        // Build reverse index: deduplicate transition IDs per place
        this.placeToTransitions = new int[placeCount][];
        for (int pid = 0; pid < placeCount; pid++) {
            var tids = placeToTransitionsList[pid].stream()
                .distinct()
                .mapToInt(Integer::intValue)
                .toArray();
            placeToTransitions[pid] = tids;
        }
    }

    // ==================== Accessors ====================

    public PetriNet net() { return net; }
    public int placeCount() { return placeCount; }
    public int transitionCount() { return transitionCount; }
    public int wordCount() { return wordCount; }

    public Place<?> place(int pid) { return placesById[pid]; }
    public Transition transition(int tid) { return transitionsById[tid]; }

    public int placeId(Place<?> place) {
        Integer id = placeIndex.get(place);
        if (id == null) throw new IllegalArgumentException("Unknown place: " + place.name());
        return id;
    }

    public int transitionId(Transition t) {
        Integer id = transitionIndex.get(t);
        if (id == null) throw new IllegalArgumentException("Unknown transition: " + t.name());
        return id;
    }

    public BitSet needsMask(int tid) { return needsMask[tid]; }
    public BitSet inhibitorMask(int tid) { return inhibitorMask[tid]; }
    public BitSet resetMask(int tid) { return resetMask[tid]; }

    public int[] affectedTransitions(int pid) { return placeToTransitions[pid]; }

    public int[] consumptionPlaceIds(int tid) { return consumptionPlaceIds[tid]; }
    public CardinalityCheck cardinalityCheck(int tid) { return cardinalityChecks[tid]; }
    public boolean hasGuards(int tid) { return hasGuards[tid]; }

    // ==================== Enablement Check ====================

    /**
     * Fast bitmap-based enablement check.
     *
     * @param tid transition ID
     * @param markingSnapshot snapshot of the marked places bitmap as long[]
     * @return true if the transition's presence requirements are met
     */
    public boolean canEnableBitmap(int tid, long[] markingSnapshot) {
        // 1. All needed places present? (snapshot AND needsMask) == needsMask
        if (!containsAll(markingSnapshot, needsMaskWords[tid])) return false;

        // 2. No inhibitors active? (snapshot AND inhibitorMask) == 0
        if (intersects(markingSnapshot, inhibitorMaskWords[tid])) return false;

        return true;
    }

    /**
     * Checks if all bits in mask are set in snapshot.
     *
     * @param snapshot current marking as long[]
     * @param maskWords precomputed long[] representation of the mask
     */
    static boolean containsAll(long[] snapshot, long[] maskWords) {
        for (int i = 0; i < maskWords.length; i++) {
            if (i >= snapshot.length) {
                // snapshot doesn't have this word, but mask needs bits there
                if (maskWords[i] != 0) return false;
            } else if ((snapshot[i] & maskWords[i]) != maskWords[i]) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks if any bit in mask is set in snapshot.
     *
     * @param snapshot current marking as long[]
     * @param maskWords precomputed long[] representation of the mask
     */
    static boolean intersects(long[] snapshot, long[] maskWords) {
        for (int i = 0; i < maskWords.length; i++) {
            if (i < snapshot.length && (snapshot[i] & maskWords[i]) != 0) {
                return true;
            }
        }
        return false;
    }
}
