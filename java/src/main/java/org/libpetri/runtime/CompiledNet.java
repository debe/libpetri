package org.libpetri.runtime;

import java.util.*;

import org.libpetri.core.*;
import org.libpetri.core.internal.OutputActionCheck;

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

    // Clock-restart screen per place (TIME-012)
    private final int[] restartThreshold;
    private final boolean[] restartAlwaysCheck;

    // Cardinality flags
    private final CardinalityCheck[] cardinalityChecks;

    /**
     * Cardinality check for transitions with non-trivial input requirements.
     * Only allocated for transitions that have In.Exactly, In.All, or In.AtLeast.
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

        // CORE-043: a transition declaring an output must not carry passthrough(), which produces
        // nothing — every firing would fail IO-015 validation. Checked before anything else.
        OutputActionCheck.requireOutputProducingActions(net);

        // Collect all places from transitions
        var allPlaces = new LinkedHashSet<Place<?>>();
        for (var t : net.transitions()) {
            for (var in : t.inputSpecs()) allPlaces.add(in.place());
            for (var arc : t.reads()) allPlaces.add(arc.place());
            for (var arc : t.inhibitors()) allPlaces.add(arc.place());
            for (var arc : t.resets()) allPlaces.add(arc.place());
            if (t.outputSpec() != null) allPlaces.addAll(t.outputSpec().allPlaces());
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

            // Determine if cardinality check is needed
            boolean needsCardinality = false;
            int inputCount = t.inputSpecs().size();

            // CORE-030 AC3: the Transition builder stays permissive; the duplicate-input
            // rejection lives here so both backends share it.
            var seenInputPlaces = new BitSet(placeCount);

            for (var in : t.inputSpecs()) {
                int pid = placeIndex.get(in.place());
                if (seenInputPlaces.get(pid)) {
                    throw new IllegalStateException(
                        ("Transition '%s' declares two input arcs on place '%s'. Duplicate "
                            + "input places have no coherent consumption semantics and are "
                            + "rejected at compile time (CORE-030). Use a single arc with "
                            + "exactly(n) / atLeast(n) instead.").formatted(t.name(), in.place().name()));
                }
                seenInputPlaces.set(pid);
                needs.set(pid);
                placeToTransitionsList[pid].add(tid);

                int required = in.requiredCount();
                if (required > 1 || in instanceof Arc.In.All || in instanceof Arc.In.AtLeast) {
                    needsCardinality = true;
                }
            }

            // Build cardinality arrays only when needed
            if (needsCardinality) {
                int[] cPids = new int[inputCount];
                int[] cReqs = new int[inputCount];
                int ci = 0;
                for (var in : t.inputSpecs()) {
                    cPids[ci] = placeIndex.get(in.place());
                    cReqs[ci] = in.requiredCount();
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

        // Clock-restart screen (TIME-012): per place, the largest count an input or read arc
        // requires of it, and whether it is a correlated input of a ν-join
        this.restartThreshold = new int[placeCount];
        this.restartAlwaysCheck = new boolean[placeCount];
        int[] requirer = new int[placeCount]; // 0 none, tid + 1 the only requiring transition, -1 several
        boolean[] drained = new boolean[placeCount];
        int tid = 0;
        for (var t : transitionsById) {
            for (var in : t.inputSpecs()) {
                int pid = placeIndex.get(in.place());
                restartThreshold[pid] = Math.max(restartThreshold[pid], in.requiredCount());
                requirer[pid] = requirer[pid] == 0 || requirer[pid] == tid + 1 ? tid + 1 : -1;
            }
            for (var arc : t.reads()) {
                int pid = placeIndex.get(arc.place());
                restartThreshold[pid] = Math.max(restartThreshold[pid], 1);
                requirer[pid] = requirer[pid] == 0 || requirer[pid] == tid + 1 ? tid + 1 : -1;
            }
            for (var arc : t.resets()) {
                drained[placeIndex.get(arc.place())] = true;
            }
            if (t.matchSpec() != null) {
                for (var key : t.matchSpec().keys()) {
                    restartAlwaysCheck[placeIndex.get(key.place())] = true;
                }
            }
            tid++;
        }
        // A place only one transition requires and no reset arc drains is taken from by that
        // transition alone, so the walk could only reach the transition that fired. Skipping it
        // keeps a linear chain's hot path at one comparison per consumed place.
        for (int pid = 0; pid < placeCount; pid++) {
            if (requirer[pid] != -1 && !drained[pid]) {
                restartThreshold[pid] = 0;
                restartAlwaysCheck[pid] = false;
            }
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

    /**
     * Like {@link #placeId(Place)} but returns {@code -1} for a place the compiled net does
     * not know. Used by the retention seams (CORE-072 AC3): tokens reaching a backend for an
     * uncompiled place are kept in the observable marking rather than failing the operation.
     */
    int placeIdOrMissing(Place<?> place) {
        Integer id = placeIndex.get(place);
        return id == null ? -1 : id;
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

    /**
     * The largest token count any input or read arc requires of {@code pid}: n for
     * {@code exactly(n)} and {@code atLeast(n)}, 1 for any other input and for a read, 0 when
     * no arc requires tokens there or one transition alone takes from it. A firing that leaves at least this many tokens in the place
     * cannot have disabled anyone through it (TIME-012); inhibitor and reset arcs contribute
     * nothing, since removing tokens never disables through them.
     */
    int restartThreshold(int pid) { return restartThreshold[pid]; }

    /**
     * True when {@code pid} is a correlated input of a ν-join. The join's binding can break at
     * any count there, so consumption from it always gets the full clock-restart check
     * (TIME-012). A place the join touches through another arc is screened like any other:
     * holding its threshold leaves the binding unchanged.
     */
    boolean restartAlwaysCheck(int pid) { return restartAlwaysCheck[pid]; }

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
