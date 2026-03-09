package org.libpetri.runtime;

import java.util.*;

import org.libpetri.core.*;

/**
 * Precompiled flat-array net representation of a {@link PetriNet} for the {@link PrecompiledNetExecutor}.
 *
 * <p>Compiles the net topology into flat arrays and operation sequences that eliminate
 * virtual dispatch and sealed-type pattern matching from the hot path.
 *
 * <h2>Consume Operations</h2>
 * <p>Each transition's input/reset arcs are compiled into a flat {@code int[]} of opcodes:
 * <pre>
 *   CONSUME_ONE(0)     placeId
 *   CONSUME_N(1)       placeId count
 *   CONSUME_ALL(2)     placeId
 *   CONSUME_ATLEAST(3) placeId minimum
 *   RESET(4)           placeId
 * </pre>
 *
 * <h2>Priority Levels</h2>
 * <p>Distinct priority values are pre-sorted descending and indexed. Each transition
 * maps to a priority index for O(1) ready-queue insertion.
 *
 * @see PrecompiledNetExecutor
 * @see CompiledNet
 */
public final class PrecompiledNet {

    // Consume operation opcodes
    static final int CONSUME_ONE     = 0;
    static final int CONSUME_N       = 1;
    static final int CONSUME_ALL     = 2;
    static final int CONSUME_ATLEAST = 3;
    static final int RESET           = 4;

    // Net identity
    final String netName;

    // Net topology
    final int placeCount;
    final int transitionCount;
    final int wordCount;

    // ID mappings
    final Place<?>[] placesById;
    final Transition[] transitionsById;
    final Map<Place<?>, Integer> placeIndex;
    final IdentityHashMap<Transition, Integer> transitionIndex;

    // Operation sequences per transition
    final int[][] consumeOps;   // consume/reset opcodes
    final int[][] readOps;      // read-arc place IDs

    // Enablement masks (reused from CompiledNet)
    final long[][] needsMaskWords;
    final long[][] inhibitorMaskWords;
    final CompiledNet.CardinalityCheck[] cardinalityChecks;

    // Reverse index
    final int[][] placeToTransitions;

    // Consumption place IDs per transition (input + reset places, deduplicated)
    final int[][] consumptionPlaceIds;

    // Timing (precomputed)
    final long[] earliestNanos;
    final long[] latestNanos;
    final long[] earliestMillis;  // precomputed to avoid Division on hot path
    final long[] latestMillis;    // precomputed to avoid virtual dispatch on hot path
    final boolean[] hasDeadline;

    // Priority
    final int[] priorities;
    final int[] transitionToPriorityIndex; // tid → index into priorityLevels
    final int[] priorityLevels;            // distinct values, sorted descending
    final int distinctPriorityCount;

    // Global flags
    final boolean allImmediate;
    final boolean allSamePriority;
    final boolean anyDeadlines;

    // Output validation: precomputed for fast path
    // For Out.Place specs, stores the single expected place ID; -1 for complex specs; -2 for no spec
    final int[] simpleOutputPlaceId;

    // Input place count per transition (for pre-sizing TokenInput)
    final int[] inputPlaceCount;

    // Input place masks for reset-clock detection (bitmask per transition)
    final long[][] inputPlaceMaskWords;

    // Sparse enablement: precomputed for O(1) single-input checks
    // -2 = empty (no inputs), -1 = multi-word, >= 0 = single word index
    final int[] needsSingleWordIndex;
    final long[] needsSingleWordMask;
    final int[][] needsSparseIndices;   // non-null only for multi-word
    final long[][] needsSparseMasks;

    final int[] inhibitorSingleWordIndex;  // -2 = no inhibitors (skip entirely)
    final long[] inhibitorSingleWordMask;
    final int[][] inhibitorSparseIndices;
    final long[][] inhibitorSparseMasks;

    private PrecompiledNet(CompiledNet compiled) {
        this.netName = compiled.net().name();
        this.placeCount = compiled.placeCount();
        this.transitionCount = compiled.transitionCount();
        this.wordCount = compiled.wordCount();

        // Copy ID mappings from CompiledNet
        this.placesById = new Place<?>[placeCount];
        for (int i = 0; i < placeCount; i++) placesById[i] = compiled.place(i);

        this.transitionsById = new Transition[transitionCount];
        this.transitionIndex = new IdentityHashMap<>(transitionCount * 2);
        for (int i = 0; i < transitionCount; i++) {
            transitionsById[i] = compiled.transition(i);
            transitionIndex.put(transitionsById[i], i);
        }

        this.placeIndex = new HashMap<>(placeCount * 2);
        for (int i = 0; i < placeCount; i++) {
            placeIndex.put(placesById[i], i);
        }

        // Reuse enablement masks
        this.needsMaskWords = new long[transitionCount][];
        this.inhibitorMaskWords = new long[transitionCount][];
        this.cardinalityChecks = new CompiledNet.CardinalityCheck[transitionCount];
        for (int tid = 0; tid < transitionCount; tid++) {
            needsMaskWords[tid] = compiled.needsMask(tid).toLongArray();
            inhibitorMaskWords[tid] = compiled.inhibitorMask(tid).toLongArray();
            cardinalityChecks[tid] = compiled.cardinalityCheck(tid);
        }

        // Reuse reverse index and consumption IDs
        this.placeToTransitions = new int[placeCount][];
        for (int pid = 0; pid < placeCount; pid++) {
            placeToTransitions[pid] = compiled.affectedTransitions(pid);
        }

        this.consumptionPlaceIds = new int[transitionCount][];
        for (int tid = 0; tid < transitionCount; tid++) {
            consumptionPlaceIds[tid] = compiled.consumptionPlaceIds(tid);
        }

        // Compile sparse enablement masks
        this.needsSingleWordIndex = new int[transitionCount];
        this.needsSingleWordMask = new long[transitionCount];
        this.needsSparseIndices = new int[transitionCount][];
        this.needsSparseMasks = new long[transitionCount][];
        this.inhibitorSingleWordIndex = new int[transitionCount];
        this.inhibitorSingleWordMask = new long[transitionCount];
        this.inhibitorSparseIndices = new int[transitionCount][];
        this.inhibitorSparseMasks = new long[transitionCount][];

        for (int tid = 0; tid < transitionCount; tid++) {
            compileSparse(needsMaskWords[tid], needsSingleWordIndex, needsSingleWordMask,
                          needsSparseIndices, needsSparseMasks, tid);
            compileSparse(inhibitorMaskWords[tid], inhibitorSingleWordIndex, inhibitorSingleWordMask,
                          inhibitorSparseIndices, inhibitorSparseMasks, tid);
        }

        // Compile consume/read operation sequences
        this.consumeOps = new int[transitionCount][];
        this.readOps = new int[transitionCount][];
        this.inputPlaceMaskWords = new long[transitionCount][];

        this.simpleOutputPlaceId = new int[transitionCount];
        this.inputPlaceCount = new int[transitionCount];

        for (int tid = 0; tid < transitionCount; tid++) {
            Transition t = transitionsById[tid];
            consumeOps[tid] = compileFireProgram(t);
            readOps[tid] = compileReadProgram(t);
            inputPlaceMaskWords[tid] = compileInputMask(t);

            // Precompute input place count (for TokenInput pre-sizing)
            inputPlaceCount[tid] = t.inputSpecs().size() + t.reads().size();

            // Precompute output validation fast path
            if (t.outputSpec() == null) {
                simpleOutputPlaceId[tid] = -2; // no spec
            } else if (t.outputSpec() instanceof Arc.Out.Place p) {
                simpleOutputPlaceId[tid] = placeIndex.get(p.place());
            } else {
                simpleOutputPlaceId[tid] = -1; // complex spec, use full validation
            }
        }

        // Precompute timing
        this.earliestNanos = new long[transitionCount];
        this.latestNanos = new long[transitionCount];
        this.earliestMillis = new long[transitionCount];
        this.latestMillis = new long[transitionCount];
        this.hasDeadline = new boolean[transitionCount];
        boolean anyDl = false;
        boolean allImm = true;

        for (int tid = 0; tid < transitionCount; tid++) {
            Transition t = transitionsById[tid];
            earliestNanos[tid] = t.timing().earliest().toNanos();
            earliestMillis[tid] = t.timing().earliest().toMillis();
            latestNanos[tid] = t.timing().hasDeadline()
                ? t.timing().latest().toNanos()
                : Long.MAX_VALUE;
            latestMillis[tid] = t.timing().hasDeadline()
                ? t.timing().latest().toMillis()
                : Long.MAX_VALUE;
            hasDeadline[tid] = t.timing().hasDeadline();
            if (hasDeadline[tid]) anyDl = true;
            if (!(t.timing() instanceof Timing.Immediate) &&
                !(t.timing() instanceof Timing.Unconstrained)) {
                allImm = false;
            }
        }
        this.anyDeadlines = anyDl;
        this.allImmediate = allImm;

        // Precompute priorities
        this.priorities = new int[transitionCount];
        var distinctPrios = new TreeSet<Integer>(Comparator.reverseOrder());
        for (int tid = 0; tid < transitionCount; tid++) {
            priorities[tid] = transitionsById[tid].priority();
            distinctPrios.add(priorities[tid]);
        }
        this.priorityLevels = distinctPrios.stream().mapToInt(Integer::intValue).toArray();
        this.distinctPriorityCount = priorityLevels.length;
        this.allSamePriority = distinctPriorityCount <= 1;

        // Map each transition to its priority index
        var prioToIndex = new HashMap<Integer, Integer>();
        for (int i = 0; i < priorityLevels.length; i++) {
            prioToIndex.put(priorityLevels[i], i);
        }
        this.transitionToPriorityIndex = new int[transitionCount];
        for (int tid = 0; tid < transitionCount; tid++) {
            transitionToPriorityIndex[tid] = prioToIndex.get(priorities[tid]);
        }
    }

    /**
     * Compiles a PetriNet into a PrecompiledNet.
     *
     * @param net the symbolic Petri net
     * @return precompiled net ready for execution
     */
    public static PrecompiledNet compile(PetriNet net) {
        return new PrecompiledNet(CompiledNet.compile(net));
    }

    /**
     * Compiles using an existing CompiledNet to reuse its masks and indices.
     *
     * @param compiled pre-compiled net
     * @return precompiled net ready for execution
     */
    public static PrecompiledNet compile(CompiledNet compiled) {
        return new PrecompiledNet(compiled);
    }

    // ==================== Operation Sequence Compilation ====================

    private int[] compileFireProgram(Transition t) {
        // Estimate size: each input spec needs 2-3 ints, each reset needs 2
        var ops = new ArrayList<Integer>();

        for (var in : t.inputSpecs()) {
            int pid = placeIndex.get(in.place());
            switch (in) {
                case Arc.In.One _ -> {
                    ops.add(CONSUME_ONE);
                    ops.add(pid);
                }
                case Arc.In.Exactly e -> {
                    ops.add(CONSUME_N);
                    ops.add(pid);
                    ops.add(e.count());
                }
                case Arc.In.All _ -> {
                    ops.add(CONSUME_ALL);
                    ops.add(pid);
                }
                case Arc.In.AtLeast a -> {
                    ops.add(CONSUME_ATLEAST);
                    ops.add(pid);
                    ops.add(a.minimum());
                }
            }
        }

        for (var arc : t.resets()) {
            int pid = placeIndex.get(arc.place());
            ops.add(RESET);
            ops.add(pid);
        }

        int[] result = new int[ops.size()];
        for (int i = 0; i < result.length; i++) result[i] = ops.get(i);
        return result;
    }

    private int[] compileReadProgram(Transition t) {
        var reads = t.reads();
        int[] result = new int[reads.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = placeIndex.get(reads.get(i).place());
        }
        return result;
    }

    private long[] compileInputMask(Transition t) {
        var bits = new BitSet(placeCount);
        for (var in : t.inputSpecs()) {
            bits.set(placeIndex.get(in.place()));
        }
        return bits.toLongArray();
    }

    // ==================== Sparse Mask Compilation ====================

    private static void compileSparse(long[] maskWords,
                                      int[] singleWordIndex, long[] singleWordMask,
                                      int[][] sparseIndices, long[][] sparseMasks, int tid) {
        // Count non-zero words
        int nonZeroCount = 0;
        int lastNonZeroWord = -1;
        for (int w = 0; w < maskWords.length; w++) {
            if (maskWords[w] != 0) {
                nonZeroCount++;
                lastNonZeroWord = w;
            }
        }

        if (nonZeroCount == 0) {
            singleWordIndex[tid] = -2; // empty
        } else if (nonZeroCount == 1) {
            singleWordIndex[tid] = lastNonZeroWord;
            singleWordMask[tid] = maskWords[lastNonZeroWord];
        } else {
            singleWordIndex[tid] = -1; // multi-word
            int[] indices = new int[nonZeroCount];
            long[] masks = new long[nonZeroCount];
            int idx = 0;
            for (int w = 0; w < maskWords.length; w++) {
                if (maskWords[w] != 0) {
                    indices[idx] = w;
                    masks[idx] = maskWords[w];
                    idx++;
                }
            }
            sparseIndices[tid] = indices;
            sparseMasks[tid] = masks;
        }
    }

    // ==================== Enablement Check ====================

    boolean canEnableBitmap(int tid, long[] markingSnapshot) {
        // Needs check (containsAll)
        int nwi = needsSingleWordIndex[tid];
        if (nwi == -1) {
            // Multi-word sparse
            int[] indices = needsSparseIndices[tid];
            long[] masks = needsSparseMasks[tid];
            for (int i = 0; i < indices.length; i++) {
                int w = indices[i];
                if (w >= markingSnapshot.length || (markingSnapshot[w] & masks[i]) != masks[i])
                    return false;
            }
        } else if (nwi >= 0) {
            // Single-word
            if (nwi >= markingSnapshot.length ||
                (markingSnapshot[nwi] & needsSingleWordMask[tid]) != needsSingleWordMask[tid])
                return false;
        }
        // nwi == -2: empty needs mask, always passes

        // Inhibitor check (intersects)
        int iwi = inhibitorSingleWordIndex[tid];
        if (iwi == -2) return true; // no inhibitors
        if (iwi >= 0) {
            // Single-word
            return iwi >= markingSnapshot.length ||
                   (markingSnapshot[iwi] & inhibitorSingleWordMask[tid]) == 0;
        }
        // Multi-word sparse
        int[] indices = inhibitorSparseIndices[tid];
        long[] masks = inhibitorSparseMasks[tid];
        for (int i = 0; i < indices.length; i++) {
            int w = indices[i];
            if (w < markingSnapshot.length && (markingSnapshot[w] & masks[i]) != 0)
                return false;
        }
        return true;
    }

    // ==================== Accessors ====================

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
}
