package org.libpetri.smt.encoding;

/**
 * Incidence matrix for a flattened Petri net.
 *
 * <p>The incidence matrix C is defined as C[t][p] = post[t][p] - pre[t][p].
 * It captures the net effect of each transition on each place.
 *
 * <p>P-invariants are solutions to y^T * C = 0, found via null space
 * computation on C^T.
 */
public final class IncidenceMatrix {

    private final int[][] pre;      // pre[t][p]
    private final int[][] post;     // post[t][p]
    private final int[][] incidence; // C[t][p] = post - pre
    private final int numTransitions;
    private final int numPlaces;

    private IncidenceMatrix(int[][] pre, int[][] post, int[][] incidence, int numTransitions, int numPlaces) {
        this.pre = pre;
        this.post = post;
        this.incidence = incidence;
        this.numTransitions = numTransitions;
        this.numPlaces = numPlaces;
    }

    /**
     * Computes the incidence matrix from a FlatNet.
     *
     * @param flatNet the flattened net
     * @return the incidence matrix
     */
    public static IncidenceMatrix from(FlatNet flatNet) {
        int T = flatNet.transitionCount();
        int P = flatNet.placeCount();

        int[][] pre = new int[T][P];
        int[][] post = new int[T][P];
        int[][] incidence = new int[T][P];

        for (int t = 0; t < T; t++) {
            var ft = flatNet.transitions().get(t);
            for (int p = 0; p < P; p++) {
                pre[t][p] = ft.preVector()[p];
                post[t][p] = ft.postVector()[p];
                incidence[t][p] = post[t][p] - pre[t][p];
            }
        }

        return new IncidenceMatrix(pre, post, incidence, T, P);
    }

    /**
     * Returns C^T (transpose of incidence matrix), dimensions [P][T].
     * Used for P-invariant computation: null space of C^T gives P-invariants.
     */
    public int[][] transposedIncidence() {
        int[][] ct = new int[numPlaces][numTransitions];
        for (int t = 0; t < numTransitions; t++) {
            for (int p = 0; p < numPlaces; p++) {
                ct[p][t] = incidence[t][p];
            }
        }
        return ct;
    }

    /**
     * Returns the pre-matrix (tokens consumed).
     * Shared reference — do not mutate.
     */
    public int[][] pre() { return pre; }

    /**
     * Returns the post-matrix (tokens produced).
     * Shared reference — do not mutate.
     */
    public int[][] post() { return post; }

    /**
     * Returns the incidence matrix C[t][p] = post - pre.
     * Shared reference — do not mutate.
     */
    public int[][] incidence() { return incidence; }

    public int numTransitions() { return numTransitions; }

    public int numPlaces() { return numPlaces; }
}
