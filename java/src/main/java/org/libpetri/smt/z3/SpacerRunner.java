package org.libpetri.smt.z3;

import com.microsoft.z3.*;

import java.time.Duration;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Manages the Z3 Context and Fixedpoint solver lifecycle for IC3/PDR verification.
 *
 * <p>Uses Z3's Spacer engine (CHC solver based on IC3/PDR) to prove or
 * disprove safety properties. Spacer incrementally constructs inductive
 * invariants without enumerating all reachable states.
 *
 * <p>Implements {@link AutoCloseable} to ensure Z3 native resources are released.
 */
public final class SpacerRunner implements AutoCloseable {

    private final Context ctx;
    private final Fixedpoint fp;
    private final Duration timeout;

    /**
     * Creates a new Spacer runner with the given timeout.
     *
     * @param timeout maximum time for the solver
     */
    public SpacerRunner(Duration timeout) {
        this.timeout = timeout;

        // Z3 context with proof generation enabled for counterexamples
        var cfg = new HashMap<String, String>();
        cfg.put("proof", "true");
        this.ctx = new Context(cfg);

        this.fp = ctx.mkFixedpoint();
        configureSpacerEngine();
    }

    private void configureSpacerEngine() {
        Params params = ctx.mkParams();
        params.add("engine", "spacer");
        params.add("spacer.global", true);
        params.add("spacer.use_bg_invs", true);

        // Timeout in milliseconds
        if (timeout != null && !timeout.isZero()) {
            params.add("timeout", (int) Math.min(timeout.toMillis(), Integer.MAX_VALUE));
        }

        fp.setParameters(params);
    }

    /**
     * Returns the Z3 context for building expressions.
     */
    public Context context() {
        return ctx;
    }

    /**
     * Returns the Fixedpoint solver for adding rules and querying.
     */
    public Fixedpoint fixedpoint() {
        return fp;
    }

    /**
     * Queries whether the error state is reachable.
     *
     * @param errorExpr the error predicate expression
     * @return the query result
     */
    public QueryResult query(BoolExpr errorExpr) {
        return query(errorExpr, null);
    }

    /**
     * Queries whether the error state is reachable, extracting the inductive
     * invariant from the proof when the property holds.
     *
     * @param errorExpr     the error predicate expression
     * @param reachableDecl the Reachable relation declaration (for invariant extraction)
     * @return the query result
     */
    public QueryResult query(BoolExpr errorExpr, FuncDecl<BoolSort> reachableDecl) {
        try {
            Status status = fp.query(errorExpr);
            return switch (status) {
                case UNSATISFIABLE -> {
                    String invariantFormula = null;
                    List<String> levelInvariants = new ArrayList<>();
                    try {
                        Expr answer = fp.getAnswer();
                        if (answer != null) {
                            invariantFormula = answer.toString();
                        }
                    } catch (Z3Exception _) {
                        // Some configurations don't produce answers
                    }

                    if (reachableDecl != null) {
                        try {
                            int levels = fp.getNumLevels(reachableDecl);
                            for (int i = 0; i < levels; i++) {
                                Expr cover = fp.getCoverDelta(i, reachableDecl);
                                if (cover != null && !cover.isTrue()) {
                                    levelInvariants.add("Level " + i + ": " + cover);
                                }
                            }
                        } catch (Z3Exception _) {
                            // Level queries may not be available in all configurations
                        }
                    }

                    yield new QueryResult.Proven(invariantFormula, List.copyOf(levelInvariants));
                }
                case SATISFIABLE -> {
                    Expr answer = null;
                    try {
                        answer = fp.getAnswer();
                    } catch (Z3Exception _) {
                        // Some configurations don't produce answers
                    }
                    yield new QueryResult.Violated(answer);
                }
                case UNKNOWN -> new QueryResult.Unknown(fp.getReasonUnknown());
            };
        } catch (Z3Exception e) {
            return new QueryResult.Unknown("Z3 exception: " + e.getMessage());
        }
    }

    @Override
    public void close() {
        ctx.close();
    }

    /**
     * Result of a Spacer query.
     */
    public sealed interface QueryResult {
        /**
         * Property proven: no reachable error state (UNSAT).
         *
         * @param invariantFormula the overall inductive invariant synthesized by IC3 (may be null)
         * @param levelInvariants  per-level invariant clauses from the IC3 frames
         */
        record Proven(String invariantFormula, List<String> levelInvariants) implements QueryResult {}

        /** Counterexample found (SAT). The answer is the derivation tree. */
        record Violated(Expr answer) implements QueryResult {}

        /** Solver could not determine (timeout, resource limit). */
        record Unknown(String reason) implements QueryResult {}
    }
}
