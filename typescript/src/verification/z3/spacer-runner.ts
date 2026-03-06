import { init } from 'z3-solver';
import type { Bool, Expr, FuncDecl } from 'z3-solver';

/**
 * Result of a Spacer query.
 */
export type QueryResult = QueryProven | QueryViolated | QueryUnknown;

/** Property proven: no reachable error state (UNSAT). */
export interface QueryProven {
  readonly type: 'proven';
  readonly invariantFormula: string | null;
  readonly levelInvariants: readonly string[];
}

/** Counterexample found (SAT). The answer is the derivation tree. */
export interface QueryViolated {
  readonly type: 'violated';
  readonly answer: Expr | null;
}

/** Solver could not determine (timeout, resource limit). */
export interface QueryUnknown {
  readonly type: 'unknown';
  readonly reason: string;
}

/**
 * The Z3 context and helpers returned by SpacerRunner.create().
 * Exposes the context object for building expressions.
 */
export interface SpacerContext {
  /** The Z3 high-level context for building expressions. */
  readonly ctx: ReturnType<Awaited<ReturnType<typeof init>>['Context']>;
  /** The Z3 Fixedpoint solver instance (Spacer engine). Z3 types are complex; using any. */
  readonly fp: any;

  /** Queries whether the error state is reachable. */
  query(errorExpr: Bool, reachableDecl?: FuncDecl): Promise<QueryResult>;

  /** Releases Z3 resources. */
  dispose(): void;
}

// Use a type alias for the Z3 context to avoid the deep inference
type Z3Context = ReturnType<Awaited<ReturnType<typeof init>>['Context']>;

/**
 * Creates a Spacer runner with the given timeout.
 *
 * Uses Z3's Spacer engine (CHC solver based on IC3/PDR) to prove or
 * disprove safety properties.
 */
export async function createSpacerRunner(timeoutMs: number): Promise<SpacerContext> {
  const { Context } = await init();
  const ctx = new Context('main') as Z3Context;
  const fp = new (ctx as any).Fixedpoint() as any;

  // Configure Spacer engine
  fp.set('engine', 'spacer');
  if (timeoutMs > 0) {
    fp.set('timeout', Math.min(timeoutMs, 2147483647));
  }

  async function query(errorExpr: Bool, reachableDecl?: FuncDecl): Promise<QueryResult> {
    try {
      const status = await fp.query(errorExpr);

      if (status === 'unsat') {
        let invariantFormula: string | null = null;
        const levelInvariants: string[] = [];

        try {
          const answer = fp.getAnswer();
          if (answer != null) {
            invariantFormula = answer.toString();
          }
        } catch {
          // Some configurations don't produce answers
        }

        if (reachableDecl != null) {
          try {
            const levels = fp.getNumLevels(reachableDecl);
            for (let i = 0; i < levels; i++) {
              const cover = fp.getCoverDelta(i, reachableDecl);
              if (cover != null && !(ctx as any).isTrue(cover)) {
                levelInvariants.push(`Level ${i}: ${cover.toString()}`);
              }
            }
          } catch {
            // Level queries may not be available
          }
        }

        return { type: 'proven', invariantFormula, levelInvariants };
      }

      if (status === 'sat') {
        let answer: Expr | null = null;
        try {
          answer = fp.getAnswer();
        } catch {
          // Some configurations don't produce answers
        }
        return { type: 'violated', answer };
      }

      // unknown
      return { type: 'unknown', reason: fp.getReasonUnknown() };
    } catch (e: any) {
      return { type: 'unknown', reason: `Z3 exception: ${e.message ?? e}` };
    }
  }

  function dispose(): void {
    try {
      fp.release();
    } catch {
      // ignore
    }
  }

  return {
    ctx,
    fp,
    query,
    dispose,
  } as SpacerContext;
}
