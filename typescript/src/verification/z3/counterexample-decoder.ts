import type { Expr } from 'z3-solver';
import { MarkingState } from '../marking-state.js';
import type { FlatNet } from '../encoding/flat-net.js';

/**
 * Structured reason why decoding degraded (never thrown — decoding a
 * counterexample must not crash a violated verdict).
 */
export type DecodeFailure =
  | { readonly kind: 'no-answer' }
  | { readonly kind: 'traversal-error'; readonly message: string }
  | { readonly kind: 'non-concrete'; readonly skipped: number };

/** Human-readable form of a {@link DecodeFailure} (or of a clean-but-empty walk). */
export function describeDecodeFailure(failure: DecodeFailure | null): string {
  if (failure == null) {
    return 'no Reachable applications with concrete arguments found in the derivation';
  }
  switch (failure.kind) {
    case 'no-answer':
      return 'Z3 produced no derivation answer';
    case 'traversal-error':
      return `derivation walk failed: ${failure.message}`;
    case 'non-concrete':
      return `${failure.skipped} Reachable application(s) had non-concrete arguments`;
  }
}

/**
 * Result of counterexample decoding.
 */
export interface DecodedTrace {
  /**
   * Reachable states in derivation-TRAVERSAL order — NOT firing order (the
   * derivation tree is walked recursively, so display order is fragile).
   * May contain duplicates. Kept for raw reporting; the replayer consumes
   * {@link states} instead.
   */
  readonly trace: readonly MarkingState[];
  /** Rule names encountered during the walk (same traversal-order caveat). */
  readonly transitions: readonly string[];
  /**
   * The decoded Reachable states as an order-free SET, deduplicated by
   * marking. This is the shape the abstract replayer chains into firing order.
   */
  readonly states: ReadonlySet<MarkingState>;
  /**
   * Structured reason when decoding degraded (partial results are still
   * returned); `null` when the walk completed cleanly.
   */
  readonly failure: DecodeFailure | null;
}

/**
 * Decodes Z3 Spacer counterexample answers into Petri net marking traces.
 *
 * When Spacer finds a counterexample (property violation), it produces
 * a derivation tree showing how the error state is reachable. This function
 * extracts the marking at each `Reachable` application. The derivation is
 * walked in TRAVERSAL order, so `trace` is not a firing sequence; `states`
 * carries the same markings as an order-free set for the abstract replayer
 * to chain. Failures degrade gracefully and are surfaced via `failure`.
 */
export function decode(ctx: any, answer: Expr | null, flatNet: FlatNet): DecodedTrace {
  const trace: MarkingState[] = [];
  const transitions: string[] = [];
  const stateByKey = new Map<string, MarkingState>();

  if (answer == null) {
    return { trace, transitions, states: new Set(), failure: { kind: 'no-answer' } };
  }

  const counters = { skipped: 0 };
  let failure: DecodeFailure | null = null;
  try {
    extractTrace(ctx, answer, flatNet, trace, transitions, stateByKey, counters);
  } catch (e: any) {
    // Z3 answer format varies; gracefully degrade — but say why.
    failure = { kind: 'traversal-error', message: String(e?.message ?? e) };
  }
  if (failure == null && counters.skipped > 0) {
    failure = { kind: 'non-concrete', skipped: counters.skipped };
  }

  return { trace, transitions, states: new Set(stateByKey.values()), failure };
}

/**
 * Recursively traverses the Z3 proof tree to extract marking states.
 */
function extractTrace(
  ctx: any,
  expr: any,
  flatNet: FlatNet,
  trace: MarkingState[],
  transitions: string[],
  stateByKey: Map<string, MarkingState>,
  counters: { skipped: number },
): void {
  if (expr == null) return;

  // Check if this is a function application
  if (!ctx.isApp(expr)) return;

  let name: string;
  try {
    const decl = expr.decl();
    name = String(decl.name());
  } catch {
    return;
  }

  // Check if this is a Reachable application with integer arguments
  const P = flatNet.places.length;
  if (name === 'Reachable') {
    const numArgs = expr.numArgs();
    if (numArgs === P) {
      const marking = extractMarking(ctx, expr, flatNet);
      if (marking != null) {
        trace.push(marking);
        // MarkingState.toString() sorts by place name — a canonical dedup key.
        const key = marking.toString();
        if (!stateByKey.has(key)) stateByKey.set(key, marking);
      } else {
        counters.skipped++;
      }
    }
  }

  // Recurse into children to find the derivation chain
  try {
    const numArgs = expr.numArgs();
    for (let i = 0; i < numArgs; i++) {
      const child = expr.arg(i);
      extractTrace(ctx, child, flatNet, trace, transitions, stateByKey, counters);
    }
  } catch {
    // Not all expressions support arg()
  }

  // Try to extract transition name from rule application
  if (name.startsWith('t_')) {
    transitions.push(name.substring(2));
  }
}

/**
 * Extracts a MarkingState from a Reachable(...) application.
 */
function extractMarking(ctx: any, reachableApp: any, flatNet: FlatNet): MarkingState | null {
  const P = flatNet.places.length;
  if (reachableApp.numArgs() !== P) return null;

  const builder = MarkingState.builder();
  for (let i = 0; i < P; i++) {
    const arg = reachableApp.arg(i);
    if (ctx.isIntVal(arg)) {
      const tokens = Number(arg.value());
      if (tokens > 0) {
        builder.tokens(flatNet.places[i]!, tokens);
      }
    } else {
      // Non-concrete value in counterexample
      return null;
    }
  }
  return builder.build();
}
