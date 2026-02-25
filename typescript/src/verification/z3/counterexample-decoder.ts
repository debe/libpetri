import type { Expr } from 'z3-solver';
import { MarkingState } from '../marking-state.js';
import type { FlatNet } from '../encoding/flat-net.js';

/**
 * Result of counterexample decoding.
 */
export interface DecodedTrace {
  readonly trace: readonly MarkingState[];
  readonly transitions: readonly string[];
}

/**
 * Decodes Z3 Spacer counterexample answers into Petri net marking traces.
 *
 * When Spacer finds a counterexample (property violation), it produces
 * a derivation tree showing how the error state is reachable. This function
 * extracts the marking at each step to produce a human-readable trace.
 */
export function decode(ctx: any, answer: Expr | null, flatNet: FlatNet): DecodedTrace {
  const trace: MarkingState[] = [];
  const transitions: string[] = [];

  if (answer == null) {
    return { trace, transitions };
  }

  try {
    extractTrace(ctx, answer, flatNet, trace, transitions);
  } catch {
    // Z3 answer format varies; gracefully degrade
  }

  return { trace, transitions };
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
      }
    }
  }

  // Recurse into children to find the derivation chain
  try {
    const numArgs = expr.numArgs();
    for (let i = 0; i < numArgs; i++) {
      const child = expr.arg(i);
      extractTrace(ctx, child, flatNet, trace, transitions);
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
