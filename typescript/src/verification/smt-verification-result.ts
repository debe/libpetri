import type { MarkingState } from './marking-state.js';
import type { PInvariant } from './invariant/p-invariant.js';

/**
 * Verification verdict.
 */
export type Verdict = Proven | Violated | Unknown;

/** Property proven safe. No reachable state violates it. */
export interface Proven {
  readonly type: 'proven';
  readonly method: string;
  readonly inductiveInvariant: string | null;
}

/** Property violated. A counterexample trace is available. */
export interface Violated {
  readonly type: 'violated';
}

/** Could not determine. */
export interface Unknown {
  readonly type: 'unknown';
  readonly reason: string;
}

/**
 * Solver statistics.
 */
export interface SmtStatistics {
  readonly places: number;
  readonly transitions: number;
  readonly invariantsFound: number;
  readonly structuralResult: string;
}

/**
 * Result of SMT-based verification.
 */
export interface SmtVerificationResult {
  readonly verdict: Verdict;
  readonly report: string;
  readonly invariants: readonly PInvariant[];
  readonly discoveredInvariants: readonly string[];
  readonly counterexampleTrace: readonly MarkingState[];
  readonly counterexampleTransitions: readonly string[];
  /**
   * Whether the counterexample behind a `violated` verdict was confirmed by
   * abstract replay:
   *
   * - `true` — an abstract firing chain from M₀ to a property-violating state
   *   was re-executed TS-side; `counterexampleTrace` is that chain in FIRING
   *   (replay) order.
   * - `false` — no states could be decoded from the Z3 derivation, so the
   *   verdict rests on Spacer's SAT answer alone (still `violated`).
   * - `null` — not applicable: non-violated verdict, replay disabled via
   *   `counterexampleReplay(false)`, or the coloured ν-encoding / Route B
   *   (whose state shapes are outside the flat replayer's scope).
   *
   * A decoded-but-unchainable counterexample never reaches this field as
   * `violated` — the verdict downgrades to `unknown` instead.
   */
  readonly counterexampleConfirmed: boolean | null;
  readonly elapsedMs: number;
  readonly statistics: SmtStatistics;
}

export function isProven(result: SmtVerificationResult): boolean {
  return result.verdict.type === 'proven';
}

export function isViolated(result: SmtVerificationResult): boolean {
  return result.verdict.type === 'violated';
}
