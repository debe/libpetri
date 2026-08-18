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
   * Outcome of the abstract counterexample replay, as a TRI-STATE. `null` means
   * "the replay did not apply"; the two booleans both mean it ran.
   *
   * - `true` — an abstract firing chain from M₀ to a property-violating state
   *   was re-executed TS-side; `counterexampleTrace` is that chain in FIRING
   *   (replay) order and the verdict is `violated`.
   * - `false` — the replay ran without confirming the trace. Either it could not
   *   settle the question (nothing decoded from the Z3 derivation, M₀ absent
   *   from the decoded set, or a node/segment budget hit), in which case the
   *   `violated` verdict rests on Spacer's SAT answer alone; or the search
   *   completed and found NO chain, in which case the verdict was downgraded to
   *   `unknown`. The report distinguishes the two ("UNCONFIRMED" vs "FAILED").
   * - `null` — replay did not apply: non-violated verdict, replay disabled via
   *   `counterexampleReplay(false)`, the coloured ν-encoding / Route B (whose
   *   state shapes are outside the flat replayer's scope), or a structural
   *   proof.
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
