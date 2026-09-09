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
 * Which route decided a verdict ([VER-003]).
 *
 * The routes do equivalent work by different means, and a consumer reading the
 * result's fields rather than its report needs to know which one answered:
 * `enumeration` and `nu-scg` decide by exploring a finite graph and compute no
 * P-invariants at all.
 *
 * The rule for {@link SmtVerificationResult.invariants} is about the *empty* case
 * only: an empty list from a route other than `smt` means "not computed", not
 * "the net has none". A non-empty list is always real — `unavailable` in
 * particular still carries the invariants the pipeline computed before it found
 * no usable solver, and `structural` carries whatever the proof rested on.
 */
export type VerificationRoute =
  /** The IC3/PDR pipeline: flatten, invariants, encode, solve ([VER-001]). */
  | 'smt'
  /** Bounded state-space enumeration ([VER-017]). */
  | 'enumeration'
  /** The ν name-partition state-class graph ([VER-012], Route B). */
  | 'nu-scg'
  /** A structural proof — Commoner's theorem, or the linear bound of [VER-015]. */
  | 'structural'
  /** No route could run (no solver, an unresolved property place). */
  | 'unavailable';

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
  /**
   * Which route decided this verdict ([VER-003]). Read it before concluding
   * anything from an **empty** {@link invariants}: off the `'smt'` route that
   * means "not computed", never "none exist". A non-empty list is real whatever
   * the route says.
   */
  readonly route: VerificationRoute;
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
   *
   * A `true` from the enumeration route ([VER-017]) means the same thing it means
   * everywhere else — the trace is an ordered firing sequence that reaches the
   * violation — even though it was read off the state-class graph rather than
   * re-executed: the graph path *is* a firing sequence, so there is nothing to
   * re-confirm. Consumers keying "are these steps ordered" off this field get the
   * right answer without special-casing the route.
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
