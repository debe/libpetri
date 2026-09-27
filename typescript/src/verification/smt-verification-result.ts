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
 * How a `violated` verdict's counterexample relates to the net's timing ([VER-003], [VER-023]).
 * The verdict itself is always the untimed claim ([VER-004]); this says what is known about the
 * counterexample under timing, and nothing here ever changes a verdict.
 */
export type CounterexampleTiming =
  /** Every transition is immediate; timing cannot affect the trace. */
  | 'untimed-net'
  /**
   * A timed net whose counterexample comes from the untimed model and was not checked under
   * timing: `SmtVerifier.timedCounterexampleCheck` is off, or it does not apply
   * (environment places, or ν-matching transitions — the timed graph is name-blind).
   */
  | 'untimed-abstraction'
  /**
   * The deciding route explores timed behaviour already (Route B on a timed net); the trace is a
   * run of the timed semantics. The graph ignores priority, so it is not necessarily a run the
   * executor takes.
   */
  | 'timed-exact'
  /**
   * The timed check ran and the timed state-class graph reaches a violating class. The
   * counterexample trace and transitions are replaced by the shortest timed-graph path, and
   * `counterexampleConfirmed` is `true`: the path is an ordered firing sequence. The timed graph
   * ignores priority: a net that relies on priority to exclude the path can still get this outcome.
   */
  | 'timed-confirmed'
  /**
   * The timed check ran, the timed state-class graph closed, and no class violates the property:
   * it holds under timing (a timed claim only). The verdict stays `violated`; the untimed trace
   * is kept.
   */
  | 'spurious-under-timing'
  /** The timed check ran but hit the class budget or the total verification budget. */
  | 'timed-undecided';

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
   * Whether the counterexample **replays in the untimed abstraction** ([VER-003]) — the
   * value-blind, timing-blind model every encoder reasons about. It says nothing about timing:
   * {@link counterexampleTiming} does.
   *
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
  /**
   * How the counterexample relates to the net's timing ([VER-003], [VER-023]) — `null` unless
   * the verdict is `violated`. {@link counterexampleConfirmed} says the trace replays in the
   * untimed abstraction; this says whether it survives timing. See {@link CounterexampleTiming}.
   */
  readonly counterexampleTiming: CounterexampleTiming | null;
  readonly elapsedMs: number;
  readonly statistics: SmtStatistics;
}

export function isProven(result: SmtVerificationResult): boolean {
  return result.verdict.type === 'proven';
}

export function isViolated(result: SmtVerificationResult): boolean {
  return result.verdict.type === 'violated';
}
