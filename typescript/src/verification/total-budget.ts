/**
 * @module total-budget
 *
 * The optional total wall-clock budget of `SmtVerifier.verify()` ([VER-013]).
 *
 * The per-call `timeout` bounds one z3 process. A verification runs several of them — the bound
 * query, the state-equation phase and its certificate check, the firing bound, the fixpoint
 * query and its certificate check — plus solver-free work: the enumeration and Route B graph
 * builds, the siphon/trap search, the semiflow enumeration. The total budget bounds all of it:
 * a {@link Deadline} starts at the top of `verify()`, every z3 process is given at most what
 * remains, and the long solver-free loops poll it. When it passes the verdict is `unknown` with
 * {@link totalBudgetReason}; a verdict reached before that stands.
 *
 * Cancellation rides the same mechanism: an `AbortSignal` given to the verifier makes the
 * deadline "passed" the moment it fires, a running z3 process is killed at once, and the
 * verdict is `unknown` with {@link cancelledReason}.
 */

/**
 * Thrown by a deadline poll once verification must stop: the total budget ran out
 * ({@link TotalBudgetExhausted}) or the caller cancelled ({@link VerificationCancelled}).
 * `verify()` turns either into `unknown`.
 */
export abstract class VerificationStopped extends Error {
  /** The `unknown` reason, and report line, for a stop during `phase`. */
  abstract reasonDuring(phase: string): string;
}

/** Thrown by a deadline poll once the deadline has passed; `verify()` turns it into `unknown`. */
export class TotalBudgetExhausted extends VerificationStopped {
  constructor(readonly budgetMs: number) {
    super(`total verification budget of ${budgetMs} ms exhausted`);
    this.name = 'TotalBudgetExhausted';
  }

  reasonDuring(phase: string): string {
    return totalBudgetReason(this.budgetMs, phase);
  }
}

/** Thrown by a deadline poll once the caller's `AbortSignal` has fired ([VER-013]). */
export class VerificationCancelled extends VerificationStopped {
  constructor() {
    super('verification cancelled');
    this.name = 'VerificationCancelled';
  }

  reasonDuring(phase: string): string {
    return cancelledReason(phase);
  }
}

/**
 * When verification must stop ([VER-013]): a wall-clock deadline `budgetMs` after it was
 * started, an `AbortSignal`, or both — one stop mechanism, so everything that polls the
 * deadline (the z3 clamp, the graph builds, the pure loops) sees a cancellation as well.
 * Cancellation wins over an elapsed budget when both apply.
 */
export class Deadline {
  private constructor(
    /** The total budget in milliseconds, or `null` when only a signal stops the run. */
    readonly budgetMs: number | null,
    private readonly endsAt: number,
    /** The caller's cancellation signal, or `null`. */
    readonly signal: AbortSignal | null,
  ) {}

  static start(budgetMs: number | null, signal: AbortSignal | null = null): Deadline {
    return new Deadline(budgetMs, budgetMs === null ? Infinity : performance.now() + budgetMs, signal);
  }

  /** Whether the caller cancelled. */
  cancelled(): boolean {
    return this.signal?.aborted === true;
  }

  /**
   * Milliseconds left; zero or negative once the deadline has passed or the run was cancelled,
   * `Infinity` with no budget.
   */
  remainingMs(): number {
    if (this.cancelled()) return 0;
    return this.endsAt - performance.now();
  }

  /** Whether verification must stop: cancelled, or the budget has run out. */
  passed(): boolean {
    return this.remainingMs() <= 0;
  }

  /** Throws {@link VerificationCancelled} or {@link TotalBudgetExhausted} once verification must stop. */
  check(): void {
    if (this.cancelled()) throw new VerificationCancelled();
    if (this.passed()) throw new TotalBudgetExhausted(this.budgetMs!);
  }

  /** The error {@link check} would throw now, or `null`. */
  stopped(): VerificationStopped | null {
    if (this.cancelled()) return new VerificationCancelled();
    if (this.passed()) return new TotalBudgetExhausted(this.budgetMs!);
    return null;
  }

  /**
   * A poll for a hot loop: {@link check} every `every` calls, so reading the clock costs
   * nothing measurable. `null` deadline → a no-op.
   */
  static poller(deadline: Deadline | null | undefined, every = 256): () => void {
    if (deadline == null) return NO_POLL;
    let n = 0;
    return () => {
      if (++n % every === 0) deadline.check();
    };
  }
}

const NO_POLL = (): void => {};

/** The `unknown` reason, and report line, for a total budget that ran out during `phase`. */
export function totalBudgetReason(budgetMs: number, phase: string): string {
  return `total verification budget of ${budgetMs} ms exhausted during ${phase}`;
}

/** The `unknown` reason, and report line, for a verification cancelled during `phase` ([VER-013]). */
export function cancelledReason(phase: string): string {
  return `verification cancelled during ${phase}`;
}
