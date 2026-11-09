/**
 * Firing timing specification for transitions.
 *
 * Based on classical Time Petri Net (TPN) semantics:
 * - Transition CANNOT fire before earliest time (lower bound)
 * - Transition MUST fire by deadline OR become disabled (upper bound)
 *
 * All durations are in milliseconds.
 */
export type Timing = TimingImmediate | TimingDeadline | TimingDelayed | TimingWindow | TimingExact;

export interface TimingImmediate {
  readonly type: 'immediate';
}

export interface TimingDeadline {
  readonly type: 'deadline';
  /** Deadline in milliseconds: `0 < byMs <= MAX_DURATION_MS` (TIME-001 AC4). */
  readonly byMs: number;
}

export interface TimingDelayed {
  readonly type: 'delayed';
  /** Minimum delay in milliseconds: `0 <= afterMs <= MAX_DURATION_MS` (TIME-001 AC4). */
  readonly afterMs: number;
}

export interface TimingWindow {
  readonly type: 'window';
  /** Earliest firing time in milliseconds: `0 <= earliestMs <= MAX_DURATION_MS` (TIME-001 AC4). */
  readonly earliestMs: number;
  /** Latest firing time in milliseconds: `earliestMs <= latestMs <= MAX_DURATION_MS` (TIME-001 AC4). */
  readonly latestMs: number;
}

export interface TimingExact {
  readonly type: 'exact';
  /** Exact firing time in milliseconds: `0 <= atMs <= MAX_DURATION_MS` (TIME-001 AC4). */
  readonly atMs: number;
}

/** ~100 years in milliseconds, used for "unconstrained" intervals. */
export const MAX_DURATION_MS = 365 * 100 * 24 * 60 * 60 * 1000;

// ==================== Factory Functions ====================

/** Immediate firing: can fire as soon as enabled, no deadline. [0, inf) */
export function immediate(): TimingImmediate {
  return { type: 'immediate' };
}

/** Immediate with deadline: can fire immediately, must fire by deadline. [0, by], 0 < by <= MAX_DURATION_MS */
export function deadline(byMs: number): TimingDeadline {
  if (byMs <= 0) {
    throw new Error(`Deadline must be positive: ${byMs}`);
  }
  // [TIME-001] AC4: a deadline past the stand-in for "no constraint" is one no run reaches, and
  // accepting it would make a transition reapable whose bound means "never".
  if (byMs > MAX_DURATION_MS) {
    throw new Error(`Deadline must be at most MAX_DURATION_MS (${MAX_DURATION_MS}): ${byMs}`);
  }
  return { type: 'deadline', byMs };
}

/** Delayed firing: must wait, then can fire anytime. [after, inf) */
export function delayed(afterMs: number): TimingDelayed {
  if (afterMs < 0) {
    throw new Error(`Delay must be non-negative: ${afterMs}`);
  }
  // [TIME-001]: [after, MAX_DURATION_MS] would be empty, and a state-class graph would read a
  // transition that can fire as one that never can.
  if (afterMs > MAX_DURATION_MS) {
    throw new Error(`Delay must be at most MAX_DURATION_MS (${MAX_DURATION_MS}): ${afterMs}`);
  }
  return { type: 'delayed', afterMs };
}

/**
 * Time window: can fire within [earliest, latest], 0 <= earliest <= latest <= MAX_DURATION_MS.
 * For no upper bound use {@link delayed}.
 */
export function window(earliestMs: number, latestMs: number): TimingWindow {
  if (earliestMs < 0) {
    throw new Error(`Earliest must be non-negative: ${earliestMs}`);
  }
  // As for delayed: a verifier that lifts the latest bound reads this as delayed(earliestMs).
  if (earliestMs > MAX_DURATION_MS) {
    throw new Error(`Earliest must be at most MAX_DURATION_MS (${MAX_DURATION_MS}): ${earliestMs}`);
  }
  if (latestMs < earliestMs) {
    throw new Error(`Latest (${latestMs}) must be >= earliest (${earliestMs})`);
  }
  // [TIME-001] AC4: as for deadline, a latest bound past the stand-in for "no constraint" is a
  // hidden "never" that still reports a deadline and makes the transition reapable.
  if (latestMs > MAX_DURATION_MS) {
    throw new Error(`Latest must be at most MAX_DURATION_MS (${MAX_DURATION_MS}): ${latestMs}`);
  }
  return { type: 'window', earliestMs, latestMs };
}

/**
 * Exact timing: targets the specified time (interval `[at, at]`).
 *
 * The zero-width interval is precise for verification/simulation. Under wall-clock execution it
 * is enforced *softly* — the transition fires at the first opportunity at or after `atMs` (like
 * {@link delayed}) and is never force-disabled for being observed late (TIME-006). Prefer
 * {@link delayed} for a plain lower bound, or {@link window} for a hard bounded window.
 */
export function exact(atMs: number): TimingExact {
  if (atMs < 0) {
    throw new Error(`Exact time must be non-negative: ${atMs}`);
  }
  if (atMs > MAX_DURATION_MS) {
    throw new Error(`Exact time must be at most MAX_DURATION_MS (${MAX_DURATION_MS}): ${atMs}`);
  }
  return { type: 'exact', atMs };
}

// ==================== Query Functions ====================

/** Returns the earliest time (ms) the transition can fire after enabling. */
export function earliest(timing: Timing): number {
  switch (timing.type) {
    case 'immediate': return 0;
    case 'deadline': return 0;
    case 'delayed': return timing.afterMs;
    case 'window': return timing.earliestMs;
    case 'exact': return timing.atMs;
  }
}

/** Returns the latest time (ms) by which the transition must fire. */
export function latest(timing: Timing): number {
  switch (timing.type) {
    case 'immediate': return MAX_DURATION_MS;
    case 'deadline': return timing.byMs;
    case 'delayed': return MAX_DURATION_MS;
    case 'window': return timing.latestMs;
    case 'exact': return timing.atMs;
  }
}

/** Returns true if this timing has a finite deadline. */
export function hasDeadline(timing: Timing): boolean {
  switch (timing.type) {
    case 'immediate': return false;
    case 'deadline': return true;
    case 'delayed': return false;
    case 'window': return true;
    case 'exact': return true;
  }
}
