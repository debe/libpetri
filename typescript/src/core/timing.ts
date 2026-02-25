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
  /** Deadline in milliseconds. Must be positive. */
  readonly byMs: number;
}

export interface TimingDelayed {
  readonly type: 'delayed';
  /** Minimum delay in milliseconds. Must be non-negative. */
  readonly afterMs: number;
}

export interface TimingWindow {
  readonly type: 'window';
  /** Earliest firing time in milliseconds. Must be non-negative. */
  readonly earliestMs: number;
  /** Latest firing time in milliseconds. Must be >= earliestMs. */
  readonly latestMs: number;
}

export interface TimingExact {
  readonly type: 'exact';
  /** Exact firing time in milliseconds. Must be non-negative. */
  readonly atMs: number;
}

/** ~100 years in milliseconds, used for "unconstrained" intervals. */
export const MAX_DURATION_MS = 365 * 100 * 24 * 60 * 60 * 1000;

// ==================== Factory Functions ====================

/** Immediate firing: can fire as soon as enabled, no deadline. [0, inf) */
export function immediate(): TimingImmediate {
  return { type: 'immediate' };
}

/** Immediate with deadline: can fire immediately, must fire by deadline. [0, by] */
export function deadline(byMs: number): TimingDeadline {
  if (byMs <= 0) {
    throw new Error(`Deadline must be positive: ${byMs}`);
  }
  return { type: 'deadline', byMs };
}

/** Delayed firing: must wait, then can fire anytime. [after, inf) */
export function delayed(afterMs: number): TimingDelayed {
  if (afterMs < 0) {
    throw new Error(`Delay must be non-negative: ${afterMs}`);
  }
  return { type: 'delayed', afterMs };
}

/** Time window: can fire within [earliest, latest]. */
export function window(earliestMs: number, latestMs: number): TimingWindow {
  if (earliestMs < 0) {
    throw new Error(`Earliest must be non-negative: ${earliestMs}`);
  }
  if (latestMs < earliestMs) {
    throw new Error(`Latest (${latestMs}) must be >= earliest (${earliestMs})`);
  }
  return { type: 'window', earliestMs, latestMs };
}

/** Exact timing: fires at precisely the specified time. [at, at] */
export function exact(atMs: number): TimingExact {
  if (atMs < 0) {
    throw new Error(`Exact time must be non-negative: ${atMs}`);
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
