/**
 * An immutable token carrying a typed value through the Petri net.
 *
 * Tokens flow from place to place as transitions fire, carrying typed
 * payloads that represent the state of a computation or workflow.
 */
export interface Token<T> {
  readonly value: T;
  /** Epoch milliseconds when the token was created. */
  readonly createdAt: number;
  /**
   * JSON-friendly projection of the token value, populated by
   * {@link SessionArchiveReader} when hydrating a v3 archive so replay
   * consumers see the same structured shape the writer emitted. Live tokens
   * (produced by {@link tokenOf} / {@link tokenAt}) leave this `undefined`;
   * the runtime ignores it. See [EVT-025](../../../spec/08-events-observability.md)
   * AC5. (libpetri 1.8.0+)
   */
  readonly structured?: unknown;
}

/** Cached singleton unit token. */
const UNIT_TOKEN: Token<null> = Object.freeze({
  value: null,
  createdAt: 0,
});

/** Creates a token with the given value and current timestamp. */
export function tokenOf<T>(value: T): Token<T> {
  return { value, createdAt: Date.now() };
}

/**
 * Returns a unit token (marker with no meaningful value).
 * Used for pure control flow where presence matters but data doesn't.
 * Returns a cached singleton whose `value` is `null`.
 */
export function unitToken(): Token<null> {
  return UNIT_TOKEN;
}

/** Creates a token with a specific timestamp (for testing/replay). */
export function tokenAt<T>(value: T, createdAt: number): Token<T> {
  return { value, createdAt };
}

/** Checks if this is the singleton unit token. */
export function isUnit(token: Token<unknown>): boolean {
  return token === UNIT_TOKEN;
}
