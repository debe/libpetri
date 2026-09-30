/**
 * Analysis mode for environment places ([VER-006]).
 */
export type EnvironmentAnalysisMode =
  | { readonly type: 'always-available' }
  | { readonly type: 'bounded'; readonly maxTokens: number }
  | { readonly type: 'arrivals'; readonly minTokens: number; readonly maxTokens: number }
  | { readonly type: 'ignore' };

/** Assumes environment places always have sufficient tokens. */
export function alwaysAvailable(): EnvironmentAnalysisMode {
  return { type: 'always-available' };
}

/**
 * At most `maxTokens` tokens **resident** in each environment place at a time ([VER-006]):
 * injection refills the place up to `maxTokens`, forever, so a transition takes at most
 * `maxTokens` from it per firing but the total injected over a run is unbounded. For a bound on
 * the total, use {@link arrivals}.
 *
 * The model is the executor only when no transition deposits into an environment place and the
 * initial marking holds at most `maxTokens` on each one ([VER-006] AC3). `SmtVerifier` checks
 * both and answers `unknown`, naming the place, when either fails.
 */
export function bounded(maxTokens: number): EnvironmentAnalysisMode {
  if (maxTokens < 0) throw new Error('maxTokens must be non-negative');
  return { type: 'bounded', maxTokens };
}

/**
 * Between `minTokens` and `maxTokens` tokens injected into each environment place **in total**,
 * over the whole run ([VER-006]). `arrivals(k)` is `arrivals(0, k)` — at most `k`, possibly none;
 * `arrivals(k, k)` is exactly `k`.
 *
 * A net rewrite, not an encoding: before any route runs, `SmtVerifier` closes the net as
 * [VER-022] closes an arrival group — the `i`-th registered environment place `P` gets a
 * mandatory source `env:arrivals[i]` holding `minTokens` tokens with an injection transition
 * `env:arrive[i]:P`, and an optional source `env:optional[i]` holding `maxTokens − minTokens`
 * with `env:arrive?[i]:P` and `env:decline[i]` discarding one; a source whose count is `0` is
 * omitted with its transitions ({@link closeArrivals}). The rewritten net has no environment
 * places, so enumeration, P-invariants and quiescence apply as on any closed net: a run comes to
 * rest only after every mandatory arrival and after any number of optional ones, so quiescence
 * sees between `minTokens` and `maxTokens` arrivals. Counterexample traces name the injection and
 * decline transitions, one firing each.
 *
 * Only `SmtVerifier` (and `SubnetDef.verify`, which uses it) applies the rewrite; the graph
 * builders and the flattener refuse this mode — close the net first.
 *
 * @throws when a bound is not a whole number, `minTokens < 0`, or `maxTokens < minTokens`
 */
export function arrivals(maxTokens: number): EnvironmentAnalysisMode;
export function arrivals(minTokens: number, maxTokens: number): EnvironmentAnalysisMode;
export function arrivals(first: number, second?: number): EnvironmentAnalysisMode {
  if (second === undefined) {
    if (!Number.isInteger(first) || first < 0) {
      throw new Error(`maxTokens must be a non-negative integer: ${first}`);
    }
    return { type: 'arrivals', minTokens: 0, maxTokens: first };
  }
  if (!Number.isInteger(first) || !Number.isInteger(second) || first < 0 || second < first) {
    throw new Error(`arrivals needs whole bounds with 0 <= minTokens <= maxTokens, got ${first}..${second}`);
  }
  return { type: 'arrivals', minTokens: first, maxTokens: second };
}

/** The refusal of a component that models injection itself, for {@link arrivals}. */
export function arrivalsNotModelled(where: string): Error {
  return new Error(
    `${where}: EnvironmentAnalysisMode.arrivals(k) is a net rewrite applied by SmtVerifier (VER-006); ` +
    'close the net first (closeArrivals) and analyse it without environment places',
  );
}

/** Treats environment places as regular places. */
export function ignore(): EnvironmentAnalysisMode {
  return { type: 'ignore' };
}
