import type { Transition } from '../../core/transition.js';

/**
 * A flattened transition with pre/post vectors for SMT encoding.
 *
 * Each Transition expands into one FlatTransition per way a firing can end
 * (`outcomes` in `analysis/branch-outcomes`): one per XOR branch its action may
 * write, then one for the timeout outcome when that deposits differently
 * ([IO-013], [IO-014]). A transition with a single outcome gives one.
 */
export interface FlatTransition {
  /** Display name: the transition's own with one outcome, else `<name>_b<i>` (e.g. "Search_b0"). */
  readonly name: string;
  /** The original transition. */
  readonly source: Transition;
  /** Which outcome of the source (a XOR branch or the timeout), -1 when it has only one. */
  readonly branchIndex: number;
  /** Tokens consumed per place (indexed by place index). */
  readonly preVector: readonly number[];
  /** Tokens produced per place (indexed by place index). */
  readonly postVector: readonly number[];
  /** Place indices where inhibitor arcs block firing. */
  readonly inhibitorPlaces: readonly number[];
  /** Place indices requiring a token without consuming. */
  readonly readPlaces: readonly number[];
  /** Place indices set to 0 on firing. */
  readonly resetPlaces: readonly number[];
  /** True at index i means place i uses All/AtLeast semantics. */
  readonly consumeAll: readonly boolean[];
  /**
   * Whether the executor can reap the source transition ([TIME-013]): a `deadline` or
   * `window` one, unless the caller assumes no reaping. Its enabledness then does not keep a
   * marking from resting, so every quiescence encoding skips it ([VER-002] reap-quiescence).
   */
  readonly reapable: boolean;
}

export function flatTransition(
  name: string,
  source: Transition,
  branchIndex: number,
  preVector: number[],
  postVector: number[],
  inhibitorPlaces: number[],
  readPlaces: number[],
  resetPlaces: number[],
  consumeAll: boolean[],
  reapable = false,
): FlatTransition {
  return {
    name,
    source,
    branchIndex,
    preVector,
    postVector,
    inhibitorPlaces,
    readPlaces,
    resetPlaces,
    consumeAll,
    reapable,
  };
}
