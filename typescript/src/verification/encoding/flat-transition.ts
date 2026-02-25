import type { Transition } from '../../core/transition.js';

/**
 * A flattened transition with pre/post vectors for SMT encoding.
 *
 * Each Transition with XOR outputs is expanded into multiple FlatTransitions
 * (one per branch). Non-XOR transitions map 1:1.
 */
export interface FlatTransition {
  /** Display name (e.g. "Search_b0", "Search_b1"). */
  readonly name: string;
  /** The original transition. */
  readonly source: Transition;
  /** Which XOR branch (-1 if no XOR). */
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
  };
}
