/**
 * @module state-space-cache
 *
 * The state-space cache of [VER-017] "Reusing the state space across queries".
 */
import type { PetriNet } from '../core/petri-net.js';
import type { MarkingState } from './marking-state.js';
import type { StateClassGraph } from './analysis/state-class-graph.js';
import { buildStateSpace } from './scg-verifier.js';

/** A remembered enumeration attempt: the graph closed, or it hit the budget `budget`. */
type Entry =
  | { readonly kind: 'closed'; readonly graph: StateClassGraph }
  | { readonly kind: 'truncated'; readonly budget: number };

/**
 * @internal What {@link resolveStateSpace} did for one query.
 *
 * - `built` — nothing usable was cached, so the graph was built at this budget (closed or not).
 * - `reused` — a closed graph was cached and the budget exceeds its class count.
 * - `declined` — the cache already knows this budget truncates, so nothing was built.
 */
export type StateSpaceLookup =
  | { readonly kind: 'built'; readonly graph: StateClassGraph }
  | { readonly kind: 'reused'; readonly graph: StateClassGraph }
  | { readonly kind: 'declined' };

/**
 * A cache of state-class graphs for the bounded state-space enumeration route ([VER-017]),
 * shared across queries on one net.
 *
 * The graph depends only on the net and its initial marking; the property and the sinks only
 * read it. Without a cache every `SmtVerifier.verify()` call rebuilds it, and on a net whose
 * graph exceeds the budget every query pays the full attempt before it falls through to the SMT
 * pipeline. Create one cache, pass it to each verifier with
 * `SmtVerifier.stateSpaceCache(cache)`, and the graph is built once:
 *
 * ```ts
 * const cache = new StateSpaceCache();
 * for (const property of properties) {
 *   await SmtVerifier.forNet(net).initialMarking(m0).property(property)
 *     .stateSpaceCache(cache).verify();
 * }
 * ```
 *
 * Entries are keyed by the net instance the caller passed to `SmtVerifier.forNet` (held
 * weakly, so a dropped net frees its entries) and by the initial marking as the caller listed
 * it. A different net instance, or a different marking, never hits another entry; an equal
 * marking listed in another order, or built from other `Place` objects, misses too, so the
 * witness is identical to the one a query without the cache returns.
 *
 * - A **closed** graph of `C` classes is reused for any budget greater than `C`. A budget of `C`
 *   or less would have truncated, and is answered as truncated without building.
 * - A **truncated** attempt at budget `B` is remembered: a later budget of `B` or less declines
 *   at once; a larger budget builds again and replaces the entry.
 *
 * The verdict, the witness and the route are the same with and without the cache; the report
 * says when a cached graph or a cached truncation was used. The build is synchronous, so
 * concurrent verifications sharing a cache build each entry once. The cache holds its graphs
 * until it is dropped or {@link clear}ed.
 */
export class StateSpaceCache {
  /** Drops every cached graph and truncation. */
  clear(): void {
    STATE.set(this, newState());
  }
}

/** A cache's entries, and the ids it gave the `Place` objects its keys name. */
interface CacheState {
  readonly entries: WeakMap<PetriNet, Map<string, Entry>>;
  readonly placeIds: WeakMap<object, number>;
  nextPlaceId: number;
}

function newState(): CacheState {
  return { entries: new WeakMap(), placeIds: new WeakMap(), nextPlaceId: 0 };
}

/**
 * Each cache's state, held outside the class so that the lookup is not part of the public
 * `StateSpaceCache` surface: only the verifier, which imports {@link resolveStateSpace} from this
 * module, reaches it.
 */
const STATE = new WeakMap<StateSpaceCache, CacheState>();

function stateOf(cache: StateSpaceCache): CacheState {
  let state = STATE.get(cache);
  if (state == null) {
    state = newState();
    STATE.set(cache, state);
  }
  return state;
}

/**
 * @internal Answers one enumeration query at `budget` through `cache`, building when nothing
 * usable is cached. Not re-exported from the package: the verifier is its only caller.
 *
 * @param keyNet the net the caller passed to `forNet` — the key
 * @param buildNet the net the graph is built from: `keyNet` after the deterministic terminal
 *   rewrite of [EXEC-042], or `keyNet` itself
 */
export function resolveStateSpace(
  cache: StateSpaceCache,
  keyNet: PetriNet,
  buildNet: PetriNet,
  initial: MarkingState,
  budget: number,
): StateSpaceLookup {
  const state = stateOf(cache);
  let byMarking = state.entries.get(keyNet);
  if (byMarking == null) {
    byMarking = new Map();
    state.entries.set(keyNet, byMarking);
  }
  const key = markingKey(state, initial);
  const entry = byMarking.get(key);
  if (entry?.kind === 'closed') {
    return budget > entry.graph.size()
      ? { kind: 'reused', graph: entry.graph }
      : { kind: 'declined' };
  }
  if (entry?.kind === 'truncated' && budget <= entry.budget) {
    return { kind: 'declined' };
  }
  const graph = buildStateSpace(buildNet, initial, budget);
  byMarking.set(key, graph.isComplete() ? { kind: 'closed', graph } : { kind: 'truncated', budget });
  return { kind: 'built', graph };
}

/**
 * The key for a marking: its places **in the caller's listing order**, each with its count and
 * the identity of its `Place` object. Every marking of a witness inherits that listing and those
 * objects from the initial marking, so an equal marking listed differently, or naming other
 * `Place` objects, misses rather than return a witness that lists differently from a query
 * without the cache ([VER-017]: a key may miss where it could hit, never the reverse).
 */
function markingKey(state: CacheState, marking: MarkingState): string {
  return JSON.stringify(marking.placesWithTokens().map(p => {
    let id = state.placeIds.get(p);
    if (id === undefined) {
      id = state.nextPlaceId++;
      state.placeIds.set(p, id);
    }
    return [p.name, id, marking.tokens(p)];
  }));
}
