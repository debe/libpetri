/**
 * @module match-engine
 *
 * ν-net binding selection — the canonical name-correlation algorithm shared by
 * both executor backends (spec NU-020).
 *
 * A transition carrying a {@link import('../core/match-spec.js').MatchSpec} is
 * enabled only when there is a single name present in every correlated input
 * with its required token count. The two executors differ only in how they read
 * tokens (`Marking` FIFO queues vs the precompiled per-place arrays); the
 * *selection* — which name satisfies the join, and the deterministic tie-break —
 * lives here so it is identical across backends and matches the Rust/Java ports.
 */
import type { Token } from '../core/token.js';
import type { Place } from '../core/place.js';
import type { Transition } from '../core/transition.js';
import type { NameId } from '../core/name.js';
import type { KeyFn } from '../core/match-spec.js';

/** Per-correlated-input statistic for one name: count + oldest timestamp (ms). */
export interface NameStat {
  count: number;
  minCreatedAt: number;
}

/**
 * Selects the satisfying correlation name across all correlated inputs, or
 * `null` when no single name is present in every input with at least its
 * required count.
 *
 * Determinism (NU-020): among satisfying names, pick the one whose oldest
 * matched token (minimum `createdAt` across the correlated inputs) is earliest;
 * break remaining ties by {@link NameId} order. Byte-identical to the Rust
 * `select_match_name` and the Java `selectMatchName`.
 *
 * The `NameId` tie-break uses JS string `<` (UTF-16 code-unit order). This is
 * byte-identical to the Java (`String.compareTo`) and Rust (UTF-8 code-point)
 * ports for ASCII/BMP names — which covers every executor-minted name
 * (`"{transition}#{n}"`). For supplementary-plane code points in user-supplied
 * correlation keys, Rust's UTF-8 order can differ from this UTF-16 order; NU-001
 * requires only per-implementation consistency, which holds.
 */
export function selectMatchName(
  perPlace: ReadonlyArray<Map<NameId, NameStat>>,
  requireds: readonly number[],
): NameId | null {
  if (perPlace.length === 0) return null;
  // Seed candidate names from the smallest index; result is seed-independent.
  let seed = 0;
  for (let i = 1; i < perPlace.length; i++) {
    if (perPlace[i]!.size < perPlace[seed]!.size) seed = i;
  }

  let bestName: NameId | null = null;
  let bestTs = 0;
  for (const [name, stat] of perPlace[seed]!) {
    if (stat.count < requireds[seed]!) continue;
    let repTs = Number.MAX_SAFE_INTEGER;
    let satisfied = true;
    for (let j = 0; j < perPlace.length; j++) {
      const s = perPlace[j]!.get(name);
      if (s === undefined || s.count < requireds[j]!) {
        satisfied = false;
        break;
      }
      repTs = Math.min(repTs, s.minCreatedAt);
    }
    if (!satisfied) continue;
    const take = bestName === null || repTs < bestTs || (repTs === bestTs && name < bestName);
    if (take) {
      bestName = name;
      bestTs = repTs;
    }
  }
  return bestName;
}

/**
 * Builds a `name → {count, minCreatedAt}` index over the given tokens. When a
 * `guard` (the correlated input's unary filter) is given, tokens failing it are
 * excluded BEFORE indexing — the filter applies first and name correlation runs
 * only over the survivors, so a token failing the filter is never selected even
 * if its name matches (NU-021). Matches the Rust/Java ports, which guard-filter
 * before building the name index.
 */
export function buildNameIndex(
  tokens: readonly Token<any>[],
  key: KeyFn,
  guard?: (value: any) => boolean,
): Map<NameId, NameStat> {
  const index = new Map<NameId, NameStat>();
  for (const token of tokens) {
    if (guard && !guard(token.value)) continue;
    const name = key(token.value);
    if (name === undefined || name === null) continue;
    const ts = token.createdAt;
    const prev = index.get(name);
    if (prev) {
      prev.count++;
      if (ts < prev.minCreatedAt) prev.minCreatedAt = ts;
    } else {
      index.set(name, { count: 1, minCreatedAt: ts });
    }
  }
  return index;
}

/**
 * Required token count for `placeName` from the transition's input spec
 * (1 for one/all, n for exactly(n), m for at-least(m)).
 */
export function requiredFor(t: Transition, placeName: string): number {
  for (const inSpec of t.inputSpecs) {
    if (inSpec.place.name === placeName) {
      if (inSpec.type === 'exactly') return inSpec.count;
      if (inSpec.type === 'at-least') return inSpec.minimum;
      return 1;
    }
  }
  return 1;
}

/**
 * Finds the correlation name satisfying `t`'s `MatchSpec`, or `null` if the join
 * is not enabled (NU-020). `getTokens` abstracts the token source so both
 * executors share this code (Marking queues vs precompiled per-place arrays).
 */
export function findBinding(
  t: Transition,
  getTokens: (place: Place<any>) => readonly Token<any>[],
): NameId | null {
  const ms = t.matchSpec;
  if (!ms) return null;
  const perPlace: Map<NameId, NameStat>[] = [];
  const requireds: number[] = [];
  for (const k of ms.keys) {
    // NU-021: apply the input's guard before indexing names, so a token failing
    // the filter is excluded from both the count and the name-presence/tie-break.
    perPlace.push(buildNameIndex(getTokens(k.place), k.key, guardFor(t, k.place.name)));
    requireds.push(requiredFor(t, k.place.name));
  }
  return selectMatchName(perPlace, requireds);
}

/** The unary guard on `t`'s input arc for `placeName`, if any (NU-021). */
function guardFor(t: Transition, placeName: string): ((value: any) => boolean) | undefined {
  for (const inSpec of t.inputSpecs) {
    if (inSpec.place.name === placeName) return inSpec.guard;
  }
  return undefined;
}
