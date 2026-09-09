/**
 * @module rest-set
 *
 * Where a token may come to rest without being stranded (VER-002, VER-014).
 *
 * `DeadlockFree` is violated by a quiescent marking that holds a token outside the
 * places where resting is permitted. The permitted set has two layers:
 *
 * - the **declared sinks** (`SmtVerifier.sinkPlaces`), where a token may always rest;
 * - the **conditional sinks** (`SmtVerifier.sinkPlacesWhen(marker, …)`), where a
 *   token may rest only while `marker` holds a token. A marked marker is a
 *   *designed terminal* — a halted or paused run — and the marker itself is at rest
 *   whenever it is marked.
 *
 * Declarations union: a token in `p` is excused when `p` is a declared sink, when
 * `p` is a marker, or when some conditional set naming `p` has its marker marked.
 * Every route that decides `DeadlockFree` — the flat and name-coloured CHC encoders,
 * the abstract counterexample replay and the Route B name-partition graph — reads
 * this one module, so the predicate cannot drift between them (VER-002 AC7).
 *
 * `TerminatesAtSink` is untouched by conditional declarations: it asks whether a
 * declared sink was reached and reads only the unconditional set.
 */
import type { Place } from '../core/place.js';
import type { FlatNet } from './encoding/flat-net.js';
import type { MarkingState } from './marking-state.js';

/** Places where a token may rest while `marker` holds a token. */
export interface ConditionalSinks {
  readonly marker: Place<any>;
  readonly places: ReadonlySet<Place<any>>;
}

/**
 * Per flat place, how a token resting there is excused: `null` when it never counts
 * as stranded (a declared sink, or a marker), otherwise the ascending flat indices of
 * the markers whose presence excuses it — empty when nothing does, so a token there
 * is stranded whenever the marking is quiescent.
 *
 * Places and markers that do not resolve in the flat net contribute nothing, as an
 * unresolved sink does: a mistyped marker makes the property stricter, never laxer.
 */
export function strandingExcuses(
  flatNet: FlatNet,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditional: readonly ConditionalSinks[],
): (readonly number[] | null)[] {
  const P = flatNet.places.length;
  const excuses: (number[] | null)[] = new Array(P);
  for (let pid = 0; pid < P; pid++) excuses[pid] = [];
  for (const sink of sinkPlaces) {
    const pid = flatNet.placeIndex.get(sink.name);
    if (pid != null) excuses[pid] = null;
  }
  for (const { marker, places } of conditional) {
    const mid = flatNet.placeIndex.get(marker.name);
    if (mid == null) continue;
    excuses[mid] = null;
    for (const place of places) {
      const pid = flatNet.placeIndex.get(place.name);
      if (pid == null) continue;
      const list = excuses[pid];
      if (list != null && !list.includes(mid)) list.push(mid);
    }
  }
  for (const list of excuses) if (list != null) list.sort((a, b) => a - b);
  return excuses;
}

/**
 * Whether `m` holds a token that is stranded — outside every place where resting is
 * permitted in `m`. The graph-route form of {@link strandingExcuses}.
 */
export function strandsToken(
  m: MarkingState,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditional: readonly ConditionalSinks[],
): boolean {
  const resting = new Set<string>();
  for (const s of sinkPlaces) resting.add(s.name);
  for (const { marker, places } of conditional) {
    resting.add(marker.name);
    if (m.hasTokens(marker)) {
      for (const p of places) resting.add(p.name);
    }
  }
  for (const p of m.placesWithTokens()) {
    if (!resting.has(p.name)) return true;
  }
  return false;
}

/**
 * The declarations as the report prints them after the property description:
 * `sinks: a, b; when h: c, d; when p`, or `null` when nothing is declared.
 * Declaration order throughout, so the four implementations render the same text.
 */
export function describeSinks(
  sinkPlaces: ReadonlySet<Place<any>>,
  conditional: readonly ConditionalSinks[],
): string | null {
  const parts: string[] = [];
  if (sinkPlaces.size > 0) parts.push(`sinks: ${[...sinkPlaces].map(p => p.name).join(', ')}`);
  for (const { marker, places } of conditional) {
    const names = [...places].map(p => p.name);
    parts.push(names.length === 0 ? `when ${marker.name}` : `when ${marker.name}: ${names.join(', ')}`);
  }
  return parts.length === 0 ? null : parts.join('; ');
}
