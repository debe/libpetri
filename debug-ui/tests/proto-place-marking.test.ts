/**
 * A place may be named `__proto__` (or `constructor`, `toString`, …). That is reachable input,
 * not a curiosity: a host compiling place names from user-supplied step or node identifiers can
 * be handed any of them, and the server keeps such a place on `subscribed.currentMarking`, on
 * every `markingSnapshot` and on every token event.
 *
 * The client re-keys markings into objects. On an ordinary `{}` that loses the place two ways:
 *
 * - `marking['__proto__'] = tokens` and `Object.assign(marking, wire)` go through `[[Set]]`, so
 *   they hit `Object.prototype`'s `__proto__` setter: no own key is created, and the token array
 *   silently becomes the marking's *prototype*;
 * - `marking['constructor']` on a marking that has no such place reads `Object.prototype` and
 *   returns a function where the code expects a token array or `undefined`.
 *
 * So every marking the UI holds is a prototype-less record (`src/net/marking-record.ts`).
 * `JSON.parse` is the transport here as it is in the browser — it defines `__proto__` as an own
 * key, which an object literal in a test would not.
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { applyEventToState, buildCheckpoints, seekToIndex } from '../src/net/actions/playback.js';
import { buildInitialUIState, applyMarkingSnapshot } from '../src/net/actions/session.js';
import { emptyMarking, copyMarking } from '../src/net/marking-record.js';
import { shared } from '../src/net/shared-state.js';
import type { UIState } from '../src/net/types.js';
import type { DebugResponse, NetEventInfo } from '../src/protocol/index.js';

const PROTO = '__proto__';

function tok(id: string) {
  return { id, type: 'String', value: `"${id}"`, timestamp: null };
}

/** What the WebSocket hands the UI: a marking that has been through JSON. */
function wireMarking(): UIState['marking'] {
  return JSON.parse(`{"${PROTO}":[${JSON.stringify(tok('w1'))}],"ordinary":[${JSON.stringify(tok('w2'))}]}`);
}

function state(marking: UIState['marking'] = {}): UIState {
  return { marking, enabledTransitions: [], inFlightTransitions: [], events: [], eventIndex: 0, totalEvents: 0 };
}

function event(overrides: Partial<NetEventInfo>): NetEventInfo {
  return { type: 'TokenAdded', timestamp: '2024-01-01T00:00:00Z', transitionName: null, placeName: null, details: {}, ...overrides };
}

function added(placeName: string, id: string): NetEventInfo {
  return event({ type: 'TokenAdded', placeName, details: { token: tok(id) } });
}

/** Own keys only — `in` and plain reads would also see an inherited `__proto__`. */
function ownIds(marking: UIState['marking'], place: string): string[] | undefined {
  const d = Object.getOwnPropertyDescriptor(marking, place);
  return d === undefined ? undefined : (d.value as { id: string }[]).map(t => t.id);
}

describe('a place named __proto__ survives every client-side re-keying of a marking', () => {
  beforeEach(() => {
    shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 2 };
  });

  it('applyEventToState: TokenAdded creates the place as an own key, not as the prototype', () => {
    const result = applyEventToState(state(), added(PROTO, 'a'));

    expect(Object.keys(result.marking)).toEqual([PROTO]);
    expect(ownIds(result.marking, PROTO)).toEqual(['a']);
    // The failure is not only a missing key: the token array became the prototype, so the
    // marking answers to `length` as though it were a place.
    expect('length' in result.marking).toBe(false);

    const drained = applyEventToState(applyEventToState(result, added(PROTO, 'b')), event({ type: 'TokenRemoved', placeName: PROTO }));
    expect(ownIds(drained.marking, PROTO)).toEqual(['b']);
  });

  it('applyEventToState: a place named after an Object.prototype member is just a place', () => {
    // `marking['constructor'] ?? []` is a function on an ordinary object, and spreading it throws.
    const result = applyEventToState(state(), added('constructor', 'c'));
    expect(ownIds(result.marking, 'constructor')).toEqual(['c']);
    expect(applyEventToState(state(), event({ type: 'TokenRemoved', placeName: 'toString' })).marking['toString']).toBeUndefined();
  });

  it('applyEventToState: MarkingSnapshot keeps the place instead of assigning it away', () => {
    const result = applyEventToState(state({ stale: [tok('s')] }), event({ type: 'MarkingSnapshot', details: { marking: wireMarking() } }));

    expect(Object.keys(result.marking).sort()).toEqual([PROTO, 'ordinary']);
    expect(ownIds(result.marking, PROTO)).toEqual(['w1']);
    expect('length' in result.marking).toBe(false);
  });

  it('buildCheckpoints: the place is in the checkpoint, and an incremental build carries it forward', () => {
    const events = [added(PROTO, 'a'), added('ordinary', 'b')];
    const first = buildCheckpoints(events, 0);
    expect(first).toHaveLength(1);
    expect(ownIds(first[0]!.marking, PROTO)).toEqual(['a']);

    // Incremental: seeded from the last checkpoint, which is the Object.assign-onto-{} site.
    shared.replay.checkpoints = first;
    const more = [...events, added(PROTO, 'c'), added('ordinary', 'd')];
    const second = buildCheckpoints(more, 2);
    expect(second).toHaveLength(2);
    expect(ownIds(second[1]!.marking, PROTO)).toEqual(['a', 'c']);
    expect(ownIds(second[1]!.marking, 'ordinary')).toEqual(['b', 'd']);
  });

  it('buildCheckpoints: a MarkingSnapshot event in the stream keeps the place', () => {
    const events = [added('stale', 's'), event({ type: 'MarkingSnapshot', details: { marking: wireMarking() } })];
    const [cp] = buildCheckpoints(events, 0);

    expect(Object.keys(cp!.marking).sort()).toEqual([PROTO, 'ordinary']);
    expect(ownIds(cp!.marking, PROTO)).toEqual(['w1']);
  });

  it('seekToIndex: replaying from a checkpoint, and from the start, both keep the place', () => {
    const events = [added('ordinary', 'a'), added('ordinary', 'b'), added(PROTO, 'c'), added(PROTO, 'd'), added(PROTO, 'e')];
    shared.replay.allEvents = events;
    shared.replay.checkpoints = buildCheckpoints(events, 0); // at 2 and 4

    // From the checkpoint at 2, which does not hold the place yet: the first add creates it.
    expect(ownIds(seekToIndex(3).marking, PROTO)).toEqual(['c']);
    // From the checkpoint at 4, which does.
    expect(ownIds(seekToIndex(5).marking, PROTO)).toEqual(['c', 'd', 'e']);
    // Landing exactly on a checkpoint replays nothing, so the marking handed to the UI is the
    // checkpoint's clone itself — which must be a record too, not structuredClone's plain object.
    expect(ownIds(seekToIndex(4).marking, PROTO)).toEqual(['c', 'd']);
    expect(seekToIndex(4).marking['constructor']).toBeUndefined();
    expect(seekToIndex(0).marking['constructor']).toBeUndefined();
    // The checkpoint itself is not mutated by the replay that starts from it.
    expect(ownIds(shared.replay.checkpoints[1]!.marking, PROTO)).toEqual(['c', 'd']);
  });

  it('buildInitialUIState: live and replay markings carry no inherited names', () => {
    const response = {
      type: 'subscribed', sessionId: 's', netName: 'N', dotDiagram: '', mode: 'live', eventCount: 0,
      structure: { places: [], transitions: [] },
      currentMarking: wireMarking(), enabledTransitions: [], inFlightTransitions: [],
    } as unknown as Extract<DebugResponse, { type: 'subscribed' }>;

    const live = buildInitialUIState(response, false);
    expect(ownIds(live.marking, PROTO)).toEqual(['w1']);
    expect(ownIds(live.marking, 'ordinary')).toEqual(['w2']);
    // What the token inspector and the place tooltip do: `uiState.marking[placeName]`.
    expect(live.marking['constructor']).toBeUndefined();

    const replay = buildInitialUIState(response, true);
    expect(Object.keys(replay.marking)).toEqual([]);
    expect(replay.marking['constructor']).toBeUndefined();
  });

  it('applyMarkingSnapshot: a server markingSnapshot replaces the marking and keeps the place', () => {
    // The t_on_marking_snapshot handler. The wire object used to be adopted as the marking
    // as it came: `__proto__` survives that (JSON.parse made it an own key) but the object is
    // an ordinary one, so the inherited names are back for every later read and write.
    const msg = {
      type: 'markingSnapshot', sessionId: 's', marking: wireMarking(),
      enabledTransitions: ['t'], inFlightTransitions: [],
    } as Extract<DebugResponse, { type: 'markingSnapshot' }>;

    const next = applyMarkingSnapshot(state({ stale: [tok('s')] }), msg);

    expect(Object.keys(next.marking).sort()).toEqual([PROTO, 'ordinary']);
    expect(ownIds(next.marking, PROTO)).toEqual(['w1']);
    expect(next.marking['constructor']).toBeUndefined();
    expect(next.enabledTransitions).toEqual(['t']);
    // A copy, not the wire object: a later in-place edit of one is not an edit of the other.
    expect(next.marking).not.toBe(msg.marking);
  });

  it('the record helpers: empty is prototype-less, copy keeps every own key and nothing else', () => {
    const empty = emptyMarking<unknown[]>();
    expect(Object.getPrototypeOf(empty)).toBeNull();

    const copy = copyMarking(wireMarking());
    expect(Object.getPrototypeOf(copy)).toBeNull();
    expect(Object.keys(copy).sort()).toEqual([PROTO, 'ordinary']);
    expect(Object.keys(copyMarking(undefined))).toEqual([]);
    // structuredClone hands back an ordinary object; a copy of it is a record again.
    expect(Object.keys(copyMarking(structuredClone(copy))).sort()).toEqual([PROTO, 'ordinary']);
  });
});
