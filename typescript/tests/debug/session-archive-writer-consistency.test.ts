/**
 * Verifies the EVT-025 invariant that an archive header's `eventCount` equals
 * the number of events actually serialized into the body, after a write→read
 * round-trip.
 *
 * Regression: on libpetri ≤ 1.8.2 the writer read header `eventCount` from
 * `eventStore.eventCount()` (lifetime cumulative counter that never decrements
 * on eviction) while the body iterated retained events. After any eviction the
 * header overstated the body by exactly the eviction count.
 *
 * TypeScript is single-threaded, so the multi-snapshot temporal race that
 * affects Java does not manifest here. This suite covers the
 * cumulative-vs-retained semantic only.
 */
import { describe, it, expect } from 'vitest';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
import { DebugSessionRegistry } from '../../src/debug/debug-session-registry.js';
import { SessionArchiveWriter } from '../../src/debug/archive/session-archive-writer.js';
import { SessionArchiveReader } from '../../src/debug/archive/session-archive-reader.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import type { NetEvent } from '../../src/event/net-event.js';

const INPUT = place<string>('Input');
const OUTPUT = place<string>('Output');

const TEST_NET = PetriNet.builder('ConsistencyNet')
  .transition(
    Transition.builder('Process')
      .inputs(one(INPUT))
      .outputs(outPlace(OUTPUT))
      .build(),
  )
  .build();

function tokenAddedEvent(i: number, ts: number): NetEvent {
  return {
    type: 'token-added',
    timestamp: ts,
    placeName: 'Output',
    token: { value: `v${i}`, createdAt: ts },
  };
}

describe('SessionArchiveWriter eventCount-vs-body consistency', () => {
  const writer = new SessionArchiveWriter();
  const reader = new SessionArchiveReader();

  for (const version of ['v1', 'v2', 'v3'] as const) {
    it(`${version}: header eventCount equals body length after eviction`, () => {
      const cap = 10;
      const totalAppends = 100;
      const registry = new DebugSessionRegistry(
        50,
        (sid) => new DebugEventStore(sid, cap),
      );
      const session = registry.register(`evict-${version}`, TEST_NET);

      const t0 = Date.now();
      for (let i = 0; i < totalAppends; i++) {
        session.eventStore.append(tokenAddedEvent(i, t0 + i));
      }

      // Sanity: the live store has cumulative=100 but only 10 retained.
      expect(session.eventStore.eventCount()).toBe(totalAppends);
      expect(session.eventStore.size()).toBe(cap);

      const compressed =
        version === 'v1'
          ? writer.writeV1(session)
          : version === 'v2'
            ? writer.writeV2(session)
            : writer.writeV3(session);

      const imported = reader.readFull(compressed);

      // Header reflects retained body length, not the cumulative counter.
      expect(imported.metadata.eventCount).toBe(cap);
      expect(imported.eventStore.events().length).toBe(cap);
      expect(imported.metadata.eventCount).toBe(imported.eventStore.events().length);

      // V2/V3: histogram must sum to header eventCount.
      const meta = imported.metadata;
      if (meta.version === 2 || meta.version === 3) {
        const sum = Object.values(meta.metadata.eventTypeHistogram).reduce(
          (a, b) => a + b,
          0,
        );
        expect(sum).toBe(meta.eventCount);
      }
    });
  }
});
