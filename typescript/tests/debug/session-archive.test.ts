import { describe, it, expect } from 'vitest';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
import { DebugSessionRegistry, buildNetStructure } from '../../src/debug/debug-session-registry.js';
import { SessionArchiveWriter } from '../../src/debug/archive/session-archive-writer.js';
import { SessionArchiveReader } from '../../src/debug/archive/session-archive-reader.js';
import { CURRENT_VERSION } from '../../src/debug/archive/session-archive.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import type { NetEvent } from '../../src/event/net-event.js';

const INPUT = place<string>('Input');
const OUTPUT = place<string>('Output');

const TEST_NET = PetriNet.builder('ArchiveTestNet')
  .transition(
    Transition.builder('Process')
      .inputs(one(INPUT))
      .outputs(outPlace(OUTPUT))
      .build()
  )
  .build();

function enabledEvent(name: string, ts = Date.now()): NetEvent {
  return { type: 'transition-enabled', timestamp: ts, transitionName: name };
}

function startedEvent(name: string, ts = Date.now()): NetEvent {
  return {
    type: 'transition-started',
    timestamp: ts,
    transitionName: name,
    consumedTokens: [{ value: 'test-value', createdAt: ts }],
  };
}

function completedEvent(name: string, ts = Date.now()): NetEvent {
  return {
    type: 'transition-completed',
    timestamp: ts,
    transitionName: name,
    producedTokens: [{ value: 'result-value', createdAt: ts }],
    durationMs: 42,
  };
}

describe('SessionArchive round-trip', () => {
  const writer = new SessionArchiveWriter();
  const reader = new SessionArchiveReader();

  it('should round-trip a session with events', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('round-trip-1', TEST_NET);

    const ts = Date.now();
    session.eventStore.append(enabledEvent('Process', ts));
    session.eventStore.append(startedEvent('Process', ts + 10));
    session.eventStore.append(completedEvent('Process', ts + 50));

    registry.complete('round-trip-1');
    const completed = registry.getSession('round-trip-1')!;

    const compressed = writer.write(completed);
    const imported = reader.readFull(compressed);

    expect(imported.metadata.version).toBe(CURRENT_VERSION);
    expect(imported.metadata.sessionId).toBe('round-trip-1');
    expect(imported.metadata.netName).toBe('ArchiveTestNet');
    expect(imported.metadata.dotDiagram).toContain('digraph');
    expect(imported.metadata.eventCount).toBe(3);
    expect(imported.eventStore.eventCount()).toBe(3);
  });

  it('should round-trip an empty session', () => {
    const registry = new DebugSessionRegistry();
    registry.register('empty-1', TEST_NET);
    registry.complete('empty-1');
    const session = registry.getSession('empty-1')!;

    const compressed = writer.write(session);
    const imported = reader.readFull(compressed);

    expect(imported.metadata.eventCount).toBe(0);
    expect(imported.eventStore.eventCount()).toBe(0);
  });

  it('should read metadata without loading events', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('meta-only-1', TEST_NET);
    session.eventStore.append(enabledEvent('Process'));
    session.eventStore.append(enabledEvent('Process'));
    registry.complete('meta-only-1');

    const compressed = writer.write(registry.getSession('meta-only-1')!);
    const metadata = reader.readMetadata(compressed);

    expect(metadata.sessionId).toBe('meta-only-1');
    expect(metadata.eventCount).toBe(2);
    expect(metadata.version).toBe(CURRENT_VERSION);
  });

  it('should preserve net structure in round-trip', () => {
    const registry = new DebugSessionRegistry();
    registry.register('struct-1', TEST_NET);
    registry.complete('struct-1');
    const session = registry.getSession('struct-1')!;

    const originalStructure = buildNetStructure(session);
    const compressed = writer.write(session);
    const imported = reader.readFull(compressed);

    expect(imported.metadata.structure.places).toHaveLength(originalStructure.places.length);
    expect(imported.metadata.structure.transitions).toHaveLength(originalStructure.transitions.length);

    for (const place of originalStructure.places) {
      const found = imported.metadata.structure.places.find(p => p.name === place.name);
      expect(found).toBeDefined();
      expect(found!.graphId).toBe(place.graphId);
      expect(found!.isStart).toBe(place.isStart);
      expect(found!.isEnd).toBe(place.isEnd);
    }
  });

  it('should handle large event counts', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('large-1', TEST_NET);

    for (let i = 0; i < 500; i++) {
      session.eventStore.append(enabledEvent(`T_${i}`, Date.now() + i));
    }
    registry.complete('large-1');

    const compressed = writer.write(registry.getSession('large-1')!);
    const imported = reader.readFull(compressed);

    expect(imported.metadata.eventCount).toBe(500);
    expect(imported.eventStore.eventCount()).toBe(500);
  });

  it('should re-import into registry', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('orig-1', TEST_NET);
    session.eventStore.append(enabledEvent('Process'));
    registry.complete('orig-1');

    const compressed = writer.write(registry.getSession('orig-1')!);
    const imported = reader.readFull(compressed);

    const importedSession = registry.registerImported(
      imported.metadata.sessionId + '-reimport',
      imported.metadata.netName,
      imported.metadata.dotDiagram,
      imported.metadata.structure,
      imported.eventStore,
      new Date(imported.metadata.startTime).getTime(),
    );

    expect(importedSession.active).toBe(false);
    expect(importedSession.importedStructure).toBeDefined();
    expect(importedSession.eventStore.eventCount()).toBe(1);

    const structure = buildNetStructure(importedSession);
    expect(structure.places.length).toBeGreaterThan(0);
    expect(structure.transitions.length).toBeGreaterThan(0);
  });

  it('should preserve event types in round-trip', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('types-1', TEST_NET);
    const ts = Date.now();

    session.eventStore.append(enabledEvent('Process', ts));
    session.eventStore.append(startedEvent('Process', ts + 10));
    session.eventStore.append(completedEvent('Process', ts + 50));
    session.eventStore.append({
      type: 'token-added',
      timestamp: ts + 60,
      placeName: 'Output',
      token: { value: 'result', createdAt: ts + 50 },
    });

    registry.complete('types-1');
    const compressed = writer.write(registry.getSession('types-1')!);
    const imported = reader.readFull(compressed);

    const events = imported.eventStore.events();
    expect(events).toHaveLength(4);
    expect(events[0]!.type).toBe('transition-enabled');
    expect(events[1]!.type).toBe('transition-started');
    expect(events[2]!.type).toBe('transition-completed');
    expect(events[3]!.type).toBe('token-added');
  });
});
