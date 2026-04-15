import { describe, it, expect, vi } from 'vitest';
import { DebugSessionRegistry, buildNetStructure } from '../../src/debug/debug-session-registry.js';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
import type { SessionCompletionListener } from '../../src/debug/session-completion-listener.js';
import type { NetStructure } from '../../src/debug/debug-response.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';

const INPUT = place<string>('Input');
const OUTPUT = place<string>('Output');

const TEST_NET = PetriNet.builder('TestNet')
  .transition(
    Transition.builder('Process')
      .inputs(one(INPUT))
      .outputs(outPlace(OUTPUT))
      .build()
  )
  .build();

describe('DebugSessionRegistry', () => {
  it('should register session', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('session-1', TEST_NET);

    expect(session).toBeDefined();
    expect(session.sessionId).toBe('session-1');
    expect(session.netName).toBe('TestNet');
    expect(session.active).toBe(true);
    expect(session.dotDiagram).toBeDefined();
    expect(session.eventStore).toBeDefined();
  });

  it('should get session by id', () => {
    const registry = new DebugSessionRegistry();
    registry.register('session-1', TEST_NET);

    const session = registry.getSession('session-1');
    expect(session).toBeDefined();
    expect(session!.sessionId).toBe('session-1');
  });

  it('should return undefined for unknown session', () => {
    const registry = new DebugSessionRegistry();
    expect(registry.getSession('unknown')).toBeUndefined();
  });

  it('should list sessions', () => {
    const registry = new DebugSessionRegistry();
    registry.register('session-1', TEST_NET);
    registry.register('session-2', TEST_NET);
    registry.register('session-3', TEST_NET);

    const sessions = registry.listSessions(10);
    expect(sessions).toHaveLength(3);
  });

  it('should limit session list', () => {
    const registry = new DebugSessionRegistry();
    for (let i = 0; i < 10; i++) {
      registry.register(`session-${i}`, TEST_NET);
    }

    const sessions = registry.listSessions(3);
    expect(sessions).toHaveLength(3);
  });

  it('should complete session', () => {
    const registry = new DebugSessionRegistry();
    registry.register('session-1', TEST_NET);

    registry.complete('session-1');

    const session = registry.getSession('session-1');
    expect(session).toBeDefined();
    expect(session!.active).toBe(false);
  });

  it('should list active sessions', () => {
    const registry = new DebugSessionRegistry();
    registry.register('session-1', TEST_NET);
    registry.register('session-2', TEST_NET);
    registry.register('session-3', TEST_NET);
    registry.complete('session-2');

    const activeSessions = registry.listActiveSessions(10);
    expect(activeSessions).toHaveLength(2);
    expect(activeSessions.every(s => s.active)).toBe(true);
  });

  it('should remove session', () => {
    const registry = new DebugSessionRegistry();
    registry.register('session-1', TEST_NET);

    const removed = registry.remove('session-1');
    expect(removed).toBeDefined();
    expect(removed!.sessionId).toBe('session-1');
    expect(registry.getSession('session-1')).toBeUndefined();
  });

  it('should evict old sessions when at capacity', () => {
    const registry = new DebugSessionRegistry(3);
    registry.register('session-1', TEST_NET);
    registry.register('session-2', TEST_NET);
    registry.register('session-3', TEST_NET);
    registry.complete('session-1'); // Mark as inactive

    // This should evict session-1 (oldest inactive)
    registry.register('session-4', TEST_NET);

    expect(registry.size).toBe(3);
    expect(registry.getSession('session-1')).toBeUndefined();
    expect(registry.getSession('session-4')).toBeDefined();
  });

  it('should generate DOT diagram', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('session-1', TEST_NET);

    expect(session.dotDiagram).toBeDefined();
    expect(session.dotDiagram).toContain('digraph');
    expect(session.dotDiagram).toContain('Input');
    expect(session.dotDiagram).toContain('Output');
    expect(session.dotDiagram).toContain('Process');
  });

  it('should use custom event store factory', () => {
    let customStoreCreated = false;
    const factory = (sessionId: string) => {
      customStoreCreated = true;
      return new DebugEventStore(sessionId);
    };

    const registry = new DebugSessionRegistry(50, factory);
    registry.register('session-1', TEST_NET);

    expect(customStoreCreated).toBe(true);
  });

  it('should store place and transition info', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('session-1', TEST_NET);

    expect(session.places).toBeDefined();
    const placesData = session.places.data;
    expect(placesData.has('Input')).toBe(true);
    expect(placesData.has('Output')).toBe(true);

    const inputInfo = placesData.get('Input')!;
    expect(inputInfo.hasIncoming).toBe(false); // Start place
    expect(inputInfo.hasOutgoing).toBe(true);

    const outputInfo = placesData.get('Output')!;
    expect(outputInfo.hasIncoming).toBe(true);
    expect(outputInfo.hasOutgoing).toBe(false); // End place

    expect(session.transitions).toBeDefined();
    expect(session.transitions.size).toBe(1);
    expect([...session.transitions].some(t => t.name === 'Process')).toBe(true);
  });

  describe('completion listeners', () => {
    it('should notify listener on session completion', () => {
      const completed: string[] = [];
      const listener: SessionCompletionListener = (session) => {
        completed.push(session.sessionId);
      };
      const registry = new DebugSessionRegistry(50, undefined, [listener]);
      registry.register('session-1', TEST_NET);

      registry.complete('session-1');

      expect(completed).toEqual(['session-1']);
    });

    it('should notify multiple listeners', () => {
      const results1: string[] = [];
      const results2: string[] = [];
      const registry = new DebugSessionRegistry(50, undefined, [
        (s) => results1.push(s.sessionId),
        (s) => results2.push(s.sessionId),
      ]);
      registry.register('session-1', TEST_NET);
      registry.complete('session-1');

      expect(results1).toEqual(['session-1']);
      expect(results2).toEqual(['session-1']);
    });

    it('should continue notifying after listener throws', () => {
      const results: string[] = [];
      const consoleSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});

      const registry = new DebugSessionRegistry(50, undefined, [
        () => { throw new Error('boom'); },
        (s) => results.push(s.sessionId),
      ]);
      registry.register('session-1', TEST_NET);
      registry.complete('session-1');

      expect(results).toEqual(['session-1']);
      consoleSpy.mockRestore();
    });

    it('should not notify on non-existent session completion', () => {
      const completed: string[] = [];
      const registry = new DebugSessionRegistry(50, undefined, [
        (s) => completed.push(s.sessionId),
      ]);

      registry.complete('nonexistent');
      expect(completed).toEqual([]);
    });
  });

  describe('registerImported', () => {
    it('should register imported session as inactive', () => {
      const registry = new DebugSessionRegistry();
      const structure: NetStructure = {
        places: [{ name: 'P1', graphId: 'p_P1', tokenType: 'String', isStart: true, isEnd: false, isEnvironment: false }],
        transitions: [{ name: 'T1', graphId: 't_T1' }],
      };
      const eventStore = new DebugEventStore('imported-1');

      const session = registry.registerImported('imported-1', 'ImportedNet', 'digraph {}', structure, eventStore, Date.now());

      expect(session.active).toBe(false);
      expect(session.sessionId).toBe('imported-1');
      expect(session.netName).toBe('ImportedNet');
      expect(session.importedStructure).toBe(structure);
      expect(session.places).toBeNull();
    });

    it('should be retrievable after import', () => {
      const registry = new DebugSessionRegistry();
      const structure: NetStructure = { places: [], transitions: [] };
      const eventStore = new DebugEventStore('imported-2');

      registry.registerImported('imported-2', 'Net', 'digraph {}', structure, eventStore, Date.now());

      expect(registry.getSession('imported-2')).toBeDefined();
      expect(registry.size).toBe(1);
    });
  });

  describe('buildNetStructure', () => {
    it('should build structure from live session', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('live-1', TEST_NET);

      const structure = buildNetStructure(session);

      expect(structure.places.length).toBeGreaterThan(0);
      expect(structure.transitions.length).toBeGreaterThan(0);
      expect(structure.places.some(p => p.name === 'Input')).toBe(true);
      expect(structure.places.some(p => p.name === 'Output')).toBe(true);
      expect(structure.transitions.some(t => t.name === 'Process')).toBe(true);
    });

    it('should return imported structure for imported session', () => {
      const registry = new DebugSessionRegistry();
      const importedStructure: NetStructure = {
        places: [{ name: 'Custom', graphId: 'p_Custom', tokenType: 'Any', isStart: true, isEnd: true, isEnvironment: false }],
        transitions: [{ name: 'CustomT', graphId: 't_CustomT' }],
      };
      const session = registry.registerImported('imp-1', 'Net', 'digraph {}', importedStructure, new DebugEventStore('imp-1'), Date.now());

      const structure = buildNetStructure(session);

      expect(structure).toBe(importedStructure);
    });

    it('should return empty structure when no places', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.registerImported('no-places', 'Net', 'digraph {}', null as unknown as NetStructure, new DebugEventStore('no-places'), Date.now());
      // importedStructure is null, places is also null
      const noImportSession = { ...session, importedStructure: null };

      const structure = buildNetStructure(noImportSession);
      expect(structure.places).toEqual([]);
      expect(structure.transitions).toEqual([]);
    });
  });

  // ======================== Tags + endTime (libpetri 1.6.0) ========================

  describe('tags and endTime', () => {
    it('should register session with tags', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET, { channel: 'voice', env: 'staging' });

      expect(registry.tagsFor('session-1')).toEqual({ channel: 'voice', env: 'staging' });
    });

    it('should default to empty tags when no tags arg provided', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET);

      expect(registry.tagsFor('session-1')).toEqual({});
    });

    it('should return empty tags for unknown session', () => {
      const registry = new DebugSessionRegistry();
      expect(registry.tagsFor('never-registered')).toEqual({});
    });

    it('should set tag after registration', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET);

      registry.tag('session-1', 'channel', 'text');
      registry.tag('session-1', 'experiment', 'abc');

      expect(registry.tagsFor('session-1')).toEqual({ channel: 'text', experiment: 'abc' });
    });

    it('should replace existing tag value', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET, { channel: 'voice' });

      registry.tag('session-1', 'channel', 'text');

      expect(registry.tagsFor('session-1')).toEqual({ channel: 'text' });
    });

    it('should no-op when tagging an unknown session', () => {
      const registry = new DebugSessionRegistry();

      registry.tag('never-registered', 'channel', 'voice');

      expect(registry.tagsFor('never-registered')).toEqual({});
      expect(registry.listSessions(10, { channel: 'voice' })).toHaveLength(0);
    });

    it('should no-op when tagging a removed session', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET);
      registry.remove('session-1');

      registry.tag('session-1', 'channel', 'voice');

      expect(registry.tagsFor('session-1')).toEqual({});
    });

    it('should filter sessions by tag', () => {
      const registry = new DebugSessionRegistry();
      registry.register('text-1', TEST_NET, { channel: 'text' });
      registry.register('voice-1', TEST_NET, { channel: 'voice' });
      registry.register('voice-2', TEST_NET, { channel: 'voice' });

      const voices = registry.listSessions(10, { channel: 'voice' });

      expect(voices).toHaveLength(2);
      expect(voices.every(s => s.sessionId.startsWith('voice'))).toBe(true);
    });

    it('should AND-match multiple tag keys', () => {
      const registry = new DebugSessionRegistry();
      registry.register('s1', TEST_NET, { channel: 'voice', env: 'staging' });
      registry.register('s2', TEST_NET, { channel: 'voice', env: 'prod' });
      registry.register('s3', TEST_NET, { channel: 'text', env: 'staging' });

      const filtered = registry.listSessions(10, { channel: 'voice', env: 'staging' });

      expect(filtered).toHaveLength(1);
      expect(filtered[0]!.sessionId).toBe('s1');
    });

    it('should not match when a filter key value differs', () => {
      const registry = new DebugSessionRegistry();
      registry.register('s1', TEST_NET, { channel: 'voice', env: 'staging' });

      const result = registry.listSessions(10, { channel: 'voice', env: 'prod' });

      expect(result).toHaveLength(0);
    });

    it('should not match when a filter key is absent from session tags', () => {
      const registry = new DebugSessionRegistry();
      registry.register('s1', TEST_NET, { channel: 'voice' });

      const result = registry.listSessions(10, { env: 'staging' });

      expect(result).toHaveLength(0);
    });

    it('should filter active sessions by tag', () => {
      const registry = new DebugSessionRegistry();
      registry.register('active-voice', TEST_NET, { channel: 'voice' });
      registry.register('completed-voice', TEST_NET, { channel: 'voice' });
      registry.register('active-text', TEST_NET, { channel: 'text' });
      registry.complete('completed-voice');

      const activeVoices = registry.listActiveSessions(10, { channel: 'voice' });

      expect(activeVoices).toHaveLength(1);
      expect(activeVoices[0]!.sessionId).toBe('active-voice');
    });

    it('should stamp endTime on complete', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('session-1', TEST_NET);
      expect(session.endTime).toBeUndefined();

      registry.complete('session-1');
      const completed = registry.getSession('session-1')!;

      expect(completed.endTime).toBeDefined();
      expect(completed.active).toBe(false);
    });

    it('should preserve endTime on second complete', () => {
      // Mock the system clock so the test proves preservation rather than racing Date.now().
      // Without this, a fast runner can return the same millisecond twice and the test would
      // pass trivially. With fake timers we *know* time advanced between the two complete()
      // calls, so `secondEnd === firstEnd` can only hold if the code actually preserved it.
      vi.useFakeTimers();
      try {
        vi.setSystemTime(new Date('2026-04-15T10:00:00Z'));

        const registry = new DebugSessionRegistry();
        registry.register('session-1', TEST_NET);

        registry.complete('session-1');
        const firstEnd = registry.getSession('session-1')!.endTime;
        expect(firstEnd).toBe(Date.now());

        vi.setSystemTime(new Date('2026-04-15T10:00:10Z'));
        registry.complete('session-1');
        const secondEnd = registry.getSession('session-1')!.endTime;

        expect(secondEnd).toBe(firstEnd);
        expect(secondEnd).not.toBe(Date.now());
      } finally {
        vi.useRealTimers();
      }
    });

    it('should have undefined duration for active session', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('session-1', TEST_NET);

      expect(session.endTime).toBeUndefined();
    });

    it('should clear tags on remove', () => {
      const registry = new DebugSessionRegistry();
      registry.register('session-1', TEST_NET, { channel: 'voice' });

      registry.remove('session-1');

      expect(registry.tagsFor('session-1')).toEqual({});
    });

    it('should register imported session with tags and endTime', () => {
      const registry = new DebugSessionRegistry();
      const structure: NetStructure = {
        places: [{ name: 'P1', graphId: 'p_P1', tokenType: 'String', isStart: true, isEnd: false, isEnvironment: false }],
        transitions: [{ name: 'T1', graphId: 't_T1' }],
      };
      const startTime = Date.now() - 60_000;
      const endTime = Date.now();

      const session = registry.registerImported(
        'imported-1', 'TestNet', 'digraph{}', structure,
        new DebugEventStore('imported-1'), startTime, endTime, { channel: 'voice', source: 'archive' }
      );

      expect(session.active).toBe(false);
      expect(session.endTime).toBe(endTime);
      expect(registry.tagsFor('imported-1')).toEqual({ channel: 'voice', source: 'archive' });
    });

    it('should preserve tag immutability', () => {
      const registry = new DebugSessionRegistry();
      const tags = { channel: 'voice' };
      registry.register('session-1', TEST_NET, tags);

      // Mutating the passed-in tags shouldn't affect stored tags
      (tags as Record<string, string>).channel = 'text';

      expect(registry.tagsFor('session-1').channel).toBe('voice');
    });

    it('should cleanup tags on eviction', () => {
      const registry = new DebugSessionRegistry(2);
      registry.register('session-1', TEST_NET, { channel: 'voice' });
      registry.register('session-2', TEST_NET, { channel: 'text' });
      registry.complete('session-1');

      registry.register('session-3', TEST_NET, { channel: 'voice' });

      expect(registry.getSession('session-1')).toBeUndefined();
      expect(registry.tagsFor('session-1')).toEqual({});
      expect(registry.tagsFor('session-2')).toEqual({ channel: 'text' });
      expect(registry.tagsFor('session-3')).toEqual({ channel: 'voice' });
    });
  });
});
