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
});
