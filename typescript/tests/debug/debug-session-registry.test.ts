import { describe, it, expect } from 'vitest';
import { DebugSessionRegistry } from '../../src/debug/debug-session-registry.js';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
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
});
