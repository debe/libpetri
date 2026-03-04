import { describe, it, expect } from 'vitest';
import { DebugAwareEventStore } from '../../src/debug/debug-aware-event-store.js';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
import { InMemoryEventStore, noopEventStore } from '../../src/event/event-store.js';
import type { NetEvent } from '../../src/event/net-event.js';

function enabledEvent(name: string): NetEvent {
  return { type: 'transition-enabled', timestamp: Date.now(), transitionName: name };
}

describe('DebugAwareEventStore', () => {
  it('should delegate append to both stores', () => {
    const primary = new InMemoryEventStore();
    const debug = new DebugEventStore('test');
    const store = new DebugAwareEventStore(primary, debug);

    const event = enabledEvent('T1');
    store.append(event);

    expect(primary.size()).toBe(1);
    expect(debug.size()).toBe(1);
    expect(primary.events()).toEqual([event]);
    expect(debug.events()).toEqual([event]);
  });

  it('should return events and size from primary only', () => {
    const primary = new InMemoryEventStore();
    const debug = new DebugEventStore('test', 1); // Small capacity
    const store = new DebugAwareEventStore(primary, debug);

    for (let i = 0; i < 5; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    expect(store.size()).toBe(5);
    expect(store.events()).toHaveLength(5);
    expect(store.isEmpty()).toBe(false);
  });

  it('should always be enabled', () => {
    const store = new DebugAwareEventStore(noopEventStore(), new DebugEventStore('test'));
    expect(store.isEnabled()).toBe(true);
  });

  it('should not break primary when debug store throws', () => {
    const primary = new InMemoryEventStore();
    const debug = new DebugEventStore('test');
    // Override append to throw
    debug.append = () => { throw new Error('debug store failure'); };
    const store = new DebugAwareEventStore(primary, debug);

    const event = enabledEvent('T1');
    expect(() => store.append(event)).not.toThrow();
    expect(primary.size()).toBe(1);
  });

  it('should expose debug store', () => {
    const debug = new DebugEventStore('my-session');
    const store = new DebugAwareEventStore(new InMemoryEventStore(), debug);
    expect(store.debugStore).toBe(debug);
    expect(store.debugStore.sessionId).toBe('my-session');
  });

  it('should report empty correctly', () => {
    const store = new DebugAwareEventStore(new InMemoryEventStore(), new DebugEventStore('test'));
    expect(store.isEmpty()).toBe(true);

    store.append(enabledEvent('T1'));
    expect(store.isEmpty()).toBe(false);
  });
});
