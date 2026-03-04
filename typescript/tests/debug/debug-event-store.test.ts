import { describe, it, expect, vi } from 'vitest';
import { DebugEventStore, DEFAULT_MAX_EVENTS } from '../../src/debug/debug-event-store.js';
import type { NetEvent } from '../../src/event/net-event.js';
import { tokenOf } from '../../src/core/token.js';

function enabledEvent(name: string, ts = Date.now()): NetEvent {
  return { type: 'transition-enabled', timestamp: ts, transitionName: name };
}

describe('DebugEventStore', () => {
  it('should store and retrieve events', () => {
    const store = new DebugEventStore('test-session');
    const e1 = enabledEvent('T1');
    const e2 = enabledEvent('T2');

    store.append(e1);
    store.append(e2);

    expect(store.size()).toBe(2);
    expect(store.eventCount()).toBe(2);
    expect(store.events()).toEqual([e1, e2]);
  });

  it('should broadcast events to subscribers', async () => {
    const store = new DebugEventStore('test-session');
    const received: NetEvent[] = [];

    store.subscribe(event => received.push(event));

    const e1 = enabledEvent('T1');
    const e2 = enabledEvent('T2');
    store.append(e1);
    store.append(e2);

    // Wait for microtask broadcast
    await new Promise(r => setTimeout(r, 10));

    expect(received).toEqual([e1, e2]);
  });

  it('should stop broadcasting after unsubscribe', async () => {
    const store = new DebugEventStore('test-session');
    const received: NetEvent[] = [];

    const subscription = store.subscribe(event => received.push(event));
    store.append(enabledEvent('T1'));

    await new Promise(r => setTimeout(r, 10));

    subscription.cancel();
    expect(subscription.isActive()).toBe(false);

    store.append(enabledEvent('T2'));
    await new Promise(r => setTimeout(r, 10));

    expect(received).toHaveLength(1);
  });

  it('should query events since timestamp', () => {
    const store = new DebugEventStore('test-session');
    const e1 = enabledEvent('T1', 100);
    const e2 = enabledEvent('T2', 200);

    store.append(e1);
    store.append(e2);

    const since = store.eventsSince(150);
    expect(since).toHaveLength(1);
    expect((since[0] as { transitionName: string }).transitionName).toBe('T2');
  });

  it('should query events between timestamps', () => {
    const store = new DebugEventStore('test-session');
    store.append(enabledEvent('T1', 100));
    store.append(enabledEvent('T2', 200));
    store.append(enabledEvent('T3', 300));

    const between = store.eventsBetween(150, 250);
    expect(between).toHaveLength(1);
    expect((between[0] as { transitionName: string }).transitionName).toBe('T2');
  });

  it('should query events from index', () => {
    const store = new DebugEventStore('test-session');
    for (let i = 0; i < 5; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    const from = store.eventsFrom(3);
    expect(from).toHaveLength(2);
    expect((from[0] as { transitionName: string }).transitionName).toBe('T3');
    expect((from[1] as { transitionName: string }).transitionName).toBe('T4');
  });

  it('should support multiple subscribers', async () => {
    const store = new DebugEventStore('test-session');
    const received1: NetEvent[] = [];
    const received2: NetEvent[] = [];

    store.subscribe(event => received1.push(event));
    store.subscribe(event => received2.push(event));

    store.append(enabledEvent('T1'));
    await new Promise(r => setTimeout(r, 10));

    expect(received1).toHaveLength(1);
    expect(received2).toHaveLength(1);
    expect(store.subscriberCount()).toBe(2);
  });

  it('should return session id', () => {
    const store = new DebugEventStore('my-session-id');
    expect(store.sessionId).toBe('my-session-id');
  });

  it('should report enabled', () => {
    const store = new DebugEventStore('test-session');
    expect(store.isEnabled()).toBe(true);
  });

  it('should evict oldest events when capacity exceeded', () => {
    const store = new DebugEventStore('test-session', 3);

    for (let i = 0; i < 5; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    expect(store.events()).toHaveLength(3);
    expect(store.eventCount()).toBe(5);
    expect(store.evictedCount()).toBe(2);
    expect(store.maxEvents).toBe(3);

    const names = store.events().map(e => (e as { transitionName: string }).transitionName);
    expect(names).toEqual(['T2', 'T3', 'T4']);
  });

  it('should adjust eventsFrom for evicted events', () => {
    const store = new DebugEventStore('test-session', 5);

    for (let i = 0; i < 8; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    // 3 events evicted (T0, T1, T2), retained: T3, T4, T5, T6, T7
    expect(store.evictedCount()).toBe(3);

    expect(store.eventsFrom(0)).toHaveLength(5);
    expect(store.eventsFrom(3)).toHaveLength(5);

    const from5 = store.eventsFrom(5);
    expect(from5).toHaveLength(3);
    expect((from5[0] as { transitionName: string }).transitionName).toBe('T5');

    expect(store.eventsFrom(8)).toHaveLength(0);
  });

  it('should not evict when under capacity', () => {
    const store = new DebugEventStore('test-session', 10);

    for (let i = 0; i < 5; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    expect(store.events()).toHaveLength(5);
    expect(store.eventCount()).toBe(5);
    expect(store.evictedCount()).toBe(0);
  });

  it('should reject non-positive maxEvents', () => {
    expect(() => new DebugEventStore('test', 0)).toThrow();
    expect(() => new DebugEventStore('test', -1)).toThrow();
  });

  it('should use default max events', () => {
    const store = new DebugEventStore('test-session');
    expect(store.maxEvents).toBe(DEFAULT_MAX_EVENTS);
  });

  it('size should equal events list size after eviction', () => {
    const store = new DebugEventStore('test-session', 3);

    for (let i = 0; i < 10; i++) {
      store.append(enabledEvent(`T${i}`));
    }

    expect(store.size()).toBe(store.events().length);
    expect(store.size()).toBe(3);
  });

  it('should not break when subscriber throws', async () => {
    const store = new DebugEventStore('test-session');
    const received: NetEvent[] = [];
    const consoleSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});

    store.subscribe(() => { throw new Error('boom'); });
    store.subscribe(event => received.push(event));

    store.append(enabledEvent('T1'));
    await new Promise(r => setTimeout(r, 10));

    expect(received).toHaveLength(1);
    consoleSpy.mockRestore();
  });

  it('should store and broadcast log message events', async () => {
    const store = new DebugEventStore('test-session');
    const received: NetEvent[] = [];

    store.subscribe(event => received.push(event));

    const logEvent: NetEvent = {
      type: 'log-message',
      timestamp: Date.now(),
      transitionName: 'T1',
      logger: 'com.example.Foo',
      level: 'INFO',
      message: 'hello world',
      error: null,
      errorMessage: null,
    };
    store.append(logEvent);

    await new Promise(r => setTimeout(r, 10));

    expect(store.events()).toHaveLength(1);
    expect(received).toHaveLength(1);
    expect(received[0]!.type).toBe('log-message');
    expect((received[0] as { message: string }).message).toBe('hello world');
  });

  it('should preserve event ordering across async broadcast', async () => {
    const store = new DebugEventStore('test-session');
    const count = 100;
    const received: NetEvent[] = [];

    store.subscribe(event => received.push(event));

    const events: NetEvent[] = [];
    for (let i = 0; i < count; i++) {
      events.push(enabledEvent(`T${i}`));
    }

    for (const event of events) {
      store.append(event);
    }

    await new Promise(r => setTimeout(r, 50));

    expect(received).toEqual(events);
  });

  it('close should stop broadcasts', async () => {
    const store = new DebugEventStore('test-session');
    const received: NetEvent[] = [];

    store.subscribe(event => received.push(event));

    store.append(enabledEvent('T1'));
    await new Promise(r => setTimeout(r, 10));

    store.close();

    store.append(enabledEvent('T2'));
    await new Promise(r => setTimeout(r, 10));

    expect(received).toHaveLength(1);
    expect(store.size()).toBe(2);
  });

  it('should report isEmpty correctly', () => {
    const store = new DebugEventStore('test-session');
    expect(store.isEmpty()).toBe(true);

    store.append(enabledEvent('T1'));
    expect(store.isEmpty()).toBe(false);
  });
});
