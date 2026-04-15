import { describe, it, expect } from 'vitest';
import { gunzipSync, gzipSync } from 'node:zlib';
import { DebugSessionRegistry } from '../../src/debug/debug-session-registry.js';
import { SessionArchiveWriter } from '../../src/debug/archive/session-archive-writer.js';
import { SessionArchiveReader } from '../../src/debug/archive/session-archive-reader.js';
import {
  CURRENT_VERSION,
  MIN_SUPPORTED_VERSION,
  type SessionArchiveV2,
} from '../../src/debug/archive/session-archive.js';
import { computeMetadata } from '../../src/debug/archive/session-metadata.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import type { NetEvent } from '../../src/event/net-event.js';

const INPUT = place<string>('Input');
const OUTPUT = place<string>('Output');

const TEST_NET = PetriNet.builder('ArchiveV2TestNet')
  .transition(
    Transition.builder('Process')
      .inputs(one(INPUT))
      .outputs(outPlace(OUTPUT))
      .build()
  )
  .build();

function transitionEnabled(name: string, ts: number): NetEvent {
  return { type: 'transition-enabled', timestamp: ts, transitionName: name };
}

function transitionStarted(name: string, ts: number): NetEvent {
  return {
    type: 'transition-started',
    timestamp: ts,
    transitionName: name,
    consumedTokens: [{ value: 'payload', createdAt: ts }],
  };
}

function transitionCompleted(name: string, ts: number): NetEvent {
  return {
    type: 'transition-completed',
    timestamp: ts,
    transitionName: name,
    producedTokens: [{ value: 'result', createdAt: ts }],
    durationMs: 20,
  };
}

function transitionFailed(name: string, ts: number): NetEvent {
  return {
    type: 'transition-failed',
    timestamp: ts,
    transitionName: name,
    errorMessage: 'boom',
    exceptionType: 'RuntimeError',
  };
}

function transitionTimedOut(name: string, ts: number): NetEvent {
  return {
    type: 'transition-timed-out',
    timestamp: ts,
    transitionName: name,
    deadlineMs: 100,
    actualDurationMs: 150,
  };
}

function actionTimedOut(name: string, ts: number): NetEvent {
  return { type: 'action-timed-out', timestamp: ts, transitionName: name, timeoutMs: 100 };
}

function logMessage(level: string, ts: number): NetEvent {
  return {
    type: 'log-message',
    timestamp: ts,
    transitionName: 'Process',
    logger: 'test',
    level,
    message: `${level} log line`,
    error: null,
    errorMessage: null,
  };
}

describe('SessionArchive v2 (libpetri 1.7.0)', () => {
  const writer = new SessionArchiveWriter();
  const reader = new SessionArchiveReader();

  describe('default write format', () => {
    it('should default to v2', () => {
      const registry = new DebugSessionRegistry();
      registry.register('default-v2', TEST_NET, { channel: 'voice' });

      const compressed = writer.write(registry.getSession('default-v2')!);
      const metadata = reader.readMetadata(compressed);

      expect(metadata.version).toBe(2);
      expect(metadata.version).toBe(CURRENT_VERSION);
    });
  });

  describe('tags + endTime round-trip', () => {
    it('should preserve tags and endTime across round-trip', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('voice-1', TEST_NET, {
        channel: 'voice',
        env: 'staging',
      });

      const t0 = Date.parse('2026-04-15T10:00:00Z');
      session.eventStore.append(transitionEnabled('Process', t0));
      session.eventStore.append(transitionStarted('Process', t0 + 10));
      session.eventStore.append(transitionCompleted('Process', t0 + 50));
      registry.complete('voice-1');

      const compressed = writer.write(registry.getSession('voice-1')!);
      const imported = reader.readFull(compressed);

      expect(imported.metadata.version).toBe(2);
      // Narrow the union via `version === 2` so TS knows v2-only fields exist.
      if (imported.metadata.version !== 2) throw new Error('expected v2');
      const v2 = imported.metadata;

      expect(v2.sessionId).toBe('voice-1');
      expect(v2.tags).toEqual({ channel: 'voice', env: 'staging' });
      expect(v2.endTime).toBeDefined();
      expect(Date.parse(v2.endTime!)).toBeGreaterThanOrEqual(t0);
    });

    it('should round-trip an empty session as v2 with empty tags', () => {
      const registry = new DebugSessionRegistry();
      registry.register('empty-v2', TEST_NET, { channel: 'text' });

      const compressed = writer.write(registry.getSession('empty-v2')!);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.eventCount).toBe(0);
      expect(imported.metadata.tags).toEqual({ channel: 'text' });
      expect(imported.metadata.metadata.eventTypeHistogram).toEqual({});
      expect(imported.metadata.metadata.hasErrors).toBe(false);
      expect(imported.metadata.endTime).toBeUndefined();
    });
  });

  describe('pre-computed metadata histogram', () => {
    it('should compute histogram with correct counts per event type', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('hist-1', TEST_NET);

      const t0 = Date.parse('2026-04-15T10:00:00Z');
      session.eventStore.append(transitionEnabled('Process', t0));
      session.eventStore.append(transitionStarted('Process', t0 + 10));
      session.eventStore.append(transitionStarted('Process', t0 + 20));
      session.eventStore.append(transitionCompleted('Process', t0 + 50));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      const histogram = imported.metadata.metadata.eventTypeHistogram;

      expect(histogram['TransitionEnabled']).toBe(1);
      expect(histogram['TransitionStarted']).toBe(2);
      expect(histogram['TransitionCompleted']).toBe(1);
      // Absent types should not appear in the histogram
      expect(histogram['TokenAdded']).toBeUndefined();
    });

    it('should emit histogram keys in alphabetical order for determinism', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('det-1', TEST_NET);

      const t0 = Date.parse('2026-04-15T10:00:00Z');
      // Append in a weird order to make sure sort happens.
      session.eventStore.append(transitionCompleted('Process', t0));
      session.eventStore.append(transitionEnabled('Process', t0 + 1));
      session.eventStore.append(transitionStarted('Process', t0 + 2));

      const metadata = computeMetadata(session.eventStore);
      const keys = Object.keys(metadata.eventTypeHistogram);
      const sorted = [...keys].sort();
      expect(keys).toEqual(sorted);
    });

    it('should track first and last event timestamps', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('ts-1', TEST_NET);

      const t0 = Date.parse('2026-04-15T10:00:00Z');
      session.eventStore.append(transitionEnabled('Process', t0));
      session.eventStore.append(transitionStarted('Process', t0 + 100));
      session.eventStore.append(transitionCompleted('Process', t0 + 200));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.metadata.firstEventTime).toBe(new Date(t0).toISOString());
      expect(imported.metadata.metadata.lastEventTime).toBe(new Date(t0 + 200).toISOString());
    });
  });

  describe('hasErrors detection', () => {
    it.each([
      ['TransitionFailed', transitionFailed],
      ['TransitionTimedOut', transitionTimedOut],
      ['ActionTimedOut', actionTimedOut],
    ] as const)('should flag hasErrors=true for %s', (_label, factory) => {
      const registry = new DebugSessionRegistry();
      const session = registry.register(`err-${_label}`, TEST_NET);
      const t0 = Date.parse('2026-04-15T10:00:00Z');
      session.eventStore.append(factory('Process', t0));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.metadata.hasErrors).toBe(true);
    });

    it('should flag hasErrors=true for LogMessage at ERROR level', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('err-log', TEST_NET);
      session.eventStore.append(logMessage('ERROR', Date.parse('2026-04-15T10:00:00Z')));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.metadata.hasErrors).toBe(true);
    });

    it('should flag hasErrors=true for LogMessage at lowercase error level', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('err-log-lower', TEST_NET);
      session.eventStore.append(logMessage('error', Date.parse('2026-04-15T10:00:00Z')));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.metadata.hasErrors).toBe(true);
    });

    it('should leave hasErrors=false for non-error events and INFO logs', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('clean', TEST_NET);
      const t0 = Date.parse('2026-04-15T10:00:00Z');
      session.eventStore.append(transitionEnabled('Process', t0));
      session.eventStore.append(logMessage('INFO', t0 + 1));
      session.eventStore.append(transitionCompleted('Process', t0 + 2));

      const compressed = writer.write(session);
      const imported = reader.readFull(compressed);

      if (imported.metadata.version !== 2) throw new Error('expected v2');
      expect(imported.metadata.metadata.hasErrors).toBe(false);
    });
  });

  describe('v1 backward compatibility', () => {
    it('should write v1 when writeV1() is called explicitly', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('legacy', TEST_NET, { channel: 'voice' });
      session.eventStore.append(transitionEnabled('Process', Date.now()));

      const compressed = writer.writeV1(session);
      const imported = reader.readFull(compressed);

      expect(imported.metadata.version).toBe(1);
      expect(imported.metadata.sessionId).toBe('legacy');
      expect(imported.eventStore.eventCount()).toBe(1);
      // v1 has no tags / endTime / metadata — narrow via discriminant.
      if (imported.metadata.version === 2) throw new Error('expected v1');
      // Accessing v2-only fields on v1 would be a compile error thanks to narrowing.
    });

    it('should read mixed v1 and v2 archives from the same reader', () => {
      const registry = new DebugSessionRegistry();
      const v1Session = registry.register('v1-session', TEST_NET);
      v1Session.eventStore.append(transitionEnabled('Process', Date.now()));

      const v2Session = registry.register('v2-session', TEST_NET, { channel: 'voice' });
      v2Session.eventStore.append(transitionEnabled('Process', Date.now()));

      const v1Bytes = writer.writeV1(v1Session);
      const v2Bytes = writer.write(v2Session); // default v2

      const v1Read = reader.readFull(v1Bytes);
      const v2Read = reader.readFull(v2Bytes);

      expect(v1Read.metadata.version).toBe(1);
      expect(v2Read.metadata.version).toBe(2);
      expect(v1Read.metadata.sessionId).toBe('v1-session');
      expect(v2Read.metadata.sessionId).toBe('v2-session');

      if (v2Read.metadata.version === 2) {
        expect(v2Read.metadata.tags).toEqual({ channel: 'voice' });
      }
    });
  });

  describe('unsupported version rejection', () => {
    it('should reject a hand-crafted header with version=99', () => {
      // Build a minimal v2-shaped header but with version=99 to simulate an
      // archive produced by a future libpetri version the current reader
      // can't understand.
      const badHeader = {
        version: 99,
        sessionId: 'x',
        netName: 'n',
        dotDiagram: 'digraph{}',
        startTime: new Date().toISOString(),
        eventCount: 0,
        structure: { places: [], transitions: [] },
      };
      const headerJson = Buffer.from(JSON.stringify(badHeader), 'utf-8');
      const metaLen = Buffer.alloc(4);
      metaLen.writeUInt32BE(headerJson.length);
      const raw = Buffer.concat([metaLen, headerJson]);
      const compressed = gzipSync(raw);

      expect(() => reader.readMetadata(compressed)).toThrow(
        /Unsupported archive version: 99/,
      );
      expect(() => reader.readMetadata(compressed)).toThrow(
        new RegExp(`${MIN_SUPPORTED_VERSION}..${CURRENT_VERSION}`),
      );
    });
  });

  describe('on-wire shape', () => {
    it('should serialize tags and metadata as first-class header fields', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('wire-1', TEST_NET, { channel: 'voice' });
      session.eventStore.append(transitionEnabled('Process', Date.parse('2026-04-15T10:00:00Z')));

      const compressed = writer.write(session);
      const raw = gunzipSync(compressed);
      const metaLen = raw.readUInt32BE(0);
      const headerJson = raw.subarray(4, 4 + metaLen).toString('utf-8');
      const headerObj = JSON.parse(headerJson) as SessionArchiveV2;

      expect(headerObj.version).toBe(2);
      expect(headerObj.tags).toEqual({ channel: 'voice' });
      expect(headerObj.metadata).toBeDefined();
      expect(headerObj.metadata.eventTypeHistogram['TransitionEnabled']).toBe(1);
      expect(headerObj.metadata.hasErrors).toBe(false);
    });
  });
});
