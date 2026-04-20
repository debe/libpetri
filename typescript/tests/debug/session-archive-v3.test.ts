import { describe, it, expect } from 'vitest';
import { DebugSessionRegistry } from '../../src/debug/debug-session-registry.js';
import { SessionArchiveWriter } from '../../src/debug/archive/session-archive-writer.js';
import { SessionArchiveReader } from '../../src/debug/archive/session-archive-reader.js';
import {
  CURRENT_VERSION,
  type SessionArchiveV3,
} from '../../src/debug/archive/session-archive.js';
import { tokenInfo } from '../../src/debug/net-event-converter.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import type { NetEvent } from '../../src/event/net-event.js';

const INPUT = place<object>('Input');

const TEST_NET = PetriNet.builder('ArchiveV3TestNet')
  .transition(Transition.builder('Process').inputs(one(INPUT)).build())
  .build();

/**
 * v3 is the default in libpetri 1.8.0. These tests cover:
 *   - default version dispatch
 *   - the `structured` field on {@code TokenInfo} survives a write/read round-trip
 *   - reader back-compat with v2 archives
 */
describe('SessionArchive v3 (libpetri 1.8.0)', () => {
  const writer = new SessionArchiveWriter();
  const reader = new SessionArchiveReader();

  describe('default write format', () => {
    it('should default to v3', () => {
      const registry = new DebugSessionRegistry();
      registry.register('default-v3', TEST_NET, { channel: 'voice' });

      const compressed = writer.write(registry.getSession('default-v3')!);
      const metadata = reader.readMetadata(compressed);

      expect(metadata.version).toBe(3);
      expect(metadata.version).toBe(CURRENT_VERSION);
    });

    it('should round-trip a v3 header with tags and pre-computed metadata', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('v3-hdr', TEST_NET, { channel: 'voice', env: 'staging' });
      const t0 = Date.parse('2026-04-17T10:00:00Z');
      session.eventStore.append({
        type: 'token-added',
        timestamp: t0,
        placeName: 'Input',
        token: { value: { kind: 'USER', text: 'hi', length: 2 }, createdAt: t0 },
      } satisfies NetEvent);
      registry.complete('v3-hdr');

      const compressed = writer.write(registry.getSession('v3-hdr')!);
      const imported = reader.readFull(compressed);

      expect(imported.metadata.version).toBe(3);
      if (imported.metadata.version !== 3) throw new Error('expected v3');
      const v3: SessionArchiveV3 = imported.metadata;

      expect(v3.tags).toEqual({ channel: 'voice', env: 'staging' });
      expect(v3.endTime).toBeDefined();
      expect(v3.metadata.eventTypeHistogram.TokenAdded).toBe(1);
    });
  });

  describe('structured token payloads', () => {
    it('should emit both value and structured on tokenInfo', () => {
      const msg = { kind: 'USER', text: 'hello', length: 5 };
      const info = tokenInfo({ value: msg, createdAt: Date.parse('2026-04-17T10:00:00Z') });

      // Display field remains the String() form for debug-UI compatibility.
      expect(info.value).toBe(String(msg));
      // Structured field carries the JSON-friendly projection.
      expect(info.structured).toEqual(msg);
      expect(info.type).toBe('Object');
    });

    it('should pass primitives through structured', () => {
      expect(
        tokenInfo({ value: 42, createdAt: 0 }).structured,
      ).toBe(42);
      expect(
        tokenInfo({ value: 'hello', createdAt: 0 }).structured,
      ).toBe('hello');
      expect(
        tokenInfo({ value: true, createdAt: 0 }).structured,
      ).toBe(true);
    });

    it('should omit structured for null/unit values', () => {
      const info = tokenInfo({ value: null, createdAt: 0 });
      expect(info.structured).toBeUndefined();
    });

    it('should serialize TS-private fields verbatim (non-#private is enumerable)', () => {
      // TypeScript's `private` is a type-only marker — the field remains enumerable at
      // runtime, so JSON.stringify picks it up. This test pins the behavior so callers
      // know archiving a `private`-field bean still exposes those fields on the wire.
      class TsPrivate {
        private readonly secret = 'hidden';
        toString() { return 'TsPrivate{***}'; }
      }
      const info = tokenInfo({ value: new TsPrivate(), createdAt: 0 });
      expect(info.value).toBe('TsPrivate{***}');
      expect(info.structured).toEqual({ secret: 'hidden' });
    });

    it('should omit structured for JS-#private-only objects (truly opaque)', () => {
      // JS `#fields` are inaccessible to JSON.stringify, so a bean whose only state is
      // #private serializes to `{}`. The empty-object guard drops `structured`.
      class JsOpaque {
        // eslint-disable-next-line @typescript-eslint/no-unused-vars
        readonly #hidden = 'secret';
        toString() { return 'JsOpaque{***}'; }
      }
      const info = tokenInfo({ value: new JsOpaque(), createdAt: 0 });
      expect(info.value).toBe('JsOpaque{***}');
      expect(info.structured).toBeUndefined();
    });
  });

  describe('round-trip preserves structured (EVT-025 AC5)', () => {
    it('should hydrate `structured` on the reconstructed token-added event', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('rt-structured', TEST_NET, { env: 'test' });
      const t0 = Date.parse('2026-04-17T10:00:00Z');
      const msg = { kind: 'USER', text: 'hi', length: 2 };
      session.eventStore.append({
        type: 'token-added',
        timestamp: t0,
        placeName: 'Input',
        token: { value: msg, createdAt: t0 },
      } satisfies NetEvent);
      registry.complete('rt-structured');

      const compressed = writer.write(registry.getSession('rt-structured')!);
      const imported = reader.readFull(compressed);

      const events = imported.eventStore.events();
      const added = events.find(e => e.type === 'token-added');
      expect(added).toBeDefined();
      if (added?.type !== 'token-added') throw new Error('expected token-added');
      // `structured` must match the writer-side projection verbatim — that is the
      // contract replay consumers (LLM-facing tools) rely on.
      expect(added.token.structured).toEqual(msg);
    });

    it('should hydrate `structured` on marking-snapshot events', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('rt-marking', TEST_NET);
      const t0 = Date.parse('2026-04-17T10:00:00Z');
      const msg = { kind: 'SYSTEM', text: 'bye' };
      session.eventStore.append({
        type: 'marking-snapshot',
        timestamp: t0,
        marking: new Map([['Input', [{ value: msg, createdAt: t0 }]]]),
      } satisfies NetEvent);
      registry.complete('rt-marking');

      const compressed = writer.write(registry.getSession('rt-marking')!);
      const imported = reader.readFull(compressed);
      const snapshot = imported.eventStore.events().find(e => e.type === 'marking-snapshot');
      if (snapshot?.type !== 'marking-snapshot') throw new Error('expected marking-snapshot');
      expect(snapshot.marking.get('Input')?.[0]?.structured).toEqual(msg);
    });

    it('should leave `structured` undefined when the writer omitted it', () => {
      const registry = new DebugSessionRegistry();
      const session = registry.register('rt-no-struct', TEST_NET);
      const t0 = Date.parse('2026-04-17T10:00:00Z');
      session.eventStore.append({
        type: 'token-added',
        timestamp: t0,
        placeName: 'Input',
        token: { value: null, createdAt: t0 },
      } satisfies NetEvent);
      registry.complete('rt-no-struct');

      const compressed = writer.write(registry.getSession('rt-no-struct')!);
      const imported = reader.readFull(compressed);
      const added = imported.eventStore.events().find(e => e.type === 'token-added');
      if (added?.type !== 'token-added') throw new Error('expected token-added');
      expect(added.token.structured).toBeUndefined();
    });
  });

  describe('version guard', () => {
    it('pins CURRENT_VERSION so bumps are explicit', () => {
      expect(CURRENT_VERSION).toBe(3);
    });
  });

  describe('back-compat with v2 readers', () => {
    it('should still read v2 archives on the v3-capable reader', () => {
      const registry = new DebugSessionRegistry();
      registry.register('legacy-v2', TEST_NET, { channel: 'text' });

      const compressed = writer.writeV2(registry.getSession('legacy-v2')!);
      const imported = reader.readFull(compressed);
      expect(imported.metadata.version).toBe(2);
      expect(imported.metadata.sessionId).toBe('legacy-v2');
    });
  });
});
