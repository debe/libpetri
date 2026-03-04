/**
 * No-op archive storage for when archival is disabled.
 *
 * All write operations are silently ignored, list returns empty,
 * and retrieve throws since no archives exist.
 */
import type { SessionArchiveStorage, ArchivedSessionSummary, OutputStreamConsumer } from './session-archive-storage.js';

export class NoOpArchiveStorage implements SessionArchiveStorage {

  async storeStreaming(_sessionId: string, _writer: OutputStreamConsumer): Promise<void> {
    // intentionally empty
  }

  async list(_limit: number, _prefix?: string): Promise<readonly ArchivedSessionSummary[]> {
    return [];
  }

  async retrieve(_sessionId: string): Promise<Buffer> {
    throw new Error('Archive storage is not available');
  }

  isAvailable(): boolean {
    return false;
  }
}
