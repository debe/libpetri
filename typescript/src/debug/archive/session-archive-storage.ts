/**
 * Storage backend interface for session archives.
 */
import type { Writable } from 'node:stream';

export interface ArchivedSessionSummary {
  readonly sessionId: string;
  readonly key: string;
  readonly sizeBytes: number;
  readonly lastModified: number; // epoch ms
}

export type OutputStreamConsumer = (out: Writable) => Promise<void>;

export interface SessionArchiveStorage {
  storeStreaming(sessionId: string, writer: OutputStreamConsumer): Promise<void>;
  list(limit: number, prefix?: string): Promise<readonly ArchivedSessionSummary[]>;
  retrieve(sessionId: string): Promise<Buffer>;
  isAvailable(): boolean;
}
