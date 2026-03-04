/**
 * Metadata header for a session archive file.
 */
import type { NetStructure } from '../debug-response.js';

export interface SessionArchive {
  readonly version: number;
  readonly sessionId: string;
  readonly netName: string;
  readonly dotDiagram: string;
  readonly startTime: string; // ISO-8601
  readonly eventCount: number;
  readonly structure: NetStructure;
}

/** Current archive format version. */
export const CURRENT_VERSION = 1;
