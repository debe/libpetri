/**
 * File-system backed storage for session archives.
 * Uses Node.js fs/promises — no external dependencies.
 */

import { mkdir, readdir, readFile, stat, writeFile } from 'node:fs/promises';
import { join, normalize, resolve } from 'node:path';
import type { ArchivedSessionSummary, SessionArchiveStorage, OutputStreamConsumer } from './session-archive-storage.js';
import { Writable } from 'node:stream';

const EXTENSION = '.archive.gz';

export class FileSessionArchiveStorage implements SessionArchiveStorage {
  private readonly _directory: string;

  constructor(directory: string) {
    this._directory = resolve(directory);
  }

  async storeStreaming(sessionId: string, writer: OutputStreamConsumer): Promise<void> {
    const target = this.archivePath(sessionId);
    const dir = join(target, '..');
    await mkdir(dir, { recursive: true });

    const chunks: Buffer[] = [];
    const writable = new Writable({
      write(chunk: Buffer, _encoding, callback) {
        chunks.push(chunk);
        callback();
      },
    });

    await writer(writable);
    await writeFile(target, Buffer.concat(chunks));
  }

  async list(limit: number, prefix?: string): Promise<readonly ArchivedSessionSummary[]> {
    try {
      await stat(this._directory);
    } catch {
      return [];
    }

    const results: ArchivedSessionSummary[] = [];
    let prefixDirs: string[];
    try {
      prefixDirs = await readdir(this._directory);
    } catch {
      return [];
    }

    for (const prefixDir of prefixDirs) {
      const prefixPath = join(this._directory, prefixDir);
      try {
        const s = await stat(prefixPath);
        if (!s.isDirectory()) continue;
      } catch {
        continue;
      }

      // Skip subdirectories that can't contain matches
      if (prefix && prefixDir.length === 1 && prefixDir[0] !== prefix[0]) continue;

      let files: string[];
      try {
        files = await readdir(prefixPath);
      } catch {
        continue;
      }

      for (const file of files) {
        if (!file.endsWith(EXTENSION)) continue;
        const sessionId = file.slice(0, -EXTENSION.length);
        if (prefix && !sessionId.startsWith(prefix)) continue;

        const filePath = join(prefixPath, file);
        try {
          const fileStat = await stat(filePath);
          const relativePath = join(prefixDir, file);
          results.push({
            sessionId,
            key: relativePath,
            sizeBytes: fileStat.size,
            lastModified: fileStat.mtimeMs,
          });
        } catch {
          // skip unreadable files
        }
      }
    }

    results.sort((a, b) => b.lastModified - a.lastModified);
    return results.slice(0, limit);
  }

  async retrieve(sessionId: string): Promise<Buffer> {
    const path = this.archivePath(sessionId);
    try {
      return await readFile(path);
    } catch {
      throw new Error(`Archive not found for session: ${sessionId}`);
    }
  }

  isAvailable(): boolean {
    return true;
  }

  private archivePath(sessionId: string): string {
    if (!sessionId || !sessionId.trim()) {
      throw new Error(`Invalid session ID: ${sessionId}`);
    }
    const prefix = sessionId[0]!;
    const resolved = normalize(join(this._directory, prefix, sessionId + EXTENSION));
    if (!resolved.startsWith(this._directory)) {
      throw new Error(`Session ID escapes archive directory: ${sessionId}`);
    }
    return resolved;
  }
}
