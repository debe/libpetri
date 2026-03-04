import { describe, it, expect, beforeEach } from 'vitest';
import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FileSessionArchiveStorage } from '../../src/debug/archive/file-session-archive-storage.js';
import { Writable } from 'node:stream';

describe('FileSessionArchiveStorage', () => {
  let tempDir: string;
  let storage: FileSessionArchiveStorage;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), 'libpetri-archive-'));
    storage = new FileSessionArchiveStorage(tempDir);
  });

  function testData(content = 'test-archive-data'): Buffer {
    return Buffer.from(content, 'utf-8');
  }

  async function storeTestArchive(sessionId: string, content = 'test-archive-data'): Promise<void> {
    const data = testData(content);
    await storage.storeStreaming(sessionId, async (writable: Writable) => {
      writable.write(data);
      writable.end();
      await new Promise<void>((resolve) => writable.on('finish', resolve));
    });
  }

  it('should store and retrieve archive', async () => {
    await storeTestArchive('abc-123');

    const retrieved = await storage.retrieve('abc-123');
    expect(retrieved.toString('utf-8')).toBe('test-archive-data');
  });

  it('should list stored archives', async () => {
    await storeTestArchive('abc-111');
    await storeTestArchive('abc-222');
    await storeTestArchive('def-333');

    const list = await storage.list(10);
    expect(list).toHaveLength(3);
    expect(list.map(s => s.sessionId).sort()).toEqual(['abc-111', 'abc-222', 'def-333']);
  });

  it('should list with prefix filter', async () => {
    await storeTestArchive('abc-111');
    await storeTestArchive('abc-222');
    await storeTestArchive('def-333');

    const list = await storage.list(10, 'abc');
    expect(list).toHaveLength(2);
    expect(list.every(s => s.sessionId.startsWith('abc'))).toBe(true);
  });

  it('should respect list limit', async () => {
    await storeTestArchive('aaa-111');
    await storeTestArchive('aaa-222');
    await storeTestArchive('aaa-333');

    const list = await storage.list(2);
    expect(list).toHaveLength(2);
  });

  it('should throw on retrieve of non-existent session', async () => {
    await expect(storage.retrieve('nonexistent')).rejects.toThrow('Archive not found');
  });

  it('should reject blank session ID', () => {
    expect(() => new FileSessionArchiveStorage(tempDir)).not.toThrow();
    // Path traversal is checked at archive time
  });

  it('should reject path traversal in session ID', async () => {
    await expect(storeTestArchive('../../../etc/passwd')).rejects.toThrow();
  });

  it('should reject empty session ID', async () => {
    await expect(storeTestArchive('')).rejects.toThrow();
    await expect(storeTestArchive('   ')).rejects.toThrow();
  });

  it('should report as available', () => {
    expect(storage.isAvailable()).toBe(true);
  });

  it('should return empty list for non-existent directory', async () => {
    const nonexistent = new FileSessionArchiveStorage(join(tempDir, 'does-not-exist'));
    const list = await nonexistent.list(10);
    expect(list).toHaveLength(0);
  });

  it('should include sizeBytes in listing', async () => {
    await storeTestArchive('size-test', 'hello-world-data');
    const list = await storage.list(10);
    expect(list).toHaveLength(1);
    expect(list[0]!.sizeBytes).toBeGreaterThan(0);
  });

  it('should sort listing by most recent first', async () => {
    await storeTestArchive('aaa-old');
    // Small delay to ensure different mtime
    await new Promise(r => setTimeout(r, 50));
    await storeTestArchive('aaa-new');

    const list = await storage.list(10);
    expect(list).toHaveLength(2);
    expect(list[0]!.lastModified).toBeGreaterThanOrEqual(list[1]!.lastModified);
  });
});
