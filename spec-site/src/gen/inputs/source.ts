/** Reads a repo file for an input module, naming the file when it cannot. */
import { readFileSync } from 'node:fs';
import { repoPath } from '../paths.js';

/** Reads a repo-relative file as UTF-8; a missing file fails with its repo-relative name. */
export function readSource(root: string, relative: string): string {
  try {
    return readFileSync(repoPath(root, relative), 'utf8');
  } catch (error) {
    throw new Error(`${relative}: cannot read (${error instanceof Error ? error.message : String(error)})`);
  }
}
