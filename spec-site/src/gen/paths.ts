/** Repository paths the generator reads and writes. Every input module takes `root` from here. */
import { fileURLToPath } from 'node:url';
import { join } from 'node:path';

/** Absolute path of the libpetri repository root (`spec-site/src/gen/../../..`). */
export const REPO_ROOT: string = fileURLToPath(new URL('../../../', import.meta.url));

/** Absolute path of the `spec-site/` package. */
export const SITE_ROOT: string = join(REPO_ROOT, 'spec-site');

/** The page the build writes, served at https://libpetri.org/spec/. */
export const DEFAULT_OUT_FILE: string = join(REPO_ROOT, 'docs', 'spec', 'index.html');

/** The landing page the build generates (whole, with the live counts). */
export const DEFAULT_LANDING_FILE: string = join(REPO_ROOT, 'docs', 'index.html');

/** Resolves a repo-relative path such as `spec/glossary.md`. */
export function repoPath(root: string, relative: string): string {
  return join(root, relative);
}
