/**
 * Drift gate for the mirrored viewer bundle.
 *
 * `typescript/src/viewer/` is the single source of truth, but three consumers
 * ship a *copy* of the built bundle as `petrinet-diagrams.{js,css}`:
 *
 *   java/src/main/resources/javadoc/
 *   rust/libpetri-docgen/resources/
 *   typescript/src/doclet/resources/
 *
 * `scripts/build-viewer.sh` distributes all three and records the canonical
 * digests in `spec/viewer-bundle.sha256`. Nothing forced a rebuild before, so a
 * consumer could sit on an old bundle indefinitely and quietly render an old
 * viewer: that is how a doc page ends up with Graphviz-routed diagonal edges
 * long after the ELK orthogonal routing shipped, with nothing in the page to
 * say so.
 *
 * This test hashes the TypeScript doclet's copy. Java (`ViewerBundleDriftTest`)
 * and Rust (`libpetri-docgen`) hash theirs against the same file, so whichever
 * port falls behind fails its own build.
 *
 * When this fails, the fix is `scripts/build-viewer.sh`, never a hand-edit of
 * the resource files.
 */

import { describe, expect, it } from 'vitest';
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(here, '../../..');
const checksumsPath = resolve(repoRoot, 'spec/viewer-bundle.sha256');
const resourceDir = resolve(repoRoot, 'typescript/src/doclet/resources');

/** Parses the `<sha256>  <filename>` lines written by `build-viewer.sh`. */
function expectedDigests(): Map<string, string> {
  const out = new Map<string, string>();
  for (const line of readFileSync(checksumsPath, 'utf-8').split('\n')) {
    const trimmed = line.trim();
    if (trimmed === '') continue;
    const [digest, name] = trimmed.split(/\s+/);
    if (digest === undefined || name === undefined) {
      throw new Error(`malformed line in spec/viewer-bundle.sha256: ${line}`);
    }
    out.set(name, digest);
  }
  return out;
}

function sha256(path: string): string {
  return createHash('sha256').update(readFileSync(path)).digest('hex');
}

describe('viewer bundle drift', () => {
  const expected = expectedDigests();

  it.each(['petrinet-diagrams.js', 'petrinet-diagrams.css'])(
    'doclet resource %s matches spec/viewer-bundle.sha256',
    (filename) => {
      const want = expected.get(filename);
      expect(want, `spec/viewer-bundle.sha256 has no entry for ${filename}`).toBeDefined();
      expect(
        sha256(resolve(resourceDir, filename)),
        `${filename} is stale — run scripts/build-viewer.sh (do not hand-edit build outputs)`,
      ).toBe(want);
    },
  );

  it('publishes the doclet resources built from the current viewer', () => {
    // dist/ is what npm ships, and the TypeDoc plugin reads its resources from
    // dist/doclet/resources at runtime. tsup's onSuccess used to copy the
    // tracked mirror into dist *before* building the IIFE, so every published
    // build shipped a plugin one viewer behind the viewer it shipped beside.
    // Structurally fixed by reordering onSuccess; pinned here so the ordering
    // cannot quietly regress.
    const iife = resolve(repoRoot, 'typescript/dist/viewer/viewer.iife.js');
    const shipped = resolve(repoRoot, 'typescript/dist/doclet/resources/petrinet-diagrams.js');
    if (!existsSync(iife) || !existsSync(shipped)) {
      // Fresh clone with no build yet. The source-mirror digests above still ran.
      return;
    }
    expect(
      sha256(shipped),
      'dist/doclet/resources is stale relative to dist/viewer/viewer.iife.js',
    ).toBe(sha256(iife));
  });

  it('ships the orthogonal-routing bundle', () => {
    // Cheap canary independent of the digests: the orthogonal edge routing
    // draws ELK's own routes under Graphviz `nop2`. A bundle predating that
    // renders ELK-placed nodes joined by diagonal splines, which looks like a
    // styling preference rather than a stale build.
    const js = readFileSync(resolve(resourceDir, 'petrinet-diagrams.js'), 'utf-8');
    expect(js).toContain('nop2');
  });
});
