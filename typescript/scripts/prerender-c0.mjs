#!/usr/bin/env node
/**
 * Pre-render a libpetri DOT source through the C0 layout pipeline and emit
 * a Graphviz neato `nop=1`-pinned SVG.
 *
 * Usage (DOT on stdin, SVG on stdout):
 *   cat my.dot | node scripts/prerender-c0.mjs > my.svg
 *
 * Consumed by the Java javadoc taglet (`PetriNetTaglet.java`) when the
 * `LIBPETRI_PRERENDER_SCRIPT` env var points at this file. When that env
 * var is unset the taglet falls through to its `dot -Tsvg` legacy path
 * (no C0), or — if `dot` is also missing — embeds DOT for the IIFE viewer
 * to render at mount.
 *
 * Prereq: run `npm run build` first so `dist/viewer/layout/index.js` exists.
 * The script reads from the built ESM output rather than the TypeScript
 * source so the consumer (Java taglet) doesn't need a TypeScript runtime.
 */
import { existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const layoutEntry = resolve(here, '..', 'dist', 'viewer', 'layout', 'index.js');

if (!existsSync(layoutEntry)) {
  process.stderr.write(
    `prerender-c0: missing ${layoutEntry}\n` +
    `Run 'npm run build' from the typescript/ directory first.\n`,
  );
  process.exit(2);
}

const { parseLibpetriDot, foldOrphans, replicateShared, elkLayout, writeBack } =
  await import(pathToFileURL(layoutEntry).href);
const { instance: vizInstance } = await import('@viz-js/viz');

const dot = readFileSync(0, 'utf8');
if (!dot.trim()) {
  process.stderr.write('prerender-c0: empty DOT input on stdin\n');
  process.exit(1);
}

const graph = replicateShared(
  foldOrphans(parseLibpetriDot(dot), 0.7),
  { max: Infinity },
);
const layout = await elkLayout(graph);
const pinnedDot = writeBack(graph, layout);

const viz = await vizInstance();
const svg = viz.renderString(pinnedDot, {
  format: 'svg',
  engine: 'nop',
  yInvert: true,
});

process.stdout.write(svg);
