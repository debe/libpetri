#!/usr/bin/env -S npx tsx
/**
 * Generates the debug UI net SVG for the README showcase.
 *
 * Usage (from repo root):
 *   cd debug-ui && npx tsx ../scripts/generate-debug-net-svg.ts
 *
 * Prerequisites:
 *   - `cd typescript && npm run build` (builds libpetri)
 *   - `cd debug-ui && npm install` (installs @viz-js/viz)
 */

import { writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(__dirname, '..');
const debugUiDir = resolve(repoRoot, 'debug-ui');
const typescriptDist = resolve(repoRoot, 'typescript', 'dist');

async function main(): Promise<void> {
  // Import the debug net definition from debug-ui source (tsx handles .ts)
  const definitionPath = resolve(debugUiDir, 'src/net/definition.ts');
  const { buildDebugNet } = await import(pathToFileURL(definitionPath).href);
  const { net } = buildDebugNet();

  // Import the DOT exporter directly from the compiled typescript dist
  const exportPath = resolve(typescriptDist, 'export/index.js');
  const { dotExport } = await import(pathToFileURL(exportPath).href);
  const dot = dotExport(net);

  // Render SVG via @viz-js/viz (Graphviz WASM, installed in debug-ui)
  const vizPath = resolve(debugUiDir, 'node_modules/@viz-js/viz/dist/viz.js');
  const { instance } = await import(pathToFileURL(vizPath).href);
  const viz = await instance();
  let svg: string = viz.renderString(dot, { format: 'svg', engine: 'dot' });

  // Strip XML prolog — invalid inside HTML <img> usage
  const svgStart = svg.indexOf('<svg');
  if (svgStart > 0) svg = svg.substring(svgStart);

  // Write to docs/
  const outPath = resolve(repoRoot, 'docs', 'showcase-debug-ui.svg');
  mkdirSync(dirname(outPath), { recursive: true });
  writeFileSync(outPath, svg, 'utf-8');

  console.log(`Generated ${outPath}`);
  console.log(`Net: ${net.name} — ${net.transitions.size} transitions, ${net.places.size} places`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
