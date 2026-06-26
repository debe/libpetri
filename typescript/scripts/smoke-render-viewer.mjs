#!/usr/bin/env node
/**
 * Headless render smoke test for the built viewer IIFE.
 *
 * Loads typescript/dist/viewer/viewer.iife.js into a real browser exactly as a
 * doc page does (a `<script src>` tag), mounts a diagram, and asserts that an
 * <svg> actually appears and that nothing logged to console.error / threw a
 * page error. This is the higher-fidelity companion to check-viewer-wasm.mjs:
 * it exercises the full mount -> ELK layout -> Graphviz pin-mode render path in
 * a genuine WASM engine, which is precisely where a corrupt bake renders blank.
 *
 * Exit non-zero on any failure.
 *
 * Browser resolution: prefers Playwright's downloaded chromium (CI installs it
 * via `npx playwright install --with-deps chromium`); falls back to the system
 * Chrome channel for local runs.
 */
import { chromium } from 'playwright';
import { writeFileSync, rmSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const viewerDir = join(here, '..', 'dist', 'viewer');
const iife = join(viewerDir, 'viewer.iife.js');
const css = join(viewerDir, 'viewer.css');

if (!existsSync(iife)) {
  console.error(`[smoke-render-viewer] FAIL: ${iife} missing (build the viewer first)`);
  process.exit(1);
}

// Temp page next to the bundle so a relative file:// <script src> resolves.
const pagePath = join(viewerDir, '.smoke.html');
writeFileSync(
  pagePath,
  `<!doctype html><html><head><meta charset="utf-8">
${existsSync(css) ? '<link rel="stylesheet" href="viewer.css">' : ''}
</head><body>
<div class="diagram-container" data-dot="digraph G { a -> b -> c; a -> c }"></div>
<script src="viewer.iife.js"></script>
<script>
  (function () {
    var el = document.querySelector('.diagram-container[data-dot]');
    Promise.resolve(LibpetriViewer.mount(el.dataset.dot, el, { chrome: true }))
      .then(function () { window.__smokeDone = 'OK'; })
      .catch(function (e) { window.__smokeDone = 'FAIL: ' + (e && e.message || e); });
  })();
</script>
</body></html>`,
);

async function launch() {
  try {
    return await chromium.launch({ headless: true });
  } catch {
    return await chromium.launch({ headless: true, channel: 'chrome' });
  }
}

let browser;
let failed = null;
try {
  browser = await launch();
  const page = await browser.newPage();
  const errors = [];
  page.on('console', (m) => {
    if (m.type() === 'error') errors.push('console.error: ' + m.text());
  });
  page.on('pageerror', (e) => errors.push('pageerror: ' + e.message));

  await page.goto('file://' + pagePath);
  await page
    .waitForFunction(() => window.__smokeDone !== undefined, { timeout: 20000 })
    .catch(() => {});

  const done = await page.evaluate(() => window.__smokeDone);
  const svgCount = await page.evaluate(
    () => document.querySelectorAll('.diagram-container svg').length,
  );

  if (done !== 'OK') failed = `mount did not resolve OK (got: ${done})`;
  else if (svgCount < 1) failed = 'no <svg> rendered into the diagram container';
  else if (errors.length) failed = 'console/page errors: ' + errors.join(' | ');
  else console.log(`[smoke-render-viewer] OK — ${svgCount} <svg> rendered, no errors`);
} catch (e) {
  failed = 'harness error: ' + (e && e.message ? e.message : String(e));
} finally {
  if (browser) await browser.close();
  rmSync(pagePath, { force: true });
}

if (failed) {
  console.error(`[smoke-render-viewer] FAIL: ${failed}`);
  process.exit(1);
}
console.log('[smoke-render-viewer] PASS');
