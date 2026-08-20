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

// A fan-out/fan-in with a skip edge, not a straight chain: a chain's edges
// come out axis-aligned even when Graphviz routes them, so it cannot tell a
// routing regression from correct output. On this net ELK's routes measure
// ~99% axis-aligned against ~15% for stock Graphviz.
//
// A libpetri-shaped net, not an arbitrary digraph. The C0 pipeline keys off
// the `p_` / `t_` id conventions and the shape attributes the exporters emit;
// fed `digraph G { a -> b -> c }` it drops every node and edge and renders an
// empty <svg>, which an `svg exists` assertion happily accepts. Multi-line on
// purpose too: parseLibpetriDot reads the source line by line.
const smokeDot = [
  'digraph G {',
  '  rankdir=TB;',
  '  p_req [shape=circle,label="",xlabel="request"];',
  '  t_split [shape=box,label="split"];',
  '  p_a [shape=circle,label="",xlabel="branch a"];',
  '  p_b [shape=circle,label="",xlabel="branch b"];',
  '  p_c [shape=circle,label="",xlabel="branch c"];',
  '  t_a [shape=box,label="handle a"];',
  '  t_b [shape=box,label="handle b"];',
  '  t_c [shape=box,label="handle c"];',
  '  p_done [shape=circle,label="",xlabel="done"];',
  '  t_collect [shape=box,label="collect"];',
  '  p_out [shape=circle,label="",xlabel="out"];',
  '  p_req -> t_split;',
  '  t_split -> p_a;',
  '  t_split -> p_b;',
  '  t_split -> p_c;',
  '  p_a -> t_a;',
  '  p_b -> t_b;',
  '  p_c -> t_c;',
  '  t_a -> p_done;',
  '  t_b -> p_done;',
  '  t_c -> p_done;',
  '  p_done -> t_collect;',
  '  t_collect -> p_out;',
  '  p_req -> t_collect;',
  '}',
].join('\n');

/** Encode for a double-quoted HTML attribute, newlines included. */
const attr = (text) =>
  text
    .replace(/&/g, '&amp;')
    .replace(/"/g, '&quot;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/\n/g, '&#10;');

// Temp page next to the bundle so a relative file:// <script src> resolves.
const pagePath = join(viewerDir, '.smoke.html');
writeFileSync(
  pagePath,
  `<!doctype html><html><head><meta charset="utf-8">
${existsSync(css) ? '<link rel="stylesheet" href="viewer.css">' : ''}
</head><body>
<div class="diagram-container" data-dot="${attr(smokeDot)}"></div>
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
  // An empty <svg> is a rendering failure, not a pass.
  const drawn = await page.evaluate(() => ({
    nodes: document.querySelectorAll('.diagram-container g.node').length,
    edges: document.querySelectorAll('.diagram-container g.edge').length,
  }));

  // Edge geometry. The viewer's whole point is right-angle edges: it draws
  // ELK's own orthogonal routes under Graphviz `nop2` rather than letting
  // Graphviz route. A regression to Graphviz routing (or to `nop`, which pins
  // nodes but routes edges) still renders a perfectly valid SVG and still
  // resolves the mount, so nothing above would notice. Measure the paths.
  //
  // Corners are genuinely diagonal for a sample or two each, and the arrowhead
  // pull-back trims the final segment, so this asserts on the bulk rather than
  // the maximum.
  const geometry = await page.evaluate(() => {
    const deviations = [];
    for (const path of Array.from(document.querySelectorAll('g.edge path'))) {
      const len = path.getTotalLength();
      if (len < 2) continue;
      const steps = Math.max(8, Math.round(len / 4));
      let prev = path.getPointAtLength(0);
      for (let i = 1; i <= steps; i++) {
        const cur = path.getPointAtLength((len * i) / steps);
        const dx = Math.abs(cur.x - prev.x);
        const dy = Math.abs(cur.y - prev.y);
        // 0 degrees = axis-aligned, 45 = perfectly diagonal.
        if (dx + dy > 0.5) {
          deviations.push(
            (Math.atan2(Math.min(dx, dy), Math.max(dx, dy)) * 180) / Math.PI,
          );
        }
        prev = cur;
      }
    }
    const axisAligned = deviations.filter((d) => d <= 5).length;
    return {
      samples: deviations.length,
      axisAlignedFraction: deviations.length ? axisAligned / deviations.length : 0,
    };
  });

  const MIN_AXIS_ALIGNED = 0.9;

  if (done !== 'OK') failed = `mount did not resolve OK (got: ${done})`;
  else if (svgCount < 1) failed = 'no <svg> rendered into the diagram container';
  else if (drawn.nodes < 11 || drawn.edges < 13)
    failed =
      `<svg> is empty or partial: ${drawn.nodes} nodes / ${drawn.edges} edges, `
      + 'expected 11 / 13 from the smoke net';
  else if (errors.length) failed = 'console/page errors: ' + errors.join(' | ');
  else if (geometry.samples < 10) failed = `only ${geometry.samples} edge samples; no edges drawn?`;
  else if (geometry.axisAlignedFraction < MIN_AXIS_ALIGNED)
    failed =
      `edges are not orthogonal: ${(geometry.axisAlignedFraction * 100).toFixed(1)}% of `
      + `${geometry.samples} samples axis-aligned, want >= ${MIN_AXIS_ALIGNED * 100}%. `
      + 'Graphviz is routing the edges again (check engine: nop2 and writeBack).';
  else
    console.log(
      `[smoke-render-viewer] OK — ${drawn.nodes} nodes / ${drawn.edges} edges drawn, `
        + `no errors, ${(geometry.axisAlignedFraction * 100).toFixed(1)}% of `
        + `${geometry.samples} edge samples axis-aligned`,
    );
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
