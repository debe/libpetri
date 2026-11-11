/**
 * Assembles the landing page (Node side): token CSS from the spec site's stylesheet, the page's
 * own CSS, the theme boot script and the client script, then the typed template in `page.ts`.
 *
 * Synchronous on purpose (esbuild's `buildSync` / `transformSync`), so the generator's landing
 * hook stays a plain function. Output is deterministic: minified, no source maps, no legal
 * comments, the working directory pinned to the package.
 */
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { buildSync, transformSync } from 'esbuild';
import type { SiteCounts } from '../model.js';
import { EVIDENCE_SVG } from './content.js';
import type { LandingAssets } from './page.js';
import { renderLandingPage } from './page.js';

/** Same baseline as the spec page (src/gen/bundle.ts). */
const BROWSER_TARGET = 'es2020';
const CSS_TARGETS = ['chrome100', 'firefox100', 'safari15'];

/** The comment that opens the base rules in src/app/style.css; everything above it is tokens. */
export const TOKENS_END_MARKER = '/* Reset and base';

/**
 * The design-token part of the spec site's stylesheet: light tokens on `:root`, the dark
 * overrides, the phone type scale and reduced motion. Throws when the stylesheet no longer has
 * the expected shape, so the two pages cannot drift apart silently.
 */
export function tokenCss(styleCss: string): string {
  const start = styleCss.indexOf(':root {');
  const end = styleCss.indexOf(TOKENS_END_MARKER);
  if (start < 0 || end < 0 || end < start) {
    throw new Error(`src/app/style.css: expected ":root {" before "${TOKENS_END_MARKER}" to cut the design tokens`);
  }
  const tokens = styleCss.slice(start, end);
  if (!tokens.includes('[data-theme="dark"]')) throw new Error('src/app/style.css: token block has no dark theme');
  return tokens;
}

/** Intrinsic size of an SVG in CSS pixels, from its root `width` / `height` (px or pt). */
export function svgSize(svg: string): { readonly width: number; readonly height: number } {
  const root = /<svg\b[^>]*>/.exec(svg)?.[0];
  if (root === undefined) throw new Error('no <svg> root element');
  const dim = (name: 'width' | 'height'): number => {
    const m = new RegExp(`\\s${name}="([0-9.]+)(px|pt)?"`).exec(root);
    if (m === null || m[1] === undefined) throw new Error(`<svg> has no numeric ${name}`);
    const value = Number(m[1]) * (m[2] === 'pt' ? 4 / 3 : 1);
    return Math.round(value);
  };
  return { width: dim('width'), height: dim('height') };
}

function bundleSync(siteRoot: string, entry: string, tsconfig: string): string {
  const result = buildSync({
    absWorkingDir: siteRoot,
    entryPoints: [entry],
    bundle: true,
    format: 'iife',
    platform: 'browser',
    target: BROWSER_TARGET,
    tsconfig: join(siteRoot, tsconfig),
    minify: true,
    sourcemap: false,
    legalComments: 'none',
    charset: 'utf8',
    write: false,
    logLevel: 'silent',
  });
  const file = result.outputFiles[0];
  if (file === undefined) throw new Error(`esbuild produced no output for ${entry}`);
  return file.text.trimEnd();
}

export function landingAssets(repoRoot: string, siteRoot: string): LandingAssets {
  const styleCss = readFileSync(join(siteRoot, 'src/app/style.css'), 'utf8');
  const pageCss = readFileSync(join(siteRoot, 'src/landing/landing.css'), 'utf8');
  const css = transformSync(`${tokenCss(styleCss)}\n${pageCss}`, {
    loader: 'css',
    minify: true,
    target: CSS_TARGETS,
    legalComments: 'none',
  }).code.trimEnd();
  return {
    css,
    bootJs: bundleSync(siteRoot, 'src/app/boot.ts', 'src/app/tsconfig.json'),
    clientJs: bundleSync(siteRoot, 'src/landing/browser/main.ts', 'src/landing/browser/tsconfig.json'),
    evidence: svgSize(readFileSync(join(repoRoot, 'docs', EVIDENCE_SVG), 'utf8')),
  };
}

/** The whole landing page for these counts. */
export function renderLanding(counts: SiteCounts, repoRoot: string, siteRoot: string): string {
  return renderLandingPage(counts, landingAssets(repoRoot, siteRoot));
}
