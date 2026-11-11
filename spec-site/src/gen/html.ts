/**
 * Writes the one self-contained page. Layout of the document:
 *
 *   <head>  meta, <title>, <style>CSS</style>, <script>boot IIFE</script>
 *   <body>  <div id="app"> (the app renders the shell into it) + <noscript>
 *           <script type="application/json" id="site-data">SiteData</script>
 *           <div id="diagrams" hidden><template id="dia-<slug>"><svg ...></template>...</div>
 *           <script>app IIFE</script>
 *
 * No timestamps, no absolute paths, no external URLs fetched: the page works from file://.
 */
import type { SiteData } from '../model.js';
import { APP_ROOT_ID, diagramTemplateId, SITE_DATA_ELEMENT_ID } from '../model.js';
import type { Bundle } from './bundle.js';
import type { DiagramMap } from './diagrams.js';
import { escapeJsonForScript, stableStringify } from './json.js';

export const PAGE_TITLE = 'libpetri spec';
export const PAGE_DESCRIPTION =
  'The libpetri specification: every requirement with its spec sentences, the Lean statement that checks it, its evidence, tests per runtime and example runs.';

function assertAbsent(haystack: string, needle: RegExp, what: string): void {
  if (needle.test(haystack)) throw new Error(`${what} contains ${String(needle)}; refusing to inline it`);
}

/** Inline script text: a literal `</script` would end the element early. */
function scriptSafe(js: string, what: string): string {
  const out = js.replace(/<\/script/gi, '<\\/script');
  assertAbsent(out, /<\/script/i, what);
  assertAbsent(out, /<!--/, what);
  return out;
}

function escapeAttr(text: string): string {
  return text.replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

export interface PageParts {
  readonly data: SiteData;
  readonly bundle: Bundle;
  readonly diagrams: DiagramMap;
}

export function renderPage({ data, bundle, diagrams }: PageParts): string {
  assertAbsent(bundle.css, /<\/style/i, 'CSS');
  const json = escapeJsonForScript(stableStringify(data));
  const templates = [...diagrams.entries()]
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
    .map(([slug, svg]) => {
      if (!svg.startsWith('<svg')) throw new Error(`diagram ${slug} does not start with <svg`);
      assertAbsent(svg, /<\/template|<script/i, `diagram ${slug}`);
      return `<template id="${escapeAttr(diagramTemplateId(slug))}">${svg}</template>`;
    })
    .join('\n');

  return [
    '<!doctype html>',
    '<html lang="en">',
    '<head>',
    '<meta charset="utf-8">',
    '<meta name="viewport" content="width=device-width, initial-scale=1">',
    '<meta name="color-scheme" content="light dark">',
    `<meta name="description" content="${escapeAttr(PAGE_DESCRIPTION)}">`,
    `<title>${escapeAttr(PAGE_TITLE)}</title>`,
    `<style>${bundle.css}</style>`,
    `<script>${scriptSafe(bundle.bootJs, 'boot script')}</script>`,
    '</head>',
    '<body>',
    `<div id="${APP_ROOT_ID}"></div>`,
    '<noscript><p class="noscript">This page needs JavaScript to show the specification. The source is in <a href="https://github.com/debe/libpetri/tree/main/spec">spec/ on GitHub</a>.</p></noscript>',
    `<script type="application/json" id="${SITE_DATA_ELEMENT_ID}">${json}</script>`,
    `<div id="diagrams" hidden>${templates}</div>`,
    `<script>${scriptSafe(bundle.appJs, 'app script')}</script>`,
    '</body>',
    '</html>',
    '',
  ].join('\n');
}
