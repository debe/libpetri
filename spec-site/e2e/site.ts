/**
 * Helpers shared by the e2e specs. The page under test is `docs/spec/index.html`, opened from
 * file:// exactly as a reader who saved it would; `SPEC_SITE_PAGE=<path>` points the run at
 * another build (`npm run build -- --out <path> --no-landing`).
 */
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import AxeBuilder from '@axe-core/playwright';
import type { Page, TestInfo } from '@playwright/test';
import { decode } from '../src/decode.js';
import { siteData } from '../src/decode-site.js';
import { SITE_DATA_ELEMENT_ID, type SiteData } from '../src/model.js';

const SITE_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

/** The built page under test. */
export const PAGE_FILE = process.env['SPEC_SITE_PAGE'] !== undefined && process.env['SPEC_SITE_PAGE'] !== ''
  ? resolve(process.env['SPEC_SITE_PAGE'])
  : join(SITE_ROOT, '..', 'docs', 'spec', 'index.html');

/** Where screenshots go (CI uploads test-results/ as an artifact). */
export const SCREENSHOT_DIR = join(SITE_ROOT, 'test-results', 'screenshots');

/** The file:// URL of the built page with a route hash, e.g. `pageUrl('#/req/CORE-001')`. */
export function pageUrl(hash = '#/'): string {
  return `${pathToFileURL(PAGE_FILE).href}${hash}`;
}

let cached: SiteData | null = null;

/** The data embedded in the built page, decoded with the app's own decoder. */
export function pageData(): SiteData {
  if (cached !== null) return cached;
  const html = readFileSync(PAGE_FILE, 'utf8');
  const open = `<script type="application/json" id="${SITE_DATA_ELEMENT_ID}">`;
  const start = html.indexOf(open);
  const end = start < 0 ? -1 : html.indexOf('</script>', start);
  if (start < 0 || end < 0) throw new Error(`${PAGE_FILE} has no #${SITE_DATA_ELEMENT_ID} element`);
  const raw: unknown = JSON.parse(html.slice(start + open.length, end));
  cached = decode(siteData, raw);
  return cached;
}

/** Schemes the page may load from: itself and inline data. Anything else breaks file:// use. */
const LOCAL = /^(file|data|blob|about):/;

/**
 * Collects uncaught page errors, console errors and every request that leaves the file into
 * `errors`. Call once per page, before the first navigation.
 */
export function watchErrors(page: Page, errors: string[]): void {
  page.on('pageerror', (e) => errors.push(`pageerror: ${e.message}`));
  page.on('console', (m) => {
    if (m.type() === 'error') errors.push(`console: ${m.text()}`);
  });
  page.on('request', (r) => {
    if (!LOCAL.test(r.url())) errors.push(`network: ${r.method()} ${r.url()}`);
  });
}

/** Waits two animation frames, so lazy first paints (the player measures on the first frame) are done. */
export async function settle(page: Page): Promise<void> {
  await page.evaluate(() => new Promise<void>((done) => requestAnimationFrame(() => requestAnimationFrame(() => done()))));
}

/** Opens a route and waits for the app's first render. Collects errors into `errors`. */
export async function openRoute(page: Page, hash: string, errors: string[]): Promise<void> {
  watchErrors(page, errors);
  await page.goto(pageUrl(hash));
  await page.locator('#app[data-ready="true"]').waitFor();
  await settle(page);
}

/** How far the page scrolls sideways (0 when it fits the viewport). */
export async function horizontalOverflow(page: Page): Promise<number> {
  return page.evaluate(() => document.documentElement.scrollWidth - document.documentElement.clientWidth);
}

/** Axe violations with impact serious or critical, one line each. */
export async function seriousViolations(page: Page): Promise<readonly string[]> {
  const result = await new AxeBuilder({ page }).analyze();
  return result.violations
    .filter((v) => v.impact === 'serious' || v.impact === 'critical')
    .map((v) => `${v.id} (${v.impact ?? ''}): ${v.help}; ${v.nodes.slice(0, 3).map((n) => n.target.join(' ')).join(' | ')}`);
}

/** Saves a full-page screenshot as `test-results/screenshots/<name>-<project>.png`. */
export async function screenshot(page: Page, info: TestInfo, name: string): Promise<void> {
  await settle(page);
  await page.screenshot({
    path: join(SCREENSHOT_DIR, `${name}-${info.project.name}.png`),
    fullPage: true,
    animations: 'disabled',
  });
}
