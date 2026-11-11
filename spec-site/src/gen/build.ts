/**
 * The build pipeline: read every input, assemble `SiteData`, render diagrams, bundle the app,
 * write the page and the landing page (generated whole, with the live counts). `generate` does no writes (tests use it);
 * `buildSite` writes only files whose bytes changed.
 */
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import type { SiteData } from '../model.js';
import { bundleApp } from './bundle.js';
import { renderDiagrams } from './diagrams.js';
import { renderPage } from './html.js';
import { readCoverage } from './inputs/coverage.js';
import { readDefects } from './inputs/defects.js';
import { readGlossary } from './inputs/glossary.js';
import { readLean } from './inputs/lean.js';
import { readSituations } from './inputs/situations.js';
import { readSpec } from './inputs/spec.js';
import { landingPage } from './landing.js';
import { SITE_ROOT } from './paths.js';
import { buildSiteData } from './site.js';

export interface Generated {
  readonly data: SiteData;
  /** The full page text. */
  readonly html: string;
}

export async function generate(root: string, siteRoot: string = SITE_ROOT): Promise<Generated> {
  const glossary = readGlossary(root);
  const spec = readSpec(root, glossary);
  const lean = readLean(root);
  const coverage = readCoverage(root);
  const defects = readDefects(root);
  const situations = readSituations(root);
  const [diagrams, bundle] = await Promise.all([renderDiagrams(situations), bundleApp(siteRoot)]);
  const data = buildSiteData({
    spec,
    glossary,
    lean,
    coverage,
    defects,
    situations,
    diagrams: new Set(diagrams.keys()),
  });
  return { data, html: renderPage({ data, bundle, diagrams }) };
}

export interface BuildOptions {
  readonly root: string;
  readonly outFile: string;
  /** Landing page to write (generated whole), or null to leave it alone. */
  readonly landingFile: string | null;
}

export interface BuildReport {
  readonly data: SiteData;
  readonly bytes: number;
  /** Files whose content changed on disk. */
  readonly written: readonly string[];
}

function writeIfChanged(file: string, text: string): boolean {
  if (existsSync(file) && readFileSync(file, 'utf8') === text) return false;
  mkdirSync(dirname(file), { recursive: true });
  writeFileSync(file, text, 'utf8');
  return true;
}

export async function buildSite(options: BuildOptions): Promise<BuildReport> {
  const { data, html } = await generate(options.root);
  const written: string[] = [];
  if (writeIfChanged(options.outFile, html)) written.push(options.outFile);
  if (options.landingFile !== null && writeIfChanged(options.landingFile, landingPage(data.counts))) written.push(options.landingFile);
  return { data, bytes: Buffer.byteLength(html, 'utf8'), written };
}
