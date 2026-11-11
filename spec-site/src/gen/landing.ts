/**
 * The generator's hook for the landing page `docs/index.html` (https://libpetri.org/).
 *
 * The page is generated whole from the typed template in `src/landing/`, with the live counts
 * of the site data. `buildSite` (build.ts) writes it, also when the file is missing, and only
 * when the bytes differ, so a second build changes nothing.
 */
import type { SiteCounts } from '../model.js';
import { renderLanding } from '../landing/build.js';
import { REPO_ROOT, SITE_ROOT } from './paths.js';

/** The landing page for these counts. The generator owns all of it; same counts, same bytes. */
export function landingPage(counts: SiteCounts, repoRoot: string = REPO_ROOT, siteRoot: string = SITE_ROOT): string {
  return renderLanding(counts, repoRoot, siteRoot);
}
