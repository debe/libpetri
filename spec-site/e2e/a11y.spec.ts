/**
 * Axe on the main views and both overlays, in light and dark (design 10): no serious or
 * critical violation.
 */
import { expect, test, type Page } from '@playwright/test';
import { openRoute, seriousViolations } from './site.js';

const VIEWS: readonly (readonly [string, string])[] = [
  ['home', '#/'],
  ['situation', '#/situation/inhibitor-blocks?step=4'],
  ['requirement', '#/req/CORE-031'],
  ['companion', '#/req/EXEC-002'],
  ['tombstone', '#/req/IO-006'],
  ['rules index', '#/req'],
  ['conformance', '#/conf'],
  ['graph', '#/graph/CORE-031'],
  ['impact', '#/graph/impact/CORE-031'],
];

const OVERLAYS: readonly (readonly [string, (page: Page) => Promise<void>])[] = [
  ['search overlay', async (page) => {
    await page.keyboard.press('/');
    await expect(page.locator('.overlay--search [role="dialog"]')).toBeVisible();
    await page.keyboard.type('inhibitor');
  }],
  ['help overlay', async (page) => {
    await page.keyboard.press('?');
    await expect(page.locator('.overlay--help [role="dialog"]')).toBeVisible();
  }],
];

for (const scheme of ['light', 'dark'] as const) {
  test.describe(`${scheme} theme`, () => {
    test.use({ colorScheme: scheme });

    for (const [name, hash] of VIEWS) {
      test(`axe: ${name}`, async ({ page }) => {
        // One axe scan of the conformance table (about 6,600 nodes) takes 17 to 20 s on an
        // idle machine, too close to the 30 s default to survive a loaded one.
        if (name === 'conformance') test.slow();
        const errors: string[] = [];
        await openRoute(page, hash, errors);
        expect(await seriousViolations(page)).toEqual([]);
        expect(errors).toEqual([]);
      });
    }

    for (const [name, open] of OVERLAYS) {
      test(`axe: ${name}`, async ({ page }) => {
        const errors: string[] = [];
        await openRoute(page, '#/req/CORE-031', errors);
        await open(page);
        expect(await seriousViolations(page)).toEqual([]);
        expect(errors).toEqual([]);
      });
    }
  });
}
