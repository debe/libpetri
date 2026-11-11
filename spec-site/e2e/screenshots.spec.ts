/**
 * Screenshots of the main views in light and dark, at desktop width (project `chromium`) and at
 * 400px (project `narrow`), saved to test-results/screenshots/ for review. CI uploads them.
 * The run fails only on page errors or sideways scroll, not on pixel differences.
 */
import { expect, test } from '@playwright/test';
import { horizontalOverflow, openRoute, screenshot } from './site.js';

const SHOTS: readonly (readonly [string, string])[] = [
  ['home', '#/'],
  ['situation', '#/situation/inhibitor-blocks?step=4'],
  ['requirement', '#/req/CORE-031'],
  ['conformance', '#/conf'],
];

for (const scheme of ['light', 'dark'] as const) {
  test.describe(`${scheme}`, () => {
    test.use({ colorScheme: scheme, reducedMotion: 'reduce' });
    for (const [name, hash] of SHOTS) {
      test(`screenshot: ${name}`, async ({ page }, info) => {
        const errors: string[] = [];
        await openRoute(page, hash, errors);
        await screenshot(page, info, `${name}-${scheme}`);
        expect(await horizontalOverflow(page), 'the page scrolls sideways').toBeLessThanOrEqual(0);
        expect(errors).toEqual([]);
      });
    }
  });
}
