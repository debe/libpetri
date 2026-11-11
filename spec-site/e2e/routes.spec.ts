/**
 * Every view, opened directly by its address: one h1 in <main>, the right view, a title, no
 * page error, console error or network request, and no sideways scroll (the narrow project is
 * 400px wide).
 */
import { expect, test } from '@playwright/test';
import type { ViewName } from '../src/app/router.js';
import { horizontalOverflow, openRoute, pageData } from './site.js';

const data = pageData();
const term = data.glossary.find((t) => t.slug === 'inhibitor-arc')?.slug ?? data.glossary[0]?.slug ?? 'inhibitor-arc';
const theorem = data.lean['CORE-031']?.[0]?.evidence[0]?.theorem ?? data.citations[0]?.theorem ?? 'Libpetri.Spec.CORE_031_reference';
const defect = data.defects[0]?.id ?? 'RD-01';

/** [hash, the view it must show, what the case covers]. */
const ROUTES: readonly (readonly [string, ViewName, string])[] = [
  ['#/', 'situations', 'home'],
  ['#/situation/inhibitor-blocks', 'situation', 'a situation with a blocked step'],
  ['#/situation/inhibitor-blocks?step=4', 'situation', 'the blocked step itself'],
  ['#/situation/xor-branch?step=1', 'situation', 'an XOR output'],
  ['#/situation/competing-for-one-token', 'situation', 'a conflict'],
  ['#/req', 'req', 'rules index'],
  ['#/req?kind=B&lean=none', 'req', 'rules index with filters'],
  ['#/req/CORE-001', 'req', 'a rule without a Lean block'],
  ['#/req/CORE-031', 'req', 'a rule with a Lean block'],
  ['#/req/EXEC-002', 'req', 'a rule with a companion Lean block'],
  ['#/req/IO-006', 'req', 'a tombstone'],
  ['#/req/NOPE-999', 'req', 'an unknown rule'],
  ['#/conf', 'conf', 'conformance'],
  ['#/conf?f=defects,untested', 'conf', 'conformance with filters'],
  ['#/graph', 'graph', 'graph picker'],
  ['#/graph/CORE-031', 'graph', 'graph of a rule'],
  ['#/graph/impact/CORE-031', 'graph', 'impact of a rule'],
  [`#/graph/term:${term}`, 'graph', 'graph of a term'],
  [`#/graph/thm:${theorem}`, 'graph', 'graph of a theorem'],
  [`#/graph/${defect}`, 'graph', 'graph of a defect'],
  ['#/graph/sit:inhibitor-blocks', 'graph', 'graph of a situation'],
  ['#/selftest', 'selftest', 'self-test'],
  ['#/no-such-page', 'notfound', 'not found'],
];

for (const [hash, view, what] of ROUTES) {
  test(`${what}: ${hash}`, async ({ page }) => {
    const errors: string[] = [];
    await openRoute(page, hash, errors);
    await expect(page.locator('html')).toHaveAttribute('data-route', view);
    await expect(page.locator('main#main h1')).toHaveCount(1);
    await expect(page.locator('main#main h1')).not.toBeEmpty();
    await expect(page.locator('main#main .view--error')).toHaveCount(0);
    expect(await page.title()).toMatch(/libpetri spec$/);
    expect(await horizontalOverflow(page), 'the page scrolls sideways').toBeLessThanOrEqual(0);
    expect(errors).toEqual([]);
  });
}

test('the shell has its landmarks and a skip link first', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/', errors);
  await expect(page.locator('header nav[aria-label="Main"], nav[aria-label="Main"]').first()).toBeAttached();
  await expect(page.locator('main#main')).toHaveCount(1);
  await expect(page.locator('footer')).toHaveCount(1);
  await page.keyboard.press('Tab');
  await expect(page.locator(':focus')).toHaveText(/skip to content/i);
  expect(errors).toEqual([]);
});

test('not found and unknown rule show their copy', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/no-such-page', errors);
  await expect(page.locator('main#main h1')).toHaveText('Nothing here');
  await expect(page.locator('main#main')).toContainText('#/no-such-page');
  await page.goto(`${page.url().split('#')[0] ?? ''}#/req/NOPE-999`);
  await expect(page.locator('html')).toHaveAttribute('data-route', 'req');
  await expect(page.locator('main#main')).toContainText('No requirement NOPE-999');
  expect(errors).toEqual([]);
});
