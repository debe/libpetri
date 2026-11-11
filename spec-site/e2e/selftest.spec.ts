/**
 * The page's own self-test (`#/selftest`): renders every situation at every step, every rule,
 * the graph of every node and the impact of every rule, the search and help panels, and checks
 * the embedded data. CI requires 0 errors; on failure the message lists what failed.
 */
import { expect, test } from '@playwright/test';
import { openRoute } from './site.js';

test('self-test reports 0 errors', async ({ page }, info) => {
  test.skip(info.project.name !== 'chromium', 'the self-test does not depend on the viewport; run it once');
  test.setTimeout(180_000);
  const errors: string[] = [];
  await openRoute(page, '#/selftest', errors);
  const result = page.locator('#selftest-result[data-selftest-done="true"]');
  await result.waitFor({ timeout: 170_000 });
  const count = Number(await result.getAttribute('data-selftest-errors'));
  const failures = count === 0 ? [] : await page.locator('.selftest__failure').allInnerTexts();
  expect(failures.map((f) => f.replace(/\s+/g, ' ').trim()), `${await result.innerText()}`).toEqual([]);
  expect(count).toBe(0);
  expect(errors).toEqual([]);
});
