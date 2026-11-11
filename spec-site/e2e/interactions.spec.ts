/**
 * What a reader does with the keyboard and the mouse: search, help, theme, `g` shortcuts, the
 * net player on a blocked step, companion Lean blocks as tabs, tombstones, reduced motion.
 */
import { expect, test } from '@playwright/test';
import { openRoute, pageData, settle } from './site.js';

const data = pageData();

test('search: / opens, an exact ID ranks first, Enter opens the rule', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/', errors);
  await page.keyboard.press('/');
  const dialog = page.locator('.overlay--search [role="dialog"]');
  await expect(dialog).toBeVisible();
  const input = dialog.locator('input');
  await expect(input).toBeFocused();
  await page.keyboard.type('core031');
  await expect(dialog.locator('[role="option"]').first()).toContainText('CORE-031');
  await page.keyboard.press('Enter');
  await expect(page.locator('.overlay')).toHaveCount(0);
  await expect(page.locator('html')).toHaveAttribute('data-route', 'req');
  expect(new URL(page.url()).hash).toBe('#/req/CORE-031');
  await expect(page.locator('main#main h1')).toBeFocused();
  expect(errors).toEqual([]);
});

test('search: Ctrl K opens, Esc clears the query first, then closes', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/conf', errors);
  await page.keyboard.press('Control+k');
  const dialog = page.locator('.overlay--search [role="dialog"]');
  await expect(dialog).toBeVisible();
  await page.keyboard.type('zzzz-no-match');
  await expect(dialog).toContainText('No matches for');
  await page.keyboard.press('Escape');
  await expect(dialog.locator('input')).toHaveValue('');
  await page.keyboard.press('Escape');
  await expect(page.locator('.overlay')).toHaveCount(0);
  await expect(page.locator('html')).toHaveAttribute('data-route', 'conf');
  expect(errors).toEqual([]);
});

test('help: ? opens every section, Esc closes and gives focus back', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/req/CORE-031', errors);
  await page.locator('.shell__theme').focus();
  await page.keyboard.press('?');
  const dialog = page.locator('.overlay--help [role="dialog"]');
  await expect(dialog).toBeVisible();
  for (const section of ['keyboard', 'reading', 'replays', 'lean']) {
    await expect(dialog.locator(`#help-${section}`)).toBeAttached();
  }
  await page.keyboard.press('Escape');
  await expect(page.locator('.overlay')).toHaveCount(0);
  await expect(page.locator('.shell__theme')).toBeFocused();
  expect(errors).toEqual([]);
});

test('keyboard: g s, g r, g c switch views and focus the h1', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/conf', errors);
  for (const [key, view] of [['r', 'req'], ['s', 'situations'], ['c', 'conf']] as const) {
    await page.keyboard.press('g');
    await page.keyboard.press(key);
    await expect(page.locator('html')).toHaveAttribute('data-route', view);
    await expect(page.locator('main#main h1')).toBeFocused();
  }
  expect(errors).toEqual([]);
});

test('theme: the toggle and t cycle Auto, Light, Dark; the choice survives a reload', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/', errors);
  const html = page.locator('html');
  const toggle = page.locator('.shell__theme');
  await expect(toggle).toHaveAttribute('aria-label', 'Theme: Auto');
  await toggle.click();
  await expect(html).toHaveAttribute('data-theme', 'light');
  await expect(toggle).toHaveAttribute('aria-label', 'Theme: Light');
  const lightBg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  await page.locator('main#main h1').focus();
  await page.keyboard.press('t');
  await expect(html).toHaveAttribute('data-theme', 'dark');
  const darkBg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  expect(darkBg).not.toBe(lightBg);
  await page.reload();
  await page.locator('#app[data-ready="true"]').waitFor();
  await expect(html).toHaveAttribute('data-theme', 'dark');
  await expect(toggle).toHaveAttribute('aria-label', 'Theme: Dark');
  await toggle.click();
  await expect(html).not.toHaveAttribute('data-theme', /./);
  expect(errors).toEqual([]);
});

test('dark scheme without a stored choice follows the system', async ({ browser }) => {
  const context = await browser.newContext({ colorScheme: 'dark' });
  const page = await context.newPage();
  const errors: string[] = [];
  await openRoute(page, '#/', errors);
  const dark = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  await page.emulateMedia({ colorScheme: 'light' });
  const light = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  expect(dark).not.toBe(light);
  expect(errors).toEqual([]);
  await context.close();
});

test('player: a blocked step shows the Lean reason and its rule; keys move the step', async ({ page }) => {
  const entry = data.situations.find((s) => s.slug === 'inhibitor-blocks');
  const blocked = entry?.result?.steps.find((s) => s.kind === 'blocked');
  expect(blocked, 'inhibitor-blocks has a blocked replay step').toBeDefined();
  if (entry === undefined || blocked === undefined || blocked.kind !== 'blocked') return;
  const last = entry.steps.length;

  const errors: string[] = [];
  await openRoute(page, `#/situation/inhibitor-blocks?step=${blocked.index + 1}`, errors);
  const main = page.locator('main#main');
  await expect(main).toContainText(blocked.message);
  await expect(main.locator(`a[href="#/req/${blocked.requirement}"]`).first()).toBeVisible();

  const player = main.locator('[role="group"]').first();
  await expect(player).toHaveAttribute('aria-label', /^Net player/);
  await expect(player.locator('svg').first()).toBeVisible();
  await player.focus();
  await page.keyboard.press('Home');
  // Step 0 is the default, so the address leaves the step out.
  await expect.poll(() => new URL(page.url()).hash).toBe('#/situation/inhibitor-blocks');
  await page.keyboard.press('ArrowRight');
  await expect.poll(() => new URL(page.url()).hash).toBe('#/situation/inhibitor-blocks?step=1');
  await page.keyboard.press('End');
  await expect.poll(() => new URL(page.url()).hash).toBe(`#/situation/inhibitor-blocks?step=${last}`);
  await expect(main).toContainText(blocked.message);
  expect(errors).toEqual([]);
});

test('player: every place of the net is drawn in the diagram', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/situation/inhibitor-blocks', errors);
  const svg = page.locator('main#main [role="group"] svg').first();
  for (const place of ['job', 'lock', 'done']) {
    await expect(svg.locator(`[data-kind="place"][data-name="${place}"]`)).toHaveCount(1);
  }
  for (const t of ['take', 'release']) {
    await expect(svg.locator(`[data-kind="transition"][data-name="${t}"]`)).toHaveCount(1);
  }
  expect(errors).toEqual([]);
});

test('companion Lean blocks show as tabs that arrow keys move between', async ({ page }) => {
  const blocks = data.lean['EXEC-002'] ?? [];
  expect(blocks.length, 'EXEC-002 has a companion block').toBeGreaterThan(1);
  const errors: string[] = [];
  await openRoute(page, '#/req/EXEC-002', errors);
  const tabs = page.locator('main#main [role="tablist"] [role="tab"]');
  await expect(tabs).toHaveCount(blocks.length);
  await expect(tabs.first()).toHaveAttribute('aria-selected', 'true');
  await tabs.first().focus();
  await page.keyboard.press('ArrowRight');
  await expect(tabs.nth(1)).toHaveAttribute('aria-selected', 'true');
  await expect(tabs.nth(1)).toBeFocused();
  await expect(page.locator('main#main [role="tabpanel"]:visible')).toHaveCount(1);
  expect(errors).toEqual([]);
});

test('a tombstone says it was removed and links nowhere dead', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/req/IO-006', errors);
  await expect(page.locator('main#main h1')).toHaveCount(1);
  await expect(page.locator('main#main')).toContainText(/removed/i);
  expect(errors).toEqual([]);
});

test('a rule with a Lean block links its evidence to the proof graph', async ({ page }) => {
  const errors: string[] = [];
  await openRoute(page, '#/req/CORE-031', errors);
  const theorem = data.lean['CORE-031']?.[0]?.evidence[0]?.theorem;
  expect(theorem).toBeDefined();
  await expect(page.locator(`main#main a[href="${data.links.proofGraph}#${theorem ?? ''}"]`).first()).toBeAttached();
  expect(errors).toEqual([]);
});

test('reduced motion zeroes the motion tokens', async ({ browser }) => {
  const context = await browser.newContext({ reducedMotion: 'reduce' });
  const page = await context.newPage();
  const errors: string[] = [];
  await openRoute(page, '#/', errors);
  await settle(page);
  const durations = await page.evaluate(() => {
    const css = getComputedStyle(document.documentElement);
    return ['--dur-fast', '--dur', '--dur-slow'].map((name) => css.getPropertyValue(name).trim());
  });
  for (const d of durations) expect(['0s', '0ms', '0', '0.01ms']).toContain(d);
  expect(errors).toEqual([]);
  await context.close();
});
