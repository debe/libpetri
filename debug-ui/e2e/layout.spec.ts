import { test, expect } from '@playwright/test';

/**
 * Layout regression guard for the debug UI.
 *
 * happy-dom (the vitest env) does not compute CSS layout, so a real
 * browser is required to catch a panel that is present in the DOM but
 * collapsed to zero size. The right inspector panel was reported
 * missing; this test asserts every primary region is actually visible
 * and the inspector has its expected ~384px (`w-96`) width.
 *
 * No debug backend is needed — the regions are static HTML and render
 * in the disconnected empty state.
 */

const APP_PATH = '/debug/petri/ui/';

test.beforeEach(async ({ page }) => {
  await page.goto(APP_PATH);
});

test('every primary layout region is visible', async ({ page }) => {
  await expect(page.locator('header')).toBeVisible();
  await expect(page.locator('#subnet-panel')).toBeVisible();
  await expect(page.locator('#diagram-container')).toBeVisible();
  await expect(page.locator('#inspector-panel')).toBeVisible();
  await expect(page.locator('footer')).toBeVisible();
});

test('right inspector panel has its w-96 width and sits inside the viewport', async ({ page }) => {
  const panel = page.locator('#inspector-panel');
  await expect(panel).toBeVisible();

  const box = await panel.boundingBox();
  expect(box, 'inspector panel must have a layout box').not.toBeNull();

  // Tailwind `w-96` = var(--spacing: .25rem) * 96 = 24rem = 384px.
  expect(box!.width).toBeGreaterThan(360);
  expect(box!.width).toBeLessThan(410);
  expect(box!.height).toBeGreaterThan(100);

  // The panel must be fully on-screen, not pushed off the right edge.
  const viewport = page.viewportSize();
  expect(viewport).not.toBeNull();
  expect(box!.x + box!.width).toBeLessThanOrEqual(viewport!.width + 1);
});

test('inspector panel renders its four sections', async ({ page }) => {
  await expect(page.locator('#marking-inspector')).toBeVisible();
  await expect(page.locator('#token-inspector')).toBeVisible();
  await expect(page.locator('#breakpoint-list')).toBeVisible();
  await expect(page.locator('#event-log')).toBeVisible();
});

test('a very wide diagram does not push the inspector panel off-screen', async ({ page }) => {
  // A large Petri net mounts as an <svg> with an explicit pt-width inside
  // #dot-diagram. If the flex diagram column lacks min-width:0 it grows to
  // that intrinsic width and shoves the inspector past the viewport edge.
  await page.locator('#dot-diagram').evaluate((host) => {
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('width', '8000');
    svg.setAttribute('height', '600');
    host.appendChild(svg);
  });

  const panel = page.locator('#inspector-panel');
  await expect(panel).toBeVisible();

  const box = await panel.boundingBox();
  expect(box, 'inspector panel must have a layout box').not.toBeNull();
  // Still its w-96 width, not collapsed.
  expect(box!.width).toBeGreaterThan(360);

  // The whole panel stays inside the viewport — the diagram column must clip
  // the oversized SVG instead of expanding the row.
  const viewport = page.viewportSize();
  expect(viewport).not.toBeNull();
  expect(box!.x + box!.width).toBeLessThanOrEqual(viewport!.width + 1);
});

test('subnet flat/clustered toggle is present in the header', async ({ page }) => {
  const toggle = page.locator('#toggle-subnets');
  await expect(toggle).toBeVisible();
  // Starts in clustered mode, so the button offers the flat view.
  await expect(toggle).toHaveText(/flat view/i);
});

test('footer debugger controls render', async ({ page }) => {
  for (const id of [
    '#btn-restart',
    '#btn-step-back',
    '#btn-pause',
    '#btn-step-forward',
    '#btn-run-to-end',
    '#timeline-slider',
  ]) {
    await expect(page.locator(id)).toBeVisible();
  }
});
