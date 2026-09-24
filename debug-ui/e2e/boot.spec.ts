import { test, expect } from '@playwright/test';

/**
 * Boot guard: the app's JavaScript must actually run.
 *
 * `layout.spec.ts` asserts on static HTML, so it stayed green while `main.ts`
 * threw at module load (the root `libpetri` entry once dragged the z3 verifier
 * and its `node:child_process` into the browser graph). This spec fails on any
 * uncaught page error during load, and requires the debug net to have fired
 * `t_connect`, i.e. opened its WebSocket to `/debug/petri`.
 *
 * Vite's HMR socket also lives under the base path (`/debug/petri/ui/?token=`),
 * so the match is on the exact pathname, not a substring.
 */

const APP_PATH = '/debug/petri/ui/';

test('app boots without page errors and opens its debug WebSocket', async ({ page }) => {
  const pageErrors: string[] = [];
  page.on('pageerror', (err) => pageErrors.push(err.message));

  const appSocket = page.waitForEvent('websocket', {
    predicate: (ws) => new URL(ws.url()).pathname === '/debug/petri',
    timeout: 10_000,
  });

  await page.goto(APP_PATH);
  const ws = await appSocket.catch(() => null);

  expect(pageErrors, 'uncaught errors during load').toEqual([]);
  expect(ws, 'the app never opened a WebSocket to /debug/petri').not.toBeNull();
});
