import { defineConfig, devices } from '@playwright/test';

/**
 * E2E config for the debug UI. Tests live in `e2e/` (kept out of `tests/`
 * so vitest's `tests/**\/*.test.ts` glob never picks them up).
 *
 * The layout regions under test are static HTML, so the Vite dev server
 * with no debug backend is enough — the page renders its "Disconnected"
 * empty state and every panel is present.
 */
const PORT = 5199;
const ORIGIN = `http://localhost:${PORT}`;

export default defineConfig({
  testDir: './e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: 0,
  reporter: 'list',
  use: {
    baseURL: ORIGIN,
    trace: 'on-first-retry',
  },
  projects: [
    { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
  ],
  webServer: {
    command: `npx vite --port ${PORT} --strictPort`,
    url: `${ORIGIN}/debug/petri/ui/`,
    reuseExistingServer: !process.env.CI,
    timeout: 60_000,
  },
});
