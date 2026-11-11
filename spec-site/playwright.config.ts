import { defineConfig, devices } from '@playwright/test';

/**
 * Browser tests over the built page, opened from file:// exactly as a reader who saved it
 * would (the page fetches nothing). Run `npm run build` first; `e2e/site.ts` holds the URL
 * helper. Screenshots and traces go to test-results/ (git-ignored).
 */
export default defineConfig({
  testDir: './e2e',
  fullyParallel: true,
  forbidOnly: !!process.env['CI'],
  retries: 0,
  reporter: process.env['CI'] ? [['list'], ['html', { open: 'never' }]] : 'list',
  use: {
    trace: 'retain-on-failure',
  },
  projects: [
    { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
    { name: 'narrow', use: { ...devices['Desktop Chrome'], viewport: { width: 400, height: 800 } } },
  ],
});
