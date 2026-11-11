import { defineConfig } from 'vitest/config';

/**
 * Unit tests live in tests/ (Node environment by default). A test that needs a DOM starts with
 * the comment `// @vitest-environment happy-dom`. Browser tests live in e2e/ (Playwright).
 */
export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
    environment: 'node',
    testTimeout: 60_000,
  },
});
