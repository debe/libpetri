import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
    globals: true,
  },
  bench: {
    include: ['tests/**/*.bench.ts'],
    globals: true,
  },
});
