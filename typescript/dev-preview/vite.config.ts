import { defineConfig } from 'vite';
import { resolve } from 'node:path';

const repoRoot = resolve(__dirname, '../..');

/**
 * Dev-preview Vite config.
 *
 * Serves the parent repo root as `publicDir` so the generated `sample.dot`
 * is reachable at `/sample.dot`. Runs from `typescript/dev-preview/`.
 */
export default defineConfig({
  root: __dirname,
  publicDir: repoRoot,
  server: {
    port: 5173,
    open: true,
  },
});
