import { defineConfig } from 'tsup';
import { copyFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { execSync } from 'node:child_process';

export default defineConfig({
  entry: {
    index: 'src/index.ts',
    'export/index': 'src/export/index.ts',
    'verification/index': 'src/verification/index.ts',
    'debug/index': 'src/debug/index.ts',
    'doclet/index': 'src/doclet/index.ts',
    'render-dom/index': 'src/render-dom/index.ts',
    'viewer/index': 'src/viewer/index.ts',
  },
  format: ['esm'],
  dts: true,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  splitting: true,
  onSuccess: async () => {
    // Copy doclet resources to dist (legacy petrinet-diagrams.{js,css}).
    {
      const src = 'src/doclet/resources';
      const dest = 'dist/doclet/resources';
      mkdirSync(dest, { recursive: true });
      for (const file of ['petrinet-diagrams.css', 'petrinet-diagrams.js']) {
        copyFileSync(join(src, file), join(dest, file));
      }
    }
    // Copy canonical viewer CSS to dist/viewer/.
    {
      mkdirSync('dist/viewer', { recursive: true });
      copyFileSync('src/viewer/resources/viewer.css', 'dist/viewer/viewer.css');
    }
    // Build the IIFE bundle (esbuild). Separate script because tsup's ESM
    // pipeline doesn't easily produce a single-file IIFE that inlines
    // wasm-bearing CommonJS deps like @viz-js/viz.
    execSync('node scripts/build-viewer-iife.mjs', { stdio: 'inherit' });
  },
});
