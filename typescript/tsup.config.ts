import { defineConfig } from 'tsup';
import { copyFileSync, mkdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { execSync } from 'node:child_process';

// Stamped into the viewer bundle so a generated doc page can report which
// viewer drew it (see src/viewer/version.ts). Kept in sync automatically by
// reading the package version rather than duplicating a literal.
const { version } = JSON.parse(readFileSync('package.json', 'utf-8')) as {
  version: string;
};

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
  define: { __LIBPETRI_VIEWER_VERSION__: JSON.stringify(version) },
  dts: true,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  splitting: true,
  onSuccess: async () => {
    // Copy canonical viewer CSS to dist/viewer/.
    {
      mkdirSync('dist/viewer', { recursive: true });
      copyFileSync('src/viewer/resources/viewer.css', 'dist/viewer/viewer.css');
    }
    // Build the IIFE bundle (esbuild). Separate script because tsup's ESM
    // pipeline doesn't easily produce a single-file IIFE that inlines
    // wasm-bearing CommonJS deps like @viz-js/viz.
    execSync('node scripts/build-viewer-iife.mjs', { stdio: 'inherit' });
    // Doclet resources come from the bundle just built, not from the tracked
    // mirror in src/doclet/resources. Copying the mirror here (which is what
    // this step used to do, before the IIFE build ran) left dist one viewer
    // build behind on every run: scripts/build-viewer.sh refreshes the mirror
    // only *after* npm run build:viewer has already finished, so the copy
    // always picked up the previous bundle. dist is what npm publishes, so the
    // shipped TypeDoc plugin lagged the shipped viewer permanently.
    //
    // The tracked mirror still exists for the Java and Rust ports and for
    // vitest, which loads the doclet from src; spec/viewer-bundle.sha256 and
    // the per-port drift tests keep all three copies honest.
    {
      const dest = 'dist/doclet/resources';
      mkdirSync(dest, { recursive: true });
      copyFileSync('dist/viewer/viewer.iife.js', join(dest, 'petrinet-diagrams.js'));
      copyFileSync('dist/viewer/viewer.css', join(dest, 'petrinet-diagrams.css'));
    }
  },
});
