import { defineConfig } from 'tsup';
import { copyFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

export default defineConfig({
  entry: {
    index: 'src/index.ts',
    'export/index': 'src/export/index.ts',
    'verification/index': 'src/verification/index.ts',
    'debug/index': 'src/debug/index.ts',
    'doclet/index': 'src/doclet/index.ts',
  },
  format: ['esm'],
  dts: true,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  splitting: true,
  onSuccess: async () => {
    // Copy doclet resources to dist
    const src = 'src/doclet/resources';
    const dest = 'dist/doclet/resources';
    mkdirSync(dest, { recursive: true });
    for (const file of ['petrinet-diagrams.css', 'petrinet-diagrams.js']) {
      copyFileSync(join(src, file), join(dest, file));
    }
  },
});
