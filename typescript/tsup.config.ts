import { defineConfig } from 'tsup';

export default defineConfig({
  entry: {
    index: 'src/index.ts',
    'export/index': 'src/export/index.ts',
    'verification/index': 'src/verification/index.ts',
    'debug/index': 'src/debug/index.ts',
  },
  format: ['esm'],
  dts: true,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  splitting: true,
});
