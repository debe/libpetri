import { defineConfig } from 'vite';
import tailwindcss from '@tailwindcss/vite';
import { viteSingleFile } from 'vite-plugin-singlefile';

export default defineConfig({
  base: '/debug/petri/ui/',
  plugins: [tailwindcss(), viteSingleFile()],
  build: {
    outDir: 'dist',
    emptyOutDir: true,
  },
});
