/**
 * Bundles the browser code and the CSS with esbuild, in memory.
 *
 * - `src/app/boot.ts`: tiny IIFE inlined in `<head>` (applies the stored theme before paint).
 * - `src/app/main.ts`: the app IIFE inlined at the end of `<body>`.
 * - CSS: `src/app/style.css` first, then `src/app/css/*.css` in file-name order, minified.
 *
 * Output is deterministic: minified (no path comments), no source maps, no legal comments,
 * fixed target, working directory pinned to the package.
 */
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { build, transform } from 'esbuild';

/** Browser baseline: every evergreen browser since 2020; esbuild cannot lower all syntax to ES5. */
export const BROWSER_TARGET = 'es2020';

export interface Bundle {
  readonly bootJs: string;
  readonly appJs: string;
  readonly css: string;
}

async function bundleEntry(siteRoot: string, entry: string): Promise<string> {
  const result = await build({
    absWorkingDir: siteRoot,
    entryPoints: [entry],
    bundle: true,
    format: 'iife',
    platform: 'browser',
    target: BROWSER_TARGET,
    tsconfig: join(siteRoot, 'src/app/tsconfig.json'),
    minify: true,
    sourcemap: false,
    legalComments: 'none',
    charset: 'utf8',
    write: false,
    logLevel: 'silent',
  });
  const file = result.outputFiles[0];
  if (file === undefined) throw new Error(`esbuild produced no output for ${entry}`);
  return file.text.trimEnd();
}

/** The CSS files in concatenation order, relative to the package root. */
export function cssFiles(siteRoot: string): readonly string[] {
  const dir = join(siteRoot, 'src/app/css');
  const extra = readdirSync(dir)
    .filter((f) => f.endsWith('.css'))
    .sort()
    .map((f) => `src/app/css/${f}`);
  return ['src/app/style.css', ...extra];
}

async function bundleCss(siteRoot: string): Promise<string> {
  const source = cssFiles(siteRoot)
    .map((f) => `/* ${f} */\n${readFileSync(join(siteRoot, f), 'utf8')}`)
    .join('\n');
  const result = await transform(source, { loader: 'css', minify: true, target: ['chrome100', 'firefox100', 'safari15'], legalComments: 'none' });
  return result.code.trimEnd();
}

export async function bundleApp(siteRoot: string): Promise<Bundle> {
  const [bootJs, appJs, css] = await Promise.all([
    bundleEntry(siteRoot, 'src/app/boot.ts'),
    bundleEntry(siteRoot, 'src/app/main.ts'),
    bundleCss(siteRoot),
  ]);
  return { bootJs, appJs, css };
}
