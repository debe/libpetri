/**
 * CLI: `npm run build` (= `tsx src/gen/main.ts`).
 *
 *   --out <file>     write the page here instead of docs/spec/index.html
 *   --no-landing     do not write the landing page docs/index.html
 */
import { resolve } from 'node:path';
import { buildSite } from './build.js';
import { DEFAULT_LANDING_FILE, DEFAULT_OUT_FILE, REPO_ROOT } from './paths.js';

interface Args {
  readonly outFile: string;
  readonly landing: boolean;
}

function parseArgs(argv: readonly string[]): Args {
  let outFile = DEFAULT_OUT_FILE;
  let landing = true;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--out') {
      const value = argv[++i];
      if (value === undefined) throw new Error('--out needs a file');
      outFile = resolve(value);
    } else if (arg === '--no-landing') {
      landing = false;
    } else {
      throw new Error(`unknown argument ${String(arg)}`);
    }
  }
  return { outFile, landing };
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv.slice(2));
  const report = await buildSite({
    root: REPO_ROOT,
    outFile: args.outFile,
    landingFile: args.landing ? DEFAULT_LANDING_FILE : null,
  });
  const c = report.data.counts;
  process.stdout.write(
    `spec-site: ${report.bytes} bytes; ${c.activeIds} active IDs, ${c.leanBlocks} Lean blocks, ` +
      `${c.situations} situations; ${report.written.length === 0 ? 'no file changed' : `wrote ${report.written.join(', ')}`}\n`,
  );
}

main().catch((error: unknown) => {
  process.stderr.write(`spec-site build failed: ${error instanceof Error ? (error.stack ?? error.message) : String(error)}\n`);
  process.exitCode = 1;
});
