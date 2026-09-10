/**
 * Hub-place benchmark for the intermediate-disablement check (TIME-012).
 *
 * k transitions share one place POOL holding k tokens. Each T_i takes one POOL token plus
 * its own GO_i token and puts the POOL token back, so one firing pass fires all k and every
 * firing takes from the hub while its siblings stay enabled. The hub never runs short, so
 * the check disables nothing and the run should grow linearly with k.
 *
 * Run: cd typescript && npx tsx scripts/bench-hub-place.ts
 * Prints the median of 5 timed runs per size, each on a fresh executor after one warm-up.
 */
import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { place } from '../src/core/place.js';
import type { Place } from '../src/core/place.js';
import { one } from '../src/core/in.js';
import { outPlace } from '../src/core/out.js';
import { tokenOf } from '../src/core/token.js';
import type { Token } from '../src/core/token.js';
import { BitmapNetExecutor } from '../src/runtime/bitmap-net-executor.js';
import { PrecompiledNet } from '../src/runtime/precompiled-net.js';
import { PrecompiledNetExecutor } from '../src/runtime/precompiled-net-executor.js';

const SIZES = [250, 500, 1000, 2000] as const;
const RUNS = 5;

function buildHubNet(k: number): { net: PetriNet; initialTokens: () => Map<Place<any>, Token<any>[]> } {
  const pool = place<string>('POOL');
  const gos = Array.from({ length: k }, (_, i) => place<string>(`GO_${i}`));

  const builder = PetriNet.builder(`Hub${k}`);
  for (let i = 0; i < k; i++) {
    builder.transition(
      Transition.builder(`T_${i}`)
        .inputs(one(pool), one(gos[i]!))
        .outputs(outPlace(pool))
        .action(async (ctx) => { ctx.output(pool, 'p'); })
        .build()
    );
  }

  // Fresh token lists per run: an executor owns the marking it is given.
  const initialTokens = () => new Map<Place<any>, Token<any>[]>([
    [pool, Array.from({ length: k }, () => tokenOf('p'))],
    ...gos.map((go): [Place<any>, Token<any>[]] => [go, [tokenOf('g')]]),
  ]);
  return { net: builder.build(), initialTokens };
}

async function medianRunMs(make: () => BitmapNetExecutor | PrecompiledNetExecutor): Promise<number> {
  await make().run(10_000); // warm-up
  const samples: number[] = [];
  for (let r = 0; r < RUNS; r++) {
    const executor = make();
    const t0 = performance.now();
    await executor.run(10_000);
    samples.push(performance.now() - t0);
  }
  samples.sort((a, b) => a - b);
  return samples[Math.floor(samples.length / 2)]!;
}

async function main() {
  console.log(`Hub place: median of ${RUNS} runs`);
  for (const k of SIZES) {
    const { net, initialTokens } = buildHubNet(k);
    const program = PrecompiledNet.compile(net);
    const bitmap = await medianRunMs(() => new BitmapNetExecutor(net, initialTokens()));
    const precompiled = await medianRunMs(() => new PrecompiledNetExecutor(net, initialTokens(), { program }));
    console.log(
      `  k=${String(k).padStart(4)}  bitmap ${bitmap.toFixed(1).padStart(7)} ms`
      + `  precompiled ${precompiled.toFixed(1).padStart(7)} ms`
    );
  }
}

main().catch(console.error);
