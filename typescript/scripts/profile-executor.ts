/**
 * CPU profiling script for PrecompiledNetExecutor vs BitmapNetExecutor.
 *
 * Run: cd typescript && npx tsx --cpu-prof scripts/profile-executor.ts
 * Output: .cpuprofile file — open in Chrome DevTools (Performance tab → Load profile)
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

function buildSyncLinearChain(n: number): { net: PetriNet; start: Place<string> } {
  const start = place<string>('sync_start');
  const places: Place<string>[] = [start];
  for (let i = 1; i <= n; i++) {
    places.push(place<string>(`sync_p${i}`));
  }

  const builder = PetriNet.builder(`SyncLinear${n}`);
  for (let i = 0; i < n; i++) {
    const to = places[i + 1]!;
    builder.transition(
      Transition.builder(`sync_t${i + 1}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(async (ctx) => { ctx.output(to, 'v'); })
        .build()
    );
  }

  return { net: builder.build(), start };
}

function initialTokens(start: Place<string>): Map<Place<any>, Token<any>[]> {
  return new Map([[start, [tokenOf('start')]]]);
}

async function profileBitmapExecutor(net: PetriNet, start: Place<string>, iterations: number): Promise<void> {
  console.log(`  BitmapNetExecutor × ${iterations}...`);
  const t0 = performance.now();
  for (let i = 0; i < iterations; i++) {
    const executor = new BitmapNetExecutor(net, initialTokens(start));
    await executor.run(5000);
  }
  const elapsed = performance.now() - t0;
  console.log(`  BitmapNetExecutor: ${elapsed.toFixed(1)}ms total, ${(elapsed / iterations).toFixed(2)}ms/iter`);
}

async function profilePrecompiledExecutor(net: PetriNet, start: Place<string>, iterations: number): Promise<void> {
  const program = PrecompiledNet.compile(net);
  console.log(`  PrecompiledNetExecutor × ${iterations}...`);
  const t0 = performance.now();
  for (let i = 0; i < iterations; i++) {
    const executor = new PrecompiledNetExecutor(net, initialTokens(start), { program });
    await executor.run(5000);
  }
  const elapsed = performance.now() - t0;
  console.log(`  PrecompiledNetExecutor: ${elapsed.toFixed(1)}ms total, ${(elapsed / iterations).toFixed(2)}ms/iter`);
}

async function main() {
  for (const [n, iterations] of [[100, 3000], [500, 1000]] as const) {
    const { net, start } = buildSyncLinearChain(n);
    console.log(`\n=== Sync Linear Chain: ${n} transitions ===`);

    // Warmup
    for (let i = 0; i < 50; i++) {
      await new BitmapNetExecutor(net, initialTokens(start)).run(5000);
      await new PrecompiledNetExecutor(net, initialTokens(start), { program: PrecompiledNet.compile(net) }).run(5000);
    }

    await profileBitmapExecutor(net, start, iterations);
    await profilePrecompiledExecutor(net, start, iterations);
  }
}

main().catch(console.error);
