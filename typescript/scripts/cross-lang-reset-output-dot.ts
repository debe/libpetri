#!/usr/bin/env -S npx tsx
/**
 * Cross-language DOT byte-parity fixture: builds a net where a transition
 * both outputs to a place and resets the same place — the renderer must
 * collapse the two arcs into a single combined edge per EXP-013.
 *
 * Mirrors `java/src/test/java/org/libpetri/export/CrossLangResetOutputDot.java`
 * and `rust/libpetri/tests/cross_lang_reset_output_dot.rs`. Consumed by
 * `scripts/cross-lang-dot-parity.sh`.
 */

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { place } from '../src/core/place.js';
import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { outPlace } from '../src/core/out.js';
import { dotExport } from '../src/export/dot-exporter.js';

const DEFAULT_OUT = 'target/cross-lang-reset-output-dot/ts.dot';

function parseOut(argv: readonly string[]): string {
  for (const arg of argv) {
    if (arg.startsWith('--out=')) return arg.slice('--out='.length);
  }
  return DEFAULT_OUT;
}

function main(): void {
  const cache = place<string>('cache');

  // refresh: outputs to cache AND resets cache -> single combined edge.
  const refresh = Transition.builder('refresh')
    .outputs(outPlace(cache))
    .reset(cache)
    .build();

  const net = PetriNet.builder('reset_collapse').place(cache).transition(refresh).build();

  const dot = dotExport(net);

  const __dirname = dirname(fileURLToPath(import.meta.url));
  const tsRoot = resolve(__dirname, '..');
  const outPath = parseOut(process.argv.slice(2));
  const target = resolve(tsRoot, outPath);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, dot);
}

main();
