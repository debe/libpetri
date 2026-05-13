#!/usr/bin/env -S npx tsx
/**
 * Cross-language DOT byte-parity fixture: builds a plain non-composed
 * {@link PetriNet} (no subnet composition, no clusters in the rendered DOT)
 * and writes the resulting DOT to the path supplied via `--out=<path>` (or
 * `target/cross-lang-flat-dot/ts.dot` by default, relative to `typescript/`).
 *
 * Mirrors `java/src/test/java/org/libpetri/export/CrossLangFlatDot.java` and
 * `rust/libpetri/tests/cross_lang_flat_dot.rs`. Consumed by
 * `scripts/cross-lang-dot-parity.sh`.
 */

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { place } from '../src/core/place.js';
import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { one } from '../src/core/in.js';
import { outPlace } from '../src/core/out.js';
import { dotExport } from '../src/export/dot-exporter.js';

const DEFAULT_OUT = 'target/cross-lang-flat-dot/ts.dot';

function parseOut(argv: readonly string[]): string {
  for (const arg of argv) {
    if (arg.startsWith('--out=')) return arg.slice('--out='.length);
  }
  return DEFAULT_OUT;
}

function main(): void {
  const p1 = place<string>('p1');
  const p2 = place<string>('p2');

  const t1 = Transition.builder('t1').inputs(one(p1)).outputs(outPlace(p2)).build();

  const net = PetriNet.builder('flat').place(p1).place(p2).transition(t1).build();

  const dot = dotExport(net);

  const __dirname = dirname(fileURLToPath(import.meta.url));
  const tsRoot = resolve(__dirname, '..');
  const outPath = parseOut(process.argv.slice(2));
  const target = resolve(tsRoot, outPath);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, dot);
}

main();
