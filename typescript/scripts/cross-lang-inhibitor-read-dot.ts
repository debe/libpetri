#!/usr/bin/env -S npx tsx
/**
 * Cross-language DOT byte-parity fixture: builds a net with at least one
 * Read arc and one Inhibitor arc on the same transition to verify the
 * renderer styles each distinctly and produces byte-identical DOT across
 * languages.
 *
 * Mirrors `java/src/test/java/org/libpetri/export/CrossLangInhibitorReadDot.java`
 * and `rust/libpetri/tests/cross_lang_inhibitor_read_dot.rs`. Consumed by
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

const DEFAULT_OUT = 'target/cross-lang-inhibitor-read-dot/ts.dot';

function parseOut(argv: readonly string[]): string {
  for (const arg of argv) {
    if (arg.startsWith('--out=')) return arg.slice('--out='.length);
  }
  return DEFAULT_OUT;
}

function main(): void {
  const req = place<string>('req');
  const done = place<string>('done');
  const lock = place<string>('lock');
  const paused = place<string>('paused');

  const processT = Transition.builder('process')
    .inputs(one(req))
    .read(lock)
    .inhibitor(paused)
    .outputs(outPlace(done))
    .build();

  // Place ordering matches the renderer's place-analysis traversal
  // (inputs -> outputs -> inhibitors -> reads), required for byte-parity
  // because some language backends ignore the builder's place list and
  // re-derive ordering from arc iteration.
  const net = PetriNet.builder('inh_read')
    .place(req)
    .place(done)
    .place(paused)
    .place(lock)
    .transition(processT)
    .build();

  const dot = dotExport(net);

  const __dirname = dirname(fileURLToPath(import.meta.url));
  const tsRoot = resolve(__dirname, '..');
  const outPath = parseOut(process.argv.slice(2));
  const target = resolve(tsRoot, outPath);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, dot);
}

main();
