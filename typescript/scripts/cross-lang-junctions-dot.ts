#!/usr/bin/env -S npx tsx
/**
 * Cross-language DOT byte-parity fixture: builds a net that exercises both
 * XOR-junction and AND-junction synthesis (per EXP-012) in a single
 * transition's output tree. The transition fires from one input place to a
 * combined output spec `AND(XOR(a, b), c)` — yielding one AND junction and
 * one nested XOR junction.
 *
 * Mirrors `java/src/test/java/org/libpetri/export/CrossLangJunctionsDot.java`
 * and `rust/libpetri/tests/cross_lang_junctions_dot.rs`. Consumed by
 * `scripts/cross-lang-dot-parity.sh`.
 */

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { place } from '../src/core/place.js';
import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { one } from '../src/core/in.js';
import { andPlaces, outPlace, xorPlaces } from '../src/core/out.js';
import { dotExport } from '../src/export/dot-exporter.js';

const DEFAULT_OUT = 'target/cross-lang-junctions-dot/ts.dot';

function parseOut(argv: readonly string[]): string {
  for (const arg of argv) {
    if (arg.startsWith('--out=')) return arg.slice('--out='.length);
  }
  return DEFAULT_OUT;
}

function main(): void {
  // Net layout — every junction-target place is "pre-seeded" into the
  // mapper's place-analysis map by an earlier source transition so the
  // junction-emitting transition's unordered Out.allPlaces() traversal does
  // NOT determine the place declaration order in the final DOT. This works
  // around an arc-iteration-order divergence in Java's Out.allPlaces()
  // (HashSet-backed, JVM-randomised).
  const srcA = place<string>('srcA');
  const srcB = place<string>('srcB');
  const srcC = place<string>('srcC');
  const srcD = place<string>('srcD');
  const a = place<string>('a');
  const b = place<string>('b');
  const c = place<string>('c');
  const d = place<string>('d');
  const srcXor = place<string>('srcXor');
  const srcAnd = place<string>('srcAnd');

  // Seed transitions: register each leaf place into the analysis map in
  // pre-order before any junction-bearing transition is examined.
  const seedA = Transition.builder('seedA').inputs(one(srcA)).outputs(outPlace(a)).build();
  const seedB = Transition.builder('seedB').inputs(one(srcB)).outputs(outPlace(b)).build();
  const seedC = Transition.builder('seedC').inputs(one(srcC)).outputs(outPlace(c)).build();
  const seedD = Transition.builder('seedD').inputs(one(srcD)).outputs(outPlace(d)).build();

  // The junction transitions — these are what actually exercise EXP-012.
  const tXor = Transition.builder('routeXor')
    .inputs(one(srcXor))
    .outputs(xorPlaces(a, b))
    .build();

  const tAnd = Transition.builder('routeAnd')
    .inputs(one(srcAnd))
    .outputs(andPlaces(c, d))
    .build();

  const net = PetriNet.builder('junctions')
    .transition(seedA)
    .transition(seedB)
    .transition(seedC)
    .transition(seedD)
    .transition(tXor)
    .transition(tAnd)
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
