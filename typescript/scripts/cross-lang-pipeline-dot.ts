#!/usr/bin/env -S npx tsx
/**
 * Cross-language DOT byte-parity fixture: builds the canonical
 * producer / bounded-buffer / consumer pipeline composed via
 * {@link PetriNet.builder().compose}, and writes the resulting DOT to the
 * path supplied via `--out=<path>` (or `target/cross-lang-pipeline-dot/ts.dot`
 * by default, relative to `typescript/`).
 *
 * Mirrors `java/src/test/java/org/libpetri/export/CrossLangPipelineDot.java`
 * and `rust/libpetri/tests/cross_lang_pipeline_dot.rs`. Consumed by
 * `scripts/cross-lang-dot-parity.sh`.
 *
 * Usage (from repo root):
 *   cd typescript && npx tsx scripts/cross-lang-pipeline-dot.ts --out=/tmp/ts.dot
 */

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { place } from '../src/core/place.js';
import { PetriNet } from '../src/core/petri-net.js';
import { dotExport } from '../src/export/dot-exporter.js';
import { boundedBuffer, consumer, producer } from '../tests/fixtures/subnet-fixtures.js';

const DEFAULT_OUT = 'target/cross-lang-pipeline-dot/ts.dot';

function parseOut(argv: readonly string[]): string {
  for (const arg of argv) {
    if (arg.startsWith('--out=')) return arg.slice('--out='.length);
  }
  return DEFAULT_OUT;
}

function main(): void {
  const producerDef = producer();
  const bufferDef = boundedBuffer(2);
  const consumerDef = consumer();

  const prodInst = producerDef.instantiate('prod');
  const bufInst = bufferDef.instantiate('buf');
  const consInst = consumerDef.instantiate('cons');

  const producerToBuffer = place<string>('producerToBuffer');
  const bufferToConsumer = place<string>('bufferToConsumer');

  const net = PetriNet.builder('pipeline')
    .compose(prodInst, (b) => b.bindPort<string>('output', producerToBuffer))
    .compose(bufInst, (b) =>
      b.bindPort<string>('put', producerToBuffer).bindPort<string>('get', bufferToConsumer),
    )
    .compose(consInst, (b) => b.bindPort<string>('input', bufferToConsumer))
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
