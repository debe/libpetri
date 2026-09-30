/**
 * Cross-language conformance of the TypeScript verifier against the Lean reference
 * (`spec/verification-fixtures/conformance/README.md`; mirrors
 * `rust/libpetri-verification/tests/conformance.rs`).
 *
 * Every corpus net runs under the four route setups of `route_agreement.rs` (`enum`,
 * `smt+lb`, `smt-lb`, `ic3`); each verdict is held to the README conformance rule. `unknown`
 * is allowed and counted; a violation must carry a trace (`[]` for the initial marking). The four
 * setups run twice: the atomic pass (`assumeAtomicFiring(true)`) is held to every rule, the
 * default pass (the VER-004 split on, as a caller gets it) to rules 1, 3 and 4, since the split
 * adds runs with an action in flight that the atomic reference does not have. A default-pass
 * trace of a split net names completion steps and is counted, not replayed or dumped. Skips while the corpus or its expected files
 * are absent; the three SMT setups skip without z3.
 *
 * Knobs: `LIBPETRI_CONFORMANCE_DIR` (corpus root), `LIBPETRI_CONFORMANCE_DUMP=<dir>` (write
 * every traced Violated to `<dir>/<id>.traces.json` for the Lean replay step),
 * `LIBPETRI_CONFORMANCE_REQUIRE=1` (fail instead of skipping when the corpus is absent).
 */
import { describe, expect, it } from 'vitest';
import { Z3_AVAILABLE } from '../../fixtures/z3.js';
import { locateCorpus, readCorpus, renderReport, runCorpus } from './corpus.js';
import { renderFinding } from './reference.js';

const corpus = readCorpus(locateCorpus());
const REQUIRE = process.env['LIBPETRI_CONFORMANCE_REQUIRE'] === '1';

if (corpus.skipReason !== null && !REQUIRE) {
  console.warn(`conformance (typescript) skipped: ${corpus.skipReason}`);
}

describe.runIf(corpus.skipReason !== null && REQUIRE)('conformance corpus required', () => {
  it('is present (LIBPETRI_CONFORMANCE_REQUIRE=1)', () => {
    expect.fail(`LIBPETRI_CONFORMANCE_REQUIRE=1 but ${corpus.skipReason}`);
  });
});

describe.skipIf(corpus.skipReason !== null)('conformance corpus (Lean reference)', () => {
  it('every verdict conforms to the reference', async () => {
    if (!Z3_AVAILABLE) console.warn('conformance (typescript): z3 not available, SMT setups skipped');
    const report = await runCorpus(corpus, { z3: Z3_AVAILABLE, dumpDir: process.env['LIBPETRI_CONFORMANCE_DUMP'] });
    console.log(renderReport(corpus, report));
    const stale = corpus.missingExpected.map(id => `${id}: no expected/${id}.json (expected/ is stale)`);
    expect([...stale, ...report.findings.map(renderFinding)], 'conformance findings').toEqual([]);
  }, 60 * 60 * 1000);
});
