import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { placeBound, unreachable, type SmtProperty } from '../../src/verification/smt-property.js';
import { ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import { resolveZ3, z3SolverAt, Z3_ENV, DUMP_ENV } from '../../src/verification/z3/z3-process.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

/**
 * End-to-end tests against a STUB `z3` (V5, V6, C4, and the VER-013 transport
 * contract), the TypeScript mirror of Rust's `tests/stub_z3.rs`.
 *
 * The verifier shells out to a `z3` executable, so the only way to pin how it reads a
 * solver reply is to control the reply. Each scenario writes a tiny POSIX shell script
 * named `z3` and points `LIBPETRI_Z3` at it (vitest gives every test file its own
 * worker, so the environment is ours to set). Every stub answers `--version` first,
 * because the transport probes the executable before it runs a script.
 */
const VERSION_OK = 'Z3 version 4.16.0 - 64 bit';

describe.skipIf(process.platform === 'win32')('stub z3 (VER-013 transport contract)', () => {
  let root: string;
  let savedEnv: string | undefined;
  let savedDump: string | undefined;
  let savedPath: string | undefined;

  beforeAll(() => {
    root = mkdtempSync(join(tmpdir(), 'libpetri-stub-z3-'));
    savedEnv = process.env[Z3_ENV];
    savedDump = process.env[DUMP_ENV];
    savedPath = process.env['PATH'];
  });

  afterAll(() => {
    restore(Z3_ENV, savedEnv);
    restore(DUMP_ENV, savedDump);
    restore('PATH', savedPath);
    rmSync(root, { recursive: true, force: true });
  });

  function restore(name: string, value: string | undefined): void {
    if (value == null) delete process.env[name];
    else process.env[name] = value;
  }

  /** Writes `<root>/<name>/z3` answering `--version` with `version`, else running `body`; points LIBPETRI_Z3 at it. */
  function stub(name: string, version: string, body: string): string {
    const dir = join(root, name);
    mkdirSync(dir, { recursive: true });
    const script = join(dir, 'z3');
    writeFileSync(script, `#!/bin/sh\nif [ "$1" = "--version" ]; then echo '${version}'; exit 0; fi\n${body}`, { mode: 0o755 });
    process.env[Z3_ENV] = script;
    return script;
  }

  const p0 = place('p0');
  const p1 = place('p1');
  const blocker = place('blocker');

  /** p0(1) -> p1: a plain chain the stub's answers are applied to. */
  function chainNet(): PetriNet {
    const t = Transition.builder('t').inputs(one(p0)).outputs(outPlace(p1)).build();
    return bindProducers(PetriNet.builder('stub_chain').transitions(t).build());
  }

  /** Nothing ever drains `blocker`, so `t` can never fire: p1 is unreachable. */
  function frozenNet(): PetriNet {
    const t = Transition.builder('t').inputs(one(p0)).inhibitors(blocker).outputs(outPlace(p1)).build();
    return bindProducers(PetriNet.builder('stub_frozen').transitions(t).build());
  }

  function verify(net: PetriNet, property: SmtProperty, timeoutMs = 5_000, tokens: Array<[typeof p0, number]> = [[p0, 1]]) {
    return SmtVerifier.forNet(net)
      .initialMarking(m => { for (const [p, n] of tokens) m.tokens(p, n); })
      .property(property)
      .environmentMode(ignore())
      .timeout(timeoutMs)
      .verify();
  }

  function unknownReason(result: { verdict: { type: string; reason?: string }; report: string }): string {
    expect(result.verdict.type, `expected unknown\n${result.report}`).toBe('unknown');
    return (result.verdict as { reason: string }).reason;
  }

  /** The V5 reply: a banner, `unsat`, the benign model error, a two-state proof. */
  const V5_BODY = `cat > /dev/null
echo 'WARNING: solver configured with a non-default strategy'
echo 'unsat'
echo '(error "model is not available")'
echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
`;

  it('V5 via PATH: a warning line before the verdict must not lose it', async () => {
    // LIBPETRI_Z3 unset, the stub's directory first on PATH: the default resolution.
    const script = stub('path', VERSION_OK, V5_BODY);
    delete process.env[Z3_ENV];
    process.env['PATH'] = `${join(root, 'path')}:${savedPath ?? ''}`;
    expect(resolveZ3().program).toBe(script);
    const result = await verify(chainNet(), placeBound(p1, 0));
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed, `the decoded chain replays\n${result.report}`).toBe(true);
    expect(result.report, 'the report names the probed solver version').toContain('  Solver: z3 4.16.0');
    restore('PATH', savedPath);
  });

  it('C4: a genuine no-chain replay is the one downgrade', async () => {
    stub('c4', VERSION_OK, `cat > /dev/null
echo 'unsat'
echo '(proof (asserted (Reachable 1 1 0)))'
`);
    const result = await verify(frozenNet(), unreachable(new Set([p1])), 5_000, [[p0, 1], [blocker, 1]]);
    expect(unknownReason(result)).toBe(
      'counterexample replay found no firing chain to the violation under the abstract semantics, so VIOLATED is withheld',
    );
    expect(result.counterexampleConfirmed).toBe(false);
  });

  it('V6: an (error …) on stderr must never leave a proven standing', async () => {
    stub('v6-stderr', VERSION_OK, `script=$(cat)
case "$script" in
  *"set-logic HORN"*)
    echo 'sat'
    echo '(error "proof is not available")'
    echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
    ;;
  *)
    echo '(error "line 4: unknown constant Reachable")' >&2
    echo 'unsat'
    echo 'unsat'
    echo 'unsat'
    ;;
esac
`);
    const result = await verify(chainNet(), placeBound(p1, 1));
    const reason = unknownReason(result);
    expect(reason.startsWith('certificate check could not run:')).toBe(true);
    expect(reason).toContain('stderr');
    expect(reason.endsWith('PROVEN is withheld without an independently validated certificate')).toBe(true);
    expect(result.report).toContain('  Certificate check: FAILED');
  });

  it('V6: a non-zero exit with truncated answers does not certify', async () => {
    stub('v6-exit', VERSION_OK, `script=$(cat)
case "$script" in
  *"set-logic HORN"*)
    echo 'sat'
    echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
    ;;
  *)
    echo 'unsat'
    exit 1
    ;;
esac
`);
    const result = await verify(chainNet(), placeBound(p1, 1));
    expect(result.verdict.type, result.report).toBe('unknown');
  });

  it('V5: an error reply without a verdict is unknown, not a rejection', async () => {
    stub('no-verdict', VERSION_OK, `cat > /dev/null
echo '(error "line 1: invalid command")'
`);
    expect(unknownReason(await verify(chainNet(), placeBound(p1, 1)))).toBe('Z3 error: (error "line 1: invalid command")');
  });

  it('VER-013 AC4: the timeout line is the backstop, not a verdict', async () => {
    stub('timeout', VERSION_OK, "cat > /dev/null\necho 'timeout'\n");
    const result = await verify(chainNet(), placeBound(p1, 1));
    expect(unknownReason(result)).toBe('z3 hard timeout after 6s');
    expect(result.report).toContain('  Status: UNKNOWN (z3 hard timeout after 6s)');
  });

  it('VER-013 AC4: a solver ignoring both timeouts is killed', async () => {
    stub('wedged', VERSION_OK, 'exec sleep 30\n');
    const result = await verify(chainNet(), placeBound(p1, 1), 200);
    expect(unknownReason(result)).toBe('z3 did not exit within 2200 ms and was killed');
  }, 20_000);

  it('VER-013 AC5: a reply larger than a pipe buffer is drained', async () => {
    stub('banner', VERSION_OK, `cat > /dev/null
yes 'WARNING: a very long banner line' | head -c 2000000
yes 'WARNING: a very long banner line' | head -c 2000000 >&2
echo
echo 'unsat'
echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
`);
    const result = await verify(chainNet(), placeBound(p1, 0));
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
  });

  it('VER-013 AC3: a solver below the version floor is refused', async () => {
    stub('too-old', 'Z3 version 4.7.1 - 64 bit', V5_BODY);
    const result = await verify(chainNet(), placeBound(p1, 0));
    expect(unknownReason(result)).toBe('z3 4.7.1 is older than the minimum 4.8.0');
    expect(result.report).toContain('  Solver: z3 unavailable (z3 4.7.1 is older than the minimum 4.8.0)');
  });

  it('VER-013 AC3: a probe that reports no version is refused', async () => {
    stub('no-version', 'not a solver', V5_BODY);
    expect(unknownReason(await verify(chainNet(), placeBound(p1, 0)))).toBe('z3 --version did not report a version: not a solver');
  });

  it('VER-013 AC2: a missing executable names the command and the env var', async () => {
    process.env[Z3_ENV] = '/nonexistent/libpetri-z3';
    const result = await verify(chainNet(), placeBound(p1, 0));
    expect(unknownReason(result)).toBe('z3 binary not found: /nonexistent/libpetri-z3; install z3 >= 4.8.0 or set LIBPETRI_Z3');
    expect(result.report).toContain('  Solver: z3 unavailable (z3 binary not found:');
    expect(() => z3SolverAt('/nonexistent/libpetri-z3')).toThrow(/z3 binary not found/);
  });

  it('VER-013: LIBPETRI_SMT_DUMP records every script and reply', async () => {
    const dump = join(root, 'dump');
    stub('dump-src', VERSION_OK, V5_BODY);
    process.env[DUMP_ENV] = dump;
    const result = await verify(chainNet(), placeBound(p1, 0));
    delete process.env[DUMP_ENV];
    expect(result.verdict.type, result.report).toBe('violated');
    const names = readdirSync(dump).sort();
    expect(names, 'one script and one reply').toHaveLength(2);
    expect(names[0]!.endsWith('-horn.out') && names[1]!.endsWith('-horn.smt2')).toBe(true);
    const script = readFileSync(join(dump, names[1]!), 'utf8');
    expect(script).toContain('(set-logic HORN)');
    expect(script.endsWith('(get-model)')).toBe(true);
    expect(readFileSync(join(dump, names[0]!), 'utf8')).toContain('\nunsat\n');
  });
});
