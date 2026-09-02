/**
 * @module z3-process
 *
 * The z3 process transport (VER-013).
 *
 * Every SMT query is one `z3` process: the SMT-LIB2 script goes to its stdin in a
 * single write, stdin is closed so the solver sees end-of-file, and both output
 * streams are collected while a wall-clock watchdog waits. The child is killed on
 * every exit path, so a wedged solver can never outlive the query that started it,
 * and no solver state survives between queries, so concurrent verifiers in one
 * process are independent. The solve runs in another process, so the event loop
 * stays free while it works.
 *
 * The executable is `z3` on `PATH` unless {@link Z3_ENV} names another one. It is
 * probed once per verification with `--version` and refused below
 * {@link MIN_Z3_VERSION}; a missing or too-old binary surfaces as an `unknown`
 * verdict whose reason names the command and the environment variable, never as a
 * rejection out of `verify()`. Setting {@link DUMP_ENV} to a directory writes every
 * script and reply there (`NNN-<phase>.smt2`, `.out`, and `.err` when stderr is not
 * empty), which is how a solver reply is reproduced outside the pipeline.
 *
 * Timeouts are per invocation: `-t:<ms>` asks z3 to answer `unknown` after the soft
 * budget, `-T:<s>` (the budget plus {@link GRACE_MS}, rounded up) makes z3 print
 * `timeout` and exit on its own, and the watchdog at the budget plus twice the grace
 * kills whatever ignored both. The Java, TypeScript and Rust transports pass
 * byte-identical argument lists and classify replies identically.
 */
import { spawn, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, statSync, writeFileSync } from 'node:fs';
import * as path from 'node:path';
import { errorLine, timeoutLine } from './smt-text.js';

/** Environment variable naming the z3 executable (default: `z3` on `PATH`). */
export const Z3_ENV = 'LIBPETRI_Z3';
/** Environment variable naming a directory that receives every script and reply. */
export const DUMP_ENV = 'LIBPETRI_SMT_DUMP';
/** Slack between the soft budget and the hard backstops, in milliseconds. */
export const GRACE_MS = 1_000;
/** How long the `--version` probe may take before it counts as unavailable. */
const VERSION_PROBE_MS = 5_000;

/** A z3 release version, ordered numerically. */
export interface Z3Version {
  readonly major: number;
  readonly minor: number;
  readonly patch: number;
}

/**
 * Oldest z3 the transport accepts: `-t`/`-T`, Spacer as `fp.engine`, and the
 * `(get-model)` / `(get-proof)` printers the decoders read are stable from here.
 */
export const MIN_Z3_VERSION: Z3Version = { major: 4, minor: 8, patch: 0 };

/** Parses the version out of a `z3 --version` reply (`Z3 version 4.16.0 - 64 bit`). */
export function parseZ3Version(text: string): Z3Version | null {
  const m = /Z3 version (\d+)\.(\d+)(?:\.(\d+))?/.exec(text);
  if (m == null) return null;
  return { major: Number(m[1]), minor: Number(m[2]), patch: m[3] == null ? 0 : Number(m[3]) };
}

export function formatZ3Version(v: Z3Version): string {
  return `${v.major}.${v.minor}.${v.patch}`;
}

export function compareZ3Version(a: Z3Version, b: Z3Version): number {
  return a.major - b.major || a.minor - b.minor || a.patch - b.patch;
}

/** A resolved z3 executable: where it is and which version answered the probe. */
export interface Z3Solver {
  /** The executable as resolved (a path, or a bare name on `PATH`). */
  readonly program: string;
  /** The version the probe reported. */
  readonly version: Z3Version;
  /** Where scripts and replies are written, or `null` for no dump. */
  readonly dumpDir: string | null;
}

/** No usable z3 resolved; the message is the `unknown` reason the verifier reports. */
export class Z3Unavailable extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'Z3Unavailable';
  }
}

/** The process could not be started; the message is the `unknown` reason. */
export class Z3ProcessError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'Z3ProcessError';
  }
}

/** How a z3 process ended. */
export type Z3Exit =
  | { readonly kind: 'exited'; readonly code: number | null }
  | { readonly kind: 'killed' };

/** The raw reply of one z3 run. */
export interface Z3Reply {
  readonly stdout: string;
  readonly stderr: string;
  readonly exit: Z3Exit;
}

/** True when the process exited with status 0. */
export function replySucceeded(reply: Z3Reply): boolean {
  return reply.exit.kind === 'exited' && reply.exit.code === 0;
}

/** The standard argument list: `-smt2 -in -t:<ms> -T:<s>`. */
export function argsFor(timeoutMs: number): string[] {
  return ['-smt2', '-in', `-t:${timeoutMs}`, `-T:${hardTimeoutSecs(timeoutMs)}`];
}

/** The `-T:` backstop in whole seconds: the soft budget plus the grace, rounded up. */
export function hardTimeoutSecs(timeoutMs: number): number {
  return Math.max(1, Math.ceil((timeoutMs + GRACE_MS) / 1000));
}

/** When the watchdog kills the process: the soft budget plus twice the grace. */
export function watchdogMs(timeoutMs: number): number {
  return timeoutMs + 2 * GRACE_MS;
}

/** The soft budget in milliseconds: at least one, so `-t:0` never means "forever". */
export function timeoutBudget(timeoutMs: number): number {
  return Math.max(1, Math.floor(Number.isFinite(timeoutMs) ? timeoutMs : 1));
}

/**
 * Why a reply carries no `(check-sat)` answer, in the order the transport contract
 * fixes: the `-T` backstop, the watchdog, an `(error …)` on either stream, anything
 * on stderr, and finally the unexpected stdout itself.
 */
export function failureReason(reply: Z3Reply, timeoutMs: number): string {
  if (timeoutLine(reply.stdout)) {
    return `z3 hard timeout after ${hardTimeoutSecs(timeoutMs)}s`;
  }
  if (reply.exit.kind === 'killed') {
    return `z3 did not exit within ${watchdogMs(timeoutMs)} ms and was killed`;
  }
  const err = errorLine(reply.stdout) ?? errorLine(reply.stderr);
  if (err != null) return `Z3 error: ${err}`;
  const stderr = reply.stderr.trim();
  if (stderr !== '') return `Z3 error: ${stderr}`;
  return `Unexpected Z3 output: ${reply.stdout.trim()}`;
}

/**
 * Where `program` resolves to: the path itself when it names a file, else the first
 * executable of that name on `PATH` (`.exe` tried on Windows); `null` when nothing
 * resolves.
 */
export function locateZ3(program: string, env: NodeJS.ProcessEnv = process.env): string | null {
  const isFile = (p: string): boolean => {
    try {
      return existsSync(p) && statSync(p).isFile();
    } catch {
      return false;
    }
  };
  if (program.includes('/') || program.includes(path.sep) || path.isAbsolute(program)) {
    return isFile(program) ? program : null;
  }
  const searchPath = env['PATH'] ?? '';
  const windows = process.platform === 'win32';
  for (const dir of searchPath.split(path.delimiter)) {
    if (dir === '') continue;
    const candidate = path.join(dir, program);
    if (isFile(candidate)) return candidate;
    if (windows && isFile(candidate + '.exe')) return candidate + '.exe';
  }
  return null;
}

/** Resolves a specific executable (tests point this at a stub). No dump directory. */
export function z3SolverAt(program: string, env: NodeJS.ProcessEnv = process.env): Z3Solver {
  const located = locateZ3(program, env);
  if (located == null) {
    throw new Z3Unavailable(
      `z3 binary not found: ${program}; install z3 >= ${formatZ3Version(MIN_Z3_VERSION)} or set ${Z3_ENV}`,
    );
  }
  const probe = spawnSync(located, ['--version'], {
    encoding: 'utf8',
    timeout: VERSION_PROBE_MS,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (probe.error != null) {
    if ((probe.error as NodeJS.ErrnoException).code === 'ETIMEDOUT') {
      throw new Z3Unavailable(`${program} --version did not answer within ${VERSION_PROBE_MS} ms`);
    }
    throw new Z3Unavailable(`failed to spawn ${program}: ${probe.error.message}`);
  }
  const version = parseZ3Version(probe.stdout ?? '');
  if (version == null) {
    const line = `${probe.stdout ?? ''}\n${probe.stderr ?? ''}`
      .split('\n')
      .map((l) => l.trim())
      .find((l) => l !== '') ?? '';
    throw new Z3Unavailable(`z3 --version did not report a version: ${line}`);
  }
  if (compareZ3Version(version, MIN_Z3_VERSION) < 0) {
    throw new Z3Unavailable(
      `z3 ${formatZ3Version(version)} is older than the minimum ${formatZ3Version(MIN_Z3_VERSION)}`,
    );
  }
  return { program: located, version, dumpDir: null };
}

/**
 * Resolves the executable named by {@link Z3_ENV}, or `z3` on `PATH`, probes its
 * version, and reads {@link DUMP_ENV}. Throws {@link Z3Unavailable}.
 */
export function resolveZ3(env: NodeJS.ProcessEnv = process.env): Z3Solver {
  const configured = env[Z3_ENV];
  const program = configured == null || configured.trim() === '' ? 'z3' : configured;
  const dump = env[DUMP_ENV];
  const solver = z3SolverAt(program, env);
  return { ...solver, dumpDir: dump == null || dump.trim() === '' ? null : dump };
}

/**
 * True if a usable `z3` executable resolves: `LIBPETRI_Z3` if set, else `z3` on
 * `PATH`, at or above {@link MIN_Z3_VERSION}. Without one every SMT path returns
 * `unknown`; the test suites use this to skip loudly rather than fail.
 */
export function z3Available(env: NodeJS.ProcessEnv = process.env): boolean {
  try {
    resolveZ3(env);
    return true;
  } catch {
    return false;
  }
}

/** Process-wide counter for dump file names (not solver state). */
let dumpCounter = 0;

function dumpSlot(solver: Z3Solver, phase: string, script: string): string | null {
  if (solver.dumpDir == null) return null;
  dumpCounter += 1;
  try {
    mkdirSync(solver.dumpDir, { recursive: true });
    const base = path.join(solver.dumpDir, `${String(dumpCounter).padStart(3, '0')}-${phase}`);
    writeFileSync(`${base}.smt2`, script);
    return base;
  } catch {
    return null;
  }
}

function dumpWrite(file: string, text: string): void {
  try {
    writeFileSync(file, text);
  } catch {
    // Dump failures are ignored: the dump is a diagnostic, never the pipeline.
  }
}

/**
 * Runs one script through one z3 process and resolves with the raw reply. `phase`
 * names the dump files; `extraArgs` follow the standard argument list. The only
 * rejection is a failed spawn: a solver that printed nothing, errored, timed out or
 * was killed still comes back as a reply for the caller to classify
 * ({@link failureReason}).
 */
export function runZ3Text(
  solver: Z3Solver,
  script: string,
  phase: string,
  timeoutMs: number,
  extraArgs: readonly string[] = [],
): Promise<Z3Reply> {
  const budget = timeoutBudget(timeoutMs);
  const base = dumpSlot(solver, phase, script);
  return new Promise<Z3Reply>((resolve, reject) => {
    const child = spawn(solver.program, [...argsFor(budget), ...extraArgs], {
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    const out: Buffer[] = [];
    const err: Buffer[] = [];
    let killed = false;
    let settled = false;
    child.stdout!.on('data', (chunk: Buffer) => out.push(chunk));
    child.stderr!.on('data', (chunk: Buffer) => err.push(chunk));
    // A solver that exited early (parse error, `-T` expiry) closes the pipe under
    // us; that is not a failure of the transport, the reply says what happened.
    child.stdin!.on('error', () => {});
    const watchdog = setTimeout(() => {
      killed = true;
      child.kill('SIGKILL');
    }, watchdogMs(budget));
    child.on('error', (e) => {
      if (settled) return;
      settled = true;
      clearTimeout(watchdog);
      reject(new Z3ProcessError(`failed to spawn ${solver.program}: ${e.message}`));
    });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      clearTimeout(watchdog);
      const reply: Z3Reply = {
        stdout: Buffer.concat(out).toString('utf8'),
        stderr: Buffer.concat(err).toString('utf8'),
        exit: killed ? { kind: 'killed' } : { kind: 'exited', code },
      };
      if (base != null) {
        dumpWrite(`${base}.out`, reply.stdout);
        if (reply.stderr.trim() !== '') dumpWrite(`${base}.err`, reply.stderr);
      }
      resolve(reply);
    });
    // The whole script in one write, then EOF.
    child.stdin!.end(script);
  });
}
