/**
 * @module certificate-checker
 *
 * Independent certificate check for IC3/PDR proofs.
 *
 * When Z3 Spacer answers `sat` on the CHC encoding ({@link module:smt-encoder}), the
 * model it prints interprets `Reachable` as an inductive invariant, the proof
 * certificate. This module re-verifies that certificate with plain (non-HORN) SMT
 * queries in a SECOND z3 run, so a `proven` verdict no longer rests on the empirical
 * HORN sat ⇒ proven mapping alone, nor on the correctness of the P-invariant
 * strengthening: the three verification conditions below are discharged against the
 * UNSTRENGTHENED step relation ({@link encodeStepRelationSmt2}).
 *
 * The candidate invariant is `R' := R ∧ Inv`, where `R` is the pasted `Reachable`
 * interpretation and `Inv` the validated P-invariant equalities the CHC encoding
 * strengthened its rule bodies with: a Spacer model is only guaranteed inductive
 * *relative to* that strengthening, so the conjuncts ride along in the candidate, but
 * the RELATION stays unstrengthened, which means VC1/VC2 re-prove each conjunct's
 * initiation and inductiveness from scratch. A wrong P-invariant cannot weaken this
 * check: it fails init or consecution instead.
 *
 * 1. **VC1 (init)**: `¬R'(M₀)` is UNSAT.
 * 2. **VC2 (consecution)**: `M ≥ 0 ∧ R'(M) ∧ T(M,M') ∧ ¬R'(M')` is UNSAT.
 * 3. **VC3 (safety)**: `M ≥ 0 ∧ R'(M) ∧ Bad(M)` is UNSAT.
 *
 * The `M ≥ 0` conjunct is the state domain: markings are token counts, so the VCs
 * range over ℕ^P; without it a certificate inductive over ℕ^P is refuted by a negative
 * predecessor in ℤ^P.
 *
 * The certificate is the `(define-fun …)` block of the `(get-model)` reply, pasted
 * verbatim: auxiliary definitions stay alongside `Reachable`, so every name resolves
 * in the fresh script. The three VCs run under `(push)`/`(pop)` in ONE script; the
 * emitted text is byte-identical to the Rust reference (`certificate_check.rs`) and
 * the Java port.
 *
 * Outcomes are split the way the caller must treat them: `failed` names the first VC
 * that was not UNSAT (with the solver status and, for SAT, a witness marking),
 * `unavailable` means the check could not run at all (missing or malformed
 * certificate, solver spawn failure, errored assert). Both withhold PROVEN; neither
 * throws.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { Place } from '../../core/place.js';
import {
  conjoin, encodePropertyViolation, encodeStepRelationSmt2, invariantConditions, resolveEnvInjection,
} from './smt-encoder.js';
import { errorLine, sexprEnd, timeoutLine } from './smt-text.js';
import {
  hardTimeoutSecs, replySucceeded, runZ3Text, timeoutBudget, watchdogMs, type Z3Solver,
} from './z3-process.js';

/** Label of a validity condition, as it appears in the downgrade reason. */
export type CertificateVc = 'initiation (VC1)' | 'consecution (VC2)' | 'safety (VC3)';

const VC_LABELS: readonly CertificateVc[] = ['initiation (VC1)', 'consecution (VC2)', 'safety (VC3)'];

/**
 * Outcome of the certificate check.
 *
 * `passed` — all three validity conditions are UNSAT; the proven verdict is certified
 * independently of the Fixedpoint engine.
 * `failed` — a validity condition was not UNSAT; `detail` carries the solver status
 * and, when the solver produced a model, a witness marking.
 * `unavailable` — the check could not run (missing/malformed certificate, solver
 * failure), so no VC is implicated.
 *
 * The caller must withhold PROVEN on `failed` and `unavailable` alike.
 */
export type CertificateCheckOutcome =
  | { readonly type: 'passed'; readonly invariant: string }
  | {
      readonly type: 'failed';
      readonly vc: CertificateVc;
      readonly detail: string;
      readonly invariant: string;
    }
  | { readonly type: 'unavailable'; readonly reason: string; readonly invariant: string | null };

/**
 * Re-verifies an extracted proof certificate against the unstrengthened step relation.
 *
 * @param certificate the `(define-fun …)` block extracted verbatim from the Spacer
 *   model (`null` when the solver printed none)
 * @param flatNet the flat net the CHC query was encoded from
 * @param initialMarking the verified initial marking (VC1)
 * @param property the verified property (VC3)
 * @param invariants the exactly-validated P-invariants the CHC bodies were
 *   strengthened with; conjoined into the CANDIDATE certificate and re-proven by the
 *   three VCs (never conjoined into the step relation)
 * @param sinkPlaces declared sink places (deadlock-freedom VC3)
 * @param solver the resolved z3 executable
 * @param timeoutMs per-invocation solver budget in milliseconds
 */
export async function checkCertificate(
  certificate: string | null,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>>,
  solver: Z3Solver,
  timeoutMs: number,
): Promise<CertificateCheckOutcome> {
  if (certificate == null) {
    return {
      type: 'unavailable',
      reason: 'no inductive invariant (define-fun block) could be extracted from the z3 model',
      invariant: null,
    };
  }
  const shape = shapeFailure(flatNet, invariants);
  if (shape != null) return { type: 'unavailable', reason: shape, invariant: certificate };
  if (!certificate.includes('(define-fun Reachable ') && !certificate.includes('(define-fun |Reachable| ')) {
    return { type: 'unavailable', reason: 'certificate does not define Reachable', invariant: certificate };
  }

  const vcs = buildVerificationConditions(certificate, flatNet, initialMarking, property, sinkPlaces, invariants);
  let results: string[];
  try {
    results = await runVcScript(script(vcs), timeoutMs, solver);
  } catch (e: any) {
    return { type: 'unavailable', reason: String(e?.message ?? e), invariant: certificate };
  }
  for (let i = 0; i < results.length; i++) {
    if (results[i] !== 'unsat') {
      const detail = await detailFor(vcs, i, results[i]!, flatNet, timeoutMs, solver);
      return { type: 'failed', vc: VC_LABELS[i]!, detail, invariant: certificate };
    }
  }
  return { type: 'passed', invariant: certificate };
}

/**
 * The certificate-check script for the given inputs, exactly as
 * {@link checkCertificate} would send it (VER-013 script parity): what the
 * cross-language golden tests diff.
 */
export function vcScript(
  certificate: string,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  invariants: readonly PInvariant[],
): string {
  return script(buildVerificationConditions(certificate, flatNet, initialMarking, property, sinkPlaces, invariants));
}

/** Why the net and invariants cannot be indexed safely, or `null`. */
function shapeFailure(flatNet: FlatNet, invariants: readonly PInvariant[]): string | null {
  const P = flatNet.places.length;
  for (const inv of invariants) {
    if (inv.weights.length !== P) {
      return `P-invariant has ${inv.weights.length} weights for a ${P}-place net`;
    }
    for (const pid of inv.support) {
      if (pid >= P || pid < 0) return `P-invariant support names place index ${pid} in a ${P}-place net`;
    }
  }
  return null;
}

/** A VC run that could not be trusted; the message is the reason. */
class VcFailure extends Error {}

/**
 * Runs one plain-SMT script and returns the three positional `(check-sat)` answers.
 * Both output channels are inspected: an `(error …)` on EITHER stream means an assert
 * was dropped, which would silently make a VC vacuous; a `timeout` line, a watchdog
 * kill and a non-success exit mean the run did not complete. Only a clean
 * three-answer stdout counts.
 */
async function runVcScript(text: string, timeoutMs: number, solver: Z3Solver): Promise<string[]> {
  const reply = await runZ3Text(solver, text, 'certificate', timeoutMs, []);
  const budget = timeoutBudget(timeoutMs);
  const err = errorLine(reply.stderr);
  if (err != null) throw new VcFailure(`z3 reported an error on stderr: ${err}`);
  if (timeoutLine(reply.stdout)) {
    throw new VcFailure(`z3 hard timeout after ${hardTimeoutSecs(budget)}s while checking the certificate`);
  }
  if (reply.exit.kind === 'killed') {
    throw new VcFailure(`z3 did not exit within ${watchdogMs(budget)} ms while checking the certificate and was killed`);
  }
  const results = parseVcResults(reply.stdout);
  if (!replySucceeded(reply)) {
    const status = reply.exit.kind === 'exited' ? `exit status: ${reply.exit.code}` : 'the watchdog kill';
    throw new VcFailure(`z3 exited with ${status} after answering [${results.join(', ')}]`);
  }
  return results;
}

/**
 * Parses the three positional `(check-sat)` answers. Any `(error …)` line fails the
 * check outright (an errored assert silently vanishes from the query, which could
 * leave a VC vacuous); a `timeout` line is z3's `-T` backstop, not a fourth answer.
 */
export function parseVcResults(stdout: string): string[] {
  const err = errorLine(stdout);
  if (err != null) throw new VcFailure(`z3 error while checking the certificate: ${err}`);
  if (timeoutLine(stdout)) throw new VcFailure('z3 hard timeout while checking the certificate');
  const results = stdout
    .split('\n')
    .map((l) => l.trim())
    .filter((l) => l === 'sat' || l === 'unsat' || l === 'unknown');
  if (results.length !== 3) {
    throw new VcFailure(`expected 3 VC answers from z3, got ${results.length}: [${results.join(', ')}]`);
  }
  return results;
}

/** The assembled VC script, kept in parts so one VC can be re-run alone. */
interface VerificationConditions {
  readonly prelude: readonly string[];
  /** The asserts of each VC, in `VC_LABELS` order. */
  readonly asserts: readonly (readonly string[])[];
}

function buildVerificationConditions(
  certificate: string,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  invariants: readonly PInvariant[],
): VerificationConditions {
  const P = flatNet.places.length;
  const mVars: string[] = [];
  const mpVars: string[] = [];
  for (let i = 0; i < P; i++) {
    mVars.push(`m${i}`);
    mpVars.push(`m${i}p`);
  }

  const prelude: string[] = [
    '; IC3/PDR certificate check (plain SMT-LIB2, not HORN):',
    '; each VC below must be unsat for the certificate to stand.',
    certificate,
    '',
  ];
  for (const v of mVars) prelude.push(`(declare-const ${v} Int)`);
  for (const v of mpVars) prelude.push(`(declare-const ${v} Int)`);

  // VC1 (init): the initial marking satisfies the candidate invariant.
  const m0: string[] = [];
  for (let i = 0; i < P; i++) m0.push(String(initialMarking.tokens(flatNet.places[i]!)));
  const vc1 = [`(assert (not ${candidate(m0, invariants)}))`];

  // The system lives in N^P, not Z^P.
  const nonNegative = mVars.map((v) => `(assert (>= ${v} 0))`);

  // VC2 (consecution): closed under the unstrengthened step relation.
  const step = encodeStepRelationSmt2(flatNet);
  const vc2 = [
    ...nonNegative,
    `(assert ${candidate(mVars, invariants)})`,
    `(assert ${step})`,
    `(assert (not ${candidate(mpVars, invariants)}))`,
  ];

  // VC3 (safety): excludes every property-violating state, exactly the violation
  // the CHC error rule encodes.
  const bad = encodePropertyViolation(flatNet, property, mVars, sinkPlaces, resolveEnvInjection(flatNet));
  const vc3 = [...nonNegative, `(assert ${candidate(mVars, invariants)})`, `(assert ${bad})`];

  return { prelude, asserts: [vc1, vc2, vc3] };
}

/** The full script: the prelude, then the three VCs under push/pop. */
function script(vcs: VerificationConditions): string {
  const lines = [...vcs.prelude];
  for (let i = 0; i < vcs.asserts.length; i++) {
    lines.push('');
    lines.push(`; VC${i + 1} ${VC_LABELS[i]}`);
    lines.push('(push)');
    lines.push(...vcs.asserts[i]!);
    lines.push('(check-sat)');
    lines.push('(pop)');
  }
  return lines.join('\n');
}

/**
 * Describes VC `i`'s non-`unsat` answer for the downgrade reason, by re-running that
 * VC alone with model/reason extraction enabled. Best effort: without it the answer is
 * still named.
 */
async function detailFor(
  vcs: VerificationConditions,
  i: number,
  answer: string,
  flatNet: FlatNet,
  timeoutMs: number,
  solver: Z3Solver,
): Promise<string> {
  const lines = ['(set-option :produce-models true)', ...vcs.prelude, ...vcs.asserts[i]!, '(check-sat)'];
  lines.push(answer === 'sat' ? '(get-model)' : '(get-info :reason-unknown)');
  let reply = '';
  try {
    reply = (await runZ3Text(solver, lines.join('\n'), 'certificate-detail', timeoutMs, [])).stdout;
  } catch {
    reply = '';
  }
  if (answer === 'sat') {
    const w = witness(reply, flatNet);
    return w == null ? 'solver returned SATISFIABLE' : `solver returned SATISFIABLE (witness: ${w})`;
  }
  const r = reasonUnknown(reply);
  return r == null ? 'solver returned UNKNOWN' : `solver returned UNKNOWN (${r})`;
}

/**
 * Reads the current-marking assignment out of a `(get-model)` reply as `p0=2, p1=1`
 * (place names, index order); `null` when no `m_i` was defined.
 */
export function witness(model: string, flatNet: FlatNet): string | null {
  const parts: string[] = [];
  for (let i = 0; i < flatNet.places.length; i++) {
    const needle = `(define-fun m${i} () Int`;
    const at = model.indexOf(needle);
    if (at < 0) continue;
    const rest = model.slice(at + needle.length).trimStart();
    let value: string;
    if (rest.startsWith('(')) {
      const end = sexprEnd(rest, 0);
      if (end < 0) continue;
      // A negative literal prints as `(- 1)`; flatten it back to `-1`.
      value = rest.slice(1, end - 1).trim().split(/\s+/).join('');
    } else {
      let end = 0;
      while (end < rest.length && !/\s/.test(rest[end]!) && rest[end] !== ')') end++;
      if (end === 0) continue;
      value = rest.slice(0, end);
    }
    parts.push(`${flatNet.places[i]!.name}=${value}`);
  }
  return parts.length === 0 ? null : parts.join(', ');
}

/** Reads z3's `(get-info :reason-unknown)` reply, e.g. `timeout`. */
export function reasonUnknown(reply: string): string | null {
  const at = reply.indexOf(':reason-unknown');
  if (at < 0) return null;
  const rest = reply.slice(at + ':reason-unknown'.length).trimStart();
  const end = rest.indexOf(')');
  if (end < 0) return null;
  let reason = rest.slice(0, end).trim();
  if (reason.startsWith('"') && reason.endsWith('"') && reason.length >= 2) reason = reason.slice(1, -1);
  reason = reason.trim();
  return reason === '' ? null : reason;
}

/**
 * The candidate invariant applied to a variable (or literal) vector:
 * `R'(vars) = (Reachable vars) ∧ Inv(vars)`.
 */
function candidate(names: readonly string[], invariants: readonly PInvariant[]): string {
  return conjoin([`(Reachable ${names.join(' ')})`, ...invariantConditions(invariants, names)]);
}
