import type { PetriNet } from '../core/petri-net.js';
import type { EnvironmentPlace, Place } from '../core/place.js';
import { MarkingState, MarkingStateBuilder } from './marking-state.js';
import type { SmtProperty } from './smt-property.js';
import { deadlockFree, propertyDescription } from './smt-property.js';
import type { SmtVerificationResult, SmtStatistics, Verdict } from './smt-verification-result.js';
import type { PInvariant } from './invariant/p-invariant.js';
import type { FlatNet } from './encoding/flat-net.js';
import { flatten } from './encoding/net-flattener.js';
import { type EnvironmentAnalysisMode, alwaysAvailable } from './analysis/environment-analysis-mode.js';
import { IncidenceMatrix } from './encoding/incidence-matrix.js';
import { computePInvariants, computePSemiflows, isCoveredByInvariants, validateInvariantsExact } from './invariant/p-invariant-computer.js';
import { structuralCheck } from './invariant/structural-check.js';
import { createSpacerRunner } from './z3/spacer-runner.js';
import { checkCertificate } from './z3/certificate-checker.js';
import { encode } from './z3/smt-encoder.js';
import { buildColouredPlan, encodeColoured, type ColouredPlan } from './z3/name-coloured-encoder.js';
import { verifyViaNameScg } from './nu-scg-verifier.js';
import type { FragmentMode } from './analysis/name-fragment.js';
import type { PrioritySemantics } from './analysis/priority-semantics.js';
import { decode, describeDecodeFailure } from './z3/counterexample-decoder.js';
import {
  replayCounterexample, vectorize, toMarkingState, stepName, type ReplayOutcome,
} from './z3/abstract-replayer.js';
import { requireOutputProducingActions } from '../core/internal/output-action-check.js';

/**
 * IC3/PDR-based safety verifier for Petri nets using Z3's Spacer engine.
 *
 * Proves safety properties (especially deadlock-freedom) without
 * enumerating all reachable states. IC3 constructs inductive invariants
 * incrementally, which works well for bounded nets.
 *
 * Key design decisions:
 * - Operates on the marking projection (integer vectors) — no timing
 * - An untimed deadlock-freedom proof is stronger than needed
 *   (timing can only restrict behavior)
 * - Input specifications are purely structural (IO-006) — there is no per-arc
 *   predicate for the encoder to be blind to
 * - If a counterexample is found, it may be spurious in timed semantics —
 *   the report notes this
 *
 * Verification Pipeline:
 * 1. Flatten — expand XOR, index places, build pre/post vectors
 * 2. Structural pre-check — siphon/trap analysis (may prove early)
 * 3. P-invariants — compute conservation laws for strengthening
 * 4. SMT encode + query — IC3/PDR via Z3 Spacer
 * 5. Decode result — proof or counterexample trace
 */
export class SmtVerifier {
  private _initialMarking: MarkingState = MarkingState.empty();
  private _property: SmtProperty = deadlockFree();
  private readonly _environmentPlaces = new Set<EnvironmentPlace<any>>();
  private readonly _sinkPlaces = new Set<Place<any>>();
  private readonly _budgetPlaces = new Set<string>();
  private _environmentMode: EnvironmentAnalysisMode = alwaysAvailable();
  private _timeoutMs: number = 60_000;
  private _certificateCheck: boolean = true;
  private _counterexampleReplay: boolean = true;
  private _nuMaxClasses: number = 100_000;
  private _fragmentMode: FragmentMode = 'base';
  private readonly _carrierPlaces = new Set<string>();
  private _prioritySemantics: PrioritySemantics = 'none';

  private constructor(private readonly net: PetriNet) {}

  static forNet(net: PetriNet): SmtVerifier {
    return new SmtVerifier(net);
  }

  initialMarking(marking: MarkingState): this;
  initialMarking(configurator: (builder: MarkingStateBuilder) => void): this;
  initialMarking(arg: MarkingState | ((builder: MarkingStateBuilder) => void)): this {
    if (arg instanceof MarkingState) {
      this._initialMarking = arg;
    } else {
      const builder = MarkingState.builder();
      arg(builder);
      this._initialMarking = builder.build();
    }
    return this;
  }

  property(property: SmtProperty): this {
    this._property = property;
    return this;
  }

  environmentPlaces(...places: EnvironmentPlace<any>[]): this {
    for (const p of places) this._environmentPlaces.add(p);
    return this;
  }

  environmentMode(mode: EnvironmentAnalysisMode): this {
    this._environmentMode = mode;
    return this;
  }

  /**
   * Declares expected sink (terminal) places for deadlock-freedom analysis.
   * Markings where any sink place has a token are not considered deadlocks.
   */
  sinkPlaces(...places: Place<any>[]): this {
    for (const p of places) this._sinkPlaces.add(p);
    return this;
  }

  /**
   * Declares ν-net budget places (NU-040): places whose token count bounds the
   * live correlation pool (they gate fresh-name minting). Declaring at least one
   * places the net in the decidable bounded fragment, so reachability-safety
   * properties over its ν-joins are verified (the matched transitions are
   * over-approximated). Without any budget place, a net that mints fresh names
   * is treated as unbounded and the verifier returns `unknown` (NU-050).
   */
  budgetPlaces(...places: Place<any>[]): this {
    for (const p of places) this._budgetPlaces.add(p.name);
    return this;
  }

  timeout(ms: number): this {
    this._timeoutMs = ms;
    return this;
  }

  /**
   * Enables/disables the independent IC3 certificate check (default: enabled).
   *
   * When a proven verdict comes from the IC3/Spacer path on the flat count
   * encoding, the synthesized inductive invariant is re-validated with a plain
   * solver against the UNSTRENGTHENED step relation — VC1 (init), VC2
   * (consecution), VC3 (safety) — so a Spacer or encoder defect cannot certify
   * a false PROVEN. A certificate that fails validation downgrades the verdict
   * to unknown. Structural proofs and the coloured ν-encoding are unaffected.
   */
  certificateCheck(enabled: boolean): this {
    this._certificateCheck = enabled;
    return this;
  }

  /**
   * Enables/disables abstract counterexample replay (default: enabled).
   *
   * When a violated verdict comes from the flat count encoding, the decoded
   * counterexample states (an order-free set — the derivation tree is walked
   * in traversal order, not firing order) are re-executed TS-side against the
   * abstract semantics the encoder emits (Lean's `fireA`, Basic.lean): a
   * bounded BFS chains the states from M₀ to a property-violating marking.
   *
   * - Chain found → the verdict stays violated with
   *   `counterexampleConfirmed: true` and the trace re-emitted in firing
   *   (replay) order.
   * - States decoded but unchainable → the counterexample is spurious or the
   *   decoder mis-read the derivation; the verdict DOWNGRADES to unknown.
   * - Nothing decoded → the verdict stays violated with
   *   `counterexampleConfirmed: false` and a report note (Spacer's SAT answer
   *   stands; there is simply nothing to replay).
   *
   * The coloured ν-encoding and Route B have their own state shapes and are
   * out of scope (replay is skipped, `counterexampleConfirmed: null`).
   */
  counterexampleReplay(enabled: boolean): this {
    this._counterexampleReplay = enabled;
    return this;
  }

  /**
   * Sets the class-count cap for the ν-aware state-class-graph analysis (NU-050,
   * Route B). When the symbolic name-aware graph would exceed this, the analysis
   * truncates and the verdict is `unknown` (the live correlation pool is not
   * structurally bounded). Default 100_000.
   */
  nuMaxClasses(max: number): this {
    this._nuMaxClasses = max;
    return this;
  }

  /**
   * Selects the ν-net coloured-place fragment for Route B (NU-051). `base`
   * (default) admits the shipped mint → matched-join fragment only; `extended`
   * additionally admits the opt-in coloured-consumer (drain/relay) role and the
   * declared {@link carrierPlaces}. When `extended` is requested but the net
   * falls outside the coloured-consumer fragment, Route B declines and a short
   * note is appended to the report before falling back to the sound
   * over-approximation.
   */
  fragmentMode(mode: FragmentMode): this {
    this._fragmentMode = mode;
    return this;
  }

  /**
   * Declares ν-net *carrier* places (NU-051, EXTENDED only): intermediate places
   * that carry a fresh name from the minting fork onward to a ν-join input. Under
   * {@link fragmentMode} `extended` they are unioned into the coloured set so the
   * existing mint co-mints one fresh name into all of them; under `base` they are
   * ignored. Accumulating. Throws if a declared place is not in the net — a
   * mistyped carrier name would let two fork branches mint independent names, so
   * the join never becomes name-enabled and the verifier would otherwise report a
   * confident false deadlock; it must surface, never silently proceed.
   */
  carrierPlaces(...places: Place<any>[]): this {
    for (const p of places) {
      if (![...this.net.places].some(np => np.name === p.name)) {
        throw new Error(`declared carrier place '${p.name}' not in the net`);
      }
      this._carrierPlaces.add(p.name);
    }
    return this;
  }

  /**
   * Selects how the Route-B name-aware analyzer treats transition priority
   * (NU-052). Defaults to `'none'` (the priority-blind over-approximation).
   * `'conflict'` models the executor's conflict-only priority resolution, so a
   * lower-priority transition pre-empted by a conflicting, no-later-ready,
   * strictly-higher-priority one is not explored — removing spurious
   * dead-letter-drain stalls the eager, priority-ordered executor never produces.
   */
  prioritySemantics(semantics: PrioritySemantics): this {
    this._prioritySemantics = semantics;
    return this;
  }

  /**
   * Runs the verification pipeline.
   *
   * @throws Error if the net violates CORE-043 — verification rejects the same nets execution rejects.
   */
  async verify(): Promise<SmtVerificationResult> {
    requireOutputProducingActions(this.net);
    const start = performance.now();
    const report: string[] = [];
    report.push('=== IC3/PDR SAFETY VERIFICATION ===\n');
    report.push(`Net: ${this.net.name}`);
    const propDesc = this._sinkPlaces.size === 0
      ? propertyDescription(this._property)
      : `${propertyDescription(this._property)} (sinks: ${[...this._sinkPlaces].map(p => p.name).join(', ')})`;
    report.push(`Property: ${propDesc}`);
    report.push(`Timeout: ${(this._timeoutMs / 1000).toFixed(0)}s\n`);

    // ν-net awareness (NU-040, NU-050). A transition with a match spec joins by
    // name equality; the untimed encoder over-approximates that (name equality
    // assumed satisfiable). Sound for reachability-safety bounds (proven holds —
    // the real net fires strictly fewer joins) but NOT for quiescence-based
    // properties, which name-blind firing distorts. `applyNuGuard` turns those
    // cases into unknown.
    const hasMatch = [...this.net.transitions].some(t => t.matchSpec !== null);
    const nuBounded = this._budgetPlaces.size > 0;

    // ν-net Route B (NU-050): the name-aware state-class-graph name-partition
    // quotient decides ν-join correlation EXACTLY — including name×time and
    // quiescence — without a budget. It "fills the gaps" the SMT / Route A path
    // cannot answer exactly: quiescence properties on a ν-net, and unbudgeted
    // reachability-safety. Budgeted, untimed reachability-safety in Route A's
    // fragment stays on Route A below (this trigger is false there). If the net is
    // outside the supported fragment, verifyViaNameScg returns null and we fall
    // through to the existing pipeline (which applies the sound unknown downgrade).
    if (hasMatch && (!isReachabilitySafety(this._property) || !nuBounded)) {
      const outcome = verifyViaNameScg(
        this.net, this._initialMarking, this._property, this._sinkPlaces,
        this._environmentPlaces, this._environmentMode, this._nuMaxClasses,
        this._fragmentMode, this._carrierPlaces, this._prioritySemantics,
      );
      // Route B truncating to unknown on a bounded quiescence ν-net is not the
      // final word: defer to the scalable Route A coloured IC3/PDR encoder
      // (NU-053) below instead of returning unknown here.
      const deferToRouteA =
        outcome !== null &&
        outcome.verdict.type === 'unknown' &&
        !isReachabilitySafety(this._property) &&
        nuBounded;
      if (outcome !== null && !deferToRouteA) {
        report.push('=== ν-net Route B: name-aware state-class graph (NU-050) ===');
        report.push(`  Name-partition state classes: ${outcome.classCount}`);
        report.push(outcome.note);
        if (outcome.transitions.length > 0) {
          report.push(`  Counterexample trace: ${outcome.trace.length} states, ${outcome.transitions.length} transitions`);
        }
        return buildResult(
          outcome.verdict, report.join('\n'), [], [], outcome.trace, outcome.transitions,
          performance.now() - start,
          {
            places: [...this.net.places].length,
            transitions: [...this.net.transitions].length,
            invariantsFound: 0,
            structuralResult: 'n/a (ν name-partition SCG)',
          },
        );
      } else if (deferToRouteA) {
        report.push(
          'ν-net Route B inconclusive (name-partition truncated); deferring to ' +
          'Route A coloured IC3/PDR (NU-053).',
        );
      }
      // EXTENDED was requested but the net is outside the coloured-consumer
      // fragment (classify declined). Surface a short note instead of a silent
      // cliff, then verify via the sound over-approximation below (NU-051, §5
      // diagnosability).
      if (this._fragmentMode === 'extended' && !deferToRouteA) {
        report.push(
          'ν-net Route B (EXTENDED) declined: net outside coloured-consumer fragment ' +
          '(a coloured place consumed count != 1 or by multiple inputs, carries a ' +
          'reset/read/inhibitor arc, or a join re-mints a coloured place); verified via ' +
          'sound over-approximation instead.',
        );
      }
    }

    // Phase 1: Flatten
    report.push('Phase 1: Flattening net...');
    const flatNet = flatten(this.net, this._environmentPlaces, this._environmentMode);
    report.push(`  Places: ${flatNet.places.length}`);
    report.push(`  Transitions (expanded): ${flatNet.transitions.length}`);
    if (flatNet.environmentBounds.size > 0) {
      report.push(`  Environment bounds: ${flatNet.environmentBounds.size} places`);
    }
    report.push('');

    // Phase 2: Structural pre-check
    report.push('Phase 2: Structural pre-check (siphon/trap)...');
    const structResult = structuralCheck(flatNet, this._initialMarking);
    let structResultStr: string;
    switch (structResult.type) {
      case 'no-potential-deadlock':
        structResultStr = 'no potential deadlock';
        break;
      case 'potential-deadlock':
        structResultStr = `potential deadlock (siphon: {${[...structResult.siphon].join(',')}})`;
        break;
      case 'inconclusive':
        structResultStr = `inconclusive (${structResult.reason})`;
        break;
    }
    report.push(`  Result: ${structResultStr}\n`);

    // If structural check proves deadlock-freedom for DeadlockFree property
    // (only valid when no sink places — structural check doesn't account for sinks).
    // Skipped when environment places are registered: the siphon/trap analysis runs
    // on the closed net and is blind to env injection (VER-006), so its early proof
    // could be unsound — fall through to the (injection-aware) SMT encoding instead.
    if (
      this._property.type === 'deadlock-free' &&
      !hasMatch &&
      this._sinkPlaces.size === 0 &&
      structResult.type === 'no-potential-deadlock' &&
      this._environmentPlaces.size === 0
    ) {
      report.push('=== RESULT ===\n');
      report.push('PROVEN (structural): Deadlock-freedom verified by Commoner\'s theorem.');
      report.push('  All siphons contain initially marked traps.');
      return buildResult(
        { type: 'proven', method: 'structural', inductiveInvariant: null },
        report.join('\n'), [], [], [], [],
        performance.now() - start,
        { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: 0, structuralResult: structResultStr },
      );
    }

    // Phase 3: P-invariants
    report.push('Phase 3: Computing P-invariants...');
    const matrix = IncidenceMatrix.from(flatNet);
    // Exact re-check (BigInt) before invariants reach the encoder: the Gaussian
    // elimination runs in f64 `number`, and a numerically wrong invariant conjoined
    // into the CHC transition bodies removes reachable successors — i.e. it could
    // certify a false PROVEN. Drop anything the exact re-verification rejects.
    const { valid: invariants, dropped: droppedInvariants } = validateInvariantsExact(
      matrix,
      computePInvariants(matrix, flatNet, this._initialMarking),
      flatNet,
      this._initialMarking,
    );
    // P-semiflows (non-negative conservation laws) bound the simultaneously-live
    // colour count that sets the name-coloured encoder's slot count `k` (see
    // buildColouredPlan / colourSlotBound) — validated the same way (incl. the H1
    // linearity guard) before they can set that bound, mirroring the Rust verifier.
    const { valid: semiflows, dropped: droppedSemiflows } = validateInvariantsExact(
      matrix,
      computePSemiflows(matrix, flatNet, this._initialMarking),
      flatNet,
      this._initialMarking,
    );
    report.push(`  Found: ${invariants.length} P-invariant(s)`);
    const structurallyBounded = isCoveredByInvariants(invariants, flatNet.places.length);
    report.push(`  Structurally bounded: ${structurallyBounded ? 'YES' : 'NO'}`);
    for (const inv of invariants) {
      report.push(`  ${formatInvariant(inv, flatNet)}`);
    }
    for (const { invariant, reason } of droppedInvariants) {
      report.push(`  Dropped invariant ${formatInvariant(invariant, flatNet)}: exact re-check failed (${reason})`);
    }
    if (droppedInvariants.length > 0) {
      report.push(`  Dropped: ${droppedInvariants.length} invariant(s) failed the exact re-check`);
    }
    for (const { invariant, reason } of droppedSemiflows) {
      report.push(`  Dropped semiflow ${formatInvariant(invariant, flatNet)}: exact re-check failed (${reason})`);
    }
    if (droppedSemiflows.length > 0) {
      report.push(`  Dropped: ${droppedSemiflows.length} semiflow(s) failed the exact re-check`);
    }
    report.push('');

    // Phase 4: SMT encode + query via Spacer
    report.push('Phase 4: IC3/PDR verification via Z3 Spacer...');

    // ν-net exact refinement (NU-050 #1, Route A). For a budget-bounded ν-net in
    // the supported fragment, encode names as a finite colour set (k = the declared
    // budget) with exact same-colour join matching, instead of the name-blind
    // over-approximation — this rules out spurious counterexamples that would equate
    // two distinct names. Reachability-safety AND quiescence (NU-053) properties are
    // both routed here; a net outside the fragment keeps the flat encoding.
    const colouredPlan: ColouredPlan | null =
      hasMatch && nuBounded
        ? buildColouredPlan(
            this.net, flatNet, this._initialMarking, this._budgetPlaces,
            this._fragmentMode, this._carrierPlaces, semiflows,
          )
        : null;

    let runner;
    try {
      runner = await createSpacerRunner(this._timeoutMs);
    } catch (e: any) {
      report.push(`  ERROR: ${e.message ?? e}\n`);
      report.push('=== RESULT ===\n');
      report.push(`UNKNOWN: Z3 initialization error: ${e.message ?? e}`);
      return buildResult(
        { type: 'unknown', reason: `Z3 init error: ${e.message ?? e}` },
        report.join('\n'), invariants, [], [], [],
        performance.now() - start,
        { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
      );
    }

    try {
      let encoding;
      if (colouredPlan != null) {
        report.push(
          `  ν-encoding: name-coloured (exact within budget k=${colouredPlan.k}; ` +
            `${colouredPlan.coloured.length} coloured place(s))`,
        );
        encoding = encodeColoured(runner.ctx, runner.fp, colouredPlan, flatNet, this._initialMarking, this._property, invariants, this._sinkPlaces);
        if (encoding == null) {
          // The property names a place that does not resolve in the net (e.g. a
          // typo'd bound/pending place). Emitting the encoding anyway would certify
          // a vacuous PROVEN; refuse and report Unknown so a mis-named place never
          // silently certifies.
          const reason =
            'property names a place that does not resolve in the net; refusing to certify ' +
            '(the encoding would be vacuously proven)';
          report.push('  Status: UNKNOWN (unresolved property place)\n');
          report.push('=== RESULT ===\n');
          report.push(`UNKNOWN: ${reason}`);
          return buildResult(
            { type: 'unknown', reason },
            report.join('\n'), invariants, [], [], [],
            performance.now() - start,
            { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
          );
        }
      } else {
        encoding = encode(runner.ctx, runner.fp, flatNet, this._initialMarking, this._property, invariants, this._sinkPlaces);
      }
      const queryResult = await runner.query(encoding.errorExpr, encoding.reachableDecl);

      switch (queryResult.type) {
        case 'proven': {
          // Guard against silent vacuous proofs (VER-006): in `ignore` mode the
          // encoding does not model env injection, so env-gated transitions never
          // fire and ANY safety bound is trivially "proven". Refuse to certify —
          // downgrade to UNKNOWN with actionable guidance.
          if (this._environmentPlaces.size > 0 && this._environmentMode.type === 'ignore') {
            const reason =
              'environment places present but not modeled (mode=ignore); a proof would be ' +
              'vacuous — use alwaysAvailable() or bounded(k) to model external injection';
            report.push(`  Status: UNSAT, but vacuous under ignore mode\n`);
            report.push('=== RESULT ===\n');
            report.push(`UNKNOWN: ${reason}`);
            return buildResult(
              { type: 'unknown', reason },
              report.join('\n'), invariants, [], [], [],
              performance.now() - start,
              { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
            );
          }

          report.push('  Status: UNSAT (property holds)');

          // Independent certificate check (flat count encoding only): re-validate
          // the IC3-synthesized invariant against the UNSTRENGTHENED step relation
          // with a plain solver, so neither a Spacer/encoder defect nor a
          // wrong-but-validated-looking invariant strengthening can certify a
          // false PROVEN. The coloured ν-encoding has its own state shape and is
          // out of scope; structural proofs return before this point.
          if (colouredPlan == null && this._certificateCheck) {
            const certificate = await checkCertificate(
              runner.ctx, queryResult.answer, flatNet, this._initialMarking,
              this._property, invariants, this._sinkPlaces, this._timeoutMs,
            );
            if (certificate.type === 'failed') {
              const reason = `Certificate check FAILED: ${certificate.reason} — verdict downgraded`;
              report.push(`  Certificate check: FAILED (${certificate.reason})`);
              if (certificate.invariant != null) {
                report.push(`  Uncertified invariant: ${substituteNames(certificate.invariant, flatNet)}`);
              }
              report.push('');
              report.push('=== RESULT ===\n');
              report.push(`UNKNOWN: ${reason}`);
              return buildResult(
                { type: 'unknown', reason },
                report.join('\n'), invariants, [], [], [],
                performance.now() - start,
                { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
              );
            }
            report.push('  Certificate check: PASSED (init, consecution, safety)');
          }
          report.push('');

          // Decode IC3-synthesized invariants with place name substitution
          const discoveredInvariants: string[] = [];
          if (queryResult.invariantFormula != null) {
            discoveredInvariants.push(substituteNames(queryResult.invariantFormula, flatNet));
          }
          for (const level of queryResult.levelInvariants) {
            discoveredInvariants.push(substituteNames(level, flatNet));
          }

          // Phase 5: Inductive invariant
          if (discoveredInvariants.length > 0) {
            report.push('Phase 5: Inductive invariant (discovered by IC3)');
            report.push(`  Spacer synthesized: ${discoveredInvariants[0]}`);
            report.push('  This formula is INDUCTIVE: preserved by all transitions.');
            if (discoveredInvariants.length > 1) {
              report.push('  Per-level clauses:');
              for (let i = 1; i < discoveredInvariants.length; i++) {
                report.push(`    ${discoveredInvariants[i]}`);
              }
            }
            report.push('');
          }

          report.push('=== RESULT ===\n');
          report.push(`PROVEN (IC3/PDR): ${propDesc}`);
          report.push('  Z3 Spacer proved no reachable state violates the property.');
          report.push('  NOTE: Verification ignores timing constraints.');
          report.push('  An untimed proof is STRONGER than a timed one (timing only restricts behavior).');

          return this.applyNuGuard(buildResult(
            {
              type: 'proven',
              method: 'IC3/PDR',
              inductiveInvariant: queryResult.invariantFormula != null
                ? substituteNames(queryResult.invariantFormula, flatNet)
                : null,
            },
            report.join('\n'), invariants, discoveredInvariants, [], [],
            performance.now() - start,
            { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
          ), hasMatch, nuBounded, colouredPlan != null);
        }

        case 'violated': {
          report.push('  Status: SAT (counterexample found)\n');

          const decoded = decode(runner.ctx, queryResult.answer, flatNet);
          const stats: SmtStatistics = {
            places: flatNet.places.length,
            transitions: flatNet.transitions.length,
            invariantsFound: invariants.length,
            structuralResult: structResultStr,
          };

          // C3: abstract counterexample replay (flat count encoding only — the
          // coloured ν-encoding's state shape is outside the replayer's scope).
          // The decoder collects Reachable states in derivation-TRAVERSAL order;
          // the replay recovers a genuine firing order or downgrades.
          let confirmed: boolean | null = null;
          let trace: readonly MarkingState[] = decoded.trace;
          let transitions: readonly string[] = decoded.transitions;
          let replayed = false;
          if (colouredPlan == null && this._counterexampleReplay) {
            if (decoded.states.size > 0) {
              let outcome: ReplayOutcome;
              try {
                outcome = replayCounterexample(
                  flatNet,
                  vectorize(this._initialMarking, flatNet),
                  [...decoded.states].map(m => vectorize(m, flatNet)),
                  this._property,
                  this._sinkPlaces,
                );
              } catch (e: any) {
                // The abstraction over-approximates (VER-004), so replay failure
                // must downgrade, never crash the verifier.
                outcome = {
                  kind: 'unchainable',
                  reason: `replay error: ${e?.message ?? e}`,
                  nodesExplored: 0,
                };
              }
              if (outcome.kind === 'confirmed') {
                confirmed = true;
                replayed = true;
                trace = outcome.states.map(s => toMarkingState(s, flatNet));
                transitions = outcome.steps.map(stepName);
                report.push('  Counterexample replay: CONFIRMED (abstract chain M0 -> bad re-executed)');
              } else {
                // Decoded states exist but no abstract chain reaches a violating
                // marking: a spurious counterexample of the untimed+value-blind
                // over-approximation, or a decoder mismatch. Never keep an
                // unreplayable VIOLATED — downgrade, with raw + decoded evidence.
                const reason = 'counterexample failed abstract replay — spurious CEX or decoder mismatch';
                report.push(`  Counterexample replay: FAILED (${outcome.reason})`);
                report.push(`  Decoded states (order-free set, ${decoded.states.size}):`);
                for (const m of decoded.states) {
                  report.push(`    ${m}`);
                }
                if (decoded.trace.length > 0) {
                  report.push(`  Raw traversal-order trace (${decoded.trace.length} states):`);
                  for (let i = 0; i < decoded.trace.length; i++) {
                    report.push(`    ${i}: ${decoded.trace[i]}`);
                  }
                }
                if (decoded.failure != null) {
                  report.push(`  Decoder degradation: ${describeDecodeFailure(decoded.failure)}`);
                }
                report.push(`  Raw Z3 answer: ${truncate(String(queryResult.answer), 2000)}`);
                report.push('');
                report.push('=== RESULT ===\n');
                report.push(`UNKNOWN: ${reason}`);
                return buildResult(
                  { type: 'unknown', reason },
                  report.join('\n'), invariants, [], [], [],
                  performance.now() - start,
                  stats,
                );
              }
            } else {
              // Nothing decodable in the derivation: the SAT verdict stands on
              // Spacer's answer alone — NOT a downgrade, but say so.
              confirmed = false;
              report.push(`  Counterexample replay: NO STATES DECODED (${describeDecodeFailure(decoded.failure)})`);
              report.push("  The verdict rests on Spacer's SAT answer; there is nothing to replay.");
            }
          }

          report.push('=== RESULT ===\n');
          report.push(`VIOLATED: ${propDesc}`);
          if (trace.length > 0) {
            report.push(`  Counterexample trace (${replayed ? 'replay order, ' : ''}${trace.length} states):`);
            for (let i = 0; i < trace.length; i++) {
              report.push(`    ${i}: ${trace[i]}`);
            }
          }
          if (transitions.length > 0) {
            report.push(`  Firing sequence: ${transitions.join(' -> ')}`);
          }
          report.push('\n  WARNING: This counterexample is in UNTIMED semantics.');
          report.push('  It may be spurious if timing constraints prevent this sequence.');

          return this.applyNuGuard(buildResult(
            { type: 'violated' },
            report.join('\n'), invariants, [], trace as MarkingState[], transitions as string[],
            performance.now() - start,
            stats,
            confirmed,
          ), hasMatch, nuBounded, colouredPlan != null);
        }

        case 'unknown': {
          report.push(`  Status: UNKNOWN (${queryResult.reason})\n`);
          report.push('=== RESULT ===\n');
          report.push(`UNKNOWN: Could not determine ${propDesc}`);
          report.push(`  Reason: ${queryResult.reason}`);

          return buildResult(
            { type: 'unknown', reason: queryResult.reason },
            report.join('\n'), invariants, [], [], [],
            performance.now() - start,
            { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
          );
        }
      }
    } catch (e: any) {
      report.push(`  ERROR: ${e.message ?? e}\n`);
      report.push('=== RESULT ===\n');
      report.push(`UNKNOWN: Z3 solver error: ${e.message ?? e}`);

      return buildResult(
        { type: 'unknown', reason: `Z3 error: ${e.message ?? e}` },
        report.join('\n'), invariants, [], [], [],
        performance.now() - start,
        { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
      );
    } finally {
      runner.dispose();
    }
  }

  /**
   * ν-net soundness guard (NU-040, NU-050). Applied only when the net contains
   * match (ν-join) transitions, and only to a proven/violated verdict (an
   * existing unknown is left as-is).
   *
   * - Quiescence-based properties (deadlock / joined-or-dead-lettered): the
   *   name-blind over-approximation over-fires joins, so it sees fewer quiescent
   *   states and may miss a real stranded marking — downgraded to unknown
   *   (exact quiescence reasoning is deferred to the SCG name-partition quotient).
   * - Reachability-safety with unbounded fresh names (no budget declared):
   *   reachability over unbounded fresh names is undecidable — unknown.
   * - Bounded reachability-safety in the name-coloured fragment (`exact`): name
   *   equality is encoded exactly via bounded name-colouring, so the verdict is
   *   sound *and* complete within the budget — no spurious different-name
   *   counterexample. The verdict is kept and the exact-path note is appended.
   * - Bounded reachability-safety outside that fragment: `proven` is sound; a
   *   `violated` may be spurious — the verdict is kept and the over-approximation
   *   caveat is appended to the report.
   */
  private applyNuGuard(
    result: SmtVerificationResult,
    hasMatch: boolean,
    nuBounded: boolean,
    exact: boolean,
  ): SmtVerificationResult {
    if (!hasMatch || result.verdict.type === 'unknown') return result;
    // Exact path FIRST (NU-050 #1 / NU-053, Route A): name equality is encoded
    // exactly via bounded name-colouring, so the verdict is sound AND complete
    // within the budget bound — no spurious different-name counterexample. This
    // holds for reachability-safety AND quiescence (deadlock / joined-or-dead-
    // lettered), so an exact coloured plan keeps its verdict for quiescence too;
    // the colour-aware deadlock encoding does not over-fire joins.
    if (exact) {
      const note =
        '\nNote: ν-join name equality is encoded exactly via bounded name-colouring ' +
        '(k = budget); the verdict is sound and complete within the budget bound — no spurious ' +
        'different-name counterexample (NU-050 #1 / NU-053).\n';
      return { ...result, report: result.report + note };
    }
    if (!isReachabilitySafety(this._property)) {
      return downgradeToUnknown(
        result,
        'ν-matching transitions present and the property depends on quiescence ' +
          '(deadlock / joined-or-dead-lettered); the name-blind over-approximation cannot ' +
          'decide it soundly — deferred to the exact ν-analysis (NU-050)',
      );
    }
    if (!nuBounded) {
      return downgradeToUnknown(
        result,
        'ν-matching transitions present with unbounded fresh names (no budget place declared ' +
          'via budgetPlaces(...)); reachability over unbounded fresh names is undecidable ' +
          '(NU-040) — declare the budget place(s) that gate minting to verify within the ' +
          'bounded fragment',
      );
    }
    // Bounded reachability-safety outside the name-coloured fragment: the matched
    // transitions are over-approximated, so a violated may be spurious.
    const note =
      "\nNote: matched (ν-join) transitions are over-approximated (name equality assumed " +
      "satisfiable). 'proven' is sound; a 'violated' counterexample may be spurious pending " +
      'the exact ν-analysis (NU-050).\n';
    return { ...result, report: result.report + note };
  }
}

/**
 * Whether a property is a reachability-safety property — one whose violation is
 * a reachable bad marking. For these the matched-transition over-approximation
 * is sound for `proven`. Quiescence-based properties (deadlock,
 * joined-or-dead-lettered) are not: their violation involves the absence of
 * enabled transitions, which the name-blind over-approximation distorts (NU-050).
 */
function isReachabilitySafety(property: SmtProperty): boolean {
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
    case 'mutual-exclusion':
    case 'unreachable':
      return true;
    case 'deadlock-free':
    case 'joined-or-dead-lettered':
      return false;
  }
}

function downgradeToUnknown(result: SmtVerificationResult, reason: string): SmtVerificationResult {
  return {
    ...result,
    verdict: { type: 'unknown', reason },
    report: result.report + `\nDowngraded to UNKNOWN: ${reason}\n`,
    discoveredInvariants: [],
    counterexampleTrace: [],
    counterexampleTransitions: [],
    counterexampleConfirmed: null,
  };
}

/** Truncates long raw solver output for the report. */
function truncate(s: string, max: number): string {
  return s.length <= max ? s : `${s.slice(0, max)}… (${s.length - max} chars truncated)`;
}

/**
 * Substitutes Z3 variable names (m0, m1, ...) with place names in a formula string.
 */
function substituteNames(formula: string, flatNet: FlatNet): string {
  // Replace from highest index first to avoid m1 matching inside m10
  for (let i = flatNet.places.length - 1; i >= 0; i--) {
    formula = formula.replace(new RegExp(`\\bm${i}\\b`, 'g'), flatNet.places[i]!.name);
  }
  return formula;
}

function formatInvariant(inv: PInvariant, flatNet: FlatNet): string {
  const parts: string[] = [];
  for (const idx of inv.support) {
    if (inv.weights[idx] !== 1) {
      parts.push(`${inv.weights[idx]}*${flatNet.places[idx]!.name}`);
    } else {
      parts.push(flatNet.places[idx]!.name);
    }
  }
  return `${parts.join(' + ')} = ${inv.constant}`;
}

function buildResult(
  verdict: Verdict,
  report: string,
  invariants: readonly PInvariant[],
  discoveredInvariants: readonly string[],
  trace: readonly MarkingState[],
  transitions: readonly string[],
  elapsedMs: number,
  statistics: SmtStatistics,
  counterexampleConfirmed: boolean | null = null,
): SmtVerificationResult {
  return { verdict, report, invariants, discoveredInvariants, counterexampleTrace: trace, counterexampleTransitions: transitions, counterexampleConfirmed, elapsedMs, statistics };
}
