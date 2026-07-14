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
import { computePInvariants, computePSemiflows, isCoveredByInvariants } from './invariant/p-invariant-computer.js';
import { structuralCheck } from './invariant/structural-check.js';
import { createSpacerRunner } from './z3/spacer-runner.js';
import { encode } from './z3/smt-encoder.js';
import { buildColouredPlan, encodeColoured, type ColouredPlan } from './z3/name-coloured-encoder.js';
import { verifyViaNameScg } from './nu-scg-verifier.js';
import type { FragmentMode } from './analysis/name-fragment.js';
import type { PrioritySemantics } from './analysis/priority-semantics.js';
import { decode } from './z3/counterexample-decoder.js';

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
 * - Guards are ignored — over-approximation is sound for safety properties
 * - If a counterexample is found, it may be spurious in timed/guarded
 *   semantics — the report notes this
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
   */
  async verify(): Promise<SmtVerificationResult> {
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
    const invariants = computePInvariants(matrix, flatNet, this._initialMarking);
    // P-semiflows (non-negative conservation laws) bound the simultaneously-live
    // colour count that sets the name-coloured encoder's slot count `k` (see
    // buildColouredPlan / colourSlotBound).
    const semiflows = computePSemiflows(matrix, flatNet, this._initialMarking);
    report.push(`  Found: ${invariants.length} P-invariant(s)`);
    const structurallyBounded = isCoveredByInvariants(invariants, flatNet.places.length);
    report.push(`  Structurally bounded: ${structurallyBounded ? 'YES' : 'NO'}`);
    for (const inv of invariants) {
      report.push(`  ${formatInvariant(inv, flatNet)}`);
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

          report.push('  Status: UNSAT (property holds)\n');

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
          report.push('  NOTE: Verification ignores timing constraints and JS guards.');
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

          report.push('=== RESULT ===\n');
          report.push(`VIOLATED: ${propDesc}`);
          if (decoded.trace.length > 0) {
            report.push(`  Counterexample trace (${decoded.trace.length} states):`);
            for (let i = 0; i < decoded.trace.length; i++) {
              report.push(`    ${i}: ${decoded.trace[i]}`);
            }
          }
          if (decoded.transitions.length > 0) {
            report.push(`  Firing sequence: ${decoded.transitions.join(' -> ')}`);
          }
          report.push('\n  WARNING: This counterexample is in UNTIMED semantics.');
          report.push('  It may be spurious if timing constraints prevent this sequence.');
          report.push('  JS guards are also ignored in this analysis.');

          return this.applyNuGuard(buildResult(
            { type: 'violated' },
            report.join('\n'), invariants, [], decoded.trace as MarkingState[], decoded.transitions as string[],
            performance.now() - start,
            { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
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
  };
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
): SmtVerificationResult {
  return { verdict, report, invariants, discoveredInvariants, counterexampleTrace: trace, counterexampleTransitions: transitions, elapsedMs, statistics };
}
