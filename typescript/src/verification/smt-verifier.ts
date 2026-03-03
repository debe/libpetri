import type { PetriNet } from '../core/petri-net.js';
import type { EnvironmentPlace, Place } from '../core/place.js';
import { MarkingState, MarkingStateBuilder } from './marking-state.js';
import type { SmtProperty } from './smt-property.js';
import { deadlockFree, propertyDescription } from './smt-property.js';
import type { SmtVerificationResult, SmtStatistics, Verdict } from './smt-verification-result.js';
import type { PInvariant } from './invariant/p-invariant.js';
import type { FlatNet } from './encoding/flat-net.js';
import { flatten, type EnvironmentAnalysisMode, unbounded } from './encoding/net-flattener.js';
import { IncidenceMatrix } from './encoding/incidence-matrix.js';
import { computePInvariants, isCoveredByInvariants } from './invariant/p-invariant-computer.js';
import { structuralCheck } from './invariant/structural-check.js';
import { createSpacerRunner } from './z3/spacer-runner.js';
import { encode } from './z3/smt-encoder.js';
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
  private _environmentMode: EnvironmentAnalysisMode = unbounded();
  private _timeoutMs: number = 60_000;

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

  timeout(ms: number): this {
    this._timeoutMs = ms;
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
    // (only valid when no sink places — structural check doesn't account for sinks)
    if (
      this._property.type === 'deadlock-free' &&
      this._sinkPlaces.size === 0 &&
      structResult.type === 'no-potential-deadlock'
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
    report.push(`  Found: ${invariants.length} P-invariant(s)`);
    const structurallyBounded = isCoveredByInvariants(invariants, flatNet.places.length);
    report.push(`  Structurally bounded: ${structurallyBounded ? 'YES' : 'NO'}`);
    for (const inv of invariants) {
      report.push(`  ${formatInvariant(inv, flatNet)}`);
    }
    report.push('');

    // Phase 4: SMT encode + query via Spacer
    report.push('Phase 4: IC3/PDR verification via Z3 Spacer...');

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
      const encoding = encode(runner.ctx, runner.fp, flatNet, this._initialMarking, this._property, invariants, this._sinkPlaces);
      const queryResult = await runner.query(encoding.errorExpr, encoding.reachableDecl);

      switch (queryResult.type) {
        case 'proven': {
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

          return buildResult(
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
          );
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

          return buildResult(
            { type: 'violated' },
            report.join('\n'), invariants, [], decoded.trace as MarkingState[], decoded.transitions as string[],
            performance.now() - start,
            { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: invariants.length, structuralResult: structResultStr },
          );
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
