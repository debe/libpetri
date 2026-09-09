import type { PetriNet } from '../core/petri-net.js';
import { rethrowIfProgrammingError } from './programming-error.js';
import type { EnvironmentPlace, Place } from '../core/place.js';
import { MarkingState, MarkingStateBuilder } from './marking-state.js';
import type { SmtProperty } from './smt-property.js';
import { deadlockFree, propertyDescription } from './smt-property.js';
import { describeSinks, type ConditionalSinks } from './rest-set.js';
import type { SmtVerificationResult, SmtStatistics, Verdict, VerificationRoute } from './smt-verification-result.js';
import type { PInvariant } from './invariant/p-invariant.js';
import type { FlatNet } from './encoding/flat-net.js';
import { flatten } from './encoding/net-flattener.js';
import { type EnvironmentAnalysisMode, alwaysAvailable } from './analysis/environment-analysis-mode.js';
import { IncidenceMatrix } from './encoding/incidence-matrix.js';
import { canonicalInvariantOrder, computePInvariants, computePSemiflows, isCoveredByInvariants, strengthenWithSemiflows, validateInvariantsExact } from './invariant/p-invariant-computer.js';
import { structuralCheck } from './invariant/structural-check.js';
import { runZ3Spacer } from './z3/spacer-runner.js';
import { checkCertificate, vcScript, type CertificateCheckOutcome } from './z3/certificate-checker.js';
import { encodeNet, quiescenceUnreachable, resolveEnvInjection, type SmtEncoding } from './z3/smt-encoder.js';
import {
  checkLinearBoundExact, decodeLinearBound, encodeLinearBound, formatLinearBound, formatLinearDemand,
} from './z3/linear-bound.js';
import { classifyFirstLine } from './z3/smt-text.js';
import { failureReason, formatZ3Version, resolveZ3, runZ3Text, timeoutBudget, Z3Unavailable, type Z3Solver } from './z3/z3-process.js';
import { buildColouredPlan, encodeColoured, type ColouredPlan } from './z3/name-coloured-encoder.js';
import { verifyViaNameScg } from './nu-scg-verifier.js';
import { verifyViaStateClassGraph, isUntimed, NOTE_ENUMERATED } from './scg-verifier.js';
import type { FragmentMode } from './analysis/name-fragment.js';
import type { PrioritySemantics } from './analysis/priority-semantics.js';
import { decode } from './z3/counterexample-decoder.js';
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
/**
 * Why a `proven` is refused under `ignore()` (VER-006). Shared by every route that can
 * return `proven`, so the guards cannot drift apart.
 */
const IGNORE_MODE_VACUITY_REASON =
  'environment places present but not modeled (mode=ignore); a proof would be ' +
  'vacuous — use alwaysAvailable() or bounded(k) to model external injection';

export class SmtVerifier {
  private _initialMarking: MarkingState = MarkingState.empty();
  private _property: SmtProperty = deadlockFree();
  private readonly _environmentPlaces = new Set<EnvironmentPlace<any>>();
  private readonly _sinkPlaces = new Set<Place<any>>();
  private readonly _conditionalSinks: { marker: Place<any>; places: Set<Place<any>> }[] = [];
  private readonly _budgetPlaces = new Set<string>();
  private _environmentMode: EnvironmentAnalysisMode = alwaysAvailable();
  private _timeoutMs: number = 60_000;
  private _certificateCheck: boolean = true;
  private _counterexampleReplay: boolean = true;
  private _semiflowInvariants: boolean | 'auto' = false;
  private _stateEquation: boolean = false;
  private _linearBound: boolean = true;
  private _nuMaxClasses: number = 100_000;
  private _enumerationMaxClasses: number = 50_000;
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
   * Declares expected sink (terminal) places for deadlock-freedom analysis
   * (VER-002): a token resting in one is never stranded, and `TerminatesAtSink`
   * asks whether one of them was reached.
   */
  sinkPlaces(...places: Place<any>[]): this {
    for (const p of places) this._sinkPlaces.add(p);
    return this;
  }

  /**
   * Declares places where a token may rest **while `marker` holds a token**
   * (VER-014) — a designed terminal such as a halt or pause marker, under which
   * the work it interrupted legitimately stays where it was delivered.
   *
   * `DeadlockFree` then reads a quiescent marking against the union of the
   * declared sinks, the markers, and every conditional set whose marker is marked:
   * a token in `p` is stranded only when none of those excuse it. The marker
   * itself is at rest whenever it is marked, so `sinkPlacesWhen(halt)` with no
   * further places excuses exactly the halt token. Repeated calls for one marker
   * accumulate; declarations for several markers union. `TerminatesAtSink` is
   * unaffected and reads only {@link sinkPlaces}.
   *
   * ```ts
   * SmtVerifier.forNet(net)
   *   .property(deadlockFree())
   *   .sinkPlaces(done)                       // may always rest
   *   .sinkPlacesWhen(halt, inbox, pending)   // may rest once the run halted
   *   .sinkPlacesWhen(pause, inbox)           // may rest while paused
   * ```
   *
   * An unresolved marker or place contributes nothing, as an unresolved sink
   * does: a mistyped marker makes the property stricter, never laxer.
   */
  sinkPlacesWhen(marker: Place<any>, ...places: Place<any>[]): this {
    let entry = this._conditionalSinks.find(c => c.marker.name === marker.name);
    if (entry == null) {
      entry = { marker, places: new Set<Place<any>>() };
      this._conditionalSinks.push(entry);
    }
    for (const p of places) entry.places.add(p);
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
   * counterexample states (an order-free set — the derivation tree is walked in
   * traversal order, not firing order) are re-executed TS-side against the
   * abstract semantics the encoder emits (Lean's `fireA`, Basic.lean), searching
   * for a firing order from M₀ to a property-violating marking. See
   * `SmtVerificationResult.counterexampleConfirmed` for how each outcome lands.
   */
  counterexampleReplay(enabled: boolean): this {
    this._counterexampleReplay = enabled;
    return this;
  }

  /**
   * Also hands the validated **P-semiflows** to the encoders as invariants
   * (VER-007; default: disabled — the encoders then see only the null-space basis).
   *
   * Every validated semiflow is a conservation law in its own right (`y >= 0`,
   * `y·C = 0`, `y·M0` exact, zero weight on every reset / consume-all place), and
   * the Farkas enumeration returns the *minimal* laws of the net. The null-space
   * basis the encoders get by default is one basis of many: elimination hands back
   * mixed-sign rows (discarded as not semi-positive) or rows that fold a reset place
   * into a chain whose other combinations avoid it (dropped by the H1 guard). On a
   * net with a few reset arcs that can lose every law of the chains those arcs
   * touch, and without them IC3 has to rediscover the conservation of each chain —
   * on a ~100-place net it does not within any practical budget.
   *
   * **Turn this on if the net has any `all()` / `atLeast(n)` or reset arc on a busy
   * place** — draining an input queue is the everyday case. Every basis row whose
   * support touches such a place fails the H1 guard and is dropped, so the encoders
   * run on a deficient invariant set and nothing in the report says a law is missing
   * beyond the `Dropped` lines.
   *
   * This reaches the **name-coloured** encoder (NU-050) as well as the flat one, and
   * it matters most there. On a 113-place ν-net, whole-net deadlock-freedom went from
   * `unknown` after 50 minutes to `proven` in about 15 seconds with this option as the
   * only change; on the flat path, reachability-safety queries that timed out at 120 s
   * close in about a second.
   *
   * Soundness is unchanged: the semiflows pass the same exact re-validation as the
   * basis rows, the union is pure strengthening (`Semiflow.lean`,
   * `semiflow_union_sound`), and the certificate check re-proves the strengthened
   * invariant — that check is flat-path only, so a coloured `proven` reports
   * `Certificate check: not applicable (name-coloured encoding)`. Off by default so
   * reports stay byte-equal.
   */
  /**
   * `'auto'` decides whether the semiflows would add **information to the
   * encoding**, which is not the same question as whether they would appear in
   * {@link SmtVerificationResult.invariants} for a caller who reads them.
   *
   * A complete basis spans every conservation law of the net, so a semiflow it
   * spans constrains nothing further and IC3 gains nothing from it — that is why
   * `'auto'` skips the enumeration there. But the basis is the *signed*
   * null-space, and a law it spans need not appear in it in **non-negative**
   * form; only the Farkas enumeration produces that. A caller inspecting the
   * invariant list for a law of a given shape — "a non-negative law weighting the
   * budget place and every running place positively" — can therefore find nothing
   * on a net that plainly has one. Such a caller should ask for the union
   * explicitly: `'auto'` is the setting to prefer for verification, not for
   * harvesting.
   */
  semiflowInvariants(enabled: boolean | 'auto'): this {
    this._semiflowInvariants = enabled;
    return this;
  }

  /**
   * Enables/disables the linear state-equation bound phase (VER-015; default:
   * enabled). A reachability-safety property whose violating markings exceed some
   * `y·M <= y·M0` with `y >= 0`, `y·C <= 0` is then proven structurally, from one
   * linear query re-checked in exact integer arithmetic, before any fixpoint search.
   * Disable it to force the IC3/PDR path — for its certificate, or to exercise the
   * fixpoint engine itself.
   */
  linearBound(enabled: boolean): this {
    this._linearBound = enabled;
    return this;
  }

  /**
   * Encodes the **state equation** with firing counters (VER-016; default:
   * disabled — the encoding then carries places only).
   *
   * The flat encoding gains one counter `n_t` per flat transition and every
   * transition rule conjoins the marking equation `M' = M0 + C·n'` for each place
   * whose column is exact (no consume-all / reset arc, not injected). Every linear
   * consequence of the marking equation — the equality laws of VER-005/VER-007
   * **and** the inequality laws `y·M ≤ y·M0` (`y ≥ 0, y·C ≤ 0`) and their mixed-sign
   * kin, which are what an *ordering* argument ("both join slots armed means every
   * upstream stage has run, so nothing can still halt") looks like in linear
   * arithmetic — is then available to Spacer as a fact rather than a lemma it has to
   * invent. On a 50-place agent-dispatch workflow, proper completion under conditional
   * sinks went from `unknown` after 120 s to `proven` in 1.5 s with this as the only
   * change; a 53-place pipeline stage before a join, `unknown` at 300 s, proves in
   * under a second.
   *
   * The cost is a larger state (places + transitions) and a slower witness search
   * on genuinely violated properties (about 1.5× on the nets above), so it is opt-in.
   * Soundness is unchanged: the counters are exact bookkeeping, the equation holds
   * on every reachable state by construction (`Strengthening.lean`, the same shape
   * as the equality laws), and the certificate check re-proves it against the raw
   * step relation, whose only counter knowledge is the increment. Not applied to the
   * name-coloured encoding or Route B, which the report says when it applies.
   */
  stateEquation(enabled: boolean): this {
    this._stateEquation = enabled;
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
   * Sets the class budget for the bounded state-space enumeration route
   * (VER-017; default 50 000). `0` disables the route, so every query goes to
   * the SMT pipeline.
   *
   * When the state-class graph closes within the budget the property is decided
   * exactly — sound and complete over the timed semantics — and no solver runs.
   * This is what makes a long pipeline tractable: IC3 needs a frame per stage and
   * its cost climbs with the cube of the length, while enumeration is linear in
   * the reachable state space. A forty-node chain (370 places, 1 967 classes)
   * takes 410 s on the fixpoint path and 0.11 s here.
   *
   * The route declines when the graph exceeds the budget, and the SMT pipeline
   * then runs unchanged — it can only add verdicts, never remove them. It is
   * skipped for ν-nets, which have their own exact route (NU-050, Route B), for
   * nets with environment places, whose injection the graph does not model, and
   * for **timed** nets, where its verdict would be the weaker timed claim rather
   * than the untimed one the encoders make (VER-004).
   */
  enumerationMaxClasses(max: number): this {
    this._enumerationMaxClasses = max;
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
   * The name-coloured plan and its encoding, or a null plan when the net is outside
   * the fragment (NU-050) and a null encoding when the property names a place the net
   * does not resolve.
   *
   * {@link verify} and {@link encodeScripts} share this deliberately. They used to
   * invoke `buildColouredPlan` and `encodeColoured` separately, so handing the encoder
   * the wrong one of the two lists changed only one of them — and the script-parity
   * goldens are generated from `encodeScripts`. Unifying the invocation closes that. It
   * does not make the two paths identical: each still computes its own invariant and
   * semiflow lists, so they can still drift through the arguments rather than the call.
   *
   * `invariants` is what the encoder conjoins into every rule body (the null-space
   * basis, unioned with the semiflows when VER-007 is enabled); `semiflows` sets the
   * colour-slot bound k (NU-053). They are not the same list.
   */
  private colouredAttempt(
    flatNet: FlatNet,
    invariants: readonly PInvariant[],
    semiflows: readonly PInvariant[],
  ): { plan: ColouredPlan | null; encoding: SmtEncoding | null } {
    const hasMatch = [...this.net.transitions].some(t => t.matchSpec !== null);
    const nuBounded = this._budgetPlaces.size > 0;
    if (!hasMatch || !nuBounded) return { plan: null, encoding: null };
    const plan = buildColouredPlan(
      this.net, flatNet, this._initialMarking, this._budgetPlaces,
      this._fragmentMode, this._carrierPlaces, semiflows,
    );
    if (plan == null) return { plan: null, encoding: null };
    return {
      plan,
      encoding: encodeColoured(
        plan, flatNet, this._initialMarking, this._property, invariants, this._sinkPlaces,
        this._conditionalSinks,
      ),
    };
  }

  /**
   * The SMT-LIB2 scripts {@link verify} would send to z3 for this configuration,
   * without running a solver (VER-013 AC1): the HORN query (flat, or name-coloured
   * when a declared budget puts the net on Route A's exact encoding) and, for the
   * flat encoding, the certificate-check script built around
   * {@link placeholderCertificate}. This is what the cross-language golden tests diff
   * byte for byte. Route B, the structural pre-check and the unresolved-place
   * refusal are bypassed: it is what Route A encodes.
   */
  encodeScripts(): EncodedScripts {
    requireOutputProducingActions(this.net);
    const flatNet = flatten(this.net, this._environmentPlaces, this._environmentMode);
    const matrix = IncidenceMatrix.from(flatNet);
    const { valid: basis, dropped: basisDropped } = validateInvariantsExact(
      matrix, computePInvariants(matrix, flatNet, this._initialMarking), flatNet, this._initialMarking,
    );
    // `'auto'` decides from the same fact here as in verify() — whether the basis
    // lost a law to the H1 guard — so the script this reports is the script that
    // would be sent. Deciding it differently would make the parity goldens pin
    // something the pipeline never emits.
    const autoUnion = this._semiflowInvariants === 'auto'
      && basisDropped.some(d => d.reason.includes('Strengthening.lean H1'));
    // Same gate as verify(): only compute what something will read (see there).
    const scriptsHasMatch = [...this.net.transitions].some(t => t.matchSpec !== null);
    const { valid: semiflows } = this._semiflowInvariants === true || autoUnion || (scriptsHasMatch && this._budgetPlaces.size > 0)
      ? validateInvariantsExact(
          matrix, computePSemiflows(matrix, flatNet, this._initialMarking), flatNet, this._initialMarking,
        )
      : { valid: [] as PInvariant[] };
    let invariants: readonly PInvariant[] = basis;
    if (this._semiflowInvariants === true || autoUnion) invariants = strengthenWithSemiflows(basis, semiflows).invariants;
    invariants = canonicalInvariantOrder(invariants);
    const attempt = this.colouredAttempt(flatNet, invariants, semiflows);
    // The bound query (VER-015) exactly when verify() would send it: flat path, enabled,
    // not refused by VER-006, and a property with a linear demand (else null).
    const bound =
      attempt.plan == null &&
      this._linearBound &&
      !(this._environmentPlaces.size > 0 && this._environmentMode.type === 'ignore')
        ? encodeLinearBound(flatNet, this._initialMarking, this._property)
        : null;
    if (attempt.encoding != null) {
      return { horn: attempt.encoding.smt2, certificate: null, coloured: true, bound };
    }
    const flat = encodeNet(flatNet, this._initialMarking, this._property, invariants, {
      sinkPlaces: this._sinkPlaces,
      produceProofs: this._counterexampleReplay,
      conditionalSinks: this._conditionalSinks,
      stateEquation: this._stateEquation,
    });
    const certificate = vcScript(
      placeholderCertificate(flatNet.places.length + flat.counterCount), flatNet, this._initialMarking,
      this._property, this._sinkPlaces, invariants, this._conditionalSinks, this._stateEquation,
    );
    return { horn: flat.smt2, certificate, coloured: false, bound };
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
    const sinkDesc = describeSinks(this._sinkPlaces, this._conditionalSinks);
    const propDesc = sinkDesc === null
      ? propertyDescription(this._property)
      : `${propertyDescription(this._property)} (${sinkDesc})`;
    report.push(`Property: ${propDesc}`);
    report.push(`Timeout: ${(this._timeoutMs / 1000).toFixed(0)}s\n`);

    // Before ANY route. Each of them answers a property naming an absent place
    // vacuously, and each returns before the flat encoder's own refusal could
    // fire, so the guard has to sit above all of them or it guards nothing.
    const absent = unresolvedPropertyPlaceInNet(this.net, this._property);
    if (absent != null) {
      const reason =
        `property names a place that does not resolve in the net ('${absent}'); ` +
        'refusing to certify (the encoding would be vacuously proven)';
      report.push('=== RESULT ===\n');
      report.push(`UNKNOWN: ${reason}`);
      return buildResult(
        { type: 'unknown', reason }, report.join('\n'), [], [], [], [],
        performance.now() - start,
        {
          places: [...this.net.places].length,
          transitions: [...this.net.transitions].length,
          invariantsFound: 0,
          structuralResult: 'n/a (unresolved property place)',
        },
        null,
        'unavailable',
      );
    }

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
        this._conditionalSinks,
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
        // VER-006 binds every route that can return `proven`, not only the SMT
        // encoding. Under `ignore` the name-partition graph treats an environment
        // place as an ordinary empty one, so a bound that holds only because
        // injection never happens is exactly the vacuous proof the guard exists to
        // refuse — and Route B returns here without passing the guard on the solver
        // path below.
        let routeBVerdict = outcome.verdict;
        if (
          routeBVerdict.type === 'proven' &&
          this._environmentPlaces.size > 0 &&
          this._environmentMode.type === 'ignore'
        ) {
          report.push(`  Downgraded to UNKNOWN: ${IGNORE_MODE_VACUITY_REASON}`);
          routeBVerdict = { type: 'unknown', reason: IGNORE_MODE_VACUITY_REASON };
        }
        return buildResult(
          routeBVerdict, report.join('\n'), [], [], outcome.trace, outcome.transitions,
          performance.now() - start,
          {
            places: [...this.net.places].length,
            transitions: [...this.net.transitions].length,
            invariantsFound: 0,
            structuralResult: 'n/a (ν name-partition SCG)',
          },
          null,
          'nu-scg',
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

    // Bounded state-space enumeration (VER-017): when the state-class graph closes
    // within the budget it decides the property exactly, with no solver at all —
    // the answer for the narrow, deep state spaces a workflow net produces, where
    // IC3 needs a frame per pipeline stage. Skipped for ν-nets (Route B above is
    // their exact route) and for nets with environment places, whose injection the
    // graph does not model; on truncation the SMT pipeline below runs unchanged.
    if (
      !hasMatch &&
      this._environmentPlaces.size === 0 &&
      this._enumerationMaxClasses > 0 &&
      isUntimed(this.net)
    ) {
      const enumerated = verifyViaStateClassGraph(
        this.net, this._initialMarking, this._property, this._sinkPlaces,
        this._enumerationMaxClasses, this._conditionalSinks,
      );
      if (enumerated.kind === 'decided') {
        report.push('=== Bounded state-space enumeration (VER-017) ===');
        report.push(`  State classes: ${enumerated.classCount}`);
        report.push('  P-invariants: not computed (no encoding is built on this route)');
        report.push(NOTE_ENUMERATED);
        if (enumerated.transitions.length > 0) {
          report.push(`  Counterexample trace: ${enumerated.trace.length} states, ${enumerated.transitions.length} transitions`);
        }
        return buildResult(
          enumerated.verdict, report.join('\n'), [], [], enumerated.trace, enumerated.transitions,
          performance.now() - start,
          {
            places: [...this.net.places].length,
            transitions: [...this.net.transitions].length,
            invariantsFound: 0,
            structuralResult: 'n/a (state-space enumeration)',
          },
          // The graph path IS a firing sequence, so a violation is ordered and
          // confirmed by construction; there is nothing left to replay.
          enumerated.verdict.type === 'violated' ? true : null,
          'enumeration',
        );
      }
      report.push(
        `Bounded state-space enumeration truncated at ${this._enumerationMaxClasses} classes ` +
        '(VER-017); verifying via the SMT pipeline.',
      );
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
    // Skipped too for any net Commoner's theorem does not govern: see
    // {@link commonerApplies}. That guard is what makes this a proof rather than a
    // guess, and it was missing.
    if (
      this._property.type === 'deadlock-free' &&
      !hasMatch &&
      commonerApplies(flatNet) &&
      this._sinkPlaces.size === 0 &&
      this._conditionalSinks.length === 0 &&
      structResult.type === 'no-potential-deadlock' &&
      this._environmentPlaces.size === 0
    ) {
      report.push('=== RESULT ===\n');
      report.push('PROVEN (structural): Deadlock-freedom verified by Commoner\'s theorem.');
      report.push('  All siphons contain initially marked traps.');
      report.push('  Certificate check: not applicable (structural proof)');
      return buildResult(
        { type: 'proven', method: 'structural', inductiveInvariant: null },
        report.join('\n'), [], [], [], [],
        performance.now() - start,
        { places: flatNet.places.length, transitions: flatNet.transitions.length, invariantsFound: 0, structuralResult: structResultStr },
        null,
        'structural',
      );
    }

    // Phase 3: P-invariants
    report.push('Phase 3: Computing P-invariants...');
    const matrix = IncidenceMatrix.from(flatNet);
    // Exact re-check (BigInt) before invariants reach the encoder: the Gaussian
    // elimination runs in f64 `number`, and a numerically wrong invariant conjoined
    // into the CHC transition bodies removes reachable successors — i.e. it could
    // certify a false PROVEN. Drop anything the exact re-verification rejects.
    const { valid: basisInvariants, dropped: droppedInvariants } = validateInvariantsExact(
      matrix,
      computePInvariants(matrix, flatNet, this._initialMarking),
      flatNet,
      this._initialMarking,
    );
    // P-semiflows (non-negative conservation laws) bound the simultaneously-live
    // colour count that sets the name-coloured encoder's slot count `k` (see
    // buildColouredPlan / colourSlotBound) — validated the same way (incl. the H1
    // linearity guard) before they can set that bound, mirroring the Rust verifier.
    //
    // Computed ONLY when something will read them: the [VER-007] union, or the
    // coloured plan's slot bound. The enumeration is worst-case exponential — the
    // minimal semiflows of `k` independent diamonds in series number 2^k, measured
    // at 2 048 for eleven and 8 189 (the backstop) beyond thirteen — so running it
    // for a caller who asked for neither is a large cost, and on a wide net an
    // uncatchable one: the heap it exhausts aborts the process rather than
    // returning a verdict. Skipping it is invisible to every other phase.
    // `'auto'` (VER-007): compute them exactly when the basis LOST a law to the H1
    // guard, which is the condition the option exists for — a consume-all / reset
    // arc on a busy place drops every basis row whose support touches it, and the
    // semiflows are the minimal laws that avoid it. On a net with a complete basis
    // they add nothing and cost the enumeration, so `'auto'` skips them there. The
    // drops are already known at this point, so this decides in ONE pass rather
    // than running the pipeline twice to read its own report.
    const basisLostALaw = droppedInvariants.some(d => d.reason.includes('Strengthening.lean H1'));
    const semiflowsWanted =
      this._semiflowInvariants === true ||
      (this._semiflowInvariants === 'auto' && basisLostALaw) ||
      (hasMatch && nuBounded);
    const { valid: semiflows, dropped: droppedSemiflows } = semiflowsWanted
      ? validateInvariantsExact(
          matrix,
          computePSemiflows(matrix, flatNet, this._initialMarking),
          flatNet,
          this._initialMarking,
        )
      : { valid: [] as PInvariant[], dropped: [] as { invariant: PInvariant; reason: string }[] };
    report.push(`  Found: ${basisInvariants.length} P-invariant(s)`);
    // VER-007: the minimal conservation laws, as extra invariants for the encoders.
    // The report line is emitted only when enabled so default reports stay
    // byte-identical (AC2/AC3).
    if (this._semiflowInvariants === 'auto') {
      report.push(basisLostALaw
        ? '  Semiflow union: ON (auto — the basis lost a law to the H1 guard)'
        : '  Semiflow union: off (auto — the basis is complete, so the semiflows would add no ' +
          'constraint the encoding does not already have; they may still differ in FORM)');
    }
    // The UNION is a separate decision from computing them: a coloured plan needs
    // the slot bound without wanting the laws conjoined.
    const unionWanted =
      this._semiflowInvariants === true || (this._semiflowInvariants === 'auto' && basisLostALaw);
    let invariants: readonly PInvariant[] = basisInvariants;
    if (unionWanted) {
      const { invariants: strengthened, added } = strengthenWithSemiflows(basisInvariants, semiflows);
      invariants = strengthened;
      report.push(`  Semiflows encoded as invariants: ${added}`);
    }
    // VER-013: canonical invariant order (support, weights, constant), so the
    // strengthened rule bodies and the certificate candidate read the same in every
    // implementation whatever order the elimination produced them in.
    invariants = canonicalInvariantOrder(invariants);
    const structurallyBounded = isCoveredByInvariants(invariants, flatNet.places.length);
    report.push(`  Structurally bounded: ${structurallyBounded ? 'YES' : 'NO'}`);
    for (const inv of invariants) {
      report.push(`  ${formatInvariant(inv, flatNet)}`);
    }
    // Canonical cross-language wording: "  Dropped <kind>: <desc> - <reason>",
    // ASCII hyphen-minus as the clause separator so the four implementations'
    // reports diff byte-for-byte. The structured {invariant, reason} pairs stay
    // on the result for callers that want more than the rendered line.
    for (const { invariant, reason } of droppedInvariants) {
      report.push(`  Dropped invariant: ${formatInvariant(invariant, flatNet)} - ${reason}`);
    }
    if (droppedInvariants.length > 0) {
      report.push(`  Dropped: ${droppedInvariants.length} invariant(s) failed the exact re-check`);
    }
    for (const { invariant, reason } of droppedSemiflows) {
      report.push(`  Dropped semiflow: ${formatInvariant(invariant, flatNet)} - ${reason}`);
    }
    if (droppedSemiflows.length > 0) {
      report.push(`  Dropped: ${droppedSemiflows.length} semiflow(s) failed the exact re-check`);
    }
    report.push('');

    // A quiescence property on a net that can never come to rest is vacuously
    // true: the verdict would be `proven` whatever the net does. Say so, or the
    // caller reads an empty claim as a guarantee about their workflow.
    if (!isReachabilitySafety(this._property) && quiescenceUnreachable(flatNet, resolveEnvInjection(flatNet))) {
      report.push(
        '  NOTE: no marking of this net can be quiescent — a transition is enabled in every ' +
        'marking (an environment-gated one under modelled injection, VER-006). Every quiescence ' +
        'property is therefore vacuously true here, and a `proven` says nothing about the net.',
      );
    }

    // Phase 4: SMT encode + query via Spacer
    report.push('Phase 4: IC3/PDR verification via Z3 Spacer...');

    // VER-013: one z3 process per query. Resolve the executable before any encoding
    // work so a missing or too-old solver is reported as such.
    const stats: SmtStatistics = {
      places: flatNet.places.length,
      transitions: flatNet.transitions.length,
      invariantsFound: invariants.length,
      structuralResult: structResultStr,
    };
    let solver: Z3Solver;
    try {
      solver = resolveZ3();
    } catch (e: any) {
      rethrowIfProgrammingError(e);
      const reason = e instanceof Z3Unavailable ? e.message : String(e?.message ?? e);
      report.push(`  Solver: z3 unavailable (${reason})`);
      report.push(`  Status: UNKNOWN (${reason})\n`);
      report.push('=== RESULT ===\n');
      report.push(`UNKNOWN: Could not determine ${propDesc}`);
      report.push(`  Reason: ${reason}`);
      return buildResult({ type: 'unknown', reason }, report.join('\n'), invariants, [], [], [], performance.now() - start, stats, null, 'unavailable');
    }
    report.push(`  Solver: z3 ${formatZ3Version(solver.version)}`);

    // ν-net exact refinement (NU-050 #1, Route A). For a budget-bounded ν-net in
    // the supported fragment, encode names as a finite colour set (k = the declared
    // budget) with exact same-colour join matching, instead of the name-blind
    // over-approximation — this rules out spurious counterexamples that would equate
    // two distinct names. Reachability-safety AND quiescence (NU-053) properties are
    // both routed here; a net outside the fragment keeps the flat encoding.
    //
    // After the solver resolves, not before: the helper encodes as well as plans, and
    // encoding for a solver that turns out to be missing is work thrown away. Java and
    // Rust order it the same way.
    const colouredAttempt = this.colouredAttempt(flatNet, invariants, semiflows);
    const colouredPlan: ColouredPlan | null = colouredAttempt.plan;

    // Linear state-equation bound (VER-015): a reachability-safety property whose
    // violating markings exceed some `y·M <= y·M0` with `y >= 0`, `y·C <= 0` is
    // proven structurally, without the fixpoint search — the ordering arguments
    // IC3 does not invent on pipeline-shaped nets. Flat path only: a net on the exact
    // name-coloured encoding keeps that route's verdict and notes. Skipped under
    // `ignore` with environment places, where VER-006 refuses every `proven`.
    if (
      this._linearBound &&
      colouredPlan == null &&
      isReachabilitySafety(this._property) &&
      !(this._environmentPlaces.size > 0 && this._environmentMode.type === 'ignore')
    ) {
      const proof = await this.linearBoundProof(flatNet, solver, report);
      if (proof != null) {
        report.push('  Certificate check: not applicable (structural proof)');
        report.push('');
        report.push('=== RESULT ===\n');
        report.push(`PROVEN (structural): ${propDesc}`);
        report.push('  Linear state-equation bound: y >= 0 with y.C <= 0 gives y.M <= y.M0 on every');
        report.push('  reachable marking, and the violating markings exceed it (VER-015).');
        report.push(`  ${proof}`);
        return this.applyNuGuard(buildResult(
          { type: 'proven', method: 'structural', inductiveInvariant: null },
          report.join('\n'), invariants, [], [], [],
          performance.now() - start,
          stats,
          null,
          'structural',
        ), hasMatch, nuBounded, false);
      }
    }

    let encoding: SmtEncoding;
    if (colouredPlan != null) {
      report.push(
        `  ν-encoding: name-coloured (exact within budget k=${colouredPlan.k}; ` +
          `${colouredPlan.coloured.length} coloured place(s))`,
      );
      const coloured = colouredAttempt.encoding;
      if (coloured == null) {
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
        return buildResult({ type: 'unknown', reason }, report.join('\n'), invariants, [], [], [], performance.now() - start, stats, null, 'unavailable');
      }
      encoding = coloured;
    } else {
      // A property naming a place outside the net would encode to a vacuous
      // violation predicate (`false` proves anything). Refuse, as the coloured path
      // does, so a mis-named place never silently certifies.
      const unresolved = unresolvedPropertyPlace(flatNet, this._property);
      if (unresolved != null) {
        const reason =
          `property names a place that does not resolve in the net ('${unresolved}'); ` +
          'refusing to certify (the encoding would be vacuously proven)';
        report.push('  Status: UNKNOWN (unresolved property place)\n');
        report.push('=== RESULT ===\n');
        report.push(`UNKNOWN: ${reason}`);
        return buildResult({ type: 'unknown', reason }, report.join('\n'), invariants, [], [], [], performance.now() - start, stats, null, 'unavailable');
      }
      // C3: request the refutation proof the replay decoder reads.
      encoding = encodeNet(flatNet, this._initialMarking, this._property, invariants, {
        sinkPlaces: this._sinkPlaces,
        produceProofs: this._counterexampleReplay,
        conditionalSinks: this._conditionalSinks,
        stateEquation: this._stateEquation,
      });
      if (this._stateEquation) {
        report.push(`  State equation: encoded over ${encoding.counterCount} firing counters (VER-016)`);
      }
    }
    if (this._stateEquation && colouredPlan != null) {
      report.push('  State equation: not applied (name-coloured encoding)');
    }
    const queryResult = await runZ3Spacer(
      solver, this._timeoutMs, encoding.smt2, colouredPlan != null ? 'horn-coloured' : 'horn',
    );

    switch (queryResult.type) {
      case 'proven': {
        // Guard against silent vacuous proofs (VER-006): in `ignore` mode the
        // encoding does not model env injection, so env-gated transitions never
        // fire and ANY safety bound is trivially "proven". Refuse to certify —
        // downgrade to UNKNOWN with actionable guidance.
        if (this._environmentPlaces.size > 0 && this._environmentMode.type === 'ignore') {
          const reason = IGNORE_MODE_VACUITY_REASON;
          report.push(`  Status: UNSAT, but vacuous under ignore mode\n`);
          report.push('=== RESULT ===\n');
          report.push(`UNKNOWN: ${reason}`);
          return buildResult({ type: 'unknown', reason }, report.join('\n'), invariants, [], [], [], performance.now() - start, stats);
        }

        report.push('  Status: UNSAT (property holds)');

        // Independent certificate check (flat count encoding only): re-validate
        // the IC3 certificate in a second z3 run against the UNSTRENGTHENED step
        // relation, so neither a Spacer/encoder defect nor a wrong-but-
        // validated-looking invariant strengthening can certify a false PROVEN.
        // The coloured ν-encoding has its own state shape and is out of scope;
        // structural proofs return before this point.
        if (colouredPlan != null) {
          report.push('  Certificate check: not applicable (name-coloured encoding)');
        } else if (!this._certificateCheck) {
          report.push('  Certificate check: not applicable (disabled)');
        } else {
          const certificate = await checkCertificate(
            queryResult.invariantFormula, flatNet, this._initialMarking,
            this._property, invariants, this._sinkPlaces, solver, this._timeoutMs,
            this._conditionalSinks, this._stateEquation,
          );
          const reason = certificateDowngradeReason(certificate);
          if (reason != null) {
            report.push('  Certificate check: FAILED');
            if (certificate.type !== 'passed' && certificate.invariant != null) {
              report.push('  Uncertified invariant:');
              for (const line of certificate.invariant.split('\n')) report.push(`    ${line}`);
            }
            report.push('');
            report.push('=== RESULT ===\n');
            report.push(`UNKNOWN: ${reason}`);
            return buildResult({ type: 'unknown', reason }, report.join('\n'), invariants, [], [], [], performance.now() - start, stats);
          }
          report.push('  Certificate check: PASSED (init, consecution, safety)');
        }
        report.push('');

        // The inductive invariant is the (define-fun …) block of the model,
        // verbatim (the certificate the check above re-validated).
        const formula = queryResult.invariantFormula;
        const discoveredInvariants: string[] = formula != null ? [formula] : [];

        // Phase 5: Inductive invariant
        if (formula != null) {
          report.push('Phase 5: Inductive invariant (discovered by IC3)');
          report.push('  Spacer synthesized:');
          for (const line of formula.split('\n')) report.push(`    ${line}`);
          report.push('  This formula is INDUCTIVE: preserved by all transitions.');
          report.push('');
        }

        report.push('=== RESULT ===\n');
        report.push(`PROVEN (IC3/PDR): ${propDesc}`);
        report.push('  Z3 Spacer proved no reachable state violates the property.');
        report.push('  NOTE: Verification ignores timing constraints.');
        report.push('  An untimed proof is STRONGER than a timed one (timing only restricts behavior).');

        return this.applyNuGuard(buildResult(
          { type: 'proven', method: 'IC3/PDR', inductiveInvariant: formula },
          report.join('\n'), invariants, discoveredInvariants, [], [],
          performance.now() - start,
          stats,
        ), hasMatch, nuBounded, colouredPlan != null);
      }

      case 'violated': {
        report.push('  Status: SAT (counterexample found)\n');

        const decoded = decode(queryResult.answer, flatNet, encoding.counterCount);
        if (decoded.note != null) report.push(`  Counterexample decoding: ${decoded.note}`);

        // C3/C4: abstract counterexample replay (flat count encoding only — the
        // coloured ν-encoding's state shape is outside the replayer's scope). The
        // decoder collects the ground Reachable states of the refutation proof as
        // an order-free set; the replay recovers a genuine firing order.
        let confirmed: boolean | null = null;
        let trace: readonly MarkingState[] = [...decoded.states];
        let transitions: readonly string[] = [];
        let replayed = false;
        if (colouredPlan == null && this._counterexampleReplay) {
          const assessment = assessCounterexample(
            flatNet, this._initialMarking, decoded.states, this._property, this._sinkPlaces,
            this._conditionalSinks,
          );
          if (assessment.kind === 'confirmed') {
            confirmed = true;
            replayed = true;
            trace = assessment.trace;
            transitions = assessment.firings;
            report.push('  Counterexample replay: CONFIRMED (abstract chain M0 -> bad re-executed)');
          } else if (assessment.kind === 'unconfirmed') {
            // The replay could not run to completion (nothing decoded, or the
            // search hit a budget). Spacer's answer stands on its own — only a
            // completed search that found no chain may withdraw it.
            confirmed = false;
            report.push(`  Counterexample replay: UNCONFIRMED (${assessment.note})`);
            report.push("  The verdict rests on Spacer's answer.");
          } else {
            // The search completed and no abstract chain reaches a violating
            // marking: a spurious counterexample of the untimed+value-blind
            // over-approximation, or a decoder mismatch. Never keep an
            // unreplayable VIOLATED — downgrade, with raw + decoded evidence.
            report.push('  Counterexample replay: FAILED');
            report.push(`  Decoded states (order-free set, ${decoded.states.size}):`);
            for (const m of decoded.states) report.push(`    ${m}`);
            report.push(`  Raw Z3 answer: ${truncate(queryResult.answer, 2000)}`);
            report.push('');
            report.push('=== RESULT ===\n');
            report.push(`UNKNOWN: ${assessment.reason}`);
            // The replay APPLIED and refuted the trace, so `false` — not `null`,
            // which is reserved for "the replay did not apply".
            return buildResult(
              { type: 'unknown', reason: assessment.reason },
              report.join('\n'), invariants, [], [], [],
              performance.now() - start,
              stats,
              false,
            );
          }
        }

        report.push('=== RESULT ===\n');
        report.push(`VIOLATED: ${propDesc}`);
        if (trace.length > 0) {
          report.push(`  Counterexample trace (${replayed ? 'replay order, ' : 'proof order, '}${trace.length} states):`);
          for (let i = 0; i < trace.length; i++) report.push(`    ${i}: ${trace[i]}`);
        }
        if (transitions.length > 0) report.push(`  Firing sequence: ${transitions.join(' -> ')}`);
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
          stats,
        );
      }
    }
  }

  /**
   * Runs the linear state-equation bound query (VER-015) and re-checks its answer in
   * exact integer arithmetic. Returns the bound as the report prints it when one
   * separates the violation, `null` otherwise (no bound, solver inconclusive, or a
   * model that failed the re-check — each named in the report). Never the last word:
   * `null` hands over to the fixpoint query.
   */
  private async linearBoundProof(flatNet: FlatNet, solver: Z3Solver, report: string[]): Promise<string | null> {
    const script = encodeLinearBound(flatNet, this._initialMarking, this._property);
    if (script == null) return null;
    let reply;
    try {
      reply = await runZ3Text(solver, script, 'bound', this._timeoutMs, []);
    } catch (e: any) {
      rethrowIfProgrammingError(e);
      report.push(`  Linear state-equation bound: inconclusive (${String(e?.message ?? e)})`);
      return null;
    }
    const stdout = reply.stdout.trim();
    switch (classifyFirstLine(stdout)) {
      case 'sat': {
        const y = decodeLinearBound(stdout, flatNet.places.length);
        const bound = y == null ? null : checkLinearBoundExact(flatNet, this._initialMarking, this._property, y);
        if (bound == null) {
          report.push('  Linear state-equation bound: inconclusive (solver model failed the exact re-check)');
          return null;
        }
        const rendered = `${formatLinearBound(flatNet, bound)}; violation needs ${formatLinearDemand(flatNet, this._property, bound)}`;
        report.push(`  Linear state-equation bound: ${rendered}`);
        report.push('  Status: bound excludes every violating marking (re-checked in exact integer arithmetic)');
        return rendered;
      }
      case 'unsat':
        report.push('  Linear state-equation bound: none separates the violation');
        return null;
      case 'unknown':
        report.push('  Linear state-equation bound: inconclusive (Z3 answered unknown)');
        return null;
      default:
        report.push(`  Linear state-equation bound: inconclusive (${failureReason(reply, timeoutBudget(this._timeoutMs))})`);
        return null;
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
 * terminates-at-sink, joined-or-dead-lettered) are not: their violation involves
 * the absence of enabled transitions, which the name-blind over-approximation
 * distorts (NU-050).
 */
function isReachabilitySafety(property: SmtProperty): boolean {
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound':
    case 'mutual-exclusion':
    case 'unreachable':
      return true;
    case 'deadlock-free':
    case 'terminates-at-sink':
    case 'joined-or-dead-lettered':
      return false;
  }
}

/**
 * Assessment of a decoded counterexample by abstract replay (C4). Pure and free
 * of Z3 types, so the verdict mapping is unit-testable without booting the WASM
 * solver — the mirror of {@link certificateDowngradeReason}.
 */
export type ReplayAssessment =
  /** The decoded states chain into an abstract run reaching the violation. */
  | {
      readonly kind: 'confirmed';
      readonly trace: readonly MarkingState[];
      readonly firings: readonly string[];
    }
  /** The replay could not complete; the VIOLATED verdict stands, unconfirmed. */
  | { readonly kind: 'unconfirmed'; readonly note: string }
  /** No firing chain exists at all; the verdict must not be trusted. */
  | { readonly kind: 'downgraded'; readonly reason: string };

/**
 * Maps a decoded counterexample to its replay assessment. Only a completed
 * search that found no chain (`no-chain`) downgrades: nothing decoded, a
 * truncated search (node/segment budget, `M₀` absent from the decoded set) and
 * a replayer crash all leave the verdict `violated` but unconfirmed, because
 * none of them is evidence that the counterexample is spurious.
 */
export function assessCounterexample(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  decodedStates: ReadonlySet<MarkingState>,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[] = [],
): ReplayAssessment {
  if (decodedStates.size === 0) {
    return {
      kind: 'unconfirmed',
      note: 'no counterexample states could be decoded from the Spacer answer, ' +
        'so the abstract replay could not run',
    };
  }

  let outcome: ReplayOutcome;
  try {
    outcome = replayCounterexample(
      flatNet,
      vectorize(initialMarking, flatNet),
      [...decodedStates].map(m => vectorize(m, flatNet)),
      property,
      sinkPlaces,
      {},
      conditionalSinks,
    );
  } catch (e: any) {
    // A replay that ran out of room degrades like a truncated search — it never
    // withdraws a verdict on its own. A replayer *defect* is not that: it would be
    // indistinguishable from an exhausted search and so invisible forever, which
    // is why a TypeError propagates and a RangeError (a deep net overflowing the
    // stack) stays the capacity verdict it really is.
    rethrowIfProgrammingError(e);
    outcome = { kind: 'exhausted', reason: `replay threw: ${e?.message ?? e}`, nodesExplored: 0 };
  }

  switch (outcome.kind) {
    case 'confirmed':
      return {
        kind: 'confirmed',
        trace: outcome.states.map(s => toMarkingState(s, flatNet)),
        firings: outcome.steps.map(stepName),
      };
    case 'exhausted':
      return { kind: 'unconfirmed', note: `abstract replay did not complete: ${outcome.reason}` };
    case 'no-chain':
      return {
        kind: 'downgraded',
        reason: 'counterexample replay found no firing chain to the violation under ' +
          'the abstract semantics, so VIOLATED is withheld',
      };
  }
}

/**
 * Maps a certificate-check outcome to the UNKNOWN downgrade reason, or null
 * when the PROVEN verdict stands. Pure (no Z3 involvement) so the verdict
 * plumbing is unit-testable without booting the WASM solver.
 */
export function certificateDowngradeReason(outcome: CertificateCheckOutcome): string | null {
  switch (outcome.type) {
    case 'passed':
      return null;
    case 'failed':
      return `certificate check failed: ${outcome.vc} was not UNSAT - ${outcome.detail}; ` +
        'the IC3 certificate could not be independently re-validated against the ' +
        'unstrengthened step relation, so PROVEN is withheld';
    case 'unavailable':
      return `certificate check could not run: ${outcome.reason}; ` +
        'PROVEN is withheld without an independently validated certificate';
  }
}

/** The scripts {@link SmtVerifier.encodeScripts} reports. */
export interface EncodedScripts {
  /** The HORN query, flat or name-coloured. */
  readonly horn: string;
  /** The certificate-check script around {@link placeholderCertificate}; `null` for the name-coloured encoding. */
  readonly certificate: string | null;
  /** Whether `horn` is the name-coloured encoding. */
  readonly coloured: boolean;
  /**
   * The linear state-equation bound query (VER-015), or `null` for a property with
   * no linear demand (the quiescence properties).
   */
  readonly bound: string | null;
}

/**
 * `(define-fun Reachable ((x!0 Int) …) Bool true)`: the certificate stand-in the
 * golden certificate scripts are built around (a real certificate is solver output
 * and never part of a golden).
 */
export function placeholderCertificate(placeCount: number): string {
  const params: string[] = [];
  for (let i = 0; i < placeCount; i++) params.push(`(x!${i} Int)`);
  return `(define-fun Reachable (${params.join(' ')}) Bool\n    true)`;
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
 * The name of the first place the property names that the NET does not declare,
 * or `null`. The flat-net twin below answers the same question after flattening;
 * this one can be asked before any route runs, which is where it has to be.
 *
 * A property naming a place the net does not have is not a question about the
 * net: every route answers it vacuously and each in its own way — the flat
 * encoder would emit a `false` violation term that proves anything, the linear
 * bound would drop the conjunct and separate a strictly stronger demand, the
 * enumeration route would find no class marking a place that cannot be marked.
 * All three then report `proven`. Refusing once, before any of them, is the only
 * way the refusal cannot be routed around.
 */
function unresolvedPropertyPlaceInNet(net: PetriNet, property: SmtProperty): string | null {
  const declared = new Set<string>();
  for (const p of net.places) declared.add(p.name);
  for (const place of propertyPlaces(property)) {
    if (!declared.has(place.name)) return place.name;
  }
  return null;
}

/**
 * Whether Commoner's theorem governs this net, so a siphon/trap answer may be
 * turned into a `proven`.
 *
 * The theorem — every siphon contains an initially marked trap implies
 * deadlock-freedom — is about an **ordinary** net, one where the only reason a
 * transition is disabled is an input place with too few tokens. The siphon and
 * trap fixpoints are computed from the pre/post vectors alone and never read
 * `readPlaces`, `inhibitorPlaces`, `resetPlaces` or `consumeAll`, so on a net
 * carrying any of those the analysis answers a question about a DIFFERENT,
 * strictly more permissive net: dropping a read or inhibitor arc can only add
 * firings, which is the wrong direction for a deadlock proof. An arc weight above
 * one is the same problem — a place holding one token satisfies `m >= 1` but not
 * `exactly(2)`.
 *
 * Each of these was demonstrated to produce a `proven` for a net both executors
 * run to a dead marking: `t1: one(a) read(g) -> g` with `t2: one(g) -> a` from
 * `{a:1}`; `t: exactly(2, a) -> a` from `{a:1}`; `t: one(a) inhibitor(b) -> a`
 * from `{a:1, b:1}`. Refusing the shortcut costs a fixpoint query and sends those
 * nets to a route that models what disables them.
 */
function commonerApplies(flatNet: FlatNet): boolean {
  for (const ft of flatNet.transitions) {
    if (ft.readPlaces.length > 0 || ft.inhibitorPlaces.length > 0 || ft.resetPlaces.length > 0) return false;
    if (ft.consumeAll.some(Boolean)) return false;
    if (ft.preVector.some(w => w > 1)) return false;
  }
  return true;
}

/** The places a property names, whichever kind it is. */
function propertyPlaces(property: SmtProperty): Place<any>[] {
  switch (property.type) {
    case 'deadlock-free': return [];
    case 'terminates-at-sink': return [];
    case 'mutual-exclusion': return [property.p1, property.p2];
    case 'place-bound': return [property.place];
    case 'branch-place-bound': return [property.place];
    case 'unreachable': return [...property.places];
    case 'joined-or-dead-lettered': return [property.pending];
  }
}

/** The name of the first place the property names that is not in the flat net, or `null`. */
function unresolvedPropertyPlace(flatNet: FlatNet, property: SmtProperty): string | null {
  const named: Place<any>[] = (() => {
    switch (property.type) {
      case 'deadlock-free': return [];
      case 'terminates-at-sink': return [];
      case 'mutual-exclusion': return [property.p1, property.p2];
      case 'place-bound': return [property.place];
      case 'branch-place-bound': return [property.place];
      case 'unreachable': return [...property.places];
      case 'joined-or-dead-lettered': return [property.pending];
    }
  })();
  for (const place of named) {
    if (!flatNet.placeIndex.has(place.name)) return place.name;
  }
  return null;
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
  // Empty support renders as `0 = c`, matching Java and Rust — the line is byte-diffed.
  return `${parts.length === 0 ? '0' : parts.join(' + ')} = ${inv.constant}`;
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
  route: VerificationRoute = 'smt',
): SmtVerificationResult {
  return { verdict, route, report, invariants, discoveredInvariants, counterexampleTrace: trace, counterexampleTransitions: transitions, counterexampleConfirmed, elapsedMs, statistics };
}
