/**
 * Shared contract of the design harness. Every module (gates, sensors, artifact, equivalence, CLI)
 * speaks these types; nothing else crosses module boundaries.
 *
 * Evidence for every design decision here is in research/net-metrics/lab/JOURNAL.md (rounds 1–17).
 */
import type { PetriNet, SubnetDef } from 'libpetri';

/** A property the design must satisfy, stated over place names so it survives scaling. */
export type PropertySpec =
  /** Strict deadlock freedom: every quiescent marking holds tokens only in declared sinks. */
  | { readonly kind: 'deadlockFree' }
  /**
   * Accounting: at quiescence the outcome places hold exactly as many tokens as the declared
   * sources supplied (every input answered or explicitly aborted; none lost). `perUnit` is how many
   * outcome tokens one unit of the scale produces (default 1). Round 6/15: deadlock freedom stays
   * green while a reset loses events; only this catches it.
   */
  | { readonly kind: 'accounting'; readonly outcomes: readonly string[]; readonly perUnit?: number }
  | { readonly kind: 'mutualExclusion'; readonly a: string; readonly b: string }
  | { readonly kind: 'placeBound'; readonly place: string; readonly bound: number }
  | { readonly kind: 'unreachable'; readonly places: readonly string[] };

export interface NamedProperty {
  readonly name: string;
  readonly spec: PropertySpec;
  /** True when the property can only hold under timing (round 8): the untimed routes cannot prove it. */
  readonly timingDependent?: boolean;
}

/**
 * What the design must do. Written by (or approved by) the developer; the agent never weakens it.
 */
export interface Contract {
  readonly name: string;
  /** Prose intent, shown in the artifact. */
  readonly intent: string;
  readonly properties: readonly NamedProperty[];
  /** Places where the net may legitimately rest. */
  readonly sinks: readonly string[];
  /**
   * Declared event sources: arrival-generator supply places or environment places. Round 15: env-
   * fedness cannot be inferred structurally; it must be declared.
   */
  readonly sources: readonly string[];
  /**
   * Environment inputs: places the design exposes for the outside world to inject into (customer
   * utterances, …). The design builds them as ordinary, initially empty places — how it reacts is up
   * to the design. For checking, the harness drives each matching place from its own arrival
   * generator: `tokens: 'k'` injects k tokens at scale k, a number injects that many at every scale.
   * Names may be patterns (`*` = any run of characters) for per-session inputs. The generators count
   * as sources for accounting.
   */
  readonly inputs?: ReadonlyArray<{ readonly place: string; readonly tokens: 'k' | number }>;
  /** Scales for the small-scope gate (round 17: every lab bug appeared at k = 1; name-blind resets need k = 2). */
  readonly scales?: readonly number[];
}

/**
 * ν verification configuration (NU-010, NU-040, NU-051), required for any net with match specs
 * (correlated joins).
 *
 * libpetri reads a transition that writes a join key without consuming a name as a fresh mint only
 * when the net declares it: listed in `mints`, or consuming a place listed in `budgets`. An
 * undeclared one keeps the net off both ν routes, and the verifier answers name-blind (sound, but
 * a quiescence property such as deadlockFree then comes back unknown).
 */
export interface NuConfig {
  /** Places whose tokens gate fresh-name minting (NU-040). A transition consuming one is a declared mint. */
  readonly budgets: readonly string[];
  /** Transitions whose action writes a name it minted with `freshName()` in that firing (NU-010). */
  readonly mints?: readonly string[];
  /** Intermediate places that carry a name from its mint to a join key (NU-051); declaring any switches the verifier to the EXTENDED fragment. */
  readonly carriers?: readonly string[];
  readonly fragmentMode?: 'base' | 'extended';
}

/** Per-subnet verification input for the compositional gate. */
export interface SubnetCheck {
  readonly def: SubnetDef<void>;
  /** Input port names to feed; each gets a generic token supplier. */
  readonly inputs: readonly string[];
  readonly properties: readonly NamedProperty[];
  /**
   * ν configuration for a subnet with match specs, in the subnet body's own place and transition
   * names (same shape as Candidate.nu). Without it a ν subnet is refused: no transition would be a
   * declared mint, so libpetri could answer only name-blind.
   */
  readonly nu?: NuConfig;
}

/** One design candidate, written as TypeScript by the agent. */
export interface Candidate {
  readonly name: string;
  /** One paragraph: what design choice distinguishes this candidate. */
  readonly rationale: string;
  /**
   * Builds the net at scale k (k units / events / copies — whatever the contract scales). Must use the
   * real libpetri builder API; actions may be omitted (the harness binds structure-only actions).
   * Returns the net and its initial marking as place-name → token count.
   */
  build(k: number): { readonly net: PetriNet; readonly marking: ReadonlyMap<string, number> };
  /** Subnets to verify in isolation (compositional gate). Optional. */
  readonly subnets?: readonly SubnetCheck[];
  /** ν verification configuration, required for any net with match specs; see {@link NuConfig}. */
  readonly nu?: NuConfig;
}

export type Verdict = 'proven' | 'violated' | 'unknown' | 'skipped';

export interface PropertyResult {
  readonly property: string;
  readonly verdict: Verdict;
  /** Which route decided (enumeration, smt, structural, nu-scg, …) or why it was skipped. */
  readonly route: string;
  readonly ms: number;
  /** Firing sequence of a counterexample, when violated. */
  readonly trace?: readonly string[];
  readonly note?: string;
}

export interface LintFinding {
  readonly rule:
    | 'dead-power-arc'          // reset/read/inhibitor on a place with no producer and no consumer (r12)
    | 'reset-across-subnet'     // reset from outside a subnet into its non-port place (r4, r9, r17)
    | 'reset-on-source-fed'     // reset on a place downstream of a declared source (r6, r15)
    | 'duplicate-input-arc'     // two input arcs on one place (r8)
    | 'nu-undeclared-carrier'   // ν join fed through intermediate transitions without carriers (r3)
    | 'encapsulation'           // any arc from outside a subnet into its internal place (r17)
    | 'build-error';            // the candidate does not build (libpetri rejected it, e.g. MOD-027 / CORE-030)
  readonly severity: 'error' | 'warning';
  readonly transition?: string;
  readonly place?: string;
  readonly message: string;
}

export interface GateReport {
  readonly lint: readonly LintFinding[];
  /** Small-scope gate: per scale, per property. */
  readonly smallScope: ReadonlyArray<{ readonly k: number; readonly results: readonly PropertyResult[] }>;
  /** Compositional gate: per subnet, per property; empty when the candidate declares no subnets. */
  readonly compositional: ReadonlyArray<{ readonly subnet: string; readonly results: readonly PropertyResult[] }>;
  /** True when no lint error and no gate result is violated or unknown. */
  readonly passed: boolean;
}

/**
 * Sensor profile. Only sensors that survived the lab (rounds 11–17) are here; size metrics appear
 * as context, never as quality signals.
 */
export interface SensorProfile {
  readonly size: { readonly places: number; readonly transitions: number; readonly arcs: number };
  readonly resets: {
    readonly count: number;
    /** Max places one transition resets (r9). */
    readonly blast: number;
    /** Other transitions touching a reset place (r9). */
    readonly reach: number;
    /** Resets on places that reachably hold > 1 token: name-blind under concurrency (r14). -1 = state space did not close. */
    readonly multiToken: number;
    /** Resets crossing a subnet boundary (r4, r13). */
    readonly crossSubnet: number;
  };
  /** Arcs from outside a subnet into its non-port places (r4, r17: blocks compositional proof). */
  readonly encapsulationViolations: number;
  /** Reset/inhibitor arcs on structurally unbounded places, after the self-guarded-latch rule (r7, r13, r14). -1 = z3 unavailable. */
  readonly essentialPowerArcs: number;
  /** Fraction of places structurally bounded (sub-invariants + latch rule). -1 = z3 unavailable. */
  readonly boundedFraction: number;
  /** Fraction of top-level transitions that are exact structural twins (r10, r15): a fold hint, not a score. */
  readonly undeclaredSymmetry: number;
  readonly routes: {
    /** Ordinary net: eligible for the structural siphon/trap route (r5, r13: only without sinks). */
    readonly ordinary: boolean;
    /** Untimed, no env places, no ν: eligible for exact enumeration (VER-017). */
    readonly enumerable: boolean;
    readonly nu: boolean;
    readonly timed: boolean;
  };
  /** Untimed state classes at k = 1 and k = 2, and their ratio: the per-unit multiplier (r2). */
  readonly stateGrowth: { readonly k1: number; readonly k2: number; readonly multiplier: number };
  /** Max non-immediate transitions enabled together (untimed graph, k = 1): timed-proof cost driver (r8). */
  readonly timedWidth: number;
}

export interface CandidateReport {
  readonly candidate: string;
  readonly rationale: string;
  readonly gates: GateReport;
  readonly sensors: SensorProfile;
  /** DOT of the candidate at k = 1, for the artifact and for the equivalence check. */
  readonly dot: string;
}

export interface DesignReport {
  readonly contract: Contract;
  readonly generatedAt: string;
  /** Iteration number of the design loop (live artifact shows history). */
  readonly iteration: number;
  readonly candidates: readonly CandidateReport[];
  /** Candidate names that pass all gates, ordered by the developer-facing comparison (not a score). */
  readonly passing: readonly string[];
}

/** Result of comparing an implementation's DOT export with the verified design's. */
export interface EquivalenceResult {
  readonly equal: boolean;
  /** Human-readable structural differences (places, transitions, arcs) when not equal. */
  readonly differences: readonly string[];
}
