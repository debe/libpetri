/**
 * @module open-net/result
 *
 * What `verifyOpenNet` returns ([VER-022]), and how a witness becomes a port trace.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import type { MarkingState } from '../marking-state.js';
import type { Verdict } from '../smt-verification-result.js';
import type { ClosedNet, EnvironmentStep } from './closure.js';

/** Which part of the contract a violation breaks. */
export type ContractViolationKind =
  /** A count clause: too few tokens across its places at quiescence with no terminal marked, or too many. */
  | 'clause'
  /** A token rests where the contract lets none rest: on an internal place, or on one only an unmarked terminal excuses. */
  | 'stranded'
  /** A run that never comes to rest: a reachable cycle. */
  | 'termination';

/** A token-count change on one contract place. */
export interface PortChange {
  readonly place: string;
  readonly delta: number;
}

/** A firing that touches the subnet's boundary: an environment step, or a change on a contract place. */
export interface PortStep {
  /** The firing's position in {@link ContractViolation.transitions}, counting from 1. */
  readonly step: number;
  readonly transition: string;
  /**
   * Set when the environment fired it: `arrival` or `decline` for an arrival group,
   * `transition` for one of the contract's environment transitions. `null` for the subnet.
   */
  readonly environment: EnvironmentStep['kind'] | null;
  /** Token changes on the contract's places, in the contract's order. */
  readonly changes: readonly PortChange[];
}

/** One broken part of the contract, with a firing sequence that breaks it. */
export interface ContractViolation {
  readonly kind: ContractViolationKind;
  /**
   * The clause's name, a stranded place's name, or `termination`. The SMT route reports one
   * stranding for the whole query, naming every stranded place comma-separated.
   */
  readonly subject: string;
  /** What was found, in words. */
  readonly detail: string;
  /** The firing sequence from the initial marking, environment transitions included. */
  readonly transitions: readonly string[];
  /** The marking before the first firing and after each one, when the route has them in order. */
  readonly markings: readonly MarkingState[];
  /** For `termination`, the index into {@link transitions} where the repeating cycle starts. */
  readonly cycleStart: number | null;
  /** The firings of {@link transitions} that touch the boundary. */
  readonly portTrace: readonly PortStep[];
  /**
   * Whether {@link transitions} is a real firing sequence in order. Always on the graph
   * route; on the SMT route it is the counterexample replay's outcome ([VER-003]).
   */
  readonly confirmed: boolean;
}

/** Which route decided the verdict. */
export type OpenNetRoute = 'enumeration' | 'smt';

/** The outcome of `verifyOpenNet`. */
export interface OpenNetResult {
  /** `proven`, `violated` (see {@link violations}), or `unknown` with the reason. */
  readonly verdict: Verdict;
  /**
   * Every broken part found. The graph route lists clauses in contract order, then stranded
   * places by name, then termination; the SMT route asks for stranding first, so it lists
   * that, then clauses in contract order, then termination.
   */
  readonly violations: readonly ContractViolation[];
  readonly route: OpenNetRoute;
  /** Classes the state-class graph explored; `0` when it was skipped. */
  readonly classCount: number;
  /** Whether the state-class graph closed within its budget. */
  readonly graphComplete: boolean;
  readonly report: string;
  /** The subnet closed by its environment: what every route verified. */
  readonly closedNet: PetriNet;
  readonly closedMarking: MarkingState;
  readonly elapsedMs: number;
}

/** A violation with its port trace, read off consecutive markings of the witness. */
export function contractViolation(
  closed: ClosedNet,
  tracedPlaces: readonly Place<any>[],
  violation: Omit<ContractViolation, 'portTrace'>,
): ContractViolation {
  const { transitions, markings } = violation;
  const portTrace: PortStep[] = [];
  if (markings.length === transitions.length + 1) {
    for (let i = 0; i < transitions.length; i++) {
      const before = markings[i]!;
      const after = markings[i + 1]!;
      const changes: PortChange[] = [];
      for (const p of tracedPlaces) {
        const delta = after.tokens(p) - before.tokens(p);
        if (delta !== 0) changes.push({ place: p.name, delta });
      }
      const env = closed.environment.get(transitions[i]!);
      if (changes.length > 0 || env !== undefined) {
        portTrace.push({ step: i + 1, transition: transitions[i]!, environment: env?.kind ?? null, changes });
      }
    }
  }
  return { ...violation, portTrace };
}
