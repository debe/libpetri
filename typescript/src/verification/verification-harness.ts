import type { PetriNet } from '../core/petri-net.js';
import type { Token } from '../core/token.js';
import type { SmtProperty } from './smt-property.js';
import type { SmtVerificationResult } from './smt-verification-result.js';
import { isProven, isViolated } from './smt-verification-result.js';

/**
 * Token-source supplier used by the verification harness to seed a synthetic
 * environment place for a given input port, per
 * `spec/11-modular-composition.md` requirement **MOD-051** AC #3.
 *
 * The supplier's presence is what bounds the input behavior in the synthetic
 * harness; it is invoked once at synthetic-net construction time so that
 * supplier-side errors surface eagerly, not at verification time. The
 * concrete token value is not consumed by the verifier itself (which operates
 * on the integer marking projection per [VER-004]); it merely materialises
 * the seed token type and surfaces user errors.
 */
export type TokenSupplier = () => Token<unknown>;

/**
 * Harness driving local property verification of a subnet definition per
 * `spec/11-modular-composition.md` requirement **MOD-051**.
 *
 * The harness is a value carrier consumed by
 * {@link import('../core/subnet-def.js').SubnetDef.verify}. It supplies the
 * three pieces of information needed to wrap a subnet in a synthetic
 * enclosing net for verification:
 *
 * 1. A {@link params} value of the subnet's parameter type.
 * 2. A {@link portInputGenerators} map from **input port name** (original /
 *    pre-prefix) to a {@link TokenSupplier}. The supplier's presence is what
 *    bounds the input behavior in the synthetic harness; the supplier is
 *    invoked at synthetic-net construction time when the harness wires up the
 *    {@link import('../core/place.js').EnvironmentPlace} associated with the
 *    port.
 * 3. A set of {@link properties} to check (per [VER-002] /
 *    {@link SmtProperty}).
 *
 * Each entry in {@link portInputGenerators} MUST correspond to an input or
 * in-out port declared on the subnet's interface. Output-only ports never
 * appear in the generator map; instead, the harness wires them to a synthetic
 * observation place visible to the verifier.
 *
 * The map and property collection accept either the canonical
 * `Map`/`ReadonlySet` form or a plain `Record`/`readonly array` for ergonomic
 * inline construction; `SubnetDef.verify` normalises both.
 *
 * @typeParam P parameter type carried through to the subnet under test
 */
export interface VerificationHarness<P = void> {
  /**
   * Parameter value supplied to
   * {@link import('../core/subnet-def.js').SubnetDef.instantiate} for the
   * system-under-test instance. Use `undefined` (or `null`) for `P = void`.
   */
  readonly params: P;

  /**
   * Map (or `Record`) from **input port name** to a {@link TokenSupplier} that
   * seeds the synthetic environment place for that port. Output-only ports
   * MUST NOT appear; in-out ports MUST appear (mirrors the Java harness).
   */
  readonly portInputGenerators:
    | ReadonlyMap<string, TokenSupplier>
    | Readonly<Record<string, TokenSupplier>>;

  /**
   * Safety properties to check on the synthetic enclosing net per
   * {@link SmtProperty}. An empty collection is permitted but yields an empty
   * {@link VerificationResult.perProperty}.
   */
  readonly properties: ReadonlySet<SmtProperty> | readonly SmtProperty[];

}

/**
 * Aggregated outcome of a
 * {@link import('../core/subnet-def.js').SubnetDef.verify} invocation per
 * `spec/11-modular-composition.md` requirement **MOD-051**.
 *
 * The verifier is invoked once per {@link SmtProperty} declared in the
 * harness; each invocation produces an {@link SmtVerificationResult}. This
 * record carries the per-property results plus the synthetic enclosing net
 * that was constructed for verification (useful for diagnostic output and
 * tooling to render the harness wiring).
 */
export interface VerificationResult {
  /**
   * The synthetic enclosing net assembled by `SubnetDef.verify(...)`: the
   * renamed body of the subnet under test, with each input port bound to a
   * synthetic environment place and each output port bound to a synthetic
   * observation place.
   */
  readonly syntheticNet: PetriNet;

  /**
   * Per-property verification results, in the iteration order of the
   * harness's {@link VerificationHarness.properties} collection.
   */
  readonly perProperty: ReadonlyMap<SmtProperty, SmtVerificationResult>;

  /**
   * Returns true when every property in the harness was proven safe.
   * An empty harness (no properties) returns `true` vacuously.
   */
  allProven(): boolean;

  /**
   * Returns true when at least one property was violated (counter-example
   * found).
   */
  anyViolated(): boolean;
}

/**
 * @internal Builds a {@link VerificationResult} value from the per-property
 * map and synthetic net. The resulting object is structurally immutable; the
 * `perProperty` map is wrapped in a defensive copy so callers cannot mutate
 * the verifier's view through retained map references.
 */
export function buildVerificationResult(
  syntheticNet: PetriNet,
  perProperty: ReadonlyMap<SmtProperty, SmtVerificationResult>,
): VerificationResult {
  const frozen = new Map(perProperty);
  return {
    syntheticNet,
    perProperty: frozen,
    allProven(): boolean {
      for (const r of frozen.values()) {
        if (!isProven(r)) return false;
      }
      return true;
    },
    anyViolated(): boolean {
      for (const r of frozen.values()) {
        if (isViolated(r)) return true;
      }
      return false;
    },
  };
}

/**
 * @internal Normalises {@link VerificationHarness.portInputGenerators} to a
 * canonical `Map<string, TokenSupplier>` regardless of whether the caller
 * supplied a `Map` or a `Record`. Iteration order is preserved.
 */
export function normaliseGenerators(
  generators: VerificationHarness<unknown>['portInputGenerators'],
): Map<string, TokenSupplier> {
  if (generators instanceof Map) return new Map(generators);
  return new Map(Object.entries(generators));
}

/**
 * @internal Normalises {@link VerificationHarness.properties} to an array of
 * {@link SmtProperty} regardless of whether the caller supplied a `Set` or an
 * array. Iteration order is preserved.
 */
export function normaliseProperties(
  properties: VerificationHarness<unknown>['properties'],
): SmtProperty[] {
  if (Array.isArray(properties)) return [...properties];
  return [...(properties as ReadonlySet<SmtProperty>)];
}
