/**
 * Lightweight, debug-UI-facing descriptor of one composed subnet instance,
 * per `spec/11-modular-composition.md` requirement **MOD-041**.
 *
 * Created by `Instance.descriptor()` after a subnet has been instantiated and
 * (eventually) composed into an enclosing net. The descriptor is consumed by
 * the debug protocol's `Subscribed` response so clients can render collapsed
 * subnet clusters, per-instance highlighting, and "show only this instance"
 * filters in the debug UI.
 *
 * This interface carries only structural metadata — it is observability-only
 * and does not affect runtime behaviour of the composed flat net.
 */
export interface SubnetInstance {
  /** The instantiation prefix (e.g. `"buf1"` or `"outer/inner"` for nested instances). */
  readonly prefix: string;
  /** The originating subnet definition's name (null when not available). */
  readonly defName: string | null;
  /** Full prefixed transition names belonging to this instance. */
  readonly transitions: readonly string[];
  /** Full prefixed place names exposed as ports. */
  readonly exposedPlaces: readonly string[];
  /** The parameter value supplied at instantiation. */
  readonly params: unknown;
  /** The parent instance prefix when this is a nested instance, otherwise null. */
  readonly parentPrefix: string | null;
}
