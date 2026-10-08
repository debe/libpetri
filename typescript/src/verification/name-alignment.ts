/**
 * @module name-alignment
 *
 * The two name-alignment properties of [NU-055] as the routes see them: only Route B, the
 * name-partition state-class graph ([NU-050]), reads the name layer, so every other route gives
 * them no verdict. Internal: not re-exported from the package index.
 */
import { propertyDescription, type NameAligned, type QuiescentNameAligned, type SmtProperty } from './smt-property.js';

/** Whether `property` is `NameAligned` or `QuiescentNameAligned` ([NU-055]). */
export function isNameAlignment(property: SmtProperty): property is NameAligned | QuiescentNameAligned {
  return property.type === 'name-aligned' || property.type === 'quiescent-name-aligned';
}

/**
 * Why a route other than Route B gives `property` no verdict ([NU-055] AC4): the name-blind
 * routes do not see names. Also the closing clause of a Route B decline, after which nothing
 * else decides it.
 */
export function routeBOnlyReason(property: NameAligned | QuiescentNameAligned): string {
  return `${propertyDescription(property)} is decided only by the name-partition state-class graph ` +
    '(NU-055, Route B)';
}
