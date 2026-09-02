/**
 * Formal verification for Petri nets via IC3/PDR (Z3 Spacer).
 *
 * Provides the 5-phase verification pipeline: flatten → structural pre-check (siphon/trap)
 * → P-invariant computation → CHC encoding → Z3 Spacer query. Entry point: `SmtVerifier`.
 *
 * Also exports sub-modules for encoding, invariants, and Z3 integration.
 *
 * @module verification
 */
export { MarkingState, MarkingStateBuilder } from './marking-state.js';
export * from './encoding/index.js';
export * from './invariant/index.js';
export * from './smt-property.js';
export * from './smt-verification-result.js';
export { SmtVerifier, placeholderCertificate } from './smt-verifier.js';
export type { EncodedScripts } from './smt-verifier.js';
export * from './z3/index.js';
export * from './analysis/index.js';
export type { VerificationHarness, VerificationResult, TokenSupplier } from './verification-harness.js';
