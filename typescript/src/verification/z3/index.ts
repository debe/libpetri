export { createSpacerRunner } from './spacer-runner.js';
export type { SpacerContext, QueryResult, QueryProven, QueryViolated, QueryUnknown } from './spacer-runner.js';
export { encode } from './smt-encoder.js';
export type { EncodingResult } from './smt-encoder.js';
export { checkCertificate } from './certificate-checker.js';
export type { CertificateCheckOutcome, CertificateVc } from './certificate-checker.js';
export { decode, describeDecodeFailure } from './counterexample-decoder.js';
export type { DecodedTrace, DecodeFailure } from './counterexample-decoder.js';
// Only the replay entry point is package API; the abstract-semantics primitives
// (enabledA/fireA/injectA/successors/satisfiesBad, vectorize/toMarkingState,
// stateKey/stepName) and the encoder's sub-builders stay module-internal —
// tests import them from their defining module.
export { replayCounterexample } from './abstract-replayer.js';
export type {
  AbstractState, ReplayStep, ReplayOptions, ReplayOutcome,
} from './abstract-replayer.js';
