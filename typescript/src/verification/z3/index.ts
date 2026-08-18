export { createSpacerRunner } from './spacer-runner.js';
export type { SpacerContext, QueryResult, QueryProven, QueryViolated, QueryUnknown } from './spacer-runner.js';
export { encode, encodeStepRelation, encodePropertyViolation, encodeInvariantConstraints } from './smt-encoder.js';
export type { EncodingResult } from './smt-encoder.js';
export { checkCertificate } from './certificate-checker.js';
export type { CertificateCheckOutcome } from './certificate-checker.js';
export { decode, describeDecodeFailure } from './counterexample-decoder.js';
export type { DecodedTrace, DecodeFailure } from './counterexample-decoder.js';
export {
  replayCounterexample, enabledA, fireA, injectA, successors, satisfiesBad,
  vectorize, toMarkingState, stateKey, stepName,
} from './abstract-replayer.js';
export type {
  AbstractState, ReplayStep, ReplayOptions, ReplayOutcome, Successor,
} from './abstract-replayer.js';
