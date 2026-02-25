/**
 * Error thrown when a transition's output doesn't satisfy its declared Out spec.
 */
export class OutViolationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'OutViolationError';
  }
}
