/**
 * Analysis mode for environment places in state class graph construction.
 */
export type EnvironmentAnalysisMode =
  | { readonly type: 'always-available' }
  | { readonly type: 'bounded'; readonly maxTokens: number }
  | { readonly type: 'ignore' };

/** Assumes environment places always have sufficient tokens. */
export function alwaysAvailable(): EnvironmentAnalysisMode {
  return { type: 'always-available' };
}

/** Analyzes with a bounded number of tokens in environment places. */
export function bounded(maxTokens: number): EnvironmentAnalysisMode {
  if (maxTokens < 0) throw new Error('maxTokens must be non-negative');
  return { type: 'bounded', maxTokens };
}

/** Treats environment places as regular places (default). */
export function ignore(): EnvironmentAnalysisMode {
  return { type: 'ignore' };
}
