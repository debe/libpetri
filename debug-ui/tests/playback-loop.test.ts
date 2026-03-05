/**
 * Unit tests for playback delay calculation.
 */
import { describe, it, expect } from 'vitest';
import { calculatePlaybackDelay } from '../src/net/actions/playback.js';
import { CONFIG } from '../src/net/types.js';

describe('calculatePlaybackDelay', () => {
  it('1x speed returns base delay (50ms)', () => {
    expect(calculatePlaybackDelay(1)).toBe(50);
  });

  it('2x speed returns half base delay (25ms)', () => {
    expect(calculatePlaybackDelay(2)).toBe(25);
  });

  it('4x speed returns 12.5ms (above min, no clamp)', () => {
    expect(calculatePlaybackDelay(4)).toBe(12.5);
  });

  it('8x speed clamps to minPlaybackDelay', () => {
    // 50 / 8 = 6.25, clamped to 10
    expect(calculatePlaybackDelay(8)).toBe(CONFIG.minPlaybackDelay);
  });

  it('0.5x speed returns double base delay (100ms)', () => {
    expect(calculatePlaybackDelay(0.5)).toBe(100);
  });

  it('0.1x speed returns 500ms (within max)', () => {
    expect(calculatePlaybackDelay(0.1)).toBe(500);
  });

  it('very slow speed clamps to maxPlaybackDelay', () => {
    // 50 / 0.01 = 5000, clamped to 2000
    expect(calculatePlaybackDelay(0.01)).toBe(CONFIG.maxPlaybackDelay);
  });

  it('result is always >= minPlaybackDelay', () => {
    for (const speed of [1, 2, 4, 8, 16, 100]) {
      expect(calculatePlaybackDelay(speed)).toBeGreaterThanOrEqual(CONFIG.minPlaybackDelay);
    }
  });

  it('result is always <= maxPlaybackDelay', () => {
    for (const speed of [0.001, 0.01, 0.1, 0.5]) {
      expect(calculatePlaybackDelay(speed)).toBeLessThanOrEqual(CONFIG.maxPlaybackDelay);
    }
  });
});
