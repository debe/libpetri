import { describe, it, expect } from 'vitest';
import { place, environmentPlace } from '../../src/core/place.js';

describe('Place', () => {
  it('creates place with name', () => {
    const p = place<string>('MyPlace');
    expect(p.name).toBe('MyPlace');
  });

  it('uses name-based equality in maps', () => {
    const p1 = place<string>('A');
    const p2 = place<string>('A');

    const map = new Map<string, number>();
    map.set(p1.name, 1);
    expect(map.get(p2.name)).toBe(1);
  });

  it('different names are not equal', () => {
    const p1 = place('A');
    const p2 = place('B');
    expect(p1.name).not.toBe(p2.name);
  });
});

describe('EnvironmentPlace', () => {
  it('wraps a regular place', () => {
    const ep = environmentPlace<string>('External');
    expect(ep.place.name).toBe('External');
  });
});
