/**
 * The abstract **name-partition** layer for the ν-aware state class graph
 * (NU-050, Route B).
 *
 * The plain {@link StateClassGraph} is name-blind: a marking is a per-place token
 * count, so a ν-join fires whenever the counts allow, ignoring whether the
 * consumed tokens share a correlation name. This carries, beside the count
 * marking, an abstract partition of the correlation tokens into name-symbols. A
 * `Sym` is an opaque identity only (NU-001) — the analyzer never evaluates the
 * runtime name projection. {@link NameMarking.canonicalKey} quotients markings
 * that differ only by a permutation of symbols (the raw ids never appear in a
 * key), keeping the graph finite when the live-name count is structurally
 * bounded. The key string format matches the Rust and Java implementations.
 */

export type Sym = number;

export class NameMarking {
  // place name -> (symbol -> count). Only coloured places appear; a place's
  // total here equals its count in the base MarkingState.
  private readonly perPlace: Map<string, Map<Sym, number>>;

  constructor(perPlace?: Map<string, Map<Sym, number>>) {
    this.perPlace = perPlace ?? new Map();
  }

  copy(): NameMarking {
    const p = new Map<string, Map<Sym, number>>();
    for (const [place, syms] of this.perPlace) {
      p.set(place, new Map(syms));
    }
    return new NameMarking(p);
  }

  add(place: string, sym: Sym, count: number): void {
    if (count === 0) return;
    let syms = this.perPlace.get(place);
    if (!syms) {
      syms = new Map();
      this.perPlace.set(place, syms);
    }
    syms.set(sym, (syms.get(sym) ?? 0) + count);
  }

  /** Removes `count` of `sym` from `place`; returns false (unchanged) if fewer present. */
  remove(place: string, sym: Sym, count: number): boolean {
    const syms = this.perPlace.get(place);
    if (!syms) return false;
    const have = syms.get(sym);
    if (have === undefined || have < count) return false;
    const left = have - count;
    if (left === 0) {
      syms.delete(sym);
      if (syms.size === 0) this.perPlace.delete(place);
    } else {
      syms.set(sym, left);
    }
    return true;
  }

  countOf(place: string, sym: Sym): number {
    return this.perPlace.get(place)?.get(sym) ?? 0;
  }

  symbolsIn(place: string): Sym[] {
    const syms = this.perPlace.get(place);
    return syms ? [...syms.keys()] : [];
  }

  private liveSymbols(): Sym[] {
    const all = new Set<Sym>();
    for (const syms of this.perPlace.values()) {
      for (const s of syms.keys()) all.add(s);
    }
    return [...all];
  }

  /**
   * Symmetry-canonical key over `colouredOrder` (the finiteness mechanism). Two
   * markings differing only by a permutation of symbols produce an identical key
   * (NU-001). Each symbol's signature is its count vector over `colouredOrder`;
   * symbols are ranked by (signature, raw id) and emitted per place as a
   * rank-multiset — a complete invariant of the symbol-permutation orbit.
   */
  canonicalKey(colouredOrder: readonly string[]): string {
    const signature = (s: Sym): number[] => colouredOrder.map(p => this.countOf(p, s));
    const ranked = this.liveSymbols().map(s => ({ sig: signature(s), sym: s }));
    ranked.sort((a, b) => {
      const c = compareNumberArrays(a.sig, b.sig);
      return c !== 0 ? c : a.sym - b.sym;
    });
    const rankOf = new Map<Sym, number>();
    ranked.forEach((r, i) => rankOf.set(r.sym, i));

    const parts = colouredOrder.map(p => {
      const syms = this.perPlace.get(p);
      const entries: Array<[number, number]> = [];
      if (syms) {
        for (const [s, c] of syms) entries.push([rankOf.get(s)!, c]);
      }
      entries.sort((a, b) => (a[0] !== b[0] ? a[0] - b[0] : a[1] - b[1]));
      const inner = entries.map(([r, c]) => `${r}x${c}`).join(',');
      return `${p}:{${inner}}`;
    });
    return parts.join('#');
  }
}

function compareNumberArrays(a: readonly number[], b: readonly number[]): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a[i]! !== b[i]!) return a[i]! - b[i]!;
  }
  return a.length - b.length;
}
