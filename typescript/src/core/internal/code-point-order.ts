/** A UTF-16 unit at which code-unit and code-point order can disagree. */
const HIGH_UNIT = /[\uD800-\uFFFF]/;

/**
 * Orders two strings by Unicode code point: negative when `a` sorts first, zero when equal,
 * positive otherwise.
 *
 * Every name order that reaches a report, witness trace, violation list or flat index uses
 * this, so a net prints and encodes the same on every host and in every implementation
 * ([VER-013], [VER-022]). `localeCompare` follows the host locale; `<` compares UTF-16 code
 * units, which puts a supplementary character (a surrogate pair from 0xD800) before one in
 * U+E000–U+FFFF. Rust's `str` order is code-point order; Java's `String` needs this fix too.
 *
 * ICU's fix-up (`uprv_strCompare`): only the first differing pair of units decides, and unit
 * and code-point order disagree only when both are ≥ 0xD800. For that pair, units ≥ 0xE000
 * move down by 0x800 and surrogates up by 0x2000. Exact for well-formed strings; a lone
 * surrogate, which no Rust `str` holds, sorts with the supplementary characters.
 *
 * Unless both strings hold a unit ≥ 0xD800 the engine's native comparison is the answer.
 * That fast path matters: a marking's `toString` in the class key and the canonical clock
 * order run it for every successor the state-class graph builds, and a JavaScript unit loop
 * made graph builds over long shared name prefixes up to a sixth slower.
 *
 * O(min(|a|, |b|)) unit comparisons, no allocation. The path check is O(1) for a string V8
 * stores one byte per unit, and a native scan otherwise.
 */
export function compareCodePoints(a: string, b: string): number {
  if (!HIGH_UNIT.test(a) || !HIGH_UNIT.test(b)) return a < b ? -1 : a > b ? 1 : 0;
  const n = a.length < b.length ? a.length : b.length;
  for (let i = 0; i < n; i++) {
    let x = a.charCodeAt(i);
    let y = b.charCodeAt(i);
    if (x !== y) {
      if (x >= 0xd800 && y >= 0xd800) {
        x += x >= 0xe000 ? -0x800 : 0x2000;
        y += y >= 0xe000 ? -0x800 : 0x2000;
      }
      return x - y;
    }
  }
  return a.length - b.length;
}
