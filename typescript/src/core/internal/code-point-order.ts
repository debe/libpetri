/** A UTF-16 unit at which code-unit and code-point order can disagree. */
const HIGH_UNIT = /[\uD800-\uFFFF]/;

/**
 * Orders two strings by Unicode code point: negative when `a` sorts first, zero when they
 * are equal, positive otherwise.
 *
 * Every ordering of place or transition names that reaches a report, a witness trace, a
 * violation list or a flat index uses this, so the same net prints and encodes the same
 * way on every host and in every implementation ([VER-013], [VER-022]). Neither built-in
 * comparison gives that:
 *
 * - `localeCompare` follows the host's default locale. `tr_TR` sorts `"Ia"` before `"ia"`,
 *   `da_DK` puts uppercase first and `"aa"` last, and `"Ärger"` moves between locales.
 * - `<` and the default `Array.prototype.sort` compare UTF-16 code units. That is a
 *   property of JavaScript's encoding, not of the string, and it disagrees with code-point
 *   order when a supplementary character (U+10000 and up, stored as a surrogate pair
 *   starting at 0xD800–0xDBFF) meets one in U+E000–U+FFFF: as units the surrogate is
 *   smaller, as code points it is larger.
 *
 * Code-point order belongs to the string, so every encoding agrees on it. Rust's `str`
 * ordering already is it (UTF-8 byte order), and Java's `String`, UTF-16 like JavaScript's,
 * needs the same correction as here.
 *
 * The correction is ICU's code-point-order fix-up (`uprv_strCompare`). Only the first pair
 * of units that differ decides, and code-unit and code-point order can disagree only when
 * both of those units are at least 0xD800. For that pair alone, units at 0xE000 and above
 * move down by 0x800 and surrogates move up by 0x2000, which lifts every surrogate above
 * every other unit while keeping the order within each range. Every other comparison is a
 * plain unit comparison. When one string is a prefix of the other, the shorter one sorts
 * first. For well-formed strings the result is exactly code-point order; a lone surrogate,
 * which no Rust `str` can hold, sorts with the supplementary characters.
 *
 * Unless both strings hold a unit at 0xD800 or above, no differing pair can need the
 * fix-up, and the engine's own code-unit comparison is the answer. That path matters: two
 * callers, a marking's `toString` in the class key and the canonical clock order, run for
 * every successor the state-class graph builds. A unit loop in JavaScript costs roughly
 * 2 ns per shared leading unit on V8, where the native comparison runs at memcmp speed,
 * and names with a long common prefix, as composed subnets have, made a graph build up to
 * a sixth slower with the loop alone.
 *
 * O(min(|a|, |b|)) unit comparisons, O(1) space, no allocation. Choosing the path costs
 * O(1) for a string V8 stores one byte per unit, which cannot hold such a unit, and a
 * native scan of at most |a| + |b| units otherwise.
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
