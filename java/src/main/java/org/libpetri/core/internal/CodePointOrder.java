package org.libpetri.core.internal;

import java.util.Comparator;

/**
 * Orders strings by Unicode code point, the one name order every implementation uses.
 *
 * <p>Every ordering of place or transition names that reaches a report, a witness trace, a
 * violation list or a flat index uses this, so the same net prints and encodes the same way in
 * every implementation ([VER-013], [VER-022]). {@link String#compareTo} does not give it: it
 * compares UTF-16 code units, which disagrees with code-point order when a supplementary
 * character (U+10000 and up, stored as a surrogate pair starting at 0xD800–0xDBFF) meets one in
 * U+E000–U+FFFF. As units the surrogate is smaller, as code points it is larger. Rust's
 * {@code str} order is code-point order already, and the TypeScript reference applies the same
 * correction as here.
 *
 * <p>The correction is ICU's code-point-order fix-up. Only the first pair of units that differ
 * decides, and the two orders can disagree only when both of those units are at least 0xD800.
 * For that pair alone, a unit at 0xE000 or above moves down by 0x800 and a surrogate moves up by
 * 0x2000, which lifts every surrogate above every other unit while keeping the order within each
 * range. When one string is a prefix of the other, the shorter one sorts first. For well-formed
 * strings the result is exactly code-point order; a lone surrogate sorts with the supplementary
 * characters.
 *
 * <p>O(min(|a|, |b|)) time, no allocation.
 */
public final class CodePointOrder {

    /** {@link #compare(String, String)} as a comparator. */
    public static final Comparator<String> COMPARATOR = CodePointOrder::compare;

    private CodePointOrder() {}

    /**
     * Compares two strings by code point.
     *
     * @return negative when {@code a} sorts first, zero when the strings are equal, positive
     *     otherwise
     */
    public static int compare(String a, String b) {
        int n = Math.min(a.length(), b.length());
        for (int i = 0; i < n; i++) {
            int x = a.charAt(i);
            int y = b.charAt(i);
            if (x != y) {
                if (x >= 0xD800 && y >= 0xD800) {
                    x += x >= 0xE000 ? -0x800 : 0x2000;
                    y += y >= 0xE000 ? -0x800 : 0x2000;
                }
                return x - y;
            }
        }
        return a.length() - b.length();
    }
}
