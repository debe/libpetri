package org.libpetri.core.internal;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cross-language acceptance vector for name order ([VER-013], [VER-022]): the TypeScript and
 * Rust suites assert the same sequence.
 */
class CodePointOrderTest {

    /** Already in code-point order. */
    private static final List<String> CANONICAL = List.of(
        "",
        "Z",
        "a",
        "ab",
        "Ä",       // Ä
        "中",       // 中
        "",       // private use, the lowest unit above the surrogates
        "Ａ",       // fullwidth Ａ
        "𝐀", // U+1D400 mathematical bold A, a surrogate pair
        "😀"  // U+1F600 grinning face, a surrogate pair
    );

    /** Lexicographic order on the code point sequences: the definition, not the fast path. */
    private static int reference(String a, String b) {
        int[] x = a.codePoints().toArray();
        int[] y = b.codePoints().toArray();
        for (int i = 0; i < Math.min(x.length, y.length); i++) {
            if (x[i] != y[i]) {
                return Integer.compare(x[i], y[i]);
            }
        }
        return Integer.compare(x.length, y.length);
    }

    @Test
    void sortsTheCrossLanguageVectorIntoCodePointOrder_fromAnyStartingOrder() {
        var reversed = new ArrayList<>(CANONICAL);
        Collections.reverse(reversed);
        var codeUnits = new ArrayList<>(CANONICAL);
        Collections.sort(codeUnits); // String.compareTo: UTF-16 code units
        var shuffled = new ArrayList<>(CANONICAL);
        Collections.shuffle(shuffled, new Random(7));
        for (var start : List.of(reversed, codeUnits, shuffled)) {
            start.sort(CodePointOrder.COMPARATOR);
            assertEquals(CANONICAL, start);
        }
    }

    @Test
    void differsFromStringCompareTo_exactlyWhereASurrogateMeetsAUnitAboveThem() {
        var codeUnits = new ArrayList<>(CANONICAL);
        Collections.sort(codeUnits);
        assertEquals(List.of("", "Z", "a", "ab", "Ä", "中", "𝐀", "😀", "", "Ａ"),
            codeUnits);
        assertTrue(CodePointOrder.compare("Ａ", "𝐀") < 0);
        assertTrue("Ａ".compareTo("𝐀") > 0);
    }

    @Test
    void agreesWithTheDefinition_signForSign() {
        var random = new Random(42);
        int[] alphabet = {'a', 'b', 'Z', '_', 0xC4, 0x4E2D, 0xD7FF, 0xE000, 0xFFFF, 0xFF21, 0x10000, 0x1D400, 0x1F600, 0x10FFFF};
        var words = new ArrayList<>(CANONICAL);
        for (int i = 0; i < 400; i++) {
            var sb = new StringBuilder();
            int length = random.nextInt(5);
            for (int j = 0; j < length; j++) {
                sb.appendCodePoint(alphabet[random.nextInt(alphabet.length)]);
            }
            words.add(sb.toString());
        }
        for (var a : words) {
            for (var b : words) {
                assertEquals(Integer.signum(reference(a, b)), Integer.signum(CodePointOrder.compare(a, b)),
                    () -> a.codePoints().boxed().toList() + " vs " + b.codePoints().boxed().toList());
            }
        }
    }
}
