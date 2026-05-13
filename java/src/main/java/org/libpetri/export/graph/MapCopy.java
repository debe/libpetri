package org.libpetri.export.graph;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Defensive map-copy utilities that preserve insertion order — required for
 * cross-language byte-parity in the DOT renderer.
 *
 * <p>{@link Map#copyOf(Map)} is unsuitable for the export pipeline because
 * its iteration order is explicitly unspecified per the JDK contract. The
 * renderer iterates these maps left-to-right while emitting attribute lines,
 * so any reorder breaks the byte-equal contract documented in
 * {@code scripts/cross-lang-dot-parity.sh}. The TypeScript exporter relies
 * on V8's object-literal insertion order, and the Rust exporter on
 * {@code Vec<(K, V)>} insertion order; the Java exporter must match.
 */
final class MapCopy {

    private MapCopy() {}

    /**
     * Returns an immutable copy of {@code in} that iterates in the same
     * order as the input. Returns {@link Map#of()} for {@code null} or
     * empty inputs.
     */
    static Map<String, String> preservingOrder(Map<String, String> in) {
        if (in == null || in.isEmpty()) return Map.of();
        return Collections.unmodifiableMap(new LinkedHashMap<>(in));
    }
}
