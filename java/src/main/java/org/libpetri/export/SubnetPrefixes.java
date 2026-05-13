package org.libpetri.export;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

/**
 * Prefix-derivation helpers for subnet-instance-aware export and debug
 * tooling, per {@code spec/11-modular-composition.md} <b>MOD-040</b>
 * (export grouping) and <b>MOD-041</b> (debug protocol subnet instances).
 *
 * <p>The {@code "/"} character is the prefix separator established by
 * <b>MOD-010</b>: a node named {@code "outer/inner/leaf"} belongs to the
 * cluster tree {@code outer -> outer/inner}, with {@code "leaf"} as the
 * un-prefixed final segment.
 *
 * <p>This class is observability-only — it never inspects {@link
 * org.libpetri.core.SubnetDef} or {@link org.libpetri.core.Instance}
 * objects, only the resulting prefixed names that survived composition.
 * That keeps consumers (DOT exporter, debug protocol handler) decoupled
 * from the modular-composition layer per <b>MOD-023</b>.
 */
public final class SubnetPrefixes {

    private SubnetPrefixes() {}

    /**
     * Returns the instance prefix carried by the given node name, or empty
     * when the name has no {@code "/"} (i.e. is not part of any composed
     * subnet instance).
     *
     * <p>The prefix is the substring up to (but not including) the
     * <b>last</b> {@code "/"} — so {@code "producer1/internal"} returns
     * {@code "producer1"} and {@code "outer/inner/leaf"} returns
     * {@code "outer/inner"}. The bare segment after the last {@code "/"}
     * is the original (un-prefixed) place or transition name.
     *
     * @param nodeName the prefixed-or-flat node name
     * @return the prefix, or {@link Optional#empty()} for flat names
     */
    public static Optional<String> instancePrefixOf(String nodeName) {
        if (nodeName == null) return Optional.empty();
        int idx = nodeName.lastIndexOf('/');
        if (idx <= 0) return Optional.empty();
        return Optional.of(nodeName.substring(0, idx));
    }

    /**
     * Returns the parent prefix of a given prefix, or empty if the prefix
     * is top-level (single segment, no {@code "/"}).
     *
     * <p>Used by the debug protocol's {@link
     * org.libpetri.core.SubnetInstance#parentPrefix()} field per
     * <b>MOD-041</b> for nested instances.
     *
     * @param prefix an instance prefix string (e.g. {@code "outer/inner"})
     * @return the parent prefix (e.g. {@code "outer"}), or empty for
     *         top-level prefixes
     */
    public static Optional<String> parentOf(String prefix) {
        if (prefix == null || prefix.isEmpty()) return Optional.empty();
        int idx = prefix.lastIndexOf('/');
        if (idx <= 0) return Optional.empty();
        return Optional.of(prefix.substring(0, idx));
    }

    /**
     * Returns the last (leaf) segment of a prefix, used as the cluster
     * label per <b>MOD-040</b>. For top-level prefixes the input itself is
     * returned unchanged.
     *
     * @param prefix an instance prefix string
     * @return the trailing segment after the last {@code "/"} (or the input
     *         when there is no {@code "/"})
     */
    public static String leafSegment(String prefix) {
        if (prefix == null || prefix.isEmpty()) return prefix;
        int idx = prefix.lastIndexOf('/');
        return idx < 0 ? prefix : prefix.substring(idx + 1);
    }

    /**
     * Builds the full set of prefixes (top-level and nested) required to
     * cover every {@code "/"}-bearing name in {@code nodeNames}.
     *
     * <p>For input names {@code ["a/x", "a/b/y", "c/z"]} the returned
     * iteration order (LinkedHashMap, insertion order) yields:
     * {@code "a"}, {@code "a/b"}, {@code "c"}. The map's value carries
     * the parent prefix (or empty for top-level) so callers can build a
     * cluster tree without re-splitting.
     *
     * @param nodeNames every node name to consider (places + transitions)
     * @return ordered map of prefix -&gt; parent prefix
     */
    public static Map<String, Optional<String>> collectPrefixes(Iterable<String> nodeNames) {
        var prefixes = new LinkedHashMap<String, Optional<String>>();
        for (var name : nodeNames) {
            var prefixOpt = instancePrefixOf(name);
            if (prefixOpt.isEmpty()) continue;
            // Walk the prefix chain root-to-leaf so parents are inserted
            // before children — matters for downstream tree assembly.
            var prefix = prefixOpt.get();
            var segments = prefix.split("/");
            var built = new StringBuilder();
            String parent = null;
            for (var seg : segments) {
                if (built.length() > 0) {
                    parent = built.toString();
                    built.append('/');
                }
                built.append(seg);
                var current = built.toString();
                prefixes.putIfAbsent(current, parent == null ? Optional.empty() : Optional.of(parent));
            }
        }
        return prefixes;
    }
}
