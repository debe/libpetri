package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.encoding.FlatNet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Where a token may come to rest without being stranded ([VER-002], [VER-014]).
 *
 * <p>{@code DeadlockFree} is violated by a quiescent marking that holds a token outside
 * the places where resting is permitted. The permitted set has two layers:
 * <ul>
 *   <li>the <b>declared sinks</b> ({@link SmtVerifier#sinkPlaces}), where a token may
 *       always rest;</li>
 *   <li>the <b>conditional sinks</b> ({@link SmtVerifier#sinkPlacesWhen}), where a token
 *       may rest only while {@code marker} holds a token. A marked marker is a
 *       <em>designed terminal</em> — a halted or paused run — and the marker itself is
 *       at rest whenever it is marked.</li>
 * </ul>
 *
 * <p>Declarations union: a token in {@code p} is excused when {@code p} is a declared
 * sink, when {@code p} is a marker, or when some conditional set naming {@code p} has
 * its marker marked. Every route that decides {@code DeadlockFree} — the flat and
 * name-coloured CHC encoders, the certificate check's safety condition, the abstract
 * counterexample replay and the Route B name-partition graph — reads this one class, so
 * the predicate cannot drift between them ([VER-014] AC5).
 *
 * <p>{@code TerminatesAtSink} is untouched by conditional declarations: it asks whether
 * a declared sink was reached and reads only the unconditional set.
 */
public final class RestSet {

    private RestSet() {}

    /**
     * Places where a token may rest while {@code marker} holds a token.
     *
     * @param marker the designed-terminal marker
     * @param places the places excused while the marker is marked, in declaration order
     */
    public record ConditionalSinks(Place<?> marker, Set<Place<?>> places) {
        public ConditionalSinks {
            marker = java.util.Objects.requireNonNull(marker);
            places = Collections.unmodifiableSet(new LinkedHashSet<>(places));
        }
    }

    /**
     * Per flat place, how a token resting there is excused: {@code null} when it never
     * counts as stranded (a declared sink, or a marker), otherwise the ascending flat
     * indices of the markers whose presence excuses it — empty when nothing does, so a
     * token there is stranded whenever the marking is quiescent.
     *
     * <p>Places and markers that do not resolve in the flat net contribute nothing, as an
     * unresolved sink does: a mistyped marker makes the property stricter, never laxer.
     */
    public static int[][] strandingExcuses(
            FlatNet flatNet, Collection<Place<?>> sinkPlaces, List<ConditionalSinks> conditional
    ) {
        int p = flatNet.placeCount();
        var lists = new ArrayList<List<Integer>>(p);
        for (int pid = 0; pid < p; pid++) {
            lists.add(new ArrayList<>());
        }
        for (var sink : sinkPlaces) {
            int pid = flatNet.indexOf(sink);
            if (pid >= 0) {
                lists.set(pid, null);
            }
        }
        for (var entry : conditional) {
            int mid = flatNet.indexOf(entry.marker());
            if (mid < 0) {
                continue;
            }
            lists.set(mid, null);
            for (var place : entry.places()) {
                int pid = flatNet.indexOf(place);
                if (pid < 0) {
                    continue;
                }
                var list = lists.get(pid);
                if (list != null && !list.contains(mid)) {
                    list.add(mid);
                }
            }
        }
        var excuses = new int[p][];
        for (int pid = 0; pid < p; pid++) {
            var list = lists.get(pid);
            if (list == null) {
                excuses[pid] = null;
            } else {
                Collections.sort(list);
                excuses[pid] = list.stream().mapToInt(Integer::intValue).toArray();
            }
        }
        return excuses;
    }

    /**
     * Whether {@code m} holds a token that is stranded — outside every place where
     * resting is permitted in {@code m}. The graph-route form of
     * {@link #strandingExcuses}.
     */
    public static boolean strandsToken(
            MarkingState m, Collection<Place<?>> sinkPlaces, List<ConditionalSinks> conditional
    ) {
        var resting = new HashSet<Place<?>>(sinkPlaces);
        for (var entry : conditional) {
            resting.add(entry.marker());
            if (m.hasTokens(entry.marker())) {
                resting.addAll(entry.places());
            }
        }
        for (var p : m.placesWithTokens()) {
            if (!resting.contains(p)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The declarations as the report prints them after the property description:
     * {@code sinks: a, b; when h: c, d; when p}, or {@code null} when nothing is declared.
     * Declaration order throughout, so the four implementations render the same text.
     */
    public static String describeSinks(Collection<Place<?>> sinkPlaces, List<ConditionalSinks> conditional) {
        var parts = new ArrayList<String>();
        if (!sinkPlaces.isEmpty()) {
            parts.add("sinks: " + names(sinkPlaces));
        }
        for (var entry : conditional) {
            parts.add(entry.places().isEmpty()
                ? "when " + entry.marker().name()
                : "when " + entry.marker().name() + ": " + names(entry.places()));
        }
        return parts.isEmpty() ? null : String.join("; ", parts);
    }

    private static String names(Collection<Place<?>> places) {
        var out = new ArrayList<String>(places.size());
        for (var p : places) {
            out.add(p.name());
        }
        return String.join(", ", out);
    }
}
