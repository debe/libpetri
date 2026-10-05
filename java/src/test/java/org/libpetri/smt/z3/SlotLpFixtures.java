package org.libpetri.smt.z3;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Flat nets for the colour-slot linear program of [NU-053], built straight from rows, and the
 * shared parity cases of {@code spec/verification-fixtures/slot-bound-lp.json}.
 *
 * <p>Each case is a flat net given as rows (pre and post counts per place, optionally the places a
 * reset or consume-all arc clears), the coloured places and an initial marking. The inputs are
 * written by hand; the {@code expected} object of every case is written by the Rust script-parity
 * test under {@code scripts/smt-script-parity.py --update} and read here. Mirrors
 * {@code rust/libpetri-verification/tests/common/slot_lp_cases.rs}.
 */
final class SlotLpFixtures {

    private SlotLpFixtures() {}

    /** One flat row: name, pre and post counts by place, and the places it resets or drains. */
    record Row(String name, Map<String, Integer> pre, Map<String, Integer> post,
               Set<String> reset, Set<String> consumeAll) {
        Row(String name, Map<String, Integer> pre, Map<String, Integer> post) {
            this(name, pre, post, Set.of(), Set.of());
        }
    }

    /** A flat net and what the program reads: initial marking and coloured places (ascending). */
    record LpCase(String id, FlatNet flat, MarkingState initial, int[] coloured, JsonNode expected) {
        int index(String place) {
            for (int i = 0; i < flat.placeCount(); i++) {
                if (flat.places().get(i).name().equals(place)) {
                    return i;
                }
            }
            throw new IllegalArgumentException("unknown place '" + place + "'");
        }
    }

    /** Places {@code names} in this order (each a {@code Place<Object>}), and the rows. */
    static FlatNet flat(List<String> names, List<Row> rows) {
        List<Place<?>> places = new ArrayList<>();
        Map<Place<?>, Integer> placeIndex = new HashMap<>();
        Map<String, Integer> byName = new HashMap<>();
        for (String name : names) {
            Place<?> p = Place.of(name, Object.class);
            placeIndex.put(p, places.size());
            byName.put(name, places.size());
            places.add(p);
        }
        int n = places.size();
        List<FlatTransition> transitions = new ArrayList<>();
        for (Row row : rows) {
            int[] pre = new int[n];
            int[] post = new int[n];
            row.pre().forEach((p, c) -> pre[index(byName, p)] += c);
            row.post().forEach((p, c) -> post[index(byName, p)] += c);
            int[] reset = row.reset().stream().mapToInt(p -> index(byName, p)).sorted().toArray();
            boolean[] consumeAll = new boolean[n];
            for (String p : row.consumeAll()) {
                consumeAll[index(byName, p)] = true;
            }
            transitions.add(new FlatTransition(row.name(), null, -1, pre, post, new int[0], new int[0],
                reset, consumeAll, false));
        }
        return new FlatNet(List.copyOf(places), Map.copyOf(placeIndex), List.copyOf(transitions), Map.of(), Map.of());
    }

    private static int index(Map<String, Integer> byName, String place) {
        Integer i = byName.get(place);
        if (i == null) {
            throw new IllegalArgumentException("unknown place '" + place + "'");
        }
        return i;
    }

    /** A marking of {@code flat}'s places by name. */
    static MarkingState marking(FlatNet flat, Map<String, Integer> tokens) {
        var b = MarkingState.builder();
        for (Place<?> p : flat.places()) {
            Integer c = tokens.get(p.name());
            if (c != null && c != 0) {
                b.tokens(p, c);
            }
        }
        return b.build();
    }

    /** The flat indices of {@code names}, ascending. */
    static int[] indices(FlatNet flat, String... names) {
        int[] out = new int[names.length];
        for (int i = 0; i < names.length; i++) {
            out[i] = -1;
            for (int p = 0; p < flat.placeCount(); p++) {
                if (flat.places().get(p).name().equals(names[i])) {
                    out[i] = p;
                }
            }
            if (out[i] < 0) {
                throw new IllegalArgumentException("unknown place '" + names[i] + "'");
            }
        }
        Arrays.sort(out);
        return out;
    }

    /** {@code spec/verification-fixtures/slot-bound-lp.json}, found upward from the module directory. */
    static Path parityFile() {
        Path dir = Path.of("").toAbsolutePath();
        for (int depth = 0; dir != null && depth < 8; depth++, dir = dir.getParent()) {
            Path candidate = dir.resolve("spec").resolve("verification-fixtures").resolve("slot-bound-lp.json");
            if (Files.isRegularFile(candidate)) {
                return candidate;
            }
        }
        throw new IllegalStateException("could not locate spec/verification-fixtures/slot-bound-lp.json upward from "
            + Path.of("").toAbsolutePath());
    }

    /** Every case of the shared parity file, built. */
    static List<LpCase> parityCases() {
        JsonNode root;
        try {
            root = new ObjectMapper().readTree(Files.readString(parityFile()));
        } catch (IOException e) {
            throw new AssertionError(e);
        }
        var out = new ArrayList<LpCase>();
        for (JsonNode c : root.get("cases")) {
            List<String> names = new ArrayList<>();
            c.get("places").forEach(p -> names.add(p.asText()));
            List<Row> rows = new ArrayList<>();
            for (JsonNode r : c.get("rows")) {
                rows.add(new Row(r.get("name").asText(), counts(r.get("pre")), counts(r.get("post")),
                    strings(r.get("reset")), strings(r.get("consumeAll"))));
            }
            FlatNet flat = flat(names, rows);
            List<String> coloured = new ArrayList<>(strings(c.get("coloured")));
            out.add(new LpCase(c.get("id").asText(), flat, marking(flat, counts(c.get("marking"))),
                indices(flat, coloured.toArray(String[]::new)), c.get("expected")));
        }
        return out;
    }

    private static Map<String, Integer> counts(JsonNode node) {
        Map<String, Integer> out = new LinkedHashMap<>();
        if (node != null) {
            node.properties().forEach(e -> out.put(e.getKey(), e.getValue().asInt()));
        }
        return out;
    }

    private static Set<String> strings(JsonNode node) {
        if (node == null) {
            return Set.of();
        }
        var out = new java.util.LinkedHashSet<String>();
        node.forEach(n -> out.add(n.asText()));
        return out;
    }
}
