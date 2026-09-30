package org.libpetri.smt.conformance;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import org.libpetri.smt.SmtVerificationResult;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.conformance.ConformanceNet.PropSpec;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.stream.Stream;

/**
 * Runs Java's verifier over a conformance corpus ({@code spec/verification-fixtures/conformance/})
 * and holds every verdict against the Lean reference's expected verdicts by the README's
 * conformance rule.
 *
 * <p>The route setups mirror {@code rust/libpetri-verification/tests/route_agreement.rs}:
 * {@code enum} (the default pipeline, enumeration first, class budget 5000), {@code smt+lb}
 * (enumeration off, linear bound on), {@code smt-lb} (linear bound off) and {@code ic3}
 * (linear bound and both VER-018/019 phases off: IC3/PDR alone).
 *
 * <p>The four setups run twice. The <b>atomic</b> pass ({@code assumeAtomicFiring(true)}) reads
 * every firing as one step, as the reference does, and is held to every rule. The <b>default</b>
 * pass ({@code <setup>/split}) leaves the in-flight split of VER-004 on, as a caller gets it, and
 * is held to rules 1, 3 and 4 only: the split adds the executor's runs with an action in flight,
 * which the atomic reference does not have, so a violation where the reference proves the
 * property is counted there, not reported. A default-pass trace of a net the split left atomic is
 * replayed and dumped with the atomic ones; a trace of a split net names {@code complete:<t>}
 * steps the reference cannot fire, and is counted instead, with whether the verifier's own
 * abstract replay confirmed it. Mirrors {@code rust/libpetri-verification/tests/conformance.rs}.
 */
public final class ConformanceRunner {

    /** The language, in the summary. */
    static final String LANG = "java";

    /**
     * One route setup. {@code atomic} selects the atomic pass (every rule) or the default, split
     * pass (rules 1, 3 and 4).
     */
    public record Route(
        String name, int enumBudget, boolean linearBound, boolean phases, boolean needsZ3, boolean atomic) {}

    public static final List<Route> ROUTES = List.of(
        new Route("enum", 5_000, true, true, false, true),
        new Route("smt+lb", 0, true, true, true, true),
        new Route("smt-lb", 0, false, true, true, true),
        new Route("ic3", 0, false, false, true, true),
        new Route("enum/split", 5_000, true, true, false, false),
        new Route("smt+lb/split", 0, true, true, true, false),
        new Route("smt-lb/split", 0, false, true, true, false),
        new Route("ic3/split", 0, false, false, true, false));

    /** A reference verdict from {@code expected/<id>.json}. */
    public record Expected(String property, String verdict, List<String> trace, String reason) {}

    /**
     * What a language route said about one property. A {@code violated} outcome's {@code trace}
     * is {@code null} when the route gave no firing sequence — a rule-3 finding (README
     * clarification 6); an initial-marking violation is the empty trace.
     */
    public record Outcome(String verdict, List<String> trace, String reason, boolean ofSplitNet, Boolean confirmed) {
        public static Outcome proven() {
            return new Outcome("proven", List.of(), null, false, null);
        }

        public static Outcome violated(List<String> trace) {
            return new Outcome("violated", List.copyOf(trace), null, false, null);
        }

        /**
         * A violation of a net the in-flight split rewrote (default pass): its trace names
         * {@code complete:<t>} steps the reference cannot fire. {@code confirmed} is the verifier's
         * own abstract replay.
         */
        public static Outcome violatedOfSplitNet(List<String> trace, Boolean confirmed) {
            return new Outcome("violated", List.copyOf(trace), null, true, confirmed);
        }

        /** A violation reported without a firing sequence: a rule-3 finding. */
        public static Outcome untraced() {
            return new Outcome("violated", null, null, false, null);
        }

        public static Outcome unknown(String reason) {
            return new Outcome("unknown", List.of(), reason, false, null);
        }
    }

    // ======================================================================
    // The conformance rule (pure)
    // ======================================================================

    /**
     * The README conformance rule for one (net, property, route). {@code ref} is {@code null}
     * only in unit tests; a corpus property without an entry is a stale-expected finding of its own.
     *
     * @return the findings; empty when conforming
     */
    public static List<String> check(ConformanceNet net, PropSpec prop, String route, Outcome outcome, Expected ref) {
        return check(net, prop, route, true, outcome, ref);
    }

    /**
     * {@link #check(ConformanceNet, PropSpec, String, Outcome, Expected)} in the atomic pass
     * ({@code atomic}, every rule) or the default, split pass (rules 1, 3 and 4): there a
     * violation where the reference proves the property is allowed, and a trace of a split net is
     * not replayed.
     */
    public static List<String> check(
            ConformanceNet net, PropSpec prop, String route, boolean atomic, Outcome outcome, Expected ref) {
        var findings = new ArrayList<String>();
        String refVerdict = ref == null ? "unknown" : ref.verdict();
        String where = "[" + net.id() + " " + prop.id() + " (" + prop.type() + ") route " + route + "] ";
        switch (outcome.verdict()) {
            case "proven" -> {
                if (refVerdict.equals("violated")) {
                    findings.add(where + "WRONG PROVEN: the reference violates it with trace " + ref.trace());
                }
            }
            case "violated" -> {
                if (outcome.trace() == null) {
                    // Rule 3 (README clarification 6): a violation must come with a firing
                    // sequence the reference can replay — [] when the initial marking violates.
                    findings.add(where + (refVerdict.equals("proven") && atomic
                        ? "WRONG VIOLATED: the reference proves it; Java reported no trace"
                        : "VIOLATED WITHOUT A TRACE (rule 3): no firing sequence to replay; an "
                            + "initial-marking violation must report the empty trace"));
                    break;
                }
                if (outcome.ofSplitNet()) {
                    // Default pass: the trace fires complete:<t> steps the atomic reference does
                    // not have. Counted with the abstract replay's confirmation, not replayed.
                    break;
                }
                Optional<String> why = ReferenceSemantics.replay(net, prop, outcome.trace());
                if (!atomic) {
                    // Rule 4 only: the reference may prove what the split net violates.
                    why.ifPresent(w -> findings.add(where + "REPLAY FAILS: trace " + outcome.trace() + ": " + w));
                } else if (refVerdict.equals("proven")) {
                    findings.add(where + (why.isEmpty()
                        ? "FALSIFIES THE REFERENCE: Java's trace " + outcome.trace()
                            + " replays under the reference firing rule, yet the reference proves the property"
                        : "WRONG VIOLATED: the reference proves it and Java's trace " + outcome.trace()
                            + " does not replay: " + why.get()));
                } else if (why.isPresent()) {
                    findings.add(where + "REPLAY FAILS: trace " + outcome.trace() + ": " + why.get());
                }
            }
            case "unknown" -> { }
            default -> throw new IllegalStateException(outcome.verdict());
        }
        return findings;
    }

    // ======================================================================
    // Corpus access
    // ======================================================================

    /** {@code LIBPETRI_CONFORMANCE_DIR} when set, else {@code spec/verification-fixtures/conformance} found upward. */
    public static Optional<Path> locateCorpus() {
        String env = System.getenv("LIBPETRI_CONFORMANCE_DIR");
        if (env != null && !env.isBlank()) {
            return Optional.of(Path.of(env));
        }
        Path dir = Path.of("").toAbsolutePath();
        for (int depth = 0; dir != null && depth < 8; depth++, dir = dir.getParent()) {
            Path candidate = dir.resolve("spec").resolve("verification-fixtures").resolve("conformance");
            if (Files.isDirectory(candidate)) {
                return Optional.of(candidate);
            }
        }
        return Optional.empty();
    }

    /** The net files, sorted by name. */
    public static List<Path> netFiles(Path corpus) {
        Path nets = corpus.resolve("nets");
        if (!Files.isDirectory(nets)) {
            return List.of();
        }
        try (Stream<Path> s = Files.list(nets)) {
            return s.filter(p -> p.getFileName().toString().endsWith(".json")).sorted().toList();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public static Path expectedFile(Path corpus, Path netFile) {
        return corpus.resolve("expected").resolve(netFile.getFileName().toString());
    }

    private static final ObjectMapper JSON = new ObjectMapper();

    static JsonNode read(Path p) {
        try {
            return JSON.readTree(Files.readString(p));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public static Map<String, Expected> readExpected(Path file, String id) {
        JsonNode root = read(file);
        if (root.hasNonNull("id") && !root.get("id").asText().equals(id)) {
            throw new IllegalStateException(file + " carries id " + root.get("id").asText() + ", expected " + id);
        }
        var out = new LinkedHashMap<String, Expected>();
        for (JsonNode r : root.get("results")) {
            var trace = new ArrayList<String>();
            if (r.hasNonNull("trace")) {
                r.get("trace").forEach(n -> trace.add(n.asText()));
            }
            out.put(r.get("property").asText(), new Expected(r.get("property").asText(), r.get("verdict").asText(),
                List.copyOf(trace), r.hasNonNull("reason") ? r.get("reason").asText() : null));
        }
        return out;
    }

    // ======================================================================
    // Running
    // ======================================================================

    /** Per-route verdict counts and unknown reasons, over everything run so far. */
    public static final class Stats {
        final Map<String, int[]> verdicts = new LinkedHashMap<>();
        final Map<String, Map<String, Integer>> unknownReasons = new LinkedHashMap<>();
        final Map<String, Integer> untraced = new LinkedHashMap<>();
        final List<String> skippedRoutes = new ArrayList<>();
        /** Properties Java's API cannot state (README clarification 1), counted, not run. */
        final List<String> skippedProperties = new ArrayList<>();
        /** Default-pass violations where the reference proves the property, per route. */
        final Map<String, Integer> splitOnly = new LinkedHashMap<>();
        /** Default-pass traces of split nets: not replayable by the atomic reference. */
        int splitTraces;
        /** Of {@link #splitTraces}, those the verifier's abstract replay did not confirm. */
        int splitUnconfirmed;
        int nets;
        int netsWithoutExpected;

        synchronized void record(Route route, Outcome o, Expected ref) {
            record(route.name(), o);
            if (route.atomic() || !o.verdict().equals("violated")) {
                return;
            }
            if (ref != null && ref.verdict().equals("proven")) {
                splitOnly.merge(route.name(), 1, Integer::sum);
            }
            if (o.ofSplitNet()) {
                splitTraces++;
                if (Boolean.FALSE.equals(o.confirmed())) {
                    splitUnconfirmed++;
                }
            }
        }

        synchronized void record(String route, Outcome o) {
            int slot = switch (o.verdict()) {
                case "proven" -> 0;
                case "violated" -> 1;
                default -> 2;
            };
            verdicts.computeIfAbsent(route, r -> new int[3])[slot]++;
            if (slot == 1 && o.trace() == null) {
                untraced.merge(route, 1, Integer::sum);
            }
            if (slot == 2) {
                unknownReasons.computeIfAbsent(route, r -> new TreeMap<>())
                    .merge(reasonKey(o.reason()), 1, Integer::sum);
            }
        }

        public int unknowns(String route) {
            int[] v = verdicts.get(route);
            return v == null ? 0 : v[2];
        }

        public String render() {
            var sb = new StringBuilder("conformance [" + LANG + "]: " + nets + " nets checked, "
                + netsWithoutExpected + " without an expected file\n");
            verdicts.forEach((route, v) -> sb.append(String.format(
                "  %-12s proven %d / violated %d (untraced %d) / unknown %d%s%n",
                route, v[0], v[1], untraced.getOrDefault(route, 0), v[2],
                route.endsWith("/split")
                    ? "  violated-where-reference-proved " + splitOnly.getOrDefault(route, 0) : "")));
            sb.append(String.format(
                "  default-pass traces of split nets %d (unconfirmed by the abstract replay %d), "
                    + "not replayed by the reference%n", splitTraces, splitUnconfirmed));
            unknownReasons.forEach((route, reasons) -> reasons.entrySet().stream()
                .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
                .limit(8)
                .forEach(e -> sb.append(String.format("  %-12s unknown x%d: %s%n", route, e.getValue(), e.getKey()))));
            skippedRoutes.forEach(s -> sb.append("  skipped: ").append(s).append('\n'));
            if (!skippedProperties.isEmpty()) {
                sb.append("  skipped ").append(skippedProperties.size())
                  .append(" mutual-exclusion propert(ies) over 3+ places (two-place API): ")
                  .append(String.join(", ", skippedProperties)).append('\n');
            }
            return sb.toString();
        }

        private static String reasonKey(String reason) {
            if (reason == null) {
                return "(no reason)";
            }
            // Names are masked so one cause on many nets counts as one reason.
            String line = reason.lines().findFirst().orElse(reason).replaceAll("'[^']*'", "'…'");
            return line.length() > 140 ? line.substring(0, 140) + "…" : line;
        }
    }

    /** The routes to run: every route with z3, else {@code enum} alone (the rest recorded as skipped). */
    public static List<Route> routes(Stats stats) {
        if (SmtVerifier.z3Available()) {
            return ROUTES;
        }
        synchronized (stats) {
            if (stats.skippedRoutes.isEmpty()) {
                stats.skippedRoutes.add("smt+lb, smt-lb, ic3 (and their /split passes): z3 is not available "
                + "(PATH / LIBPETRI_Z3)");
            }
        }
        return ROUTES.stream().filter(r -> !r.needsZ3()).toList();
    }

    static Outcome run(ConformanceNet net, org.libpetri.core.PetriNet built, PropSpec prop, Route route) {
        SmtVerificationResult r = SmtVerifier.forNet(built)
            // The Lean reference fires atomically and does not model the in-flight split of
            // VER-004: the atomic pass compares on that reading, the default pass on the split.
            .assumeAtomicFiring(route.atomic())
            .initialMarking(net.initialMarking())
            .property(net.toSmt(prop))
            .sinkPlaces(net.sinks(prop))
            .enumerationMaxClasses(route.enumBudget())
            .linearBound(route.linearBound())
            .stateEquationPhase(route.phases())
            .firingBound(route.phases())
            .certificateCheck(true)
            .counterexampleReplay(true)
            .timeout(Duration.ofSeconds(4))
            .totalBudget(Duration.ofSeconds(12))
            .verify();
        return switch (r.verdict()) {
            case SmtVerificationResult.Verdict.Proven p -> Outcome.proven();
            // Traced iff it names a step, or its one marking is the initial marking itself (trace []).
            case SmtVerificationResult.Verdict.Violated v ->
                !r.counterexampleTransitions().isEmpty() || r.counterexampleTrace().size() == 1
                    ? !route.atomic() && r.report().contains("In-flight actions (VER-004):")
                        ? Outcome.violatedOfSplitNet(r.counterexampleTransitions(), r.counterexampleConfirmed())
                        : Outcome.violated(r.counterexampleTransitions())
                    : Outcome.untraced();
            case SmtVerificationResult.Verdict.Unknown u -> Outcome.unknown(u.reason());
        };
    }

    /**
     * Checks one net against its expected file on every route; returns the findings. Writes the
     * traced Violated traces to {@code <LIBPETRI_CONFORMANCE_DUMP>/<id>.traces.json} when set (the
     * input of {@code scripts/conformance-replay.py}).
     */
    public static List<String> checkNet(Path netFile, Path expectedFile, Stats stats) {
        var net = ConformanceNet.parse(read(netFile));
        var expected = readExpected(expectedFile, net.id());
        // A schema construct Java cannot express throws ConformanceNet.NotExpressible here: the
        // net's test fails loudly rather than dropping out of the count, as in TS and Python.
        // The one exception is documented: Java's mutualExclusion takes exactly two places
        // (README clarification 1, VER-002), so a longer pairwise list is skipped and counted.
        var built = net.build();
        net.properties().stream().filter(p -> !ConformanceNet.beyondTwoPlaceApi(p)).forEach(net::toSmt);
        synchronized (stats) {
            stats.nets++;
        }
        var findings = new ArrayList<String>();
        var dump = new LinkedHashSet<Map<String, Object>>();
        for (PropSpec prop : net.properties()) {
            if (ConformanceNet.beyondTwoPlaceApi(prop)) {
                synchronized (stats) {
                    stats.skippedProperties.add(net.id() + "/" + prop.id());
                }
                continue;
            }
            for (Route route : routes(stats)) {
                Outcome o;
                try {
                    o = run(net, built, prop, route);
                } catch (RuntimeException e) {
                    findings.add("[" + net.id() + " " + prop.id() + " route " + route.name()
                        + "] VERIFIER THREW: " + e);
                    continue;
                }
                stats.record(route, o, expected.get(prop.id()));
                findings.addAll(check(net, prop, route.name(), route.atomic(), o, expected.get(prop.id())));
                if (!expected.containsKey(prop.id()) && route == ROUTES.getFirst()) {
                    findings.add(net.id() + "/" + prop.id() + ": no reference verdict (expected/ is stale)");
                }
                if (o.verdict().equals("violated") && o.trace() != null && !o.ofSplitNet()) {
                    var entry = new LinkedHashMap<String, Object>();
                    entry.put("property", prop.id());
                    entry.put("trace", o.trace().stream().map(n -> ReferenceSemantics.strip(net, n)).toList());
                    dump.add(entry);
                }
            }
        }
        writeDump(net.id(), new ArrayList<>(dump));
        return findings;
    }

    private static void writeDump(String id, List<Map<String, Object>> entries) {
        String dir = System.getenv("LIBPETRI_CONFORMANCE_DUMP");
        if (dir == null || dir.isBlank() || entries.isEmpty()) {
            return;
        }
        try {
            Path out = Path.of(dir);
            Files.createDirectories(out);
            Files.writeString(out.resolve(id + ".traces.json"),
                JSON.copy().enable(SerializationFeature.INDENT_OUTPUT).writeValueAsString(entries) + "\n");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
