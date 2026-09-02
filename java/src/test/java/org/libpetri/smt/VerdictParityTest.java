package org.libpetri.smt;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.Place;
import org.libpetri.smt.fixtures.VerificationNets;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.junit.jupiter.api.condition.EnabledIf;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Cross-language verdict-parity runner (C4) over
 * {@code spec/verification-fixtures/fixtures.json}.
 *
 * <p>The JSON carries the shared expectations; each language implements the
 * named net builders in its own test code ({@link VerificationNets} here,
 * following the cross-lang-dot-parity.sh pattern of shared expectations with
 * per-language builders). Every fixture is verified with the certificate check
 * ON and counterexample replay ON, and the verdict is asserted against
 * {@code expected} (plus {@code expectReportContains} where present).
 *
 * <p><b>A disagreement with {@code expected} is a parity FINDING</b> — to be
 * reported as a cross-language divergence, never papered over by adjusting the
 * fixture or the assertion.
 *
 * <p>Z3-gated: runs in CI, skipped where the native library is absent.
 */
@EnabledIf("z3Available")
class VerdictParityTest {

    /**
     * The line every implementation prints when the &nu; name-aware
     * state-class-graph verifier (NU-050 Route B) — not the SMT / Route A
     * encoders — decided the query. Fixtures marked {@code "route": "B"} assert
     * it BEFORE their verdict, so a silent fall-back to Route A fails loudly
     * instead of passing vacuously.
     */
    private static final String ROUTE_B_MARKER =
        "\u03bd-net Route B: name-aware state-class graph (NU-050)";

    static boolean z3Available() {
        return org.libpetri.smt.SmtVerifier.z3Available();
    }

    @TestFactory
    List<DynamicTest> verdictParity() throws IOException {
        JsonNode root = new ObjectMapper().readTree(Files.readString(locateFixtures()));
        var tests = new ArrayList<DynamicTest>();
        for (JsonNode fixture : root.get("fixtures")) {
            tests.add(DynamicTest.dynamicTest(fixture.get("id").asText(), () -> runFixture(fixture)));
        }
        assertFalse(tests.isEmpty(), "fixtures.json contained no fixtures");
        return tests;
    }

    private static void runFixture(JsonNode fixture) {
        String id = fixture.get("id").asText();
        String expected = fixture.get("expected").asText();
        var named = VerificationNets.build(fixture.get("net").asText());
        var property = parseProperty(fixture.get("property"));

        var verifier = SmtVerifier.forNet(named.net())
            .initialMarking(named.initialMarking())
            .property(property)
            .certificateCheck(true)
            .counterexampleReplay(true)
            .timeout(Duration.ofSeconds(30));
        if (!named.environmentPlaces().isEmpty()) {
            verifier
                .environmentPlaces(named.environmentPlaces().toArray(new EnvironmentPlace<?>[0]))
                .environmentMode(named.environmentMode());
        }
        // Optional shared-schema field: expected terminal places, per [VER-002].
        var sinks = sinkPlaces(fixture);
        if (!sinks.isEmpty()) {
            verifier.sinkPlaces(sinks.toArray(new Place<?>[0]));
        }
        var result = verifier.verify();

        // The route marker is checked FIRST: a `route: "B"` fixture that
        // silently fell back to Route A would pin nothing, so name that failure
        // directly rather than letting it surface as a confusing verdict
        // mismatch.
        if (fixture.hasNonNull("route") && "B".equals(fixture.get("route").asText())) {
            assertTrue(result.report().contains(ROUTE_B_MARKER), () ->
                "ROUTE FINDING [" + id + "]: fixture declares route \"B\" but the report does not "
                + "name the \u03bd name-aware state-class graph — the query fell back to Route A, "
                + "so the Route B deadlock predicate was never exercised\n" + result.report());
        }

        switch (expected) {
            case "proven" -> assertTrue(result.isProven(), () -> parityFinding(id, expected, result));
            case "violated" -> assertTrue(result.isViolated(), () -> parityFinding(id, expected, result));
            default -> fail("fixture '" + id + "' carries unknown expected verdict: " + expected);
        }

        if (fixture.hasNonNull("expectReportContains")) {
            String needle = fixture.get("expectReportContains").asText();
            assertTrue(result.report().contains(needle), () ->
                "PARITY FINDING [" + id + "]: report does not contain \"" + needle
                + "\" — report this cross-language disagreement, do not adjust the fixture\n"
                + result.report());
        }
    }

    /** The fixture's optional {@code sinkPlaces} array, resolved to places. */
    private static List<Place<?>> sinkPlaces(JsonNode fixture) {
        var out = new ArrayList<Place<?>>();
        if (fixture.hasNonNull("sinkPlaces")) {
            for (JsonNode name : fixture.get("sinkPlaces")) {
                out.add(place(name.asText()));
            }
        }
        return out;
    }

    private static SmtProperty parseProperty(JsonNode property) {
        String type = property.get("type").asText();
        return switch (type) {
            case "deadlock-free" -> SmtProperty.deadlockFree();
            case "mutual-exclusion" -> {
                JsonNode places = property.get("places");
                yield SmtProperty.mutualExclusion(
                    place(places.get(0).asText()), place(places.get(1).asText()));
            }
            case "place-bound" -> SmtProperty.placeBound(
                place(property.get("place").asText()), property.get("bound").asInt());
            case "unreachable" -> SmtProperty.unreachable(
                Set.of(place(property.get("place").asText())));
            default -> throw new IllegalArgumentException("unknown fixture property type: " + type);
        };
    }

    /** All fixture places are String-typed by the {@link VerificationNets} contract. */
    private static Place<String> place(String name) {
        return Place.of(name, String.class);
    }

    private static String parityFinding(String id, String expected, SmtVerificationResult result) {
        return "PARITY FINDING [" + id + "]: expected " + expected + " but the Java verifier "
            + "returned " + result.verdict() + " — report this cross-language disagreement, "
            + "do not adjust the fixture\n" + result.report();
    }

    /**
     * Resolves the shared fixture file upward from the module directory
     * (surefire runs with cwd {@code java/}, so the first hit is
     * {@code ../spec/verification-fixtures/fixtures.json}).
     */
    private static Path locateFixtures() {
        Path dir = Path.of("").toAbsolutePath();
        for (int depth = 0; dir != null && depth < 8; depth++, dir = dir.getParent()) {
            Path candidate = dir.resolve("spec").resolve("verification-fixtures").resolve("fixtures.json");
            if (Files.isRegularFile(candidate)) {
                return candidate;
            }
        }
        throw new IllegalStateException(
            "could not locate spec/verification-fixtures/fixtures.json upward from "
            + Path.of("").toAbsolutePath());
    }
}
