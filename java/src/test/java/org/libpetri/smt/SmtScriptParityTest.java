package org.libpetri.smt;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.Place;
import org.libpetri.smt.fixtures.VerificationNets;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Cross-language SMT script parity (VER-013 AC1) over
 * {@code spec/verification-fixtures/fixtures.json}.
 *
 * <p>For every fixture the scripts this verifier would send to z3
 * ({@link SmtVerifier#encodeScripts()}) must equal the committed goldens under
 * {@code spec/verification-fixtures/scripts/<id>/}, byte for byte. The goldens are
 * written by the Rust verifier ({@code scripts/smt-script-parity.py --update}); the
 * TypeScript and Python suites diff them too. A diff is a parity FINDING in whichever
 * emitter drifted, never a reason to edit a golden by hand.
 *
 * <p>No solver is needed: the encoders are pure text.
 */
class SmtScriptParityTest {

    @TestFactory
    List<DynamicTest> scriptParity() throws IOException {
        Path fixturesFile = VerdictParityTest.locateFixtures();
        JsonNode root = new ObjectMapper().readTree(Files.readString(fixturesFile));
        Path scripts = fixturesFile.getParent().resolve("scripts");
        var tests = new ArrayList<DynamicTest>();
        for (JsonNode fixture : root.get("fixtures")) {
            tests.add(DynamicTest.dynamicTest(fixture.get("id").asText(),
                () -> runFixture(fixture, scripts.resolve(fixture.get("id").asText()))));
        }
        assertFalse(tests.isEmpty(), "fixtures.json contained no fixtures");
        return tests;
    }

    /**
     * The [NU-054] relay fixtures of {@code spec/verification-fixtures/nu-relay-fixtures.json},
     * whose nets are given inline as rows ({@code [transition, [inputs], [outputs], [match keys],
     * [relay targets]]}) and built as {@link JoinRelayTest.Net} builds them, diffed against the
     * same Rust-written goldens.
     */
    @TestFactory
    List<DynamicTest> relayScriptParity() throws IOException {
        Path relayFile = VerdictParityTest.locateFixtures().resolveSibling("nu-relay-fixtures.json");
        JsonNode root = new ObjectMapper().readTree(Files.readString(relayFile));
        Path scripts = relayFile.getParent().resolve("scripts");
        var tests = new ArrayList<DynamicTest>();
        for (JsonNode fixture : root.get("fixtures")) {
            tests.add(DynamicTest.dynamicTest(fixture.get("id").asText(),
                () -> runRelayFixture(fixture, scripts.resolve(fixture.get("id").asText()))));
        }
        assertFalse(tests.isEmpty(), "nu-relay-fixtures.json contained no fixtures");
        return tests;
    }

    private static void runRelayFixture(JsonNode fixture, Path goldenDir) throws IOException {
        String id = fixture.get("id").asText();
        var net = new JoinRelayTest.Net(fixture.get("net").asText());
        for (JsonNode row : fixture.get("rows")) {
            net.t(row.get(0).asText(), names(row.get(1)), names(row.get(2)), names(row.get(3)), names(row.get(4)));
        }
        var verifier = SmtVerifier.forNet(net.build())
            .initialMarking(m -> fixture.get("marking").properties()
                .forEach(e -> m.tokens(net.p(e.getKey()), e.getValue().asInt())))
            .property(VerdictParityTest.parseProperty(fixture.get("property")))
            .certificateCheck(true)
            .counterexampleReplay(true)
            .timeout(Duration.ofSeconds(30));
        var sinks = names(fixture.get("sinkPlaces"));
        if (!sinks.isEmpty()) {
            verifier.sinkPlaces(sinks.stream().map(net::p).toArray(Place<?>[]::new));
        }
        var budgets = names(fixture.get("budgetPlaces"));
        if (!budgets.isEmpty()) {
            verifier.budgetPlaces(budgets.stream().map(net::p).toArray(Place<?>[]::new));
        }
        var carriers = names(fixture.get("carrierPlaces"));
        if (!carriers.isEmpty()) {
            verifier.carrierPlaces(carriers.stream().map(net::p).toArray(Place<?>[]::new));
        }
        var mode = fixture.get("fragmentMode");
        if (mode != null) {
            verifier.fragmentMode(switch (mode.asText()) {
                case "base" -> FragmentMode.BASE;
                case "extended" -> FragmentMode.EXTENDED;
                default -> throw new IllegalArgumentException("unknown fixture fragmentMode: " + mode.asText());
            });
        }
        var encoded = verifier.encodeScripts();

        compare(id, goldenDir.resolve("horn.smt2"), encoded.horn());
        compare(id, goldenDir.resolve("certificate.smt2"), encoded.certificate());
        compare(id, goldenDir.resolve("bound.smt2"), encoded.bound());
        compare(id, goldenDir.resolve("state-equation.smt2"), encoded.stateEquation());
    }

    /** A JSON array of place names; empty when the field is absent. */
    private static List<String> names(JsonNode array) {
        var out = new ArrayList<String>();
        if (array != null) {
            array.forEach(n -> out.add(n.asText()));
        }
        return out;
    }

    private static void runFixture(JsonNode fixture, Path goldenDir) throws IOException {
        String id = fixture.get("id").asText();
        var named = VerificationNets.withTerminals(
            VerificationNets.build(fixture.get("net").asText()),
            VerdictParityTest.terminalNames(fixture));
        var verifier = SmtVerifier.forNet(named.net())
            .initialMarking(named.initialMarking())
            .property(VerdictParityTest.parseProperty(fixture.get("property")))
            .certificateCheck(true)
            .counterexampleReplay(true)
            .timeout(Duration.ofSeconds(30));
        if (!named.environmentPlaces().isEmpty()) {
            verifier
                .environmentPlaces(named.environmentPlaces().toArray(new EnvironmentPlace<?>[0]))
                .environmentMode(named.environmentMode());
        }
        var sinks = VerdictParityTest.sinkPlaces(fixture);
        if (!sinks.isEmpty()) {
            verifier.sinkPlaces(sinks.toArray(new Place<?>[0]));
        }
        var budgets = VerdictParityTest.budgetPlaces(fixture);
        if (!budgets.isEmpty()) {
            verifier.budgetPlaces(budgets.toArray(new Place<?>[0]));
        }
        VerdictParityTest.sinkPlacesWhen(fixture).forEach((marker, places) ->
            verifier.sinkPlacesWhen(marker, places.toArray(new Place<?>[0])));
        verifier.semiflowInvariants(VerdictParityTest.semiflowInvariants(fixture));
        verifier.stateEquation(VerdictParityTest.stateEquation(fixture));
        var scripts = verifier.encodeScripts();

        compare(id, goldenDir.resolve("horn.smt2"), scripts.horn());
        compare(id, goldenDir.resolve("certificate.smt2"), scripts.certificate());
        // The linear state-equation bound query ([VER-015]); absent for a quiescence property.
        compare(id, goldenDir.resolve("bound.smt2"), scripts.bound());
        // The state-equation phase's first query ([VER-018] AC7); absent where the phase does
        // not run (a ν-net, Ignore with environment places).
        compare(id, goldenDir.resolve("state-equation.smt2"), scripts.stateEquation());
    }

    private static void compare(String id, Path golden, String actual) throws IOException {
        if (!Files.isRegularFile(golden)) {
            assertNull(actual, () -> "SCRIPT PARITY FINDING [" + id + "]: this encoding emits "
                + golden.getFileName() + " but no golden exists at " + golden
                + " (run scripts/smt-script-parity.py --update)");
            return;
        }
        String expected = Files.readString(golden);
        assertNotNull(actual, () -> "SCRIPT PARITY FINDING [" + id + "]: " + golden
            + " exists but this encoding emits no such script");
        assertEquals(expected, actual, () -> "SCRIPT PARITY FINDING [" + id + "]: "
            + golden.getFileName() + " differs from the Rust golden at "
            + firstDifference(expected, actual)
            + " — report the divergence, never edit the golden by hand");
    }

    private static String firstDifference(String expected, String actual) {
        String[] e = expected.split("\n", -1);
        String[] a = actual.split("\n", -1);
        for (int i = 0; i < Math.min(e.length, a.length); i++) {
            if (!e[i].equals(a[i])) {
                return "line " + (i + 1) + ":\n  golden: " + e[i] + "\n  actual: " + a[i];
            }
        }
        return "one text is a prefix of the other (golden " + e.length + " lines, actual "
            + a.length + " lines)";
    }
}
