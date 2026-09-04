package org.libpetri.smt;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
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

    private static void runFixture(JsonNode fixture, Path goldenDir) throws IOException {
        String id = fixture.get("id").asText();
        var named = VerificationNets.build(fixture.get("net").asText());
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
        verifier.semiflowInvariants(VerdictParityTest.semiflowInvariants(fixture));
        var scripts = verifier.encodeScripts();

        compare(id, goldenDir.resolve("horn.smt2"), scripts.horn());
        compare(id, goldenDir.resolve("certificate.smt2"), scripts.certificate());
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
