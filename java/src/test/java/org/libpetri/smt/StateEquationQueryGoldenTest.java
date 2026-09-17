package org.libpetri.smt;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.libpetri.core.Place;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.fixtures.VerificationNets;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.libpetri.smt.z3.StateEquationQuery;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-018] AC7 / [VER-013] AC1: the state-equation phase's first query, as
 * {@link StateEquationQuery#encode} writes it, against the Rust goldens under
 * {@code spec/verification-fixtures/scripts/<id>/state-equation.smt2}, byte for byte.
 *
 * <p>A golden exists exactly where the TypeScript and Rust verifiers would send the query, so
 * this test reads the builder inputs from the same fixture fields {@link SmtScriptParityTest}
 * does and calls the encoder directly, with no refinement.
 */
class StateEquationQueryGoldenTest {

    @TestFactory
    List<DynamicTest> firstQueryMatchesTheGolden() throws IOException {
        Path fixturesFile = VerdictParityTest.locateFixtures();
        JsonNode root = new ObjectMapper().readTree(Files.readString(fixturesFile));
        Path scripts = fixturesFile.getParent().resolve("scripts");
        var tests = new ArrayList<DynamicTest>();
        for (JsonNode fixture : root.get("fixtures")) {
            String id = fixture.get("id").asText();
            Path golden = scripts.resolve(id).resolve("state-equation.smt2");
            if (Files.isRegularFile(golden)) {
                tests.add(DynamicTest.dynamicTest(id, () -> compare(fixture, golden)));
            }
        }
        assertFalse(tests.isEmpty(), "no state-equation golden under " + scripts);
        return tests;
    }

    /** The two fixtures the port is pinned on must be compared, never skipped. */
    @Test
    void pinsTheLinearFixtures() throws IOException {
        Path fixturesFile = VerdictParityTest.locateFixtures();
        JsonNode root = new ObjectMapper().readTree(Files.readString(fixturesFile));
        Path scripts = fixturesFile.getParent().resolve("scripts");
        int compared = 0;
        for (JsonNode fixture : root.get("fixtures")) {
            String id = fixture.get("id").asText();
            if (!id.equals("mutex-with-lock-proven") && !id.equals("conserved-bound-proven")) {
                continue;
            }
            assertTrue(PInvariantComputer.nonlinearPlaces(flatten(fixture)).isEmpty(), id);
            compare(fixture, scripts.resolve(id).resolve("state-equation.smt2"));
            compared++;
        }
        assertEquals(2, compared);
    }

    private static FlatNet flatten(JsonNode fixture) {
        var named = VerificationNets.build(fixture.get("net").asText());
        return NetFlattener.flatten(named.net(), named.environmentPlaces(), named.environmentMode());
    }

    private static void compare(JsonNode fixture, Path golden) throws IOException {
        String id = fixture.get("id").asText();
        var named = VerificationNets.build(fixture.get("net").asText());
        FlatNet flat = flatten(fixture);
        var conditional = new ArrayList<RestSet.ConditionalSinks>();
        VerdictParityTest.sinkPlacesWhen(fixture).forEach((marker, places) ->
            conditional.add(new RestSet.ConditionalSinks(marker, new LinkedHashSet<Place<?>>(places))));
        String actual = StateEquationQuery.encode(flat, named.initialMarking(),
            VerdictParityTest.parseProperty(fixture.get("property")),
            new LinkedHashSet<>(VerdictParityTest.sinkPlaces(fixture)), conditional, List.of());
        assertEquals(Files.readString(golden), actual, () -> "SCRIPT PARITY FINDING [" + id + "]: "
            + golden + " differs from StateEquationQuery.encode — report the divergence, never edit the golden by hand");
    }
}
