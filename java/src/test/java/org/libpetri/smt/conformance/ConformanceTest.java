package org.libpetri.smt.conformance;

import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.libpetri.smt.conformance.ConformanceNet.OutSpec;
import org.libpetri.smt.conformance.ConformanceRunner.Expected;
import org.libpetri.smt.conformance.ConformanceRunner.Outcome;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Cross-language conformance of Java's verifier against the Lean reference
 * ({@code spec/verification-fixtures/conformance/README.md}).
 *
 * <p>One dynamic test per corpus net that has an expected file, then a summary that prints the
 * per-route verdict and {@code unknown} counts (incompleteness is allowed, not hidden). Skips when
 * the corpus or its expected files are absent — fails instead under
 * {@code LIBPETRI_CONFORMANCE_REQUIRE=1} — and runs {@code enum} alone when z3 is absent.
 * {@code LIBPETRI_CONFORMANCE_DIR} points it at another corpus; {@code LIBPETRI_CONFORMANCE_DUMP}
 * collects every traced Violated trace for {@code scripts/conformance-replay.py}.
 *
 * <p>The plain tests below pin the loader, the reference replay and the checker on inline nets,
 * and show the checker goes red on each failure it exists to catch.
 */
class ConformanceTest {

    @TestFactory
    List<DynamicTest> conformance() {
        var corpus = ConformanceRunner.locateCorpus();
        if (corpus.isEmpty()) {
            return skipped("conformance corpus directory not found");
        }
        return tests(corpus.get());
    }

    /** One test that skips with {@code why} (or fails, under {@code LIBPETRI_CONFORMANCE_REQUIRE=1}). */
    static List<DynamicTest> skipped(String why) {
        boolean require = "1".equals(System.getenv("LIBPETRI_CONFORMANCE_REQUIRE"));
        return List.of(DynamicTest.dynamicTest("corpus", () -> {
            if (require) {
                fail(why + " (LIBPETRI_CONFORMANCE_REQUIRE=1)");
            }
            assumeTrue(false, why + "; skipping");
        }));
    }

    /** The per-net tests and a closing summary over {@code corpus}; skips when there is nothing to check. */
    static List<DynamicTest> tests(Path corpus) {
        var nets = ConformanceRunner.netFiles(corpus);
        if (nets.isEmpty()) {
            return skipped("no conformance nets under " + corpus.resolve("nets"));
        }
        var withExpected = nets.stream().filter(n -> Files.isRegularFile(ConformanceRunner.expectedFile(corpus, n))).toList();
        if (withExpected.isEmpty()) {
            return skipped("no expected verdicts under " + corpus.resolve("expected") + " (written by `lake exe reference`)");
        }
        var stats = new ConformanceRunner.Stats();
        stats.netsWithoutExpected = nets.size() - withExpected.size();
        var tests = new ArrayList<DynamicTest>();
        // Once the reference has written expected/, a net without its verdicts is stale (as in Rust).
        for (Path net : nets) {
            Path exp = ConformanceRunner.expectedFile(corpus, net);
            if (!Files.isRegularFile(exp)) {
                tests.add(DynamicTest.dynamicTest(net.getFileName().toString().replaceFirst("\\.json$", ""),
                    () -> fail("no " + exp + " (expected/ is stale)")));
            }
        }
        for (Path net : withExpected) {
            String name = net.getFileName().toString().replaceFirst("\\.json$", "");
            tests.add(DynamicTest.dynamicTest(name, () -> {
                var findings = ConformanceRunner.checkNet(net, ConformanceRunner.expectedFile(corpus, net), stats);
                assertTrue(findings.isEmpty(), () -> "CONFORMANCE FINDING(S) — report, do not adjust the corpus:\n  "
                    + String.join("\n  ", findings));
            }));
        }
        tests.add(DynamicTest.dynamicTest("summary", () -> {
            System.out.print(stats.render());
            stats.skippedRoutes.forEach(r -> System.out.println("conformance [java] SKIPPED " + r));
        }));
        return tests;
    }

    // ======================================================================
    // Loader, reference replay and checker on inline nets
    // ======================================================================

    private static ConformanceNet net(String json) throws Exception {
        return ConformanceNet.parse(new ObjectMapper().readTree(json));
    }

    /** Every input kind, arc kind and output kind; {@code z} is marked, undeclared and on no arc. */
    private static final String KINDS = """
        { "id": "kinds", "places": ["a", "b", "c", "d", "e", "g", "r", "q"],
          "marking": { "a": 2, "b": 3, "r": 1, "z": 1 },
          "transitions": [
            { "name": "t_ex", "inputs": [ { "place": "a", "kind": "exactly", "n": 2 } ], "reads": ["r"],
              "output": { "type": "xor", "children": [ { "type": "place", "place": "c" },
                { "type": "timeout", "afterMs": 50, "child": { "type": "forward", "from": "a", "to": "d" } } ] },
              "priority": 1 },
            { "name": "t_all", "inputs": [ { "place": "b", "kind": "all" } ], "inhibitors": ["c"],
              "output": { "type": "and", "children": [ { "type": "place", "place": "e" }, { "type": "place", "place": "g" } ] } },
            { "name": "t_al", "inputs": [ { "place": "e", "kind": "atLeast", "n": 1 } ], "resets": ["g"], "output": null },
            { "name": "t_one", "inputs": [ { "place": "z", "kind": "one" } ], "inhibitors": ["z"] } ],
          "properties": [
            { "id": "k0", "type": "place-bound", "place": "d", "bound": 1 },
            { "id": "k1", "type": "mutual-exclusion", "places": ["c", "e"] },
            { "id": "k2", "type": "unreachable", "places": ["c", "d"] },
            { "id": "k3", "type": "deadlock-free", "sinks": ["r", "c", "d", "z"] },
            { "id": "k4", "type": "terminates-at-sink", "sinks": ["c"] },
            { "id": "k5", "type": "quiescent-count", "places": ["b"], "min": 0 } ] }""";

    /** {@code t: one(a) -> b}. */
    private static final String SEQ = """
        { "id": "seq", "places": ["a", "b"], "marking": { "a": 1 },
          "transitions": [ { "name": "t", "inputs": [ { "place": "a", "kind": "one" } ],
                             "output": { "type": "place", "place": "b" } } ],
          "properties": [ { "id": "b0", "type": "place-bound", "place": "b", "bound": 0 },
                          { "id": "a1", "type": "place-bound", "place": "a", "bound": 1 } ] }""";

    @Test
    void theLoaderReadsEverySchemaConstruct() throws Exception {
        var n = net(KINDS);
        assertEquals(List.of("exactly", "all", "atLeast", "one"),
            n.transitions().stream().map(t -> t.inputs().getFirst().kind()).toList());
        assertEquals(2, n.transitions().getFirst().inputs().getFirst().n());
        assertEquals(List.of("r"), n.transitions().get(0).reads());
        assertEquals(List.of("c"), n.transitions().get(1).inhibitors());
        assertEquals(List.of("g"), n.transitions().get(2).resets());
        assertEquals(1, n.transitions().get(0).priority());
        var xor = assertInstanceOf(OutSpec.XorOut.class, n.transitions().get(0).output());
        var timeout = assertInstanceOf(OutSpec.TimeoutOut.class, xor.children().get(1));
        assertEquals(50, timeout.afterMs());
        assertEquals(new OutSpec.ForwardOut("a", "d"), timeout.child());
        assertEquals(null, n.transitions().get(2).output());
        assertEquals(null, n.transitions().get(3).output());
        assertEquals(null, n.properties().get(5).max());
        assertEquals(List.of("place-bound", "mutual-exclusion", "unreachable", "deadlock-free",
            "terminates-at-sink", "quiescent-count"), n.properties().stream().map(ConformanceNet.PropSpec::type).toList());
        n.properties().forEach(n::toSmt);

        var built = n.build();
        // `q` is declared with no arcs and is a place of the net; `z` is only marked.
        assertTrue(built.places().contains(ConformanceNet.place("q")));
        assertEquals(Map.of("a", 2, "b", 3, "r", 1, "z", 1), n.marking());
        assertEquals(1, n.initialMarking().tokens(ConformanceNet.place("z")));
    }

    @Test
    void aConstructJavaCannotExpressFailsLoudly() throws Exception {
        var n = net("""
            { "id": "three-way", "places": ["a", "b", "c"], "marking": {}, "transitions": [],
              "properties": [ { "id": "m", "type": "mutual-exclusion", "places": ["a", "b", "c"] } ] }""");
        var e = assertThrows(ConformanceNet.NotExpressible.class, () -> n.toSmt(n.properties().getFirst()));
        assertTrue(e.getMessage().contains("exactly 2 places"), e.getMessage());
    }

    @Test
    void theReplayFollowsTheReferenceFiringRule() throws Exception {
        var n = net(KINDS);
        var p = n.properties();
        // The timeout outcome forwards both consumed tokens of `exactly(2, a)` ([IO-014]).
        assertTrue(ReferenceSemantics.replay(n, p.get(0), List.of("t_ex")).isEmpty());
        // A flattener's branch suffix resolves to its transition.
        assertTrue(ReferenceSemantics.replay(n, p.get(0), List.of("t_ex_b1")).isEmpty());
        assertTrue(ReferenceSemantics.replay(n, p.get(1), List.of("t_all", "t_ex")).isEmpty());
        // The inhibitor on `c` blocks `t_all` once `t_ex` put a token there.
        assertTrue(ReferenceSemantics.replay(n, p.get(1), List.of("t_ex", "t_all")).isPresent());
        // `all` drains `b`, the reset clears `g`: {r, d:2} is quiescent without a `c`.
        assertTrue(ReferenceSemantics.replay(n, p.get(4), List.of("t_ex", "t_all", "t_al")).isEmpty());
        // `z` is marked and inhibits its own reader: the inert token strands at quiescence
        // unless it is a sink, which it is for k3.
        assertTrue(ReferenceSemantics.replay(n, p.get(3), List.of("t_all", "t_al", "t_ex")).isPresent());
        // Unbounded quiescent-count max: never violated from above.
        assertTrue(ReferenceSemantics.replay(n, p.get(5), List.of("t_ex")).isPresent());
    }

    /**
     * A completing action writes one token per claimed place ([IO-016]); only the timeout outcome
     * forwards the consumed multiplicity ([IO-014]). The completion leaves {@code {p1:1, s0:1}},
     * quiescent with {@code p1} stranded; the timeout outcome is a self-loop.
     */
    @Test
    void aTimeoutHasBothTheCompletionAndTheTimeoutOutcome() throws Exception {
        var n = net("""
            { "id": "timeout-outcomes", "places": ["p0", "p1"], "marking": { "p1": 3, "s0": 1 },
              "transitions": [ { "name": "t2", "inputs": [ { "place": "p1", "kind": "exactly", "n": 3 } ],
                "inhibitors": ["p0"],
                "output": { "type": "timeout", "afterMs": 50,
                            "child": { "type": "forward", "from": "p1", "to": "p1" } } } ],
              "properties": [ { "id": "d", "type": "deadlock-free", "sinks": ["p0", "s0"] },
                              { "id": "b", "type": "place-bound", "place": "p1", "bound": 2 } ] }""");
        assertTrue(ReferenceSemantics.replay(n, n.properties().get(0), List.of("t2")).isEmpty());
        assertTrue(ReferenceSemantics.replay(n, n.properties().get(1), List.of("t2")).isEmpty());
    }

    @Test
    void theCheckerFlagsAProvenTheReferenceViolates() throws Exception {
        var n = net(SEQ);
        var findings = ConformanceRunner.check(n, n.properties().get(0), "fabricated", Outcome.proven(),
            new Expected("b0", "violated", List.of("t"), null));
        assertTrue(findings.size() == 1 && findings.getFirst().contains("WRONG PROVEN"), findings::toString);
    }

    @Test
    void theCheckerFlagsATraceThatDoesNotReplay() throws Exception {
        var n = net(SEQ);
        var b0 = n.properties().get(0);
        var ref = new Expected("b0", "violated", List.of("t"), null);
        var twice = ConformanceRunner.check(n, b0, "fabricated", Outcome.violated(List.of("t", "t")), ref);
        assertTrue(twice.size() == 1 && twice.getFirst().contains("REPLAY FAILS"), twice::toString);
        var notBad = ConformanceRunner.check(n, b0, "fabricated", Outcome.violated(List.of()), null);
        assertTrue(notBad.size() == 1 && notBad.getFirst().contains("REPLAY FAILS"), notBad::toString);
        assertEquals(List.of(), ConformanceRunner.check(n, b0, "fabricated", Outcome.violated(List.of("t")), ref));
        assertEquals(List.of(), ConformanceRunner.check(n, b0, "fabricated", Outcome.unknown("cap"), ref));
        // A violation without a firing sequence fails rule 3 (README clarification 6) ...
        var untraced = ConformanceRunner.check(n, b0, "fabricated", Outcome.untraced(), ref);
        assertTrue(untraced.size() == 1 && untraced.getFirst().contains("WITHOUT A TRACE"), untraced::toString);
        // ... and rule 2 when the reference proves the property.
        var untracedWrong = ConformanceRunner.check(n, n.properties().get(1), "fabricated", Outcome.untraced(),
            new Expected("a1", "proven", List.of(), null));
        assertTrue(untracedWrong.size() == 1 && untracedWrong.getFirst().contains("WRONG VIOLATED"), untracedWrong::toString);
    }

    @Test
    void theCheckerFlagsAViolatedTheReferenceProves() throws Exception {
        var n = net(SEQ);
        var a1 = n.properties().get(1);
        var wrong = ConformanceRunner.check(n, a1, "fabricated", Outcome.violated(List.of("t")),
            new Expected("a1", "proven", List.of(), null));
        assertTrue(wrong.size() == 1 && wrong.getFirst().contains("WRONG VIOLATED"), wrong::toString);
        // A trace that replays against a `proven` reference falsifies the reference: loud.
        var falsifies = ConformanceRunner.check(n, n.properties().get(0), "fabricated", Outcome.violated(List.of("t")),
            new Expected("b0", "proven", List.of(), null));
        assertTrue(falsifies.size() == 1 && falsifies.getFirst().contains("FALSIFIES THE REFERENCE"), falsifies::toString);
    }

    /**
     * The default, split pass is held to rules 1, 3 and 4: a violation the reference proves is
     * allowed there (the split adds runs the atomic reference lacks), a trace of a split net is not
     * replayed, and a proven the reference violates, a missing trace and a trace of an unsplit net
     * that does not replay are still findings.
     */
    @Test
    void theDefaultPassHoldsRulesOneThreeAndFour() throws Exception {
        var n = net(SEQ);
        var b0 = n.properties().get(0);
        var a1 = n.properties().get(1);
        var proven = new Expected("a1", "proven", List.of(), null);
        var violated = new Expected("b0", "violated", List.of("t"), null);
        // Rule 2 is off: a replaying trace against a proven reference is counted, not reported.
        assertEquals(List.of(), ConformanceRunner.check(n, b0, "enum/split", false, Outcome.violated(List.of("t")),
            new Expected("b0", "proven", List.of(), null)));
        // A trace of a split net is not replayed, even one the reference could not fire.
        assertEquals(List.of(), ConformanceRunner.check(n, b0, "enum/split", false,
            Outcome.violatedOfSplitNet(List.of("t", "complete:t"), true), violated));
        // Rule 1, rule 3 and rule 4 still hold.
        var wrongProven = ConformanceRunner.check(n, b0, "enum/split", false, Outcome.proven(), violated);
        assertTrue(wrongProven.size() == 1 && wrongProven.getFirst().contains("WRONG PROVEN"), wrongProven::toString);
        var untraced = ConformanceRunner.check(n, a1, "enum/split", false, Outcome.untraced(), proven);
        assertTrue(untraced.size() == 1 && untraced.getFirst().contains("WITHOUT A TRACE"), untraced::toString);
        var noReplay = ConformanceRunner.check(n, b0, "enum/split", false, Outcome.violated(List.of("t", "t")), violated);
        assertTrue(noReplay.size() == 1 && noReplay.getFirst().contains("REPLAY FAILS"), noReplay::toString);
        // The atomic pass still reports rule 2.
        var rule2 = ConformanceRunner.check(n, a1, "enum", true, Outcome.violated(List.of("t")), proven);
        assertTrue(rule2.size() == 1 && rule2.getFirst().contains("WRONG VIOLATED"), rule2::toString);
    }
}
