package org.libpetri.smt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.IOException;
import java.nio.file.Files;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.function.Function;

import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.runtime.BitmapNetExecutor;
import org.libpetri.runtime.PetriNetExecutor;
import org.libpetri.runtime.PrecompiledNetExecutor;
import org.libpetri.smt.SmtVerificationResult.Route;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.BoundedRun;
import org.libpetri.smt.z3.LinearBound;
import org.libpetri.smt.z3.NameColouredEncoder;
import org.libpetri.smt.z3.SlotBoundLp;
import org.libpetri.smt.z3.SmtEncoder;
import org.libpetri.smt.z3.StateEquationPhase;
import org.libpetri.smt.z3.StateEquationQuery;

/**
 * [NU-055] name alignment: the fixtures of {@code spec/verification-fixtures/nu-aligned-fixtures.json}
 * (AC1, AC2, AC3, AC6), the routes that must not decide it (AC4), the predicate's invariance under
 * name permutation and a run with a pinned minting scope (AC5). The fixture nets are built as
 * {@link JoinRelayTest.Net} builds the relay fixtures, from the same row schema.
 */
class NuNameAlignmentTest {

    private static final String ONLY_B = "decided only by the name-partition state-class graph (NU-055, Route B)";

    // ── fixtures ──────────────────────────────────────────────────────────────────────────

    private static List<JsonNode> fixtures() throws IOException {
        var file = VerdictParityTest.locateFixtures().resolveSibling("nu-aligned-fixtures.json");
        var out = new ArrayList<JsonNode>();
        new ObjectMapper().readTree(Files.readString(file)).get("fixtures").forEach(out::add);
        return out;
    }

    private static JsonNode fixture(String id) throws IOException {
        return fixtures().stream().filter(f -> f.get("id").asText().equals(id)).findFirst().orElseThrow();
    }

    private static List<String> names(JsonNode array) {
        var out = new ArrayList<String>();
        if (array != null) {
            array.forEach(n -> out.add(n.asText()));
        }
        return out;
    }

    /** The fixture's net, built from its rows. */
    private static JoinRelayTest.Net net(JsonNode f) {
        var net = new JoinRelayTest.Net(f.get("net").asText());
        for (JsonNode row : f.get("rows")) {
            net.t(row.get(0).asText(), names(row.get(1)), names(row.get(2)), names(row.get(3)), names(row.get(4)));
        }
        return net;
    }

    private static SmtProperty property(JsonNode f, JoinRelayTest.Net net) {
        var prop = f.get("property");
        var places = names(prop.get("places"));
        return switch (prop.get("type").asText()) {
            case "name-aligned" -> SmtProperty.nameAligned(net.p(places.get(0)), net.p(places.get(1)));
            case "quiescent-name-aligned" ->
                SmtProperty.quiescentNameAligned(net.p(places.get(0)), net.p(places.get(1)));
            case "quiescent-count" -> SmtProperty.quiescentCount(places.stream().map(net::p).toList(),
                prop.get("min").asInt(), OptionalInt.of(prop.get("max").asInt()));
            default -> throw new IllegalArgumentException("unknown fixture property type: " + prop.get("type"));
        };
    }

    /** A verifier configured as the fixture says, over {@code net}. */
    private static SmtVerifier verifier(JsonNode f, JoinRelayTest.Net net) {
        var v = SmtVerifier.forNet(net.build())
            .initialMarking(m -> f.get("marking").properties().forEach(e -> m.tokens(net.p(e.getKey()), e.getValue().asInt())))
            .property(property(f, net))
            .mintTransitions(names(f.get("mintTransitions")).toArray(String[]::new))
            .carrierPlaces(names(f.get("carrierPlaces")).stream().map(net::p).toArray(Place<?>[]::new))
            .fragmentMode(switch (f.get("fragmentMode").asText()) {
                case "base" -> FragmentMode.BASE;
                case "extended" -> FragmentMode.EXTENDED;
                default -> throw new IllegalArgumentException("unknown fixture fragmentMode: " + f.get("fragmentMode"));
            })
            .timeout(Duration.ofSeconds(30));
        var budgets = names(f.get("budgetPlaces"));
        if (!budgets.isEmpty()) {
            v.budgetPlaces(budgets.stream().map(net::p).toArray(Place<?>[]::new));
        }
        var env = names(f.get("environmentPlaces"));
        if (!env.isEmpty()) {
            v.environmentPlaces(env.stream().map(n -> EnvironmentPlace.of(net.p(n))).toArray(EnvironmentPlace<?>[]::new));
            if ("always-available".equals(f.get("environmentMode").asText())) {
                v.environmentMode(EnvironmentAnalysisMode.alwaysAvailable());
            }
        }
        return v;
    }

    private static SmtVerifier verifier(JsonNode f) {
        return verifier(f, net(f));
    }

    private static String verdict(SmtVerificationResult r) {
        return r.isProven() ? "proven" : r.isViolated() ? "violated" : "unknown";
    }

    private static String reason(SmtVerificationResult r) {
        return r.verdict() instanceof SmtVerificationResult.Verdict.Unknown(var why) ? why : "";
    }

    /**
     * What the reason of an {@code unknown} fixture must name: EXTENDED for a BASE run, else the
     * environment place, else the coloured place the initial marking marks, else the uncoloured
     * property place.
     */
    private static String namedByReason(JsonNode f) {
        if (f.get("fragmentMode").asText().equals("base")) {
            return "EXTENDED";
        }
        var env = names(f.get("environmentPlaces"));
        if (!env.isEmpty()) {
            return "'" + env.get(0) + "'";
        }
        var coloured = new HashSet<>(names(f.get("carrierPlaces")));
        for (JsonNode row : f.get("rows")) {
            coloured.addAll(names(row.get(3)));
            coloured.addAll(names(row.get(4)));
        }
        for (var it = f.get("marking").fieldNames(); it.hasNext(); ) {
            var n = it.next();
            if (coloured.contains(n)) {
                return "'" + n + "'";
            }
        }
        var uncoloured = names(f.get("property").get("places")).stream().filter(n -> !coloured.contains(n))
            .findFirst().orElseThrow(() -> new AssertionError(f.get("id") + ": nothing for the reason to name"));
        return "'" + uncoloured + "'";
    }

    /** The NU-055 fixture runner: verdict, Route B attribution and witness length of every fixture. */
    @TestFactory
    List<DynamicTest> nu055_alignedFixtures() throws IOException {
        var all = fixtures();
        assertEquals(10, all.size(), "nu-aligned-fixtures.json lists ten fixtures");
        var tests = new ArrayList<DynamicTest>();
        for (var f : all) {
            tests.add(DynamicTest.dynamicTest(f.get("id").asText(), () -> {
                var result = verifier(f).verify();
                // Route attribution first: every fixture is decided (or refused) by Route B.
                assertEquals("B", f.get("route").asText());
                assertEquals(Route.NU_SCG, result.route(), result.report());
                assertTrue(result.report().contains("Route B"), result.report());
                assertEquals(f.get("expected").asText(), verdict(result), result.report());
                if (!result.isProven() && !result.isViolated()) {
                    assertTrue(reason(result).contains(namedByReason(f)), reason(result));
                }
                if (f.has("witnessLength")) {
                    assertEquals(f.get("witnessLength").asInt(), result.counterexampleTransitions().size(),
                        result.report());
                    // NU-055 "Violated": a path of the graph, not of the flat abstract semantics.
                    assertNull(result.counterexampleConfirmed());
                }
            }));
        }
        return tests;
    }

    // ── description and refusals ──────────────────────────────────────────────────────────

    private static JsonNode fixed() throws IOException {
        return fixture("nu-aligned-search-quiescent-proven");
    }

    @Test
    void nu055_describesBothPropertiesByteForByte() throws IOException {
        var box = Place.of("box", String.class);
        var list = Place.of("list", String.class);
        assertEquals("Name alignment of box and list", SmtProperty.nameAligned(box, list).description());
        assertEquals("Quiescent name alignment of box and list",
            SmtProperty.quiescentNameAligned(box, list).description());
        var result = verifier(fixed()).verify();
        assertTrue(result.report().contains("Property: Quiescent name alignment of box and list"), result.report());
    }

    @Test
    void nu055_ac2_aPlaceAbsentFromTheNetIsUnknownNamingIt() throws IOException {
        var f = fixed();
        var net = net(f);
        var result = verifier(f, net)
            .property(SmtProperty.quiescentNameAligned(net.p("box"), Place.of("ghost", String.class))).verify();
        assertEquals("unknown", verdict(result), result.report());
        assertTrue(reason(result).contains("'ghost'"), reason(result));
    }

    @Test
    void nu055_ac2_nameAlignedOnAnUncolouredPlaceIsUnknownNamingIt() throws IOException {
        var f = fixed();
        var net = net(f);
        var result = verifier(f, net).property(SmtProperty.nameAligned(net.p("ready"), net.p("list"))).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertTrue(reason(result).contains("'ready'"), result.report());
    }

    @Test
    void nu055_ac3_underBaseACarrierIsUncolouredAndTheReasonNamesExtended() {
        // BASE colours the match keys alone; on a net inside the BASE fragment a carrier is
        // uncoloured, which the reason names together with the mode that colours it.
        var n = new JoinRelayTest.Net("baseCarrier")
            .t("send", List.of("go"), List.of("box", "reply"))
            .t("join", List.of("box", "reply"), List.of("done"), List.of("box", "reply"), List.of());
        var result = SmtVerifier.forNet(n.build())
            .initialMarking(m -> m.tokens(n.p("go"), 1))
            .mintTransitions("send")
            .carrierPlaces(n.p("done"))
            .property(SmtProperty.nameAligned(n.p("box"), n.p("done")))
            .verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertTrue(reason(result).contains("'done'"), result.report());
        assertTrue(reason(result).contains("EXTENDED"), result.report());
    }

    @Test
    void nu055_ac3_theBaseRunNamesTheIgnoredRelayDeclarations() throws IOException {
        var result = verifier(fixture("nu-aligned-search-base-unknown")).verify();
        assertTrue(result.report().contains(
            "ν relay declarations ignored under BASE fragment mode (NU-054): 'apply' -> 'box', 'apply' -> 'staged'"),
            result.report());
    }

    /** NU-051: outside the EXTENDED fragment the verdict is unknown and no other route is named. */
    @Test
    void nu055_outsideTheExtendedFragmentIsUnknownAndNamesNoOtherRoute() throws IOException {
        var f = fixed();
        var net = net(f);
        // A read arc on the coloured `box` puts the net outside every fragment.
        net.add(Transition.builder("peek").inputs(Arc.In.one(net.p("idle"))).outputs(Arc.Out.place(net.p("idle")))
            .read(net.p("box")).build());
        var result = verifier(f, net).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertEquals("unknown", verdict(result), result.report());
        assertTrue(reason(result).contains("EXTENDED"), reason(result));
        assertFalse(reason(result).contains("over-approximation"), reason(result));
        assertFalse(result.report().contains("verified via sound over-approximation"), result.report());
    }

    @Test
    void nu055_ac6_theBugVariantWithAColouredInitialTokenIsUnknownNamingThePlace() throws IOException {
        var f = fixture("nu-aligned-search-bug-quiescent-violated");
        var net = net(f);
        var result = verifier(f, net).initialMarking(m -> {
            f.get("marking").properties().forEach(e -> m.tokens(net.p(e.getKey()), e.getValue().asInt()));
            m.tokens(net.p("reply"), 1);
        }).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertTrue(reason(result).contains("'reply'"), result.report());
    }

    @Test
    void nu055_quiescentNameAlignedCarriesNoSinkClause() throws IOException {
        var f = fixture("nu-aligned-search-bug-quiescent-violated");
        var net = net(f);
        var result = verifier(f, net).sinkPlaces(net.p("box"), net.p("list")).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertEquals("violated", verdict(result), result.report());
        assertEquals(12, result.counterexampleTransitions().size(), result.report());
    }

    /** NU-055 reads the reap-aware quiescence of VER-002 (TIME-013). */
    @Test
    void nu055_quiescentNameAlignedReadsReapAwareQuiescence() {
        // `sendA` and `sendB` mint two names into `box` and `list`; `drop`, a deadline drain of
        // `list`, is all that realigns them. A late executor reaps it and rests misaligned.
        var n = new JoinRelayTest.Net("reapedAlignment")
            .t("sendA", List.of("a"), List.of("box"))
            .t("sendB", List.of("b"), List.of("list"));
        n.add(Transition.builder("drop").inputs(Arc.In.one(n.p("list"))).outputs(Arc.Out.place(n.p("done")))
            .timing(Timing.deadline(Duration.ofMillis(10))).build());
        Function<Boolean, SmtVerifier> verifier = noReaping -> SmtVerifier.forNet(n.build())
            .initialMarking(m -> m.tokens(n.p("a"), 1).tokens(n.p("b"), 1))
            .mintTransitions("sendA", "sendB")
            .carrierPlaces(n.p("box"), n.p("list"))
            .fragmentMode(FragmentMode.EXTENDED)
            .assumeNoReaping(noReaping)
            .property(SmtProperty.quiescentNameAligned(n.p("box"), n.p("list")));
        var late = verifier.apply(false).verify();
        assertEquals(Route.NU_SCG, late.route(), late.report());
        assertEquals("violated", verdict(late), late.report());
        assertEquals(List.of("sendA", "sendB"), late.counterexampleTransitions());
        var onTime = verifier.apply(true).verify();
        assertEquals(Route.NU_SCG, onTime.route(), onTime.report());
        assertEquals("proven", verdict(onTime), onTime.report());
    }

    /** NU-055 "Modelled injection": under arrivals(2) the keystrokes are closed into the net and Route B decides it. */
    @Test
    void nu055_underArrivalsTheKeystrokesAreClosedIntoTheNet() throws IOException {
        for (var c : List.of(
                Map.entry("nu-aligned-search-env-quiescent-unknown", "proven"),
                Map.entry("nu-aligned-search-bug-env-quiescent-unknown", "violated"))) {
            var result = verifier(fixture(c.getKey())).environmentMode(EnvironmentAnalysisMode.arrivals(2, 2)).verify();
            assertEquals(Route.NU_SCG, result.route(), c.getKey() + "\n" + result.report());
            assertEquals(c.getValue(), verdict(result), result.report());
        }
    }

    @Test
    void nu055_ac6_underBoundedTheEnvironmentPlaceIsNamedAndArrivalsPointedTo() throws IOException {
        var result = verifier(fixture("nu-aligned-search-env-quiescent-unknown"))
            .environmentMode(EnvironmentAnalysisMode.bounded(2)).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertTrue(reason(result).contains("'typed'"), reason(result));
        assertTrue(reason(result).contains("arrivals(k)"), reason(result));
    }

    // ── AC4: no other route decides name alignment ────────────────────────────────────────

    /** The fixed net, its initial marking and flat net, and both properties over box and list. */
    private record Routes(PetriNet net, MarkingState m0, FlatNet flat, JsonNode f,
                          List<SmtProperty> props) {
        static Routes of() throws IOException {
            var f = fixed();
            var n = NuNameAlignmentTest.net(f);
            var b = MarkingState.builder();
            f.get("marking").properties().forEach(e -> b.tokens(n.p(e.getKey()), e.getValue().asInt()));
            var net = n.build();
            return new Routes(net, b.build(), NetFlattener.flatten(net, Set.of(),
                EnvironmentAnalysisMode.ignore()), f, List.of(
                SmtProperty.nameAligned(n.p("box"), n.p("list")),
                SmtProperty.quiescentNameAligned(n.p("box"), n.p("list"))));
        }
    }

    @Test
    void nu055_ac4_encodeScriptsReturnsNoScript() throws IOException {
        var f = fixed();
        var net = net(f);
        for (var prop : Routes.of().props()) {
            var e = assertThrows(IllegalStateException.class, () -> verifier(f, net).property(prop).encodeScripts());
            assertTrue(e.getMessage().contains(ONLY_B), e.getMessage());
        }
    }

    @Test
    void nu055_ac4_routeAGivesNoEncoding() throws IOException {
        // With the budget fixture's declaration the net is in Route A's fragment: a plan exists,
        // but a colour slot is not a name, so it encodes no name-alignment query.
        var r = Routes.of();
        var mints = NameFragment.declaredMints(r.net(), Set.of("slot"), Set.copyOf(names(r.f().get("mintTransitions"))));
        var plan = NameColouredEncoder.buildPlan(r.net(), r.flat(), r.m0(), mints, FragmentMode.EXTENDED,
            Set.copyOf(names(r.f().get("carrierPlaces"))), c -> SlotBoundLp.solve(r.flat(), r.m0(), c), _ -> {});
        assertNotNull(plan);
        for (var prop : r.props()) {
            assertNull(NameColouredEncoder.encode(plan, r.flat(), r.m0(), prop, List.of(), Set.of()));
        }
    }

    @Test
    void nu055_ac4_theFlatEncoderGivesNoScript() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            var e = assertThrows(IllegalArgumentException.class,
                () -> SmtEncoder.encode(r.flat(), r.m0(), prop, List.of(), Set.of(), false));
            assertTrue(e.getMessage().contains(ONLY_B), e.getMessage());
        }
    }

    @Test
    void nu055_ac4_theLinearBoundHasNoDemand() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            assertNull(LinearBound.violationDemand(r.flat(), prop));
            assertNull(LinearBound.encode(r.flat(), r.m0(), prop));
        }
    }

    @Test
    void nu055_ac4_theStateEquationPhaseIsInconclusive() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            var e = assertThrows(IllegalArgumentException.class,
                () -> StateEquationQuery.encode(r.flat(), r.m0(), prop, Set.of(), List.of(), List.of()));
            assertTrue(e.getMessage().contains(ONLY_B), e.getMessage());
            var outcome = StateEquationPhase.runStateEquationPhase(r.flat(), r.m0(), prop, Set.of(), List.of(),
                (script, phase, timeoutMs) -> { throw new AssertionError("no solver call expected"); });
            var inconclusive = assertInstanceOf(StateEquationPhase.StateEquationOutcome.Inconclusive.class, outcome);
            assertTrue(inconclusive.reason().contains(ONLY_B), inconclusive.reason());
        }
    }

    @Test
    void nu055_ac4_theFiringBoundPhaseIsInconclusive() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            var outcome = BoundedRun.runFiringBoundPhase(r.flat(), r.m0(), prop, Set.of(), List.of(),
                (script, phase, timeoutMs) -> { throw new AssertionError("no solver call expected"); });
            var inconclusive = assertInstanceOf(BoundedRun.FiringBoundOutcome.Inconclusive.class, outcome);
            assertTrue(inconclusive.reason().contains(ONLY_B), inconclusive.reason());
        }
    }

    @Test
    void nu055_ac4_theBoundedEnumerationIsUnknown() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            var outcome = ScgVerifier.verify(r.net(), r.m0(), prop, Set.of(), 10_000, List.of());
            var decided = assertInstanceOf(ScgVerifier.Outcome.Decided.class, outcome);
            var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, decided.verdict());
            assertTrue(unknown.reason().contains(ONLY_B), unknown.reason());
        }
    }

    @Test
    void nu055_ac4_aGraphWithoutANameLayerRefusesToDecideIt() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            // With or without a resting class: no class may be read as aligned for want of names.
            for (boolean quiescent : new boolean[] {true, false}) {
                var view = new GraphDecision.ClassView() {
                    @Override
                    public int count() {
                        return 1;
                    }

                    @Override
                    public MarkingState markingOf(int i) {
                        return r.m0();
                    }

                    @Override
                    public boolean isQuiescent(int i) {
                        return quiescent;
                    }
                };
                var e = assertThrows(IllegalArgumentException.class,
                    () -> GraphDecision.decideOverClasses(view, prop, Set.of(), List.of()));
                assertTrue(e.getMessage().contains(ONLY_B), e.getMessage());
            }
        }
    }

    @Test
    void nu055_ac4_theAbstractReplayerReadsNoNames() throws IOException {
        var r = Routes.of();
        for (var prop : r.props()) {
            var e = assertThrows(IllegalArgumentException.class,
                () -> AbstractReplayer.violates(r.flat(), prop, Set.of(), AbstractReplayer.toVector(r.flat(), r.m0())));
            assertTrue(e.getMessage().contains(ONLY_B), e.getMessage());
        }
    }

    @Test
    void nu055_ac4_aDeclaredBudgetPlaceStillSendsNameAlignedToRouteB() throws IOException {
        var result = verifier(fixture("nu-aligned-search-budget-transient-violated")).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertFalse(result.report().contains("Route A"), result.report());
    }

    @Test
    void nu055_ac4_aRouteBTruncationStaysUnknownWithNoDeferralToRouteA() throws IOException {
        var f = fixed();
        var net = net(f);
        var result = verifier(f, net).budgetPlaces(net.p("slot")).nuMaxClasses(5).verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertEquals("unknown", verdict(result), result.report());
        assertFalse(result.report().contains("deferring to Route A"), result.report());
    }

    @Test
    void nu055_ac4_prefixRule_aTruncatedNameAlignedGraphIsViolatedByAStoredClass() throws IOException {
        // The fixed net's graph closes at 31 classes and its first misaligned class is the 24th.
        var f = fixture("nu-aligned-search-transient-violated");
        // A reachability-safety property: the build stops at its first violating class (VER-012).
        var full = verifier(f).verify();
        assertTrue(full.report().contains("Route B stopped at the first violating class"), full.report());
        var cut = verifier(f).nuMaxClasses(20).verify();
        assertEquals(Route.NU_SCG, cut.route(), cut.report());
        assertEquals("unknown", verdict(cut), cut.report());
        var prefix = verifier(f).nuMaxClasses(25).verify();
        assertEquals("violated", verdict(prefix), prefix.report());
        assertEquals(8, prefix.counterexampleTransitions().size(), prefix.report());
    }

    @Test
    void nu055_ac4_prefixRule_aTruncatedQuiescentNameAlignedGraphIsViolatedByAnExpandedClassAtRest() {
        // `gen` grows `junk` without bound, so the graph never closes; `stop` ends the generator,
        // and after `sendA` and `sendB` minted two names into `box` and `list` the net rests misaligned.
        var n = new JoinRelayTest.Net("unboundedRest")
            .t("sendA", List.of("a"), List.of("box"))
            .t("sendB", List.of("b"), List.of("list"))
            .t("gen", List.of("g"), List.of("g", "junk"))
            .t("stop", List.of("g"), List.of("done"));
        var result = SmtVerifier.forNet(n.build())
            .initialMarking(m -> m.tokens(n.p("a"), 1).tokens(n.p("b"), 1).tokens(n.p("g"), 1))
            .mintTransitions("sendA", "sendB")
            .carrierPlaces(n.p("box"), n.p("list"))
            .fragmentMode(FragmentMode.EXTENDED)
            .nuMaxClasses(50)
            .property(SmtProperty.quiescentNameAligned(n.p("box"), n.p("list")))
            .verify();
        assertEquals(Route.NU_SCG, result.route(), result.report());
        assertEquals("violated", verdict(result), result.report());
        assertEquals(3, result.counterexampleTransitions().size(), result.report());
        assertTrue(result.report().contains("was truncated at 50 classes; the violation was found in the explored prefix"),
            result.report());
    }

    @Test
    void nu055_ac4_existingPropertiesOnTheMatchlessBugVariantKeepTheirRoute() throws IOException {
        // The has-match gate is lifted for name alignment only: a quiescentCount on a net without a
        // matched transition is still decided by the plain enumeration (VER-017).
        var f = fixture("nu-aligned-search-bug-quiescent-violated");
        var net = net(f);
        var count = verifier(f, net)
            .property(SmtProperty.quiescentCount(List.of(net.p("list")), 1, OptionalInt.of(1))).verify();
        assertEquals(Route.ENUMERATION, count.route(), count.report());
        var dl = verifier(f, net).property(SmtProperty.deadlockFree()).verify();
        assertNotEquals(Route.NU_SCG, dl.route(), dl.report());
    }

    // ── AC5: invariance under name permutation ────────────────────────────────────────────

    /**
     * The class-level predicate and canonical key under a symbol permutation live in the analysis
     * package ({@code NameMarkingAlignmentTest}); here the predicate is read through the decision.
     */
    @Test
    void nu055_ac5_safetyViolationReadsTheNameLayerForNameAlignedOnly() {
        var box = Place.of("box", String.class);
        var list = Place.of("list", String.class);
        var view = new GraphDecision.NamedClassView() {
            @Override
            public int count() {
                return 1;
            }

            @Override
            public MarkingState markingOf(int i) {
                return MarkingState.empty();
            }

            @Override
            public boolean isQuiescent(int i) {
                return true;
            }

            @Override
            public boolean namesAligned(int i, Place<?> p, Place<?> q) {
                return false;
            }
        };
        assertTrue(GraphDecision.safetyViolation(SmtProperty.nameAligned(box, list)).violates(view, 0));
        assertNull(GraphDecision.safetyViolation(SmtProperty.quiescentNameAligned(box, list)));
        assertEquals(0, GraphDecision.decideOverClasses(view, SmtProperty.quiescentNameAligned(box, list),
            Set.of(), List.of()));
    }

    @Test
    void nu055_ac5_theBugVariantClassifiesOnlyWithTheMatchlessGateLifted() throws IOException {
        var f = fixture("nu-aligned-search-bug-quiescent-violated");
        var net = net(f).build();
        assertTrue(net.transitions().stream().allMatch(t -> t.matchSpec() == null));
        var carriers = Set.copyOf(names(f.get("carrierPlaces")));
        var mints = Set.copyOf(names(f.get("mintTransitions")));
        // Without a matched transition the default classifier sees no ν-net; a name-alignment query lifts that.
        assertNull(NameFragment.classify(net, FragmentMode.EXTENDED, carriers, mints));
        var fragment = NameFragment.classify(net, FragmentMode.EXTENDED, carriers, mints, true);
        assertNotNull(fragment);
        for (var c : carriers) {
            assertTrue(fragment.isColoured(c), c);
        }
        assertFalse(fragment.isColoured("ready"));
    }

    // ── AC5: a run with a pinned minting scope (NU-010, NU-011) ──────────────────────────

    private static final List<Map.Entry<String, Integer>> INITIAL =
        List.of(Map.entry("typed", 2), Map.entry("idle", 1), Map.entry("listEmpty", 1), Map.entry("slot", 1));

    /**
     * The search-as-you-type net of NU-055 with executable actions: each token of a coloured place
     * is its name. {@code fetchA} answers only once {@code show} has shown a result, so the reply to
     * the first keystroke lands after the reply to the second, deterministically: the run the bug
     * variant's counterexample describes.
     */
    private static final class SearchAsYouType {
        final Map<String, Place<String>> places = new LinkedHashMap<>();
        final PetriNet net;

        SearchAsYouType(boolean bug) {
            var firstShown = new CompletableFuture<Void>();
            Function<String, TransitionAction> unit = out -> ctx -> {
                ctx.output(p(out), "unit");
                return CompletableFuture.completedFuture(null);
            };
            Function<String, TransitionAction> mint = inflight -> ctx -> {
                var n = ctx.freshName().toString();
                ctx.output(p("box"), n);
                ctx.output(p(inflight), n);
                return CompletableFuture.completedFuture(null);
            };
            Function<String, NameId> key = NameId::of;
            var ts = new ArrayList<Transition>();
            ts.add(Transition.builder("first").inputs(Arc.In.one(p("idle")), Arc.In.one(p("typed")))
                .outputs(Arc.Out.place(p("armedA"))).action(unit.apply("armedA")).build());
            ts.add(Transition.builder("retire").inputs(Arc.In.one(p("box")), Arc.In.one(p("typed")))
                .outputs(Arc.Out.place(p("armedB"))).action(unit.apply("armedB")).build());
            ts.add(Transition.builder("sendA").inputs(Arc.In.one(p("armedA")))
                .outputs(Arc.Out.and(p("box"), p("inflightA"))).action(mint.apply("inflightA")).build());
            ts.add(Transition.builder("sendB").inputs(Arc.In.one(p("armedB")))
                .outputs(Arc.Out.and(p("box"), p("inflightB"))).action(mint.apply("inflightB")).build());
            ts.add(Transition.builder("fetchA").inputs(Arc.In.one(p("inflightA"))).outputs(Arc.Out.place(p("reply")))
                .action(ctx -> {
                    var n = ctx.input(p("inflightA"));
                    return firstShown.thenRun(() -> ctx.output(p("reply"), n));
                }).build());
            ts.add(Transition.builder("fetchB").inputs(Arc.In.one(p("inflightB"))).outputs(Arc.Out.place(p("reply")))
                .action(ctx -> {
                    ctx.output(p("reply"), ctx.input(p("inflightB")));
                    return CompletableFuture.completedFuture(null);
                }).build());
            if (bug) {
                ts.add(Transition.builder("apply_bug").inputs(Arc.In.one(p("reply")), Arc.In.one(p("slot")))
                    .outputs(Arc.Out.and(p("staged"), p("clr"))).action(ctx -> {
                        ctx.output(p("staged"), ctx.input(p("reply")));
                        ctx.output(p("clr"), "unit");
                        return CompletableFuture.completedFuture(null);
                    }).build());
            } else {
                ts.add(Transition.builder("apply")
                    .inputs(Arc.In.one(p("reply")), Arc.In.one(p("box")), Arc.In.one(p("slot")))
                    .match(MatchSpec.builder().key(p("reply"), key).key(p("box"), key)
                        .relayTo(p("box"), key).relayTo(p("staged"), key).build())
                    .outputs(Arc.Out.and(p("box"), p("staged"), p("clr"))).action(ctx -> {
                        var n = ctx.input(p("reply"));
                        ctx.output(p("box"), n);
                        ctx.output(p("staged"), n);
                        ctx.output(p("clr"), "unit");
                        return CompletableFuture.completedFuture(null);
                    }).build());
            }
            ts.add(Transition.builder("clearNone").inputs(Arc.In.one(p("listEmpty")), Arc.In.one(p("clr")))
                .outputs(Arc.Out.place(p("ready"))).action(unit.apply("ready")).build());
            ts.add(Transition.builder("clear").inputs(Arc.In.one(p("list")), Arc.In.one(p("clr")))
                .outputs(Arc.Out.place(p("ready"))).action(unit.apply("ready")).build());
            ts.add(Transition.builder("show").inputs(Arc.In.one(p("staged")), Arc.In.one(p("ready")))
                .outputs(Arc.Out.and(p("list"), p("slot"))).action(ctx -> {
                    ctx.output(p("list"), ctx.input(p("staged")));
                    ctx.output(p("slot"), "unit");
                    firstShown.complete(null);
                    return CompletableFuture.completedFuture(null);
                }).build());
            net = PetriNet.builder(bug ? "searchAsYouTypeBug" : "searchAsYouType")
                .transitions(ts.toArray(new Transition[0])).build();
        }

        Place<String> p(String name) {
            return places.computeIfAbsent(name, k -> Place.of(k, String.class));
        }

        Map<Place<?>, List<Token<?>>> initialTokens() {
            var out = new LinkedHashMap<Place<?>, List<Token<?>>>();
            for (var e : INITIAL) {
                out.put(p(e.getKey()), new ArrayList<>(Collections.nCopies(e.getValue(), Token.of("unit"))));
            }
            return out;
        }
    }

    private static PetriNetExecutor executor(boolean precompiled, SearchAsYouType s, String scope) {
        if (precompiled) {
            var b = PrecompiledNetExecutor.builder(s.net, s.initialTokens());
            if (scope != null) b.executionScope(scope);
            return b.build();
        }
        var b = BitmapNetExecutor.builder(s.net, s.initialTokens());
        if (scope != null) b.executionScope(scope);
        return b.build();
    }

    @TestFactory
    List<DynamicTest> nu055_ac5_aRunWithAPinnedMintingScopeRestsAsTheFixturesSay() {
        var tests = new ArrayList<DynamicTest>();
        for (boolean precompiled : new boolean[] {false, true}) {
            for (String scope : new String[] {null, "nu055-scope"}) {
                for (boolean bug : new boolean[] {false, true}) {
                    String name = (precompiled ? "PrecompiledNetExecutor" : "BitmapNetExecutor") + ", "
                        + (scope == null ? "default" : scope) + " scope, " + (bug ? "bug variant" : "fixed net");
                    tests.add(DynamicTest.dynamicTest(name, () -> {
                        var s = new SearchAsYouType(bug);
                        try (var executor = executor(precompiled, s, scope)) {
                            var marking = executor.run(Duration.ofSeconds(30)).toCompletableFuture().join();
                            var box = marking.peekTokens(s.p("box")).stream().map(Token::value).toList();
                            var list = marking.peekTokens(s.p("list")).stream().map(Token::value).toList();
                            assertEquals(1, box.size(), "box: " + box);
                            assertEquals(1, list.size(), "list: " + list);
                            if (scope != null) {
                                assertTrue(box.get(0).contains("#" + scope + ":"), box.get(0));
                            }
                            // The fixed net rests aligned (QuiescentNameAligned proven); the bug variant,
                            // with the first reply answered last, rests on the old results (violated with
                            // 12 firings).
                            if (bug) {
                                assertNotEquals(box.get(0), list.get(0));
                            } else {
                                assertEquals(box.get(0), list.get(0));
                            }
                        }
                    }));
                }
            }
        }
        return tests;
    }

    @Test
    void nu055_ac5_theVerdictsOnTheExecutableNetsMatchTheFixtures() {
        for (boolean bug : new boolean[] {false, true}) {
            var s = new SearchAsYouType(bug);
            var carriers = bug ? List.of("box", "inflightA", "inflightB", "reply", "staged", "list")
                : List.of("inflightA", "inflightB", "list");
            var result = SmtVerifier.forNet(s.net)
                .initialMarking(m -> INITIAL.forEach(e -> m.tokens(s.p(e.getKey()), e.getValue())))
                .property(SmtProperty.quiescentNameAligned(s.p("box"), s.p("list")))
                .mintTransitions("sendA", "sendB")
                .carrierPlaces(carriers.stream().map(s::p).toArray(Place<?>[]::new))
                .fragmentMode(FragmentMode.EXTENDED)
                .verify();
            assertEquals(Route.NU_SCG, result.route(), result.report());
            assertEquals(bug ? "violated" : "proven", verdict(result), result.report());
        }
    }
}
