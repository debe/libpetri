package org.libpetri.verification;

import java.time.Duration;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.Instance;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.SubnetVerifyOptions;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerificationResult;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [MOD-051] {@link SubnetDef#verify(VerificationHarness, SubnetVerifyOptions)}: the configure hook
 * reaches every per-property verifier (AC6) and carries the ν options that change the model
 * (AC7); {@code arrivals(k)} bounds the input's total (AC5); {@link SubnetDef#bindActions}
 * (AC8).
 */
class SubnetVerifyOptionsTest {

    static boolean z3Available() {
        return org.libpetri.smt.SmtVerifier.z3Available();
    }

    private static Place<String> s(String name) {
        return Place.of(name, String.class);
    }

    /** {@code IN -> forward -> OUT}, ports {@code in} / {@code out}. */
    private static SubnetDef<Void> forwarder() {
        var in = s("IN");
        var out = s("OUT");
        var body = SubnetDef.builder("Forward").place(in).place(out)
            .transition(Transition.builder("forward").inputs(In.one(in)).outputs(Out.place(out))
                .action(TransitionAction.fork()).build())
            .inputPort("in", in).outputPort("out", out)
            .build();
        return body;
    }

    private static VerificationHarness<Void> harness(SmtProperty... properties) {
        var b = VerificationHarness.builder().input("in", () -> Token.of("x"));
        for (var p : properties) b.property(p);
        return b.build();
    }

    private static final Place<String> OUT_OBSERVED = s("harness_out_out");

    @Test
    void arrivalsBoundsTheTotalInput_boundedOnlyTheResidentTokens() {
        var def = forwarder();
        var underArrivals = def.verify(harness(SmtProperty.placeBound(OUT_OBSERVED, 2)),
            SubnetVerifyOptions.DEFAULT.withEnvironmentMode(EnvironmentAnalysisMode.arrivals(2)));
        var r = underArrivals.perProperty().get(SmtProperty.placeBound(OUT_OBSERVED, 2));
        assertTrue(r.isProven(), r.report());
        var tighter = def.verify(harness(SmtProperty.placeBound(OUT_OBSERVED, 1)),
            SubnetVerifyOptions.DEFAULT.withEnvironmentMode(EnvironmentAnalysisMode.arrivals(2)));
        assertTrue(tighter.anyViolated(), "arrivals(2) delivers two tokens");
    }

    @Test
    @EnabledIf("z3Available")
    void boundedRefillsForever_soTheSameBoundIsViolated() {
        var r = forwarder().verify(harness(SmtProperty.placeBound(OUT_OBSERVED, 2)),
            EnvironmentAnalysisMode.bounded(2));
        assertTrue(r.anyViolated(), r.perProperty().values().iterator().next().report());
    }

    @Test
    void theHookRunsOncePerProperty_withTheSyntheticNet_andWinsOverTheSetup() {
        var calls = new AtomicInteger();
        var props = new SmtProperty[] {
            SmtProperty.placeBound(OUT_OBSERVED, 2), SmtProperty.deadlockFree()};
        var result = forwarder().verify(harness(props), SubnetVerifyOptions.DEFAULT
            .withEnvironmentMode(EnvironmentAnalysisMode.arrivals(2))
            .withConfigure((v, synth) -> {
                calls.incrementAndGet();
                assertTrue(synth.places().stream().anyMatch(p -> p.name().equals("harness_out_out")));
                // A total budget of 0 ms leaves no time for anything: every query stops at once.
                return v.totalBudget(Duration.ZERO);
            }));
        assertEquals(2, calls.get());
        for (var r : result.perProperty().values()) {
            var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
            assertTrue(unknown.reason().startsWith("total verification budget of 0 ms exhausted during "),
                unknown.reason());
        }
    }

    @Test
    void aSinkNamedThroughTheHookChangesAQuiescenceVerdict() {
        var harness = harness(SmtProperty.deadlockFree());
        var arrivals = SubnetVerifyOptions.DEFAULT.withEnvironmentMode(EnvironmentAnalysisMode.arrivals(1));
        var without = forwarder().verify(harness, arrivals);
        assertTrue(without.anyViolated(), "the token rests on the output place, which is no sink");
        var with = forwarder().verify(harness, arrivals.withConfigure((v, synth) -> v.sinkPlaces(OUT_OBSERVED)));
        assertTrue(with.allProven(), with.perProperty().values().iterator().next().report());
    }

    // ---- AC7: the ν options reach the per-property verifier -----------------------------------

    /**
     * {@code fork: IN -> A, C} mints a name onto {@code A} and the carrier {@code C};
     * {@code relay: C -> B} hands it on; {@code join: A, B} matches it; output port {@code done}.
     */
    private static SubnetDef<Void> forkRelayJoin() {
        var in = s("IN");
        var a = s("A");
        var b = s("B");
        var c = s("C");
        var done = s("DONE");
        var match = MatchSpec.builder().key(a, (String v) -> NameId.of(v)).key(b, (String v) -> NameId.of(v)).build();
        var def = SubnetDef.builder("ForkRelayJoin").place(in).place(a).place(b).place(c).place(done)
            .transition(Transition.builder("fork").inputs(In.one(in)).outputs(Out.and(a, c)).build())
            .transition(Transition.builder("relay").inputs(In.one(c)).outputs(Out.place(b)).build())
            .transition(Transition.builder("join").inputs(In.one(a), In.one(b)).match(match)
                .outputs(Out.place(done)).build())
            .inputPort("in", in).outputPort("done", done)
            .build();
        return def.bindActions(_ -> StructureOnly.ACTION);
    }

    @Test
    void theNuOptionsChangeTheModel_baseProves_extendedWithTheCarrierViolates() {
        var doneObserved = s("harness_out_done");
        var property = SmtProperty.unreachable(Set.of(doneObserved));
        var harness = harness(property);
        var arrivals = SubnetVerifyOptions.DEFAULT.withEnvironmentMode(EnvironmentAnalysisMode.arrivals(1));

        // BASE reads the relay as a fresh mint: the join's two names never match.
        var base = forkRelayJoin().verify(harness, arrivals).perProperty().get(property);
        assertTrue(base.isProven(), "BASE, the relay read as a mint:\n" + base.report());

        var extended = forkRelayJoin().verify(harness, arrivals.withConfigure((v, synth) -> v
            .fragmentMode(FragmentMode.EXTENDED)
            .carrierPlaces(synth.places().stream().filter(p -> p.name().equals("sut/C")).findFirst().orElseThrow())))
            .perProperty().get(property);
        assertTrue(extended.isViolated(), "EXTENDED with carrier sut/C:\n" + extended.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, extended.route(), extended.report());
        assertEquals(java.util.List.of("env:arrive?[0]:harness_in_in", "sut/fork", "sut/relay", "sut/join"),
            extended.counterexampleTransitions());
    }

    // ---- AC8: bindActions on a definition ------------------------------------------------------

    private static TransitionAction actionOf(Instance<?> instance, String name) {
        return instance.renamedBody().transitions().stream()
            .filter(t -> t.name().equals(instance.prefix() + "/" + name)).findFirst().orElseThrow().action();
    }

    @Test
    void bindActions_returnsANewDefinition_keyedByUnprefixedNames_receiverUnchanged() {
        var in = s("IN");
        var out = s("OUT");
        var tick = Transition.builder("tick").inputs(In.one(out)).build();
        var def = SubnetDef.builder("Two").place(in).place(out)
            .transition(Transition.builder("forward").inputs(In.one(in)).outputs(Out.place(out)).build())
            .transition(tick)
            .inputPort("in", in).outputPort("out", out)
            .channel("tick", tick)
            .build();
        TransitionAction bound = TransitionAction.fork();

        var rebound = def.bindActions(Map.of("forward", bound));
        assertNotSame(def, rebound);
        assertSame(bound, actionOf(rebound.instantiate("a"), "forward"));
        assertTrue(TransitionAction.isPassthrough(actionOf(def.instantiate("b"), "forward")),
            "the receiver's instances keep the old action");
        assertEquals(def.iface().ports(), rebound.iface().ports());
        assertEquals(def.name(), rebound.name());
        assertEquals(def.paramType(), rebound.paramType());
        // The channel points at the rebound body's transition.
        var channel = (org.libpetri.core.Interface.Channel.SyncChannel) rebound.iface().channels().iterator().next();
        assertTrue(rebound.body().transitions().contains(channel.transition()));

        // Resolver form: null keeps what is bound.
        var staged = rebound.bindActions(name -> name.equals("tick") ? TransitionAction.fork() : null);
        assertSame(bound, actionOf(staged.instantiate("c"), "forward"));

        // The composed net verifies: CORE-043 is satisfied by the bound definition.
        var net = PetriNet.builder("host").compose(rebound.instantiate("x"), Map.of("in", s("GO"), "out", s("END")))
            .build();
        assertTrue(net.transitions().stream().anyMatch(t -> t.name().equals("x/forward") && t.action() == bound));
    }
}
