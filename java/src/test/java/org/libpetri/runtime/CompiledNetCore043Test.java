package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.*;

import java.time.Duration;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.*;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;

/**
 * CORE-043: a transition that declares an output spec must not carry the built-in
 * {@link TransitionAction#passthrough()} in a net handed to an executor or a verifier.
 */
class CompiledNetCore043Test {

    private static final Place<Void> IN = Place.of("In", Void.class);
    private static final Place<Void> OUT = Place.of("Out", Void.class);

    private static PetriNet netOf(Transition... transitions) {
        return PetriNet.builder("Test").transitions(transitions).build();
    }

    private static PetriNet offendingNet(String name) {
        return netOf(Transition.builder(name)
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.place(OUT))
            .build());
    }

    // ---------------------------------------------------------------- rejection paths

    @Test
    void compile_rejectsBuilderDefaultPassthroughOnOutputDeclaringTransition() {
        var ex = assertThrows(IllegalStateException.class, () -> CompiledNet.compile(offendingNet("t")));
        assertTrue(ex.getMessage().contains("'t'"),
            "the message must name the transition: " + ex.getMessage());
    }

    @Test
    void compile_rejectsExplicitlyBoundPassthrough() {
        var net = netOf(Transition.builder("t")
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.place(OUT))
            .action(TransitionAction.fork())
            .build())
            .bindActions(Map.of("t", TransitionAction.passthrough()));

        var ex = assertThrows(IllegalStateException.class, () -> CompiledNet.compile(net));
        assertTrue(ex.getMessage().contains("'t'"), ex.getMessage());
    }

    @Test
    void compile_rejectsTransitionOmittedFromBindingMap() {
        var net = offendingNet("typoed").bindActions(Map.of("typoedd", TransitionAction.fork()));

        var ex = assertThrows(IllegalStateException.class, () -> CompiledNet.compile(net));
        assertTrue(ex.getMessage().contains("'typoed'"), ex.getMessage());
    }

    /**
     * A {@code Timeout} spec is no escape hatch: its child is produced by the executor, but only
     * when the budget expires — and passthrough completes immediately.
     */
    @Test
    void compile_rejectsTimeoutOnlyOutputSpec() {
        var net = netOf(Transition.builder("t")
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.timeout(Duration.ofMillis(100), Arc.Out.forwardInput(IN, OUT)))
            .build());

        var ex = assertThrows(IllegalStateException.class, () -> CompiledNet.compile(net));
        assertTrue(ex.getMessage().contains("'t'"), ex.getMessage());
    }

    @Test
    void precompile_rejectsTheSameNet() {
        assertThrows(IllegalStateException.class, () -> PrecompiledNet.compile(offendingNet("t")));
    }

    // ---------------------------------------------------------------- verification entry points

    @Test
    void stateClassGraph_rejectsTheSameNet() {
        var net = offendingNet("t");
        var marking = MarkingState.builder().tokens(IN, 1).build();

        var ex = assertThrows(IllegalStateException.class,
            () -> StateClassGraph.build(net, marking, 100));
        assertTrue(ex.getMessage().contains("'t'"), ex.getMessage());
    }

    @Test
    void smtVerifier_rejectsTheSameNet() {
        var net = offendingNet("t");

        var ex = assertThrows(IllegalStateException.class, () -> SmtVerifier.forNet(net)
            .property(SmtProperty.deadlockFree())
            .verify());
        assertTrue(ex.getMessage().contains("'t'"), ex.getMessage());
    }

    // ---------------------------------------------------------------- accepted paths

    @Test
    void compile_acceptsPassthroughOnSinkTransition() {
        var net = netOf(Transition.builder("sink").inputs(Arc.In.one(IN)).build());

        assertDoesNotThrow(() -> CompiledNet.compile(net));
    }

    @Test
    void compile_acceptsForkOnOutputDeclaringTransition() {
        var net = netOf(Transition.builder("t")
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.place(OUT))
            .action(TransitionAction.fork())
            .build());

        assertDoesNotThrow(() -> CompiledNet.compile(net));
    }

    /** Identity-based: a hand-written no-op is indistinguishable from a conditional producer. */
    @Test
    void compile_acceptsHandWrittenNoOpAction() {
        var net = netOf(Transition.builder("t")
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.place(OUT))
            .action(ctx -> java.util.concurrent.CompletableFuture.completedFuture(null))
            .build());

        assertDoesNotThrow(() -> CompiledNet.compile(net),
            "only TransitionAction.passthrough() is provably inert; anything else may produce");
    }
}
