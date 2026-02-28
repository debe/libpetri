package org.libpetri.analysis;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for environment place support in formal analysis.
 */
class EnvironmentPlaceAnalysisTest {

    @Test
    @DisplayName("Analysis with ALWAYS_AVAILABLE mode treats environment places as always having tokens")
    void analysisAlwaysAvailable() {
        var inputEnv = EnvironmentPlace.of(Place.of("Input", String.class));
        var output = Place.of("Output", String.class);

        var process = Transition.builder("Process")
            .inputs(In.one(inputEnv.place()))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .maxClasses(100)
            .build()
            .analyze();

        // With ALWAYS_AVAILABLE, Process is always enabled and can reach output
        assertTrue(result.isGoalLive(), "Goal should be reachable when input always available");
    }

    @Test
    @DisplayName("Analysis with IGNORE mode requires tokens in environment places")
    void analysisIgnoreMode() {
        var inputEnv = EnvironmentPlace.of(Place.of("Input", String.class));
        var output = Place.of("Output", String.class);

        var process = Transition.builder("Process")
            .inputs(In.one(inputEnv.place()))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        // With IGNORE mode and no initial tokens, goal is not reachable
        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.ignore())
            .maxClasses(100)
            .build()
            .analyze();

        assertFalse(result.isGoalLive(), "Goal should not be reachable without tokens in IGNORE mode");
    }

    @Test
    @DisplayName("Analysis with IGNORE mode succeeds when environment place has initial tokens")
    void analysisIgnoreModeWithTokens() {
        var inputEnv = EnvironmentPlace.of(Place.of("Input", String.class));
        var output = Place.of("Output", String.class);

        var process = Transition.builder("Process")
            .inputs(In.one(inputEnv.place()))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        // With IGNORE mode but initial token, goal is reachable
        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(m -> m.tokens(inputEnv.place(), 1))
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.ignore())
            .maxClasses(100)
            .build()
            .analyze();

        assertTrue(result.isGoalLive(), "Goal should be reachable with initial token");
    }

    @Test
    @DisplayName("Analysis with BOUNDED mode respects token bounds")
    void analysisBoundedMode() {
        var inputEnv = EnvironmentPlace.of(Place.of("Input", String.class));
        var output = Place.of("Output", String.class);

        // Transition requires 2 input tokens
        var process = Transition.builder("ProcessTwo")
            .inputs(In.exactly(2, inputEnv.place()))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        // BOUNDED(1) - environment can only provide 1 token
        var resultBounded1 = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.bounded(1))
            .maxClasses(100)
            .build()
            .analyze();

        assertFalse(resultBounded1.isGoalLive(), "Goal should not be reachable with BOUNDED(1) when 2 tokens needed");

        // BOUNDED(2) - environment can provide 2 tokens
        var resultBounded2 = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.bounded(2))
            .maxClasses(100)
            .build()
            .analyze();

        assertTrue(resultBounded2.isGoalLive(), "Goal should be reachable with BOUNDED(2) when 2 tokens needed");
    }

    @Test
    @DisplayName("Analysis without environment places uses standard semantics")
    void analysisWithoutEnvironmentPlaces() {
        var input = Place.of("Input", String.class);
        var output = Place.of("Output", String.class);

        var process = Transition.builder("Process")
            .inputs(In.one(input))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        // No environment places - standard analysis
        var resultNoToken = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .maxClasses(100)
            .build()
            .analyze();

        assertFalse(resultNoToken.isGoalLive(), "Goal should not be reachable without initial token");

        var resultWithToken = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(m -> m.tokens(input, 1))
            .goalPlaces(output)
            .maxClasses(100)
            .build()
            .analyze();

        assertTrue(resultWithToken.isGoalLive(), "Goal should be reachable with initial token");
    }

    @Test
    @DisplayName("EnvironmentAnalysisMode factory methods work correctly")
    void environmentAnalysisModeFactories() {
        var alwaysAvailable = EnvironmentAnalysisMode.alwaysAvailable();
        assertInstanceOf(EnvironmentAnalysisMode.AlwaysAvailable.class, alwaysAvailable);

        var bounded = EnvironmentAnalysisMode.bounded(5);
        assertInstanceOf(EnvironmentAnalysisMode.Bounded.class, bounded);
        assertEquals(5, ((EnvironmentAnalysisMode.Bounded) bounded).maxTokens());

        var ignore = EnvironmentAnalysisMode.ignore();
        assertInstanceOf(EnvironmentAnalysisMode.Ignore.class, ignore);

        // Negative bounds should throw
        assertThrows(IllegalArgumentException.class, () -> EnvironmentAnalysisMode.bounded(-1));
    }

    @Test
    @DisplayName("State class graph reports environment place configuration")
    void stateClassGraphReportsEnvironmentConfig() {
        var inputEnv = EnvironmentPlace.of(Place.of("Input", String.class));
        var output = Place.of("Output", String.class);

        var process = Transition.builder("Process")
            .inputs(In.one(inputEnv.place()))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(process).build();

        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.empty())
            .goalPlaces(output)
            .environmentPlaces(inputEnv)
            .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .maxClasses(100)
            .build()
            .analyze();

        // Report should mention environment places
        assertTrue(result.report().contains("Environment places: 1"),
            "Report should mention environment place count");
        assertTrue(result.report().contains("AlwaysAvailable"),
            "Report should mention environment mode");
    }
}
