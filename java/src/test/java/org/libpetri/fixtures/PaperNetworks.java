package org.libpetri.fixtures;

import java.time.Duration;

import org.libpetri.core.In;
import org.libpetri.core.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;

/**
 * Factory for creating the Petri nets from the paper:
 * "Apply Time Petri Nets with Colored Tokens to Model and Verify Agentic Systems"
 *
 * These nets can be used for:
 * - PNML/Mermaid/DOT export
 */
public final class PaperNetworks {

    /**
     * Creates the Extended TPN from Section 4 of the paper (Figure 4).
     *
     * This includes:
     * - Parallel branches (Guard/Intent, Topic/Search)
     * - Fallback transition when Search fails
     * - Retry transition when Compose fails (inhibited by Urgent)
     * - ShowError transition when Compose fails AND Urgent is active
     * - Global timeout with inhibitor arcs
     *
     * The Retry/ShowError pair ensures no deadlock:
     * - If ComposeFail + no Urgent → Retry fires (retry composition)
     * - If ComposeFail + Urgent → ShowError fires (display error to customer)
     *
     * Timing (in milliseconds):
     * - ask: [0, 100]
     * - Guard: [0, 500]
     * - Intent: [0, 2000]
     * - Topic: [0, 4500]
     * - Search: [0, 3500]
     * - Fallback: [0, 100] (inhibited by Urgent)
     * - Compose: [0, 6000]
     * - Retry: [0, 1000] (inhibited by Urgent)
     * - ShowError: [0, 100] (requires Urgent)
     * - Filter: [0, 500]
     * - Timeout: [9000, 9000] (exact)
     */
    public static PetriNet createExtendedTpn() {
        // Places
        var pending = Place.of("Pending", String.class);
        var ready = Place.of("Ready", String.class);
        var validated = Place.of("Validated", String.class);
        var understood = Place.of("Understood", String.class);
        var informed = Place.of("Informed", String.class);
        var promoted = Place.of("Promoted", String.class);
        var found = Place.of("Found", String.class);
        var drafted = Place.of("Drafted", String.class);
        var answered = Place.of("Answered", String.class);
        var urgent = Place.of("Urgent", String.class);
        var searchFail = Place.of("SearchFail", String.class);
        var composeFail = Place.of("ComposeFail", String.class);
        var errorShown = Place.of("ErrorShown", String.class);

        // Transitions with timing intervals [0, deadline]
        var ask = Transition.builder("ask")
            .inputs(In.one(pending))
            .outputs(Out.place(ready))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .build();

        var guard = Transition.builder("Guard")
            .read(ready)
            .outputs(Out.place(validated))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .build();

        var intent = Transition.builder("Intent")
            .read(ready)
            .outputs(Out.place(understood))
            .timing(Timing.deadline(Duration.ofMillis(2000)))
            .build();

        var topic = Transition.builder("Topic")
            .inputs(In.one(understood))
            .outputs(Out.and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(4500)))
            .build();

        var search = Transition.builder("Search")
            .inputs(In.one(understood))
            .outputs(Out.xor(found, searchFail))
            .timing(Timing.deadline(Duration.ofMillis(3500)))
            .build();

        var fallback = Transition.builder("Fallback")
            .inputs(In.one(searchFail))
            .outputs(Out.place(found))
            .inhibitor(urgent)
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .build();

        var compose = Transition.builder("Compose")
            .inputs(In.one(validated), In.one(informed), In.one(promoted), In.one(found))
            .outputs(Out.xor(drafted, composeFail))
            .timing(Timing.deadline(Duration.ofMillis(6000)))
            .build();

        var retry = Transition.builder("Retry")
            .inputs(In.one(composeFail))
            .outputs(Out.place(drafted))
            .inhibitor(urgent)
            .timing(Timing.deadline(Duration.ofMillis(1000)))
            .build();

        // ShowError: when ComposeFail + Urgent, show error to customer
        // This consumes ComposeFail when there's no time left for retry
        var showError = Transition.builder("ShowError")
            .inputs(In.one(composeFail), In.one(urgent))
            .outputs(Out.place(errorShown))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .build();

        var filter = Transition.builder("Filter")
            .inputs(In.one(drafted))
            .outputs(Out.place(answered))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .build();

        var timeout = Transition.builder("Timeout")
            .read(pending)
            .outputs(Out.place(urgent))
            .timing(Timing.exact(Duration.ofMillis(9000)))
            .build();

        return PetriNet.builder("ExtendedTPN-Paper")
            .transitions(ask, guard, intent, topic, search, fallback, compose, retry, showError, filter, timeout)
            .build();
    }

    /**
     * Creates the basic TPN from Section 3 of the paper (Figure 3).
     *
     * This is a simpler version without retries/fallbacks/timeout.
     */
    public static PetriNet createBasicTpn() {
        var pending = Place.of("Pending", String.class);
        var ready = Place.of("Ready", String.class);
        var validated = Place.of("Validated", String.class);
        var understood = Place.of("Understood", String.class);
        var informed = Place.of("Informed", String.class);
        var promoted = Place.of("Promoted", String.class);
        var found = Place.of("Found", String.class);
        var drafted = Place.of("Drafted", String.class);
        var answered = Place.of("Answered", String.class);

        var ask = Transition.builder("ask")
            .inputs(In.one(pending))
            .outputs(Out.place(ready))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .build();

        var guard = Transition.builder("Guard")
            .read(ready)
            .outputs(Out.place(validated))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .build();

        var intent = Transition.builder("Intent")
            .read(ready)
            .outputs(Out.place(understood))
            .timing(Timing.deadline(Duration.ofMillis(2000)))
            .build();

        var topic = Transition.builder("Topic")
            .inputs(In.one(understood))
            .outputs(Out.and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(4500)))
            .build();

        var search = Transition.builder("Search")
            .inputs(In.one(understood))
            .outputs(Out.place(found))
            .timing(Timing.deadline(Duration.ofMillis(3500)))
            .build();

        var compose = Transition.builder("Compose")
            .inputs(In.one(validated), In.one(informed), In.one(promoted), In.one(found))
            .outputs(Out.place(drafted))
            .timing(Timing.deadline(Duration.ofMillis(6000)))
            .build();

        var filter = Transition.builder("Filter")
            .inputs(In.one(drafted))
            .outputs(Out.place(answered))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .build();

        return PetriNet.builder("BasicTPN-Paper")
            .transitions(ask, guard, intent, topic, search, compose, filter)
            .build();
    }

    private PaperNetworks() {}
}
