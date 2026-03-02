package org.libpetri.benchmark;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.debug.DebugAwareEventStore;
import org.libpetri.debug.DebugEventStore;
import org.libpetri.debug.LogCaptureScopeForwardingExecutor;
import org.libpetri.event.EventStore;
import org.libpetri.runtime.BitmapNetExecutor;

import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.RunResult;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.OptionsBuilder;

/**
 * JMH benchmarks for BitmapNetExecutor performance scaling and debug infrastructure regression detection.
 *
 * <p>Tests workflows of different sizes to determine O-notation scaling,
 * plus complex workflow benchmarks that isolate EventStore and LogCaptureScope overhead.
 */
@BenchmarkMode({Mode.AverageTime, Mode.SampleTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(value = 1, jvmArgs = { "--enable-preview" })
public class BitmapNetExecutorBenchmark {

    record BenchToken(String value) {}

    // Workflow token types
    record GuardResult(boolean safe) {}
    record IntentResult(String intent) {}
    record SearchResult(int productCount) {}
    record TopicKnowledge(String topic) {}
    record ComposeResult(String response) {}

    private ExecutorService virtualExecutor;
    private ExecutorService logCaptureExecutor;

    // Different sized workflows
    private PetriNet linearNet5; // 5 transitions, 6 places
    private PetriNet linearNet10; // 10 transitions, 11 places
    private PetriNet linearNet20; // 20 transitions, 21 places
    private PetriNet linearNet50; // 50 transitions, 51 places

    private PetriNet parallelNet5; // 5 parallel branches
    private PetriNet parallelNet10; // 10 parallel branches
    private PetriNet parallelNet20; // 20 parallel branches

    private PetriNet largeNet; // Full Large: 16 transitions, 17 places

    private Place<BenchToken> start5, start10, start20, start50;

    private PetriNet linearNet100, linearNet200, linearNet500;
    private Place<BenchToken> start100, start200, start500;
    private Place<BenchToken> pstart5, pstart10, pstart20;
    private Place<BenchToken> largeStart;

    // Sync linear chains (completedFuture actions)
    private PetriNet syncLinearNet10, syncLinearNet20, syncLinearNet50, syncLinearNet100, syncLinearNet200, syncLinearNet500;
    private Place<BenchToken> syncStart10, syncStart20, syncStart50, syncStart100, syncStart200, syncStart500;

    // Mixed linear chains (2 async + rest sync)
    private PetriNet mixedLinearNet10, mixedLinearNet20, mixedLinearNet50, mixedLinearNet100, mixedLinearNet200, mixedLinearNet500;
    private Place<BenchToken> mixedStart10, mixedStart20, mixedStart50, mixedStart100, mixedStart200, mixedStart500;

    // Complex workflow
    private WorkflowNetWithStart complexWorkflow;

    @State(Scope.Thread)
    public static class EventStoreState {
        @Param({"noop", "inMemory", "debug", "debugAware"})
        public String storeType;

        private EventStore store;
        private DebugEventStore debugStoreInstance;

        @Setup(Level.Invocation)
        public void setup() {
            switch (storeType) {
                case "noop" -> store = EventStore.noop();
                case "inMemory" -> store = EventStore.inMemory();
                case "debug" -> {
                    debugStoreInstance = new DebugEventStore("bench-" + System.nanoTime());
                    store = debugStoreInstance;
                }
                case "debugAware" -> {
                    debugStoreInstance = new DebugEventStore("bench-" + System.nanoTime());
                    store = new DebugAwareEventStore(EventStore.inMemory(), debugStoreInstance);
                }
                default -> throw new IllegalArgumentException("Unknown store type: " + storeType);
            }
        }

        @TearDown(Level.Invocation)
        public void teardown() {
            if (debugStoreInstance != null) {
                debugStoreInstance.close();
                debugStoreInstance = null;
            }
        }
    }

    @Setup(Level.Trial)
    public void setup() {
        virtualExecutor = Executors.newVirtualThreadPerTaskExecutor();
        logCaptureExecutor = LogCaptureScopeForwardingExecutor.wrap(
            Executors.newVirtualThreadPerTaskExecutor()
        );

        // Build linear chains of different sizes
        var linear5 = buildLinearChain(5);
        linearNet5 = linear5.net;
        start5 = linear5.start;

        var linear10 = buildLinearChain(10);
        linearNet10 = linear10.net;
        start10 = linear10.start;

        var linear20 = buildLinearChain(20);
        linearNet20 = linear20.net;
        start20 = linear20.start;

        var linear50 = buildLinearChain(50);
        linearNet50 = linear50.net;
        start50 = linear50.start;

        var linear100 = buildLinearChain(100);
        linearNet100 = linear100.net;
        start100 = linear100.start;

        var linear200 = buildLinearChain(200);
        linearNet200 = linear200.net;
        start200 = linear200.start;

        var linear500 = buildLinearChain(500);
        linearNet500 = linear500.net;
        start500 = linear500.start;

        // Build sync linear chains
        var syncLinear10 = buildSyncLinearChain(10);
        syncLinearNet10 = syncLinear10.net;
        syncStart10 = syncLinear10.start;

        var syncLinear20 = buildSyncLinearChain(20);
        syncLinearNet20 = syncLinear20.net;
        syncStart20 = syncLinear20.start;

        var syncLinear50 = buildSyncLinearChain(50);
        syncLinearNet50 = syncLinear50.net;
        syncStart50 = syncLinear50.start;

        var syncLinear100 = buildSyncLinearChain(100);
        syncLinearNet100 = syncLinear100.net;
        syncStart100 = syncLinear100.start;

        var syncLinear200 = buildSyncLinearChain(200);
        syncLinearNet200 = syncLinear200.net;
        syncStart200 = syncLinear200.start;

        var syncLinear500 = buildSyncLinearChain(500);
        syncLinearNet500 = syncLinear500.net;
        syncStart500 = syncLinear500.start;

        // Build mixed linear chains (2 async, rest sync)
        var mixedLinear10 = buildMixedLinearChain(10, 2);
        mixedLinearNet10 = mixedLinear10.net;
        mixedStart10 = mixedLinear10.start;

        var mixedLinear20 = buildMixedLinearChain(20, 2);
        mixedLinearNet20 = mixedLinear20.net;
        mixedStart20 = mixedLinear20.start;

        var mixedLinear50 = buildMixedLinearChain(50, 2);
        mixedLinearNet50 = mixedLinear50.net;
        mixedStart50 = mixedLinear50.start;

        var mixedLinear100 = buildMixedLinearChain(100, 2);
        mixedLinearNet100 = mixedLinear100.net;
        mixedStart100 = mixedLinear100.start;

        var mixedLinear200 = buildMixedLinearChain(200, 2);
        mixedLinearNet200 = mixedLinear200.net;
        mixedStart200 = mixedLinear200.start;

        var mixedLinear500 = buildMixedLinearChain(500, 2);
        mixedLinearNet500 = mixedLinear500.net;
        mixedStart500 = mixedLinear500.start;

        // Build parallel fan-out/fan-in of different sizes
        var parallel5 = buildParallelFanOut(5);
        parallelNet5 = parallel5.net;
        pstart5 = parallel5.start;

        var parallel10 = buildParallelFanOut(10);
        parallelNet10 = parallel10.net;
        pstart10 = parallel10.start;

        var parallel20 = buildParallelFanOut(20);
        parallelNet20 = parallel20.net;
        pstart20 = parallel20.start;

        // Build large workflow
        var large = buildLargeWorkflow();
        largeNet = large.net;
        largeStart = large.start;

        // Build complex workflow
        complexWorkflow = buildComplexWorkflow();
    }

    record NetWithStart(PetriNet net, Place<BenchToken> start) {}

    /**
     * Builds a linear chain: start -> t1 -> p1 -> t2 -> p2 -> ... -> end
     */
    private NetWithStart buildLinearChain(int transitions) {
        var start = Place.of("start", BenchToken.class);
        var places = new ArrayList<Place<BenchToken>>();
        places.add(start);

        for (int i = 1; i <= transitions; i++) {
            places.add(Place.of("p" + i, BenchToken.class));
        }

        var builder = PetriNet.builder("Linear" + transitions);
        for (int i = 0; i < transitions; i++) {
            var from = places.get(i);
            var to = places.get(i + 1);
            builder.transition(
                Transition.builder("t" + (i + 1))
                    .inputs(In.one(from))
                    .outputs(Out.place(to))
                    .action(ctx -> {
                        Blackhole.consumeCPU(100);
                        ctx.output(to, new BenchToken("v"));
                        return CompletableFuture.supplyAsync(() -> {
                            Blackhole.consumeCPU(100);
                            return null;
                        }, virtualExecutor);
                    })
                    .build()
            );
        }

        return new NetWithStart(builder.build(), start);
    }

    /**
     * Builds a sync linear chain: same topology as {@link #buildLinearChain} but actions use
     * {@code CompletableFuture.completedFuture(null)} to isolate pure engine overhead without
     * virtual thread scheduling noise.
     */
    private NetWithStart buildSyncLinearChain(int transitions) {
        var start = Place.of("sync_start", BenchToken.class);
        var places = new ArrayList<Place<BenchToken>>();
        places.add(start);

        for (int i = 1; i <= transitions; i++) {
            places.add(Place.of("sync_p" + i, BenchToken.class));
        }

        var builder = PetriNet.builder("SyncLinear" + transitions);
        for (int i = 0; i < transitions; i++) {
            var to = places.get(i + 1);
            builder.transition(
                Transition.builder("sync_t" + (i + 1))
                    .inputs(In.one(places.get(i)))
                    .outputs(Out.place(to))
                    .action(ctx -> {
                        Blackhole.consumeCPU(100);
                        ctx.output(to, new BenchToken("v"));
                        return CompletableFuture.completedFuture(null);
                    })
                    .build()
            );
        }

        return new NetWithStart(builder.build(), start);
    }

    /**
     * Builds a mixed linear chain: the first {@code asyncCount} transitions use
     * {@code supplyAsync} and the rest use {@code completedFuture}. Models a typical FSM
     * where I/O happens at the entry boundary and the rest is in-memory logic.
     */
    private NetWithStart buildMixedLinearChain(int total, int asyncCount) {
        var start = Place.of("mix_start", BenchToken.class);
        var places = new ArrayList<Place<BenchToken>>();
        places.add(start);

        for (int i = 1; i <= total; i++) {
            places.add(Place.of("mix_p" + i, BenchToken.class));
        }

        var builder = PetriNet.builder("MixedLinear" + total + "_" + asyncCount + "async");
        for (int i = 0; i < total; i++) {
            var to = places.get(i + 1);
            boolean async = i < asyncCount;
            builder.transition(
                Transition.builder("mix_t" + (i + 1))
                    .inputs(In.one(places.get(i)))
                    .outputs(Out.place(to))
                    .action(ctx -> {
                        Blackhole.consumeCPU(100);
                        ctx.output(to, new BenchToken("v"));
                        if (async) {
                            return CompletableFuture.supplyAsync(() -> {
                                Blackhole.consumeCPU(100);
                                return null;
                            }, virtualExecutor);
                        }
                        return CompletableFuture.completedFuture(null);
                    })
                    .build()
            );
        }

        return new NetWithStart(builder.build(), start);
    }

    /**
     * Builds parallel fan-out/fan-in: start -> fork -> [p1,p2,...,pN] -> [t1,t2,...,tN] -> join -> end
     */
    private NetWithStart buildParallelFanOut(int branches) {
        var start = Place.of("pstart", BenchToken.class);
        var join = Place.of("pjoin", BenchToken.class);
        var end = Place.of("pend", BenchToken.class);

        var branchPlaces = new ArrayList<Place<BenchToken>>();
        for (int i = 0; i < branches; i++) {
            branchPlaces.add(Place.of("branch" + i, BenchToken.class));
        }

        // Fork transition
        var fork = Transition.builder("fork")
            .inputs(In.one(start))
            .outputs(Out.and(branchPlaces.toArray(new Place[0])))
            .action(ctx -> {
                for (var bp : branchPlaces) {
                    ctx.output(bp, new BenchToken("v"));
                }
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var builder = PetriNet.builder("Parallel" + branches).transition(fork);

        // Work transitions (one per branch)
        for (int i = 0; i < branches; i++) {
            var bp = branchPlaces.get(i);
            builder.transition(
                Transition.builder("work" + i)
                    .inputs(In.one(bp))
                    .outputs(Out.place(join))
                    .action(ctx -> {
                        ctx.output(join, new BenchToken("v"));
                        return CompletableFuture.supplyAsync(() -> {
                            Blackhole.consumeCPU(100);
                            return null;
                        }, virtualExecutor);
                    })
                    .build()
            );
        }

        // Join transition (needs N tokens from join place)
        var joinTrans = Transition.builder("join")
            .inputs(In.exactly(branches, join))
            .outputs(Out.place(end))
            .action(ctx -> {
                ctx.output(end, new BenchToken("done"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        builder.transition(joinTrans);

        return new NetWithStart(builder.build(), start);
    }

    /**
     * Builds Large workflow: 16 transitions, 17 places
     */
    private NetWithStart buildLargeWorkflow() {
        var pending = Place.of("Pending", BenchToken.class);
        var urgent = Place.of("Urgent", BenchToken.class);
        var guardResult = Place.of("GuardResult", BenchToken.class);
        var guardFired = Place.of("GuardFired", BenchToken.class);
        var intentReady = Place.of("IntentReady", BenchToken.class);
        var intentFailed = Place.of("IntentFailed", BenchToken.class);
        var topicsLoaded = Place.of("TopicsLoaded", BenchToken.class);
        var searchReady = Place.of("SearchReady", BenchToken.class);
        var searchFired = Place.of("SearchFired", BenchToken.class);
        var compareTopicsFired = Place.of("CompareTopicsFired", BenchToken.class);
        var reSearchNeeded = Place.of("ReSearchNeeded", BenchToken.class);
        var recoReady = Place.of("RecoReady", BenchToken.class);
        var injectReady = Place.of("InjectReady", BenchToken.class);
        var responseReady = Place.of("ResponseReady", BenchToken.class);
        var composeFailed = Place.of("ComposeFailed", BenchToken.class);
        var delivered = Place.of("Delivered", BenchToken.class);
        var fallbackDelivered = Place.of("FallbackDelivered", BenchToken.class);

        // 16 TRANSITIONS (16 transitions, 17 places)

        var timeout = Transition.builder("Timeout")
            .read(pending)
            .outputs(Out.place(urgent))
            .inhibitor(urgent)
            .inhibitor(delivered)
            .inhibitor(fallbackDelivered)
            .timing(Timing.exact(java.time.Duration.ofMillis(1)))
            .action(ctx -> {
                ctx.output(urgent, new BenchToken("urgent"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var guard = Transition.builder("Guard")
            .read(pending)
            .outputs(Out.and(guardResult, guardFired))
            .inhibitor(guardFired)
            .action(ctx -> {
                ctx.output(guardFired, new BenchToken("fired"));
                ctx.output(guardResult, new BenchToken("passed"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var intent = Transition.builder("Intent")
            .read(pending)
            .outputs(Out.xor(Out.place(intentReady), Out.place(intentFailed)))
            .inhibitor(intentReady)
            .inhibitor(intentFailed)
            .action(ctx -> {
                ctx.output(intentReady, new BenchToken("intent"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var retryIntent = Transition.builder("RetryIntent")
            .inputs(In.one(intentFailed))
            .outputs(Out.xor(Out.place(intentReady), Out.place(intentFailed)))
            .inhibitor(urgent)
            .action(ctx -> {
                ctx.output(intentReady, new BenchToken("retry"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var search = Transition.builder("Search")
            .read(intentReady)
            .outputs(Out.and(searchReady, searchFired))
            .inhibitor(searchFired)
            .action(ctx -> {
                ctx.output(searchFired, new BenchToken("fired"));
                ctx.output(searchReady, new BenchToken("products"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var topicKnowledge = Transition.builder("TopicKnowledge")
            .read(intentReady)
            .outputs(Out.place(topicsLoaded))
            .inhibitor(topicsLoaded)
            .action(ctx -> {
                ctx.output(topicsLoaded, new BenchToken("topics"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var compareTopics = Transition.builder("CompareTopics")
            .read(topicsLoaded)
            .outputs(Out.xor(Out.place(reSearchNeeded), Out.place(compareTopicsFired)))
            .inhibitor(compareTopicsFired)
            .action(ctx -> {
                ctx.output(compareTopicsFired, new BenchToken("fired"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var reSearch = Transition.builder("ReSearch")
            .inputs(In.one(reSearchNeeded))
            .reset(searchReady)
            .outputs(Out.place(searchReady))
            .action(ctx -> {
                ctx.output(searchReady, new BenchToken("research"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var productReco = Transition.builder("ProductReco")
            .inputs(In.one(searchReady))
            .read(compareTopicsFired)
            .inhibitor(reSearchNeeded)
            .outputs(Out.place(recoReady))
            .action(ctx -> {
                ctx.output(recoReady, new BenchToken("reco"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var urgentInject = Transition.builder("UrgentInject")
            .inputs(In.one(urgent), In.one(searchReady))
            .outputs(Out.place(injectReady))
            .inhibitor(injectReady)
            .action(ctx -> {
                ctx.output(injectReady, new BenchToken("urgent"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var decideInject = Transition.builder("DecideInject")
            .inputs(In.one(recoReady))
            .outputs(Out.place(injectReady))
            .action(ctx -> {
                ctx.output(injectReady, new BenchToken("inject"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var compose = Transition.builder("Compose")
            .inputs(In.one(guardResult), In.one(injectReady))
            .outputs(Out.xor(Out.place(responseReady), Out.place(composeFailed)))
            .action(ctx -> {
                ctx.output(responseReady, new BenchToken("response"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var retryCompose = Transition.builder("RetryCompose")
            .inputs(In.one(composeFailed))
            .outputs(Out.xor(Out.place(responseReady), Out.place(composeFailed)))
            .inhibitor(urgent)
            .action(ctx -> {
                ctx.output(responseReady, new BenchToken("retry"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var fallback = Transition.builder("Fallback")
            .inputs(In.one(composeFailed), In.one(urgent))
            .outputs(Out.place(fallbackDelivered))
            .action(ctx -> {
                ctx.output(fallbackDelivered, new BenchToken("fallback"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var intentFallback = Transition.builder("IntentFallback")
            .inputs(In.one(intentFailed), In.one(urgent))
            .outputs(Out.place(fallbackDelivered))
            .action(ctx -> {
                ctx.output(fallbackDelivered, new BenchToken("fallback"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var outputGuard = Transition.builder("OutputGuard")
            .inputs(In.one(responseReady))
            .outputs(Out.place(delivered))
            .action(ctx -> {
                ctx.output(delivered, new BenchToken("delivered"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var net = PetriNet.builder("LargeWorkflow")
            .transitions(
                timeout,
                guard,
                intent,
                retryIntent,
                search,
                topicKnowledge,
                compareTopics,
                reSearch,
                productReco,
                urgentInject,
                decideInject,
                compose,
                retryCompose,
                fallback,
                intentFallback,
                outputGuard
            )
            .build();

        return new NetWithStart(net, pending);
    }

    // ==================== COMPLEX WORKFLOW ====================

    record WorkflowNetWithStart(PetriNet net, Place<BenchToken> start) {}

    /**
     * Builds a complex workflow net: 10 transitions, 13 places.
     *
     * <p>Exercises fork, XOR output, read arcs, inhibitor arcs, priority, AND-join,
     * and the new In/Out API (In.one(), Out.xor(), Out.place()).
     *
     * <p>Topology:
     * <pre>
     * v_input -> [Fork] -> v_guardIn, v_intentIn, v_searchIn, v_outputGuardIn
     *
     * v_guardIn -> [Guard, XOR] -> v_guardSafe | v_guardViolation
     * v_guardViolation -> [HandleViolation, inhibitor(v_guardSafe)] -> v_violated
     *
     * v_intentIn -> [Intent] -> v_intentReady -> [TopicKnowledge] -> v_topicReady
     *
     * v_searchIn -> [Search, read(v_intentReady), inhibitor(v_guardViolation), priority=-5] -> v_searchReady
     *
     * v_outputGuardIn -> [OutputGuard, read(v_guardSafe)] -> v_outputGuardDone
     *
     * v_guardSafe + v_searchReady + v_topicReady -> [Compose, priority=10] -> v_response
     * </pre>
     */
    private WorkflowNetWithStart buildComplexWorkflow() {
        // 13 places
        var v_input = Place.of("v_input", BenchToken.class);
        var v_guardIn = Place.of("v_guardIn", BenchToken.class);
        var v_intentIn = Place.of("v_intentIn", BenchToken.class);
        var v_searchIn = Place.of("v_searchIn", BenchToken.class);
        var v_outputGuardIn = Place.of("v_outputGuardIn", BenchToken.class);
        var v_guardSafe = Place.of("v_guardSafe", BenchToken.class);
        var v_guardViolation = Place.of("v_guardViolation", BenchToken.class);
        var v_violated = Place.of("v_violated", BenchToken.class);
        var v_intentReady = Place.of("v_intentReady", BenchToken.class);
        var v_topicReady = Place.of("v_topicReady", BenchToken.class);
        var v_searchReady = Place.of("v_searchReady", BenchToken.class);
        var v_outputGuardDone = Place.of("v_outputGuardDone", BenchToken.class);
        var v_response = Place.of("v_response", BenchToken.class);

        // T1: Fork (1-to-4 fan-out) using TransitionAction.fork()
        var forkTrans = Transition.builder("Fork")
            .inputs(In.one(v_input))
            .outputs(Out.and(v_guardIn, v_intentIn, v_searchIn, v_outputGuardIn))
            .action(TransitionAction.fork())
            .build();

        // T2: Guard (XOR output - safe or violation)
        var guardTrans = Transition.builder("Guard")
            .inputs(In.one(v_guardIn))
            .outputs(Out.xor(v_guardSafe, v_guardViolation))
            .action(ctx -> {
                // Always produce to v_guardSafe for deterministic termination
                ctx.output(v_guardSafe, new BenchToken("safe"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T3: HandleViolation (inhibited by v_guardSafe — won't fire in normal path)
        var handleViolation = Transition.builder("HandleViolation")
            .inputs(In.one(v_guardViolation))
            .outputs(Out.place(v_violated))
            .inhibitor(v_guardSafe)
            .action(ctx -> {
                ctx.output(v_violated, new BenchToken("violated"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T4: Intent
        var intentTrans = Transition.builder("Intent")
            .inputs(In.one(v_intentIn))
            .outputs(Out.place(v_intentReady))
            .action(ctx -> {
                ctx.output(v_intentReady, new BenchToken("intent"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T5: TopicKnowledge (reads intentReady)
        var topicTrans = Transition.builder("TopicKnowledge")
            .inputs(In.one(v_intentReady))
            .outputs(Out.place(v_topicReady))
            .action(ctx -> {
                ctx.output(v_topicReady, new BenchToken("topic"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T6: Search (read intentReady, inhibited by guardViolation, low priority)
        var searchTrans = Transition.builder("Search")
            .inputs(In.one(v_searchIn))
            .outputs(Out.place(v_searchReady))
            .read(v_intentReady)
            .inhibitor(v_guardViolation)
            .priority(-5)
            .action(ctx -> {
                ctx.output(v_searchReady, new BenchToken("results"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T7: OutputGuard (reads guardSafe)
        var outputGuardTrans = Transition.builder("OutputGuard")
            .inputs(In.one(v_outputGuardIn))
            .outputs(Out.place(v_outputGuardDone))
            .read(v_guardSafe)
            .action(ctx -> {
                ctx.output(v_outputGuardDone, new BenchToken("checked"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        // T8: Compose (AND-join of 3 parallel paths, high priority)
        var composeTrans = Transition.builder("Compose")
            .inputs(In.one(v_guardSafe), In.one(v_searchReady), In.one(v_topicReady))
            .outputs(Out.place(v_response))
            .priority(10)
            .action(ctx -> {
                ctx.output(v_response, new BenchToken("composed"));
                return CompletableFuture.supplyAsync(() -> {
                    Blackhole.consumeCPU(100);
                    return null;
                }, virtualExecutor);
            })
            .build();

        var net = PetriNet.builder("ComplexWorkflow")
            .transitions(
                forkTrans,
                guardTrans,
                handleViolation,
                intentTrans,
                topicTrans,
                searchTrans,
                outputGuardTrans,
                composeTrans
            )
            .build();

        return new WorkflowNetWithStart(net, v_input);
    }

    @TearDown(Level.Trial)
    public void teardown() {
        virtualExecutor.shutdown();
        logCaptureExecutor.shutdown();
    }

    // ==================== SYNC LINEAR CHAIN BENCHMARKS ====================

    @Benchmark
    public void sync_linear_10t(Blackhole bh) {
        runBitmapNet(syncLinearNet10, syncStart10, bh);
    }

    @Benchmark
    public void sync_linear_20t(Blackhole bh) {
        runBitmapNet(syncLinearNet20, syncStart20, bh);
    }

    @Benchmark
    public void sync_linear_50t(Blackhole bh) {
        runBitmapNet(syncLinearNet50, syncStart50, bh);
    }

    @Benchmark
    public void sync_linear_100t(Blackhole bh) {
        runBitmapNet(syncLinearNet100, syncStart100, bh);
    }

    @Benchmark
    public void sync_linear_200t(Blackhole bh) {
        runBitmapNet(syncLinearNet200, syncStart200, bh);
    }

    @Benchmark
    public void sync_linear_500t(Blackhole bh) {
        runBitmapNet(syncLinearNet500, syncStart500, bh);
    }

    // ==================== MIXED LINEAR CHAIN BENCHMARKS ====================

    @Benchmark
    public void mixed_linear_10t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet10, mixedStart10, bh);
    }

    @Benchmark
    public void mixed_linear_20t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet20, mixedStart20, bh);
    }

    @Benchmark
    public void mixed_linear_50t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet50, mixedStart50, bh);
    }

    @Benchmark
    public void mixed_linear_100t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet100, mixedStart100, bh);
    }

    @Benchmark
    public void mixed_linear_200t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet200, mixedStart200, bh);
    }

    @Benchmark
    public void mixed_linear_500t_2async(Blackhole bh) {
        runBitmapNet(mixedLinearNet500, mixedStart500, bh);
    }

    // ==================== ASYNC LINEAR CHAIN BENCHMARKS ====================

    @Benchmark
    public void linear_05t(Blackhole bh) {
        runBitmapNet(linearNet5, start5, bh);
    }

    @Benchmark
    public void linear_10t(Blackhole bh) {
        runBitmapNet(linearNet10, start10, bh);
    }

    @Benchmark
    public void linear_20t(Blackhole bh) {
        runBitmapNet(linearNet20, start20, bh);
    }

    @Benchmark
    public void linear_50t(Blackhole bh) {
        runBitmapNet(linearNet50, start50, bh);
    }

    @Benchmark
    public void linear_100t(Blackhole bh) {
        runBitmapNet(linearNet100, start100, bh);
    }

    @Benchmark
    public void linear_200t(Blackhole bh) {
        runBitmapNet(linearNet200, start200, bh);
    }

    @Benchmark
    public void linear_500t(Blackhole bh) {
        runBitmapNet(linearNet500, start500, bh);
    }

    // ==================== PARALLEL FAN-OUT BENCHMARKS ====================

    @Benchmark
    public void parallel_05_branches(Blackhole bh) {
        runBitmapNet(parallelNet5, pstart5, bh);
    }

    @Benchmark
    public void parallel_10_branches(Blackhole bh) {
        runBitmapNet(parallelNet10, pstart10, bh);
    }

    @Benchmark
    public void parallel_20_branches(Blackhole bh) {
        runBitmapNet(parallelNet20, pstart20, bh);
    }

    // ==================== LARGE WORKFLOW ====================

    @Benchmark
    public void large_16t_17p(Blackhole bh) {
        runBitmapNet(largeNet, largeStart, bh);
    }

    // ==================== COMPLEX WORKFLOW BENCHMARKS ====================

    @Benchmark
    public void complex_baseline(Blackhole bh) {
        runComplexBitmapNet(EventStore.noop(), virtualExecutor, bh);
    }

    @Benchmark
    public void complex_eventStore(EventStoreState storeState, Blackhole bh) {
        runComplexBitmapNet(storeState.store, virtualExecutor, bh);
    }

    @Benchmark
    public void complex_logCapture(Blackhole bh) {
        var debugStore = new DebugEventStore("lc-" + System.nanoTime());
        try {
            runComplexBitmapNet(debugStore, logCaptureExecutor, bh);
        } finally {
            debugStore.close();
        }
    }

    // ==================== HELPERS ====================

    private void runBitmapNet(PetriNet net, Place<BenchToken> start, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var exec = BitmapNetExecutor.create(
                net,
                input,
                EventStore.noop(),
                virtualExecutor
            )
        ) {
            bh.consume(exec.run());
        }
    }

    private void runComplexBitmapNet(EventStore store, ExecutorService exec, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            complexWorkflow.start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var executor = BitmapNetExecutor.create(
                complexWorkflow.net,
                input,
                store,
                exec
            )
        ) {
            bh.consume(executor.run());
        }
    }

    // ==================== MAIN ====================

    public static void main(String[] args) throws RunnerException {
        var opt = new OptionsBuilder()
            .include(BitmapNetExecutorBenchmark.class.getSimpleName())
            .addProfiler("gc")
            .result("benchmark-results.json")
            .resultFormat(ResultFormatType.JSON)
            .build();
        var results = new Runner(opt).run();
        printScalingSummary(results);
    }

    private static final Pattern SYNC_PATTERN = Pattern.compile("^sync_linear_(\\d+)t$");
    private static final Pattern MIXED_PATTERN = Pattern.compile("^mixed_linear_(\\d+)t_2async$");
    private static final Pattern ASYNC_PATTERN = Pattern.compile("^linear_(\\d+)t(?:_\\d+p)?$");

    private static void printScalingSummary(Collection<RunResult> results) {
        // mode -> transitionCount -> score (us)
        var data = new TreeMap<String, TreeMap<Integer, Double>>();

        for (var r : results) {
            if (r.getParams().getMode() != Mode.AverageTime) continue;

            var benchName = r.getParams().getBenchmark();
            // strip class prefix
            var methodName = benchName.substring(benchName.lastIndexOf('.') + 1);
            double score = r.getPrimaryResult().getScore();

            var syncM = SYNC_PATTERN.matcher(methodName);
            var mixedM = MIXED_PATTERN.matcher(methodName);
            var asyncM = ASYNC_PATTERN.matcher(methodName);

            if (syncM.find()) {
                data.computeIfAbsent("sync", _ -> new TreeMap<>())
                    .put(Integer.parseInt(syncM.group(1)), score);
            } else if (mixedM.find()) {
                data.computeIfAbsent("mixed", _ -> new TreeMap<>())
                    .put(Integer.parseInt(mixedM.group(1)), score);
            } else if (asyncM.find()) {
                data.computeIfAbsent("async", _ -> new TreeMap<>())
                    .put(Integer.parseInt(asyncM.group(1)), score);
            }
        }

        if (data.isEmpty()) return;

        // Collect all transition counts across all modes
        var allSizes = new TreeSet<Integer>();
        data.values().forEach(m -> allSizes.addAll(m.keySet()));

        System.out.println();
        System.out.println("=== LINEAR SCALING SUMMARY (avgt, us/op) ===");
        System.out.printf("%-12s │ %10s │ %5s │ %11s │ %5s │ %11s │ %5s%n",
            "Transitions", "sync (us)", "us/t",
            "mixed (us)", "us/t",
            "async (us)", "us/t");
        System.out.println("─".repeat(12) + "─┼─" + "─".repeat(10) + "─┼─" + "─".repeat(5)
            + "─┼─" + "─".repeat(11) + "─┼─" + "─".repeat(5)
            + "─┼─" + "─".repeat(11) + "─┼─" + "─".repeat(5));

        for (int size : allSizes) {
            var syncScore = data.getOrDefault("sync", new TreeMap<>()).get(size);
            var mixedScore = data.getOrDefault("mixed", new TreeMap<>()).get(size);
            var asyncScore = data.getOrDefault("async", new TreeMap<>()).get(size);

            System.out.printf("%-12d │ %10s │ %5s │ %11s │ %5s │ %11s │ %5s%n",
                size,
                fmtScore(syncScore), fmtPerT(syncScore, size),
                fmtScore(mixedScore), fmtPerT(mixedScore, size),
                fmtScore(asyncScore), fmtPerT(asyncScore, size));
        }
        System.out.println();
    }

    private static String fmtScore(Double score) {
        return score == null ? "?" : String.format("%.2f", score);
    }

    private static String fmtPerT(Double score, int transitions) {
        return score == null ? "?" : String.format("%.2f", score / transitions);
    }
}
