package org.libpetri.benchmark;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.debug.DebugAwareEventStore;
import org.libpetri.debug.DebugEventStore;
import org.libpetri.debug.LogCaptureScopeForwardingExecutor;
import org.libpetri.event.EventStore;
import org.libpetri.runtime.BitmapNetExecutor;
import org.libpetri.runtime.NetExecutor;
import org.libpetri.runtime.PrecompiledNetExecutor;

import java.time.Duration;
import java.time.Instant;
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
@Warmup(iterations = 2, time = 1)
@Measurement(iterations = 3, time = 1)
@Fork(1)
public class BitmapNetExecutorBenchmark {

    record BenchToken(String value) {}

    /** ν-net correlation message: a single opaque correlation id (spec NU-001). */
    record NuMsg(String cid) {}

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
    private PetriNet syncLinearNet1000, syncLinearNet2000, syncLinearNet5000, syncLinearNet10000;
    private Place<BenchToken> syncStart10, syncStart20, syncStart50, syncStart100, syncStart200, syncStart500;
    private Place<BenchToken> syncStart1000, syncStart2000, syncStart5000, syncStart10000;

    // Out.Timeout chains — the only benchmarks exercising the timeout path.
    private PetriNet timeoutLinearNet10, timeoutLinearNet50, timeoutLinearNet100;
    private Place<BenchToken> timeoutStart10, timeoutStart50, timeoutStart100;

    // Mixed linear chains (2 async + rest sync)
    private PetriNet mixedLinearNet10, mixedLinearNet20, mixedLinearNet50, mixedLinearNet100, mixedLinearNet200, mixedLinearNet500;
    private Place<BenchToken> mixedStart10, mixedStart20, mixedStart50, mixedStart100, mixedStart200, mixedStart500;

    // Complex workflow
    private WorkflowNetWithStart complexWorkflow;

    // Precompiled nets (avoid recompilation per invocation)
    private java.util.Map<PetriNet, org.libpetri.runtime.PrecompiledNet> compiledPrograms;

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

        var syncLinear1000 = buildSyncLinearChain(1000);
        syncLinearNet1000 = syncLinear1000.net;
        syncStart1000 = syncLinear1000.start;

        var syncLinear2000 = buildSyncLinearChain(2000);
        syncLinearNet2000 = syncLinear2000.net;
        syncStart2000 = syncLinear2000.start;

        var syncLinear5000 = buildSyncLinearChain(5000);
        syncLinearNet5000 = syncLinear5000.net;
        syncStart5000 = syncLinear5000.start;

        var syncLinear10000 = buildSyncLinearChain(10000);
        syncLinearNet10000 = syncLinear10000.net;
        syncStart10000 = syncLinear10000.start;

        // Build mixed linear chains (~2% sync, rest async)
        var mixedLinear10 = buildMixedLinearChain(10);
        mixedLinearNet10 = mixedLinear10.net;
        mixedStart10 = mixedLinear10.start;

        var mixedLinear20 = buildMixedLinearChain(20);
        mixedLinearNet20 = mixedLinear20.net;
        mixedStart20 = mixedLinear20.start;

        var mixedLinear50 = buildMixedLinearChain(50);
        mixedLinearNet50 = mixedLinear50.net;
        mixedStart50 = mixedLinear50.start;

        var mixedLinear100 = buildMixedLinearChain(100);
        mixedLinearNet100 = mixedLinear100.net;
        mixedStart100 = mixedLinear100.start;

        var mixedLinear200 = buildMixedLinearChain(200);
        mixedLinearNet200 = mixedLinear200.net;
        mixedStart200 = mixedLinear200.start;

        var mixedLinear500 = buildMixedLinearChain(500);
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

        // Build Out.Timeout chains
        var timeout10 = buildTimeoutLinearChain(10);
        timeoutLinearNet10 = timeout10.net;
        timeoutStart10 = timeout10.start;

        var timeout50 = buildTimeoutLinearChain(50);
        timeoutLinearNet50 = timeout50.net;
        timeoutStart50 = timeout50.start;

        var timeout100 = buildTimeoutLinearChain(100);
        timeoutLinearNet100 = timeout100.net;
        timeoutStart100 = timeout100.start;

        // Build complex workflow
        complexWorkflow = buildComplexWorkflow();

        // Precompile nets for PrecompiledNetExecutor benchmarks
        compiledPrograms = new java.util.IdentityHashMap<>();
        for (var net : List.of(
            syncLinearNet10, syncLinearNet20, syncLinearNet50, syncLinearNet100, syncLinearNet200, syncLinearNet500,
            syncLinearNet1000, syncLinearNet2000, syncLinearNet5000, syncLinearNet10000,
            mixedLinearNet10, mixedLinearNet20, mixedLinearNet50, mixedLinearNet100, mixedLinearNet200, mixedLinearNet500,
            linearNet5, linearNet10, linearNet20, linearNet50, linearNet100, linearNet200, linearNet500,
            parallelNet5, parallelNet10, parallelNet20,
            timeoutLinearNet10, timeoutLinearNet50, timeoutLinearNet100,
            largeNet, complexWorkflow.net
        )) {
            compiledPrograms.put(net, org.libpetri.runtime.PrecompiledNet.compile(net));
        }
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
     * Builds a linear chain whose every transition carries an {@code Out.Timeout} that never
     * fires (the budget is far longer than the action).
     *
     * <p>This path was entirely unmeasured: none of the other benchmarks declare a timeout, and
     * a timed transition is deliberately excluded from the sync fast path. The action returns an
     * <em>incomplete</em> future (via {@code supplyAsync}), so {@code withActionTimeout} genuinely
     * arms and then cancels a budget timer per firing — a completed future would short-circuit it.
     * Compare against {@code linear_*} (also async), not the sync chain. Any change to timeout
     * handling shows up here.
     */
    private NetWithStart buildTimeoutLinearChain(int transitions) {
        var start = Place.of("to_start", BenchToken.class);
        var places = new ArrayList<Place<BenchToken>>();
        places.add(start);

        for (int i = 1; i <= transitions; i++) {
            places.add(Place.of("to_p" + i, BenchToken.class));
        }

        var timeoutSink = Place.of("to_timeout", BenchToken.class);

        var builder = PetriNet.builder("TimeoutLinear" + transitions);
        for (int i = 0; i < transitions; i++) {
            var to = places.get(i + 1);
            builder.transition(
                Transition.builder("to_t" + (i + 1))
                    .inputs(In.one(places.get(i)))
                    .outputs(Out.xor(
                        Out.place(to),
                        Out.timeout(Duration.ofMinutes(5), Out.place(timeoutSink))
                    ))
                    .action(ctx -> {
                        Blackhole.consumeCPU(100);
                        ctx.output(to, new BenchToken("v"));
                        // Incomplete future so the budget timer is genuinely armed per firing.
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
     * Builds a mixed linear chain: ~2% of transitions are synchronous
     * fast-paths ({@code completedFuture}) and the rest dispatch async work
     * ({@code supplyAsync}) — the common real-world shape where most work is
     * I/O / network / LLM and only a small fraction is in-memory decisions.
     * Formula: {@code syncCount = total / 50} — total=50 → 1 sync,
     * total=100 → 2 sync, total=500 → 10 sync; chains of total ≤ 20 are
     * 100% async (the 2% formula rounds to zero).
     */
    private NetWithStart buildMixedLinearChain(int total) {
        int syncCount = total / 50;
        var start = Place.of("mix_start", BenchToken.class);
        var places = new ArrayList<Place<BenchToken>>();
        places.add(start);

        for (int i = 1; i <= total; i++) {
            places.add(Place.of("mix_p" + i, BenchToken.class));
        }

        var builder = PetriNet.builder("MixedLinear" + total);
        for (int i = 0; i < total; i++) {
            var to = places.get(i + 1);
            boolean async = i >= syncCount;
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

    @Benchmark
    public void sync_linear_1000t(Blackhole bh) {
        runBitmapNet(syncLinearNet1000, syncStart1000, bh);
    }

    @Benchmark
    public void sync_linear_2000t(Blackhole bh) {
        runBitmapNet(syncLinearNet2000, syncStart2000, bh);
    }

    @Benchmark
    public void sync_linear_5000t(Blackhole bh) {
        runBitmapNet(syncLinearNet5000, syncStart5000, bh);
    }

    @Benchmark
    public void sync_linear_10000t(Blackhole bh) {
        runBitmapNet(syncLinearNet10000, syncStart10000, bh);
    }

    // ==================== MIXED LINEAR CHAIN BENCHMARKS ====================

    @Benchmark
    public void mixed_linear_10t(Blackhole bh) {
        runBitmapNet(mixedLinearNet10, mixedStart10, bh);
    }

    @Benchmark
    public void mixed_linear_20t(Blackhole bh) {
        runBitmapNet(mixedLinearNet20, mixedStart20, bh);
    }

    @Benchmark
    public void mixed_linear_50t(Blackhole bh) {
        runBitmapNet(mixedLinearNet50, mixedStart50, bh);
    }

    @Benchmark
    public void mixed_linear_100t(Blackhole bh) {
        runBitmapNet(mixedLinearNet100, mixedStart100, bh);
    }

    @Benchmark
    public void mixed_linear_200t(Blackhole bh) {
        runBitmapNet(mixedLinearNet200, mixedStart200, bh);
    }

    @Benchmark
    public void mixed_linear_500t(Blackhole bh) {
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

    // ==================== COMPILED VM: SYNC LINEAR CHAIN ====================

    // ==================== Out.Timeout chains ====================
    // A timed transition is excluded from the sync fast path, so these measure the
    // in-flight bookkeeping + per-firing timer arm that no other benchmark touches.

    @Benchmark
    public void timeout_linear_10t(Blackhole bh) {
        runBitmapNet(timeoutLinearNet10, timeoutStart10, bh);
    }

    @Benchmark
    public void timeout_linear_50t(Blackhole bh) {
        runBitmapNet(timeoutLinearNet50, timeoutStart50, bh);
    }

    @Benchmark
    public void timeout_linear_100t(Blackhole bh) {
        runBitmapNet(timeoutLinearNet100, timeoutStart100, bh);
    }

    @Benchmark
    public void compiled_timeout_linear_10t(Blackhole bh) {
        runCompiledNet(timeoutLinearNet10, timeoutStart10, bh);
    }

    @Benchmark
    public void compiled_timeout_linear_50t(Blackhole bh) {
        runCompiledNet(timeoutLinearNet50, timeoutStart50, bh);
    }

    @Benchmark
    public void compiled_timeout_linear_100t(Blackhole bh) {
        runCompiledNet(timeoutLinearNet100, timeoutStart100, bh);
    }

    @Benchmark
    public void compiled_sync_linear_10t(Blackhole bh) {
        runCompiledNet(syncLinearNet10, syncStart10, bh);
    }

    @Benchmark
    public void compiled_sync_linear_20t(Blackhole bh) {
        runCompiledNet(syncLinearNet20, syncStart20, bh);
    }

    @Benchmark
    public void compiled_sync_linear_50t(Blackhole bh) {
        runCompiledNet(syncLinearNet50, syncStart50, bh);
    }

    @Benchmark
    public void compiled_sync_linear_100t(Blackhole bh) {
        runCompiledNet(syncLinearNet100, syncStart100, bh);
    }

    @Benchmark
    public void compiled_sync_linear_200t(Blackhole bh) {
        runCompiledNet(syncLinearNet200, syncStart200, bh);
    }

    @Benchmark
    public void compiled_sync_linear_500t(Blackhole bh) {
        runCompiledNet(syncLinearNet500, syncStart500, bh);
    }

    @Benchmark
    public void compiled_sync_linear_1000t(Blackhole bh) {
        runCompiledNet(syncLinearNet1000, syncStart1000, bh);
    }

    @Benchmark
    public void compiled_sync_linear_2000t(Blackhole bh) {
        runCompiledNet(syncLinearNet2000, syncStart2000, bh);
    }

    @Benchmark
    public void compiled_sync_linear_5000t(Blackhole bh) {
        runCompiledNet(syncLinearNet5000, syncStart5000, bh);
    }

    @Benchmark
    public void compiled_sync_linear_10000t(Blackhole bh) {
        runCompiledNet(syncLinearNet10000, syncStart10000, bh);
    }

    // ==================== COMPILED VM: MIXED LINEAR CHAIN ====================

    @Benchmark
    public void compiled_mixed_linear_10t(Blackhole bh) {
        runCompiledNet(mixedLinearNet10, mixedStart10, bh);
    }

    @Benchmark
    public void compiled_mixed_linear_20t(Blackhole bh) {
        runCompiledNet(mixedLinearNet20, mixedStart20, bh);
    }

    @Benchmark
    public void compiled_mixed_linear_50t(Blackhole bh) {
        runCompiledNet(mixedLinearNet50, mixedStart50, bh);
    }

    @Benchmark
    public void compiled_mixed_linear_100t(Blackhole bh) {
        runCompiledNet(mixedLinearNet100, mixedStart100, bh);
    }

    @Benchmark
    public void compiled_mixed_linear_200t(Blackhole bh) {
        runCompiledNet(mixedLinearNet200, mixedStart200, bh);
    }

    @Benchmark
    public void compiled_mixed_linear_500t(Blackhole bh) {
        runCompiledNet(mixedLinearNet500, mixedStart500, bh);
    }

    // ==================== COMPILED VM: ASYNC LINEAR CHAIN ====================

    @Benchmark
    public void compiled_linear_5t(Blackhole bh) {
        runCompiledNet(linearNet5, start5, bh);
    }

    @Benchmark
    public void compiled_linear_10t(Blackhole bh) {
        runCompiledNet(linearNet10, start10, bh);
    }

    @Benchmark
    public void compiled_linear_20t(Blackhole bh) {
        runCompiledNet(linearNet20, start20, bh);
    }

    @Benchmark
    public void compiled_linear_50t(Blackhole bh) {
        runCompiledNet(linearNet50, start50, bh);
    }

    @Benchmark
    public void compiled_linear_100t(Blackhole bh) {
        runCompiledNet(linearNet100, start100, bh);
    }

    @Benchmark
    public void compiled_linear_200t(Blackhole bh) {
        runCompiledNet(linearNet200, start200, bh);
    }

    @Benchmark
    public void compiled_linear_500t(Blackhole bh) {
        runCompiledNet(linearNet500, start500, bh);
    }

    // ==================== COMPILED VM: PARALLEL FAN-OUT ====================

    @Benchmark
    public void compiled_parallel_5b(Blackhole bh) {
        runCompiledNet(parallelNet5, pstart5, bh);
    }

    @Benchmark
    public void compiled_parallel_10b(Blackhole bh) {
        runCompiledNet(parallelNet10, pstart10, bh);
    }

    @Benchmark
    public void compiled_parallel_20b(Blackhole bh) {
        runCompiledNet(parallelNet20, pstart20, bh);
    }

    // ==================== COMPILED VM: LARGE + COMPLEX ====================

    @Benchmark
    public void compiled_large(Blackhole bh) {
        runCompiledNet(largeNet, largeStart, bh);
    }

    @Benchmark
    public void compiled_complex(Blackhole bh) {
        runComplexCompiledNet(EventStore.noop(), virtualExecutor, bh);
    }

    @Benchmark
    public void compiled_complex_eventStore(EventStoreState storeState, Blackhole bh) {
        runComplexCompiledNet(storeState.store, virtualExecutor, bh);
    }

    // ==================== NET EXECUTOR (REFERENCE): SYNC LINEAR CHAIN ====================

    @Benchmark
    public void ref_sync_linear_10t(Blackhole bh) {
        runNetExecutor(syncLinearNet10, syncStart10, bh);
    }

    @Benchmark
    public void ref_sync_linear_20t(Blackhole bh) {
        runNetExecutor(syncLinearNet20, syncStart20, bh);
    }

    @Benchmark
    public void ref_sync_linear_50t(Blackhole bh) {
        runNetExecutor(syncLinearNet50, syncStart50, bh);
    }

    @Benchmark
    public void ref_sync_linear_100t(Blackhole bh) {
        runNetExecutor(syncLinearNet100, syncStart100, bh);
    }

    @Benchmark
    public void ref_sync_linear_200t(Blackhole bh) {
        runNetExecutor(syncLinearNet200, syncStart200, bh);
    }

    @Benchmark
    public void ref_sync_linear_500t(Blackhole bh) {
        runNetExecutor(syncLinearNet500, syncStart500, bh);
    }

    // ==================== NET EXECUTOR (REFERENCE): COMPLEX WORKFLOW ====================

    @Benchmark
    public void ref_complex_noop(Blackhole bh) {
        runComplexNetExecutor(EventStore.noop(), virtualExecutor, bh);
    }

    // ==================== HELPERS ====================

    private void runNetExecutor(PetriNet net, Place<BenchToken> start, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var exec = NetExecutor.create(
                net,
                input,
                EventStore.noop(),
                virtualExecutor
            )
        ) {
            bh.consume(exec.run());
        }
    }

    private void runComplexNetExecutor(EventStore store, ExecutorService exec, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            complexWorkflow.start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var executor = NetExecutor.create(
                complexWorkflow.net,
                input,
                store,
                exec
            )
        ) {
            bh.consume(executor.run());
        }
    }

    private void runCompiledNet(PetriNet net, Place<BenchToken> start, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var exec = PrecompiledNetExecutor.builder(net, input)
                .program(compiledPrograms.get(net))
                .eventStore(EventStore.noop())
                .orchestratorExecutor(virtualExecutor)
                .build()
        ) {
            bh.consume(exec.run());
        }
    }

    private void runComplexCompiledNet(EventStore store, ExecutorService exec, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            complexWorkflow.start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var executor = PrecompiledNetExecutor.builder(complexWorkflow.net, input)
                .program(compiledPrograms.get(complexWorkflow.net))
                .eventStore(store)
                .orchestratorExecutor(exec)
                .build()
        ) {
            bh.consume(executor.run());
        }
    }

    private void runBitmapNet(PetriNet net, Place<BenchToken> start, Blackhole bh) {
        var input = Map.<Place<?>, List<Token<?>>>of(
            start,
            List.of(Token.of(new BenchToken("start")))
        );
        try (
            var exec = BitmapNetExecutor.builder(net, input)
                .eventStore(EventStore.noop())
                .orchestratorExecutor(virtualExecutor)
                .build()
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

    // ==================== ν-net Firing-Check Benchmarks (spec NU-020/040) ====================
    //
    // A transition carrying a MatchSpec is enabled only when a single correlation
    // name is present in every correlated input (findMatchBinding → selectMatchName).
    // Unlike the cardinality check, that re-builds a name → {count, oldest} index
    // over EVERY token in each correlated input on each enablement re-evaluation —
    // so draining a deep pool re-indexes the shrinking pool every fire (≈ O(k·depth²)).
    // The PrecompiledNetExecutor also re-computes the binding on consume, so the
    // compiled benches reflect the real production cost. The hasMatch gate means
    // non-ν transitions pay nothing, so the benchmarks above are unaffected.
    //
    // NU-021 (input-arc guards) has no scenario here: the Java In factory exposes
    // no guard predicate. That guard-eval cost is covered by the byte-identical
    // match engine in the Rust/TS suites (nu_join_drain_guarded).

    record NuDrainNet(PetriNet net, List<Place<NuMsg>> inputs) {}

    record NuScatterNet(PetriNet net, Place<Integer> source, Place<Integer> budget) {}

    /** k-way ν-net join correlating all inputs by cid, drained to a String sink. */
    private static NuDrainNet buildNuJoinDrain(int branches) {
        var inputs = new ArrayList<Place<NuMsg>>();
        for (int i = 0; i < branches; i++) {
            inputs.add(Place.of("branch" + i, NuMsg.class));
        }
        var merged = Place.of("merged", String.class);

        var inSpecs = new In[branches];
        for (int i = 0; i < branches; i++) {
            inSpecs[i] = In.one(inputs.get(i));
        }
        var msb = MatchSpec.builder();
        for (var p : inputs) {
            msb = msb.key(p, (NuMsg m) -> NameId.of(m.cid()));
        }
        var join = Transition.builder("join")
            .inputs(inSpecs)
            .match(msb.build())
            .outputs(Out.place(merged))
            .action(ctx -> {
                ctx.output(merged, "m");
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("NuJoinDrain").transition(join).build();
        return new NuDrainNet(net, inputs);
    }

    /** Structurally identical k=2 join with NO MatchSpec — the plain-join baseline. */
    private static NuDrainNet buildPlainJoinDrain() {
        var a = Place.of("branch0", NuMsg.class);
        var b = Place.of("branch1", NuMsg.class);
        var merged = Place.of("merged", String.class);
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .outputs(Out.place(merged))
            .action(ctx -> {
                ctx.output(merged, "m");
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var net = PetriNet.builder("PlainJoinDrain").transition(join).build();
        return new NuDrainNet(net, List.of(a, b));
    }

    /**
     * Realistic fork(freshName)/join end-to-end. When {@code budgeted}, a budget
     * place (k=1) caps live fork groups (NU-040): the fork consumes a budget token
     * and the join returns it, keeping the branch pools shallow.
     */
    private static NuScatterNet buildNuScatterGather(boolean budgeted) {
        var source = Place.of("source", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var a = Place.of("branchA", NuMsg.class);
        var b = Place.of("branchB", NuMsg.class);
        var merged = Place.of("merged", String.class);

        var forkInputs = budgeted
            ? new In[] {In.one(source), In.one(budget)}
            : new In[] {In.one(source)};
        var fork = Transition.builder("fork")
            .inputs(forkInputs)
            .outputs(Out.and(a, b))
            .action(ctx -> {
                var id = ctx.freshName();
                ctx.output(a, new NuMsg(id.value()));
                ctx.output(b, new NuMsg(id.value()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        Out joinOut = budgeted ? Out.and(merged, budget) : Out.place(merged);
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder()
                .key(a, (NuMsg m) -> NameId.of(m.cid()))
                .key(b, (NuMsg m) -> NameId.of(m.cid()))
                .build())
            .outputs(joinOut)
            .action(ctx -> {
                ctx.output(merged, ctx.input(a).cid());
                if (budgeted) {
                    ctx.output(budget, 0);
                }
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("NuScatterGather").transitions(fork, join).build();
        return new NuScatterNet(net, source, budgeted ? budget : null);
    }

    /** Fresh marking: each correlated input seeded with {@code depth} distinct cids. */
    private static Map<Place<?>, List<Token<?>>> seedDrain(List<Place<NuMsg>> inputs, int depth) {
        var map = new HashMap<Place<?>, List<Token<?>>>();
        for (var p : inputs) {
            var toks = new ArrayList<Token<?>>(depth);
            for (int j = 0; j < depth; j++) {
                toks.add(new Token<>(new NuMsg("c" + j), Instant.ofEpochMilli(j)));
            }
            map.put(p, toks);
        }
        return map;
    }

    private static Map<Place<?>, List<Token<?>>> seedScatter(Place<Integer> source, Place<Integer> budget, int groups) {
        var map = new HashMap<Place<?>, List<Token<?>>>();
        var src = new ArrayList<Token<?>>(groups);
        for (int j = 0; j < groups; j++) {
            src.add(Token.of(0));
        }
        map.put(source, src);
        if (budget != null) {
            map.put(budget, List.of(Token.of(0)));
        }
        return map;
    }

    @State(Scope.Benchmark)
    public static class NuDrainState {
        @Param({"10", "50", "100", "200", "500"})
        public int depth;
        PetriNet net;
        List<Place<NuMsg>> inputs;
        org.libpetri.runtime.PrecompiledNet program;

        @Setup(Level.Trial)
        public void setup() {
            var b = buildNuJoinDrain(2);
            net = b.net();
            inputs = b.inputs();
            program = org.libpetri.runtime.PrecompiledNet.compile(net);
        }
    }

    @State(Scope.Benchmark)
    public static class PlainDrainState {
        @Param({"10", "50", "100", "200", "500"})
        public int depth;
        PetriNet net;
        List<Place<NuMsg>> inputs;
        org.libpetri.runtime.PrecompiledNet program;

        @Setup(Level.Trial)
        public void setup() {
            var b = buildPlainJoinDrain();
            net = b.net();
            inputs = b.inputs();
            program = org.libpetri.runtime.PrecompiledNet.compile(net);
        }
    }

    @State(Scope.Benchmark)
    public static class NuArityState {
        @Param({"4", "8"})
        public int arity;
        PetriNet net;
        List<Place<NuMsg>> inputs;
        org.libpetri.runtime.PrecompiledNet program;

        @Setup(Level.Trial)
        public void setup() {
            var b = buildNuJoinDrain(arity);
            net = b.net();
            inputs = b.inputs();
            program = org.libpetri.runtime.PrecompiledNet.compile(net);
        }
    }

    @State(Scope.Benchmark)
    public static class NuScatterState {
        @Param({"10", "50", "100"})
        public int groups;
        PetriNet net;
        Place<Integer> source;
        org.libpetri.runtime.PrecompiledNet program;

        @Setup(Level.Trial)
        public void setup() {
            var b = buildNuScatterGather(false);
            net = b.net();
            source = b.source();
            program = org.libpetri.runtime.PrecompiledNet.compile(net);
        }
    }

    @State(Scope.Benchmark)
    public static class NuBudgetState {
        @Param({"10", "50", "100"})
        public int groups;
        PetriNet net;
        Place<Integer> source;
        Place<Integer> budget;
        org.libpetri.runtime.PrecompiledNet program;

        @Setup(Level.Trial)
        public void setup() {
            var b = buildNuScatterGather(true);
            net = b.net();
            source = b.source();
            budget = b.budget();
            program = org.libpetri.runtime.PrecompiledNet.compile(net);
        }
    }

    private void runNuBitmap(PetriNet net, Map<Place<?>, List<Token<?>>> input, Blackhole bh) {
        try (var exec = BitmapNetExecutor.create(net, input, EventStore.noop(), virtualExecutor)) {
            bh.consume(exec.run());
        }
    }

    private void runNuCompiled(
        PetriNet net,
        org.libpetri.runtime.PrecompiledNet prog,
        Map<Place<?>, List<Token<?>>> input,
        Blackhole bh
    ) {
        try (
            var exec = PrecompiledNetExecutor.builder(net, input)
                .program(prog)
                .eventStore(EventStore.noop())
                .orchestratorExecutor(virtualExecutor)
                .build()
        ) {
            bh.consume(exec.run());
        }
    }

    // -------- ν join drain: the primary cost curve (depth) + arity axis --------

    @Benchmark
    public void nu_join_drain_bitmap(NuDrainState s, Blackhole bh) {
        runNuBitmap(s.net, seedDrain(s.inputs, s.depth), bh);
    }

    @Benchmark
    public void nu_join_drain_compiled(NuDrainState s, Blackhole bh) {
        runNuCompiled(s.net, s.program, seedDrain(s.inputs, s.depth), bh);
    }

    @Benchmark
    public void plain_join_drain_bitmap(PlainDrainState s, Blackhole bh) {
        runNuBitmap(s.net, seedDrain(s.inputs, s.depth), bh);
    }

    @Benchmark
    public void plain_join_drain_compiled(PlainDrainState s, Blackhole bh) {
        runNuCompiled(s.net, s.program, seedDrain(s.inputs, s.depth), bh);
    }

    @Benchmark
    public void nu_join_drain_arity_bitmap(NuArityState s, Blackhole bh) {
        runNuBitmap(s.net, seedDrain(s.inputs, 100), bh);
    }

    @Benchmark
    public void nu_join_drain_arity_compiled(NuArityState s, Blackhole bh) {
        runNuCompiled(s.net, s.program, seedDrain(s.inputs, 100), bh);
    }

    // -------- ν scatter/gather: realistic end-to-end, with/without budget --------

    @Benchmark
    public void nu_scatter_gather_bitmap(NuScatterState s, Blackhole bh) {
        runNuBitmap(s.net, seedScatter(s.source, null, s.groups), bh);
    }

    @Benchmark
    public void nu_scatter_gather_compiled(NuScatterState s, Blackhole bh) {
        runNuCompiled(s.net, s.program, seedScatter(s.source, null, s.groups), bh);
    }

    @Benchmark
    public void nu_scatter_gather_budgeted_bitmap(NuBudgetState s, Blackhole bh) {
        runNuBitmap(s.net, seedScatter(s.source, s.budget, s.groups), bh);
    }

    @Benchmark
    public void nu_scatter_gather_budgeted_compiled(NuBudgetState s, Blackhole bh) {
        runNuCompiled(s.net, s.program, seedScatter(s.source, s.budget, s.groups), bh);
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

    private static final Pattern SYNC_PATTERN = Pattern.compile("^(?:compiled_|ref_)?sync_linear_(\\d+)t$");
    private static final Pattern MIXED_PATTERN = Pattern.compile("^(?:compiled_|ref_)?mixed_linear_(\\d+)t$");
    private static final Pattern ASYNC_PATTERN = Pattern.compile("^(?:compiled_|ref_)?linear_(\\d+)t(?:_\\d+p)?$");

    private static void printScalingSummary(Collection<RunResult> results) {
        // engine -> mode -> transitionCount -> score (us)
        var bitmap = new TreeMap<String, TreeMap<Integer, Double>>();
        var compiled = new TreeMap<String, TreeMap<Integer, Double>>();
        var reference = new TreeMap<String, TreeMap<Integer, Double>>();

        for (var r : results) {
            if (r.getParams().getMode() != Mode.AverageTime) continue;

            var benchName = r.getParams().getBenchmark();
            var methodName = benchName.substring(benchName.lastIndexOf('.') + 1);
            double score = r.getPrimaryResult().getScore();
            boolean isCompiled = methodName.startsWith("compiled_");
            boolean isRef = methodName.startsWith("ref_");
            var target = isCompiled ? compiled : isRef ? reference : bitmap;

            var syncM = SYNC_PATTERN.matcher(methodName);
            var mixedM = MIXED_PATTERN.matcher(methodName);
            var asyncM = ASYNC_PATTERN.matcher(methodName);

            if (syncM.find()) {
                target.computeIfAbsent("sync", _ -> new TreeMap<>())
                    .put(Integer.parseInt(syncM.group(1)), score);
            } else if (mixedM.find()) {
                target.computeIfAbsent("mixed", _ -> new TreeMap<>())
                    .put(Integer.parseInt(mixedM.group(1)), score);
            } else if (asyncM.find()) {
                target.computeIfAbsent("async", _ -> new TreeMap<>())
                    .put(Integer.parseInt(asyncM.group(1)), score);
            }
        }

        if (bitmap.isEmpty() && compiled.isEmpty() && reference.isEmpty()) return;

        var allSizes = new TreeSet<Integer>();
        bitmap.values().forEach(m -> allSizes.addAll(m.keySet()));
        compiled.values().forEach(m -> allSizes.addAll(m.keySet()));
        reference.values().forEach(m -> allSizes.addAll(m.keySet()));

        for (var mode : List.of("sync", "mixed", "async")) {
            var rData = reference.getOrDefault(mode, new TreeMap<>());
            var bData = bitmap.getOrDefault(mode, new TreeMap<>());
            var cData = compiled.getOrDefault(mode, new TreeMap<>());
            if (bData.isEmpty() && cData.isEmpty() && rData.isEmpty()) continue;

            System.out.println();
            System.out.printf("=== %s LINEAR SCALING (avgt, us/op) ===%n", mode.toUpperCase());
            System.out.printf("%-12s │ %10s │ %10s │ %10s │ %10s │ %10s%n",
                "Transitions", "Reference", "Bitmap", "Compiled", "Ref/Bitmap", "Bitmap/Comp");
            System.out.println("─".repeat(12) + "─┼─" + "─".repeat(10) + "─┼─"
                + "─".repeat(10) + "─┼─" + "─".repeat(10) + "─┼─"
                + "─".repeat(10) + "─┼─" + "─".repeat(10));

            for (int size : allSizes) {
                var rScore = rData.get(size);
                var bScore = bData.get(size);
                var cScore = cData.get(size);
                String refVsBitmap = (rScore != null && bScore != null && bScore > 0)
                    ? String.format("%.2fx", rScore / bScore) : "";
                String bitmapVsCompiled = (bScore != null && cScore != null && cScore > 0)
                    ? String.format("%.2fx", bScore / cScore) : "";
                System.out.printf("%-12d │ %10s │ %10s │ %10s │ %10s │ %10s%n",
                    size, fmtScore(rScore), fmtScore(bScore), fmtScore(cScore),
                    refVsBitmap, bitmapVsCompiled);
            }
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
