use criterion::{Criterion, black_box, criterion_group, criterion_main};

use libpetri::runtime::environment::ExecutorSignal;
use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
use libpetri::runtime::precompiled_net::PrecompiledNet;
use libpetri::*;

fn build_linear_chain(n: usize) -> (PetriNet, Place<i32>) {
    let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
    let transitions: Vec<Transition> = (0..n)
        .map(|i| {
            Transition::builder(format!("t{i}"))
                .input(one(&places[i]))
                .output(out_place(&places[i + 1]))
                .action(fork())
                .build()
        })
        .collect();

    let net = PetriNet::builder("chain").transitions(transitions).build();
    (net, places[0].clone())
}

fn single_passthrough(c: &mut Criterion) {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("single").transition(t).build();

    c.bench_function("single_passthrough", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));
            let mut executor =
                BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
            executor.run_sync();
            black_box(executor.marking().count("p2"));
        })
    });
}

fn sync_linear_chain(c: &mut Criterion) {
    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        c.bench_function(&format!("sync_linear_chain/{n}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                marking.add(&start, Token::at(1, 0));
                let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                    &net,
                    marking,
                    ExecutorOptions::default(),
                );
                executor.run_sync();
                black_box(executor.marking().count(&format!("p{n}")));
            })
        });
    }
}

fn build_fan_out(fan: usize) -> (PetriNet, Place<i32>, Place<i32>) {
    let start = Place::<i32>::new("start");
    let mid: Vec<Place<i32>> = (0..fan).map(|i| Place::new(format!("mid{i}"))).collect();
    let end = Place::<i32>::new("end");

    let mut transitions = Vec::new();

    // Fan out: start -> mid[i]
    for (i, m) in mid.iter().enumerate() {
        transitions.push(
            Transition::builder(format!("fan_out_{i}"))
                .input(one(&start))
                .output(out_place(m))
                .action(fork())
                .build(),
        );
    }

    // Fan in: mid[i] -> end
    for (i, m) in mid.iter().enumerate() {
        transitions.push(
            Transition::builder(format!("fan_in_{i}"))
                .input(one(m))
                .output(out_place(&end))
                .action(fork())
                .build(),
        );
    }

    let net = PetriNet::builder("fan_out")
        .transitions(transitions)
        .build();
    (net, start, end)
}

fn parallel_fan_out(c: &mut Criterion) {
    for &fan in &[5, 10, 20] {
        let (net, start, _end) = build_fan_out(fan);
        c.bench_function(&format!("parallel_fan_out/{fan}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                // Add enough tokens for all fan-out transitions
                for _ in 0..fan {
                    marking.add(&start, Token::at(1, 0));
                }
                let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                    &net,
                    marking,
                    ExecutorOptions::default(),
                );
                executor.run_sync();
                black_box(executor.marking().count("end"));
            })
        });
    }
}

fn compilation(c: &mut Criterion) {
    for &n in &[10, 50, 100, 500] {
        let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
        let transitions: Vec<Transition> = (0..n)
            .map(|i| {
                Transition::builder(format!("t{i}"))
                    .input(one(&places[i]))
                    .output(out_place(&places[i + 1]))
                    .action(fork())
                    .build()
            })
            .collect();

        let net = PetriNet::builder("chain").transitions(transitions).build();

        c.bench_function(&format!("compilation/{n}"), |b| {
            b.iter(|| {
                let marking = Marking::new();
                let executor = BitmapNetExecutor::<NoopEventStore>::new(
                    black_box(&net),
                    marking,
                    ExecutorOptions::default(),
                );
                black_box(&executor);
            })
        });
    }
}

fn noop_vs_inmemory(c: &mut Criterion) {
    let (net, start) = build_linear_chain(10);

    c.bench_function("noop_event_store/10", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&start, Token::at(1, 0));
            let mut executor =
                BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
            executor.run_sync();
        })
    });

    c.bench_function("inmemory_event_store/10", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&start, Token::at(1, 0));
            let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
                &net,
                marking,
                ExecutorOptions::default(),
            );
            executor.run_sync();
        })
    });
}

fn async_linear_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        c.bench_function(&format!("async_linear_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                        &net,
                        marking,
                        ExecutorOptions::default(),
                    );
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    executor.run_async(rx).await;
                    black_box(executor.marking().count(&format!("p{n}")));
                })
            })
        });
    }
}

fn build_mixed_chain(n: usize, async_count: usize) -> (PetriNet, Place<i32>) {
    let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
    let transitions: Vec<Transition> = (0..n)
        .map(|i| {
            let mut builder = Transition::builder(format!("t{i}"))
                .input(one(&places[i]))
                .output(out_place(&places[i + 1]));
            if i < async_count {
                builder = builder.action(async_action(|ctx| async { Ok(ctx) }));
            } else {
                builder = builder.action(fork());
            }
            builder.build()
        })
        .collect();

    let net = PetriNet::builder("mixed_chain")
        .transitions(transitions)
        .build();
    (net, places[0].clone())
}

fn mixed_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[10, 20, 50, 100, 200, 500] {
        let (net, start) = build_mixed_chain(n, 2);
        c.bench_function(&format!("mixed_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                        &net,
                        marking,
                        ExecutorOptions::default(),
                    );
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    executor.run_async(rx).await;
                    black_box(executor.marking().count(&format!("p{n}")));
                })
            })
        });
    }
}

fn async_fan_out(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &fan in &[5, 10, 20] {
        let (net, start, _end) = build_fan_out(fan);
        c.bench_function(&format!("async_fan_out/{fan}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    for _ in 0..fan {
                        marking.add(&start, Token::at(1, 0));
                    }
                    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                        &net,
                        marking,
                        ExecutorOptions::default(),
                    );
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    executor.run_async(rx).await;
                    black_box(executor.marking().count("end"));
                })
            })
        });
    }
}

fn build_complex_workflow() -> (PetriNet, Place<i32>) {
    let input = Place::<i32>::new("v_input");
    let guard_in = Place::<i32>::new("v_guardIn");
    let intent_in = Place::<i32>::new("v_intentIn");
    let search_in = Place::<i32>::new("v_searchIn");
    let output_guard_in = Place::<i32>::new("v_outputGuardIn");
    let guard_safe = Place::<i32>::new("v_guardSafe");
    let guard_violation = Place::<i32>::new("v_guardViolation");
    let violated = Place::<i32>::new("v_violated");
    let intent_ready = Place::<i32>::new("v_intentReady");
    let topic_ready = Place::<i32>::new("v_topicReady");
    let search_ready = Place::<i32>::new("v_searchReady");
    let output_guard_done = Place::<i32>::new("v_outputGuardDone");
    let response = Place::<i32>::new("v_response");

    // T1: Fork (1-to-4 fan-out)
    let fork_trans = Transition::builder("Fork")
        .input(one(&input))
        .output(and(vec![
            out_place(&guard_in),
            out_place(&intent_in),
            out_place(&search_in),
            out_place(&output_guard_in),
        ]))
        .action(fork())
        .build();

    // T2: Guard (XOR output - safe or violation)
    let guard_trans = Transition::builder("Guard")
        .input(one(&guard_in))
        .output(xor(vec![
            out_place(&guard_safe),
            out_place(&guard_violation),
        ]))
        .action(fork())
        .build();

    // T3: HandleViolation (inhibited by guard_safe)
    let handle_violation = Transition::builder("HandleViolation")
        .input(one(&guard_violation))
        .output(out_place(&violated))
        .inhibitor(inhibitor(&guard_safe))
        .action(fork())
        .build();

    // T4: Intent
    let intent_trans = Transition::builder("Intent")
        .input(one(&intent_in))
        .output(out_place(&intent_ready))
        .action(fork())
        .build();

    // T5: TopicKnowledge
    let topic_trans = Transition::builder("TopicKnowledge")
        .input(one(&intent_ready))
        .output(out_place(&topic_ready))
        .action(fork())
        .build();

    // T6: Search (read intentReady, inhibited by guardViolation, low priority)
    let search_trans = Transition::builder("Search")
        .input(one(&search_in))
        .output(out_place(&search_ready))
        .read(read(&intent_ready))
        .inhibitor(inhibitor(&guard_violation))
        .priority(-5)
        .action(fork())
        .build();

    // T7: OutputGuard (reads guardSafe)
    let output_guard_trans = Transition::builder("OutputGuard")
        .input(one(&output_guard_in))
        .output(out_place(&output_guard_done))
        .read(read(&guard_safe))
        .action(fork())
        .build();

    // T8: Compose (AND-join of 3 parallel paths, high priority)
    let compose_trans = Transition::builder("Compose")
        .input(one(&guard_safe))
        .input(one(&search_ready))
        .input(one(&topic_ready))
        .output(out_place(&response))
        .priority(10)
        .action(fork())
        .build();

    let net = PetriNet::builder("ComplexWorkflow")
        .transition(fork_trans)
        .transition(guard_trans)
        .transition(handle_violation)
        .transition(intent_trans)
        .transition(topic_trans)
        .transition(search_trans)
        .transition(output_guard_trans)
        .transition(compose_trans)
        .build();

    (net, input)
}

fn complex_workflow(c: &mut Criterion) {
    let (net, start) = build_complex_workflow();
    c.bench_function("complex_workflow/8t_13p", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&start, Token::at(1, 0));
            let mut executor =
                BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
            executor.run_sync();
            black_box(executor.marking().count("v_response"));
        })
    });
}

// ==================== Precompiled Executor Benchmarks ====================

fn precompiled_single_passthrough(c: &mut Criterion) {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("single").transition(t).build();
    let compiled = CompiledNet::compile(&net);
    let prog = PrecompiledNet::from_compiled(&compiled);

    c.bench_function("precompiled_single_passthrough", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let result = executor.run_sync();
            black_box(result.count("p2"));
        })
    });
}

fn precompiled_sync_linear_chain(c: &mut Criterion) {
    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);
        c.bench_function(&format!("precompiled_sync_linear_chain/{n}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                marking.add(&start, Token::at(1, 0));
                let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
                let result = executor.run_sync();
                black_box(result.count(&format!("p{n}")));
            })
        });
    }
}

fn precompiled_parallel_fan_out(c: &mut Criterion) {
    for &fan in &[5, 10, 20] {
        let (net, start, _end) = build_fan_out(fan);
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);
        c.bench_function(&format!("precompiled_parallel_fan_out/{fan}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                for _ in 0..fan {
                    marking.add(&start, Token::at(1, 0));
                }
                let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
                let result = executor.run_sync();
                black_box(result.count("end"));
            })
        });
    }
}

fn precompiled_compilation(c: &mut Criterion) {
    for &n in &[10, 50, 100, 500] {
        let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
        let transitions: Vec<Transition> = (0..n)
            .map(|i| {
                Transition::builder(format!("t{i}"))
                    .input(one(&places[i]))
                    .output(out_place(&places[i + 1]))
                    .action(fork())
                    .build()
            })
            .collect();

        let net = PetriNet::builder("chain").transitions(transitions).build();

        c.bench_function(&format!("precompiled_compilation/{n}"), |b| {
            b.iter(|| {
                let compiled = CompiledNet::compile(black_box(&net));
                let prog = PrecompiledNet::from_compiled(&compiled);
                black_box(&prog);
            })
        });
    }
}

fn precompiled_complex_workflow(c: &mut Criterion) {
    let (net, start) = build_complex_workflow();
    let compiled = CompiledNet::compile(&net);
    let prog = PrecompiledNet::from_compiled(&compiled);
    c.bench_function("precompiled_complex_workflow/8t_13p", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&start, Token::at(1, 0));
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let result = executor.run_sync();
            black_box(result.count("v_response"));
        })
    });
}

fn precompiled_async_linear_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);
        c.bench_function(&format!("precompiled_async_linear_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let mut executor =
                        PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    let result = executor.run_async(rx).await;
                    black_box(result.count(&format!("p{n}")));
                })
            })
        });
    }
}

fn precompiled_mixed_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[10, 20, 50, 100, 200, 500] {
        let (net, start) = build_mixed_chain(n, 2);
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);
        c.bench_function(&format!("precompiled_mixed_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let mut executor =
                        PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    let result = executor.run_async(rx).await;
                    black_box(result.count(&format!("p{n}")));
                })
            })
        });
    }
}

criterion_group!(
    benches,
    single_passthrough,
    sync_linear_chain,
    parallel_fan_out,
    compilation,
    noop_vs_inmemory,
    async_linear_chain,
    mixed_chain,
    async_fan_out,
    complex_workflow,
    precompiled_single_passthrough,
    precompiled_sync_linear_chain,
    precompiled_parallel_fan_out,
    precompiled_compilation,
    precompiled_complex_workflow,
    precompiled_async_linear_chain,
    precompiled_mixed_chain,
);
criterion_main!(benches);
