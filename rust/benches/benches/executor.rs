use criterion::{black_box, criterion_group, criterion_main, Criterion};

use libpetri::*;
use libpetri::runtime::environment::ExternalEvent;

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
            let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                &net,
                marking,
                ExecutorOptions::default(),
            );
            executor.run_sync();
            black_box(executor.marking().count("p2"));
        })
    });
}

fn sync_linear_chain(c: &mut Criterion) {
    for &n in &[5, 10, 50, 100, 500] {
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

    let net = PetriNet::builder("fan_out").transitions(transitions).build();
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
            let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                &net,
                marking,
                ExecutorOptions::default(),
            );
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

    for &n in &[5, 10, 50] {
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
                    let (_tx, rx) =
                        tokio::sync::mpsc::unbounded_channel::<ExternalEvent>();
                    executor.run_async(rx).await;
                    black_box(executor.marking().count(&format!("p{n}")));
                })
            })
        });
    }
}

fn build_mixed_chain(n: usize) -> (PetriNet, Place<i32>) {
    let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
    let transitions: Vec<Transition> = (0..n)
        .map(|i| {
            let mut builder = Transition::builder(format!("t{i}"))
                .input(one(&places[i]))
                .output(out_place(&places[i + 1]));
            if i % 2 == 0 {
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

    for &n in &[10, 50] {
        let (net, start) = build_mixed_chain(n);
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
                    let (_tx, rx) =
                        tokio::sync::mpsc::unbounded_channel::<ExternalEvent>();
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

    for &fan in &[5, 10] {
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
                    let (_tx, rx) =
                        tokio::sync::mpsc::unbounded_channel::<ExternalEvent>();
                    executor.run_async(rx).await;
                    black_box(executor.marking().count("end"));
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
    async_fan_out
);
criterion_main!(benches);
