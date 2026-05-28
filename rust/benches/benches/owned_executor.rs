//! Criterion benchmarks for the `OwnedPrecompiledNet` execution path.
//!
//! These mirror a representative subset of the `precompiled_*` benchmarks in
//! `executor.rs`. The owned path is what the Python bindings (`libpetri-py`)
//! use internally, so its Rust numbers are the apples-to-apples baseline
//! against which Python FFI overhead (+ optional GIL bridge) shows up.
//!
//! Naming: every benchmark here has an `owned_` prefix corresponding to a
//! `precompiled_` benchmark in `executor.rs`.
//!
//! Note on expected overhead vs. `precompiled_*`:
//! The `precompiled_*` benchmarks build a `PrecompiledNetExecutor` directly
//! over a precompiled program held in a local variable. `OwnedPrecompiledNet`
//! caches the precompiled program in an `Arc<PrecompiledNet>` (built once at
//! construction — no per-call recompilation), and each `run_sync` / `run_async`
//! still allocates a fresh `OwnedPrecompiledExecutorBuilder`, a fresh
//! `PrecompiledNetExecutor`, the per-run ring-buffer / dirty / enabled bitmaps,
//! and clones the `HashSet<Arc<str>>` of environment places. That allocation
//! tax — not recompilation — is the source of the per-iteration delta vs.
//! `precompiled_*`. It shrinks relatively as chain length grows because the
//! firing work dominates. The Python bindings inherit this cost on every
//! `lp.run_sync`.

use criterion::{Criterion, black_box, criterion_group, criterion_main};

use libpetri::runtime::environment::ExecutorSignal;
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

fn build_fan_out(fan: usize) -> (PetriNet, Place<i32>, Place<i32>) {
    let start = Place::<i32>::new("start");
    let mid: Vec<Place<i32>> = (0..fan).map(|i| Place::new(format!("mid{i}"))).collect();
    let end = Place::<i32>::new("end");

    let mut transitions = Vec::new();
    for (i, m) in mid.iter().enumerate() {
        transitions.push(
            Transition::builder(format!("fan_out_{i}"))
                .input(one(&start))
                .output(out_place(m))
                .action(fork())
                .build(),
        );
    }
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

fn owned_single_passthrough(c: &mut Criterion) {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("single").transition(t).build();
    let owned = OwnedPrecompiledNet::compile(&net);

    c.bench_function("owned_single_passthrough", |b| {
        b.iter(|| {
            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));
            let result = owned.run_sync::<NoopEventStore>(marking);
            black_box(result.count("p2"));
        })
    });
}

fn owned_sync_linear_chain(c: &mut Criterion) {
    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_sync_linear_chain/{n}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                marking.add(&start, Token::at(1, 0));
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count(&format!("p{n}")));
            })
        });
    }
}

fn owned_parallel_fan_out(c: &mut Criterion) {
    for &fan in &[5, 10, 20] {
        let (net, start, _end) = build_fan_out(fan);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_parallel_fan_out/{fan}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                for _ in 0..fan {
                    marking.add(&start, Token::at(1, 0));
                }
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("end"));
            })
        });
    }
}

fn owned_compilation(c: &mut Criterion) {
    for &n in &[10, 50, 100, 500] {
        let (net, _start) = build_linear_chain(n);
        c.bench_function(&format!("owned_compilation/{n}"), |b| {
            b.iter(|| {
                let owned = OwnedPrecompiledNet::compile(black_box(&net));
                black_box(&owned);
            })
        });
    }
}

fn owned_async_linear_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[5, 10, 20, 50, 100, 200, 500] {
        let (net, start) = build_linear_chain(n);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_async_linear_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    let result = owned.run_async::<NoopEventStore>(marking, rx).await;
                    black_box(result.count(&format!("p{n}")));
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

fn owned_mixed_chain(c: &mut Criterion) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    for &n in &[10, 20, 50, 100, 200, 500] {
        let (net, start) = build_mixed_chain(n, 2);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_mixed_chain/{n}"), |b| {
            b.iter(|| {
                rt.block_on(async {
                    let mut marking = Marking::new();
                    marking.add(&start, Token::at(1, 0));
                    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
                    let result = owned.run_async::<NoopEventStore>(marking, rx).await;
                    black_box(result.count(&format!("p{n}")));
                })
            })
        });
    }
}

criterion_group!(
    benches,
    owned_single_passthrough,
    owned_sync_linear_chain,
    owned_parallel_fan_out,
    owned_compilation,
    owned_async_linear_chain,
    owned_mixed_chain,
);
criterion_main!(benches);
