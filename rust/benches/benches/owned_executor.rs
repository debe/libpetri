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

use libpetri::core::input::one_guarded;
use libpetri::core::match_spec::MatchSpec;
use libpetri::core::name::NameId;
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

/// Builds a chain where ~2% of transitions are synchronous and the rest are
/// async — the typical real-world workload shape.
fn build_mixed_chain(n: usize) -> (PetriNet, Place<i32>) {
    let sync_count = n / 50;
    let places: Vec<Place<i32>> = (0..=n).map(|i| Place::new(format!("p{i}"))).collect();
    let transitions: Vec<Transition> = (0..n)
        .map(|i| {
            let mut builder = Transition::builder(format!("t{i}"))
                .input(one(&places[i]))
                .output(out_place(&places[i + 1]));
            if i < sync_count {
                builder = builder.action(fork());
            } else {
                builder = builder.action(async_action(|ctx| async { Ok(ctx) }));
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
        let (net, start) = build_mixed_chain(n);
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

// ==================== ν-net Benchmarks (spec NU-020/021/040) ====================
//
// `OwnedPrecompiledNet` is the path the Python bindings hit, so these owned_*
// numbers are the apples-to-apples baseline for Python's ν-net FFI overhead.
// See `executor.rs` for the full rationale: a `MatchSpec` join re-builds a name
// index over every token in each correlated input on each enablement check, so
// draining a deep pool re-indexes the shrinking pool every fire (≈ O(k·depth²)).

#[derive(Clone)]
struct NuMsg {
    cid: String,
}

fn build_nu_join_drain(branches: usize, guarded: bool) -> (PetriNet, Vec<Place<NuMsg>>) {
    let inputs: Vec<Place<NuMsg>> = (0..branches)
        .map(|i| Place::new(format!("branch{i}")))
        .collect();
    let merged = Place::<String>::new("merged");

    let mut join = Transition::builder("join");
    for p in &inputs {
        join = if guarded {
            join.input(one_guarded(p, |m: &NuMsg| m.cid != "skip"))
        } else {
            join.input(one(p))
        };
    }
    let mut ms = MatchSpec::builder();
    for p in &inputs {
        ms = ms.key(p, |m: &NuMsg| NameId::new(m.cid.clone()));
    }
    let join = join
        .match_spec(ms.build())
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            ctx.output("merged", String::from("m"))?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_join_drain").transition(join).build();
    (net, inputs)
}

fn build_plain_join_drain() -> (PetriNet, Vec<Place<NuMsg>>) {
    let a = Place::<NuMsg>::new("branch0");
    let b = Place::<NuMsg>::new("branch1");
    let merged = Place::<String>::new("merged");
    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            ctx.output("merged", String::from("m"))?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("plain_join_drain").transition(join).build();
    (net, vec![a, b])
}

fn seed_drain_marking(inputs: &[Place<NuMsg>], depth: usize) -> Marking {
    let mut marking = Marking::new();
    for p in inputs {
        for j in 0..depth {
            marking.add(p, Token::at(NuMsg { cid: format!("c{j}") }, j as u64));
        }
    }
    marking
}

fn build_nu_scatter_gather(budgeted: bool) -> (PetriNet, Place<i32>, Place<i32>) {
    let source = Place::<i32>::new("source");
    let budget = Place::<i32>::new("budget");
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let mut fork_b = Transition::builder("fork").input(one(&source));
    if budgeted {
        fork_b = fork_b.input(one(&budget));
    }
    let fork_t = fork_b
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let cid = ctx.fresh_name().as_str().to_string();
            ctx.output("branchA", NuMsg { cid: cid.clone() })?;
            ctx.output("branchB", NuMsg { cid })?;
            Ok(())
        }))
        .build();

    let join_out = if budgeted {
        and(vec![out_place(&merged), out_place(&budget)])
    } else {
        out_place(&merged)
    };
    let join_t = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(join_out)
        .action(sync_action(move |ctx| {
            let m = ctx.input::<NuMsg>("branchA")?;
            ctx.output("merged", m.cid.clone())?;
            if budgeted {
                ctx.output("budget", 0_i32)?;
            }
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_scatter_gather")
        .transition(fork_t)
        .transition(join_t)
        .build();
    (net, source, budget)
}

fn owned_nu_join_drain(c: &mut Criterion) {
    for &depth in &[10, 50, 100, 200, 500] {
        let (net, inputs) = build_nu_join_drain(2, false);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_nu_join_drain/2/{depth}"), |b| {
            b.iter(|| {
                let marking = seed_drain_marking(&inputs, depth);
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
            })
        });
    }
    for &k in &[4, 8] {
        let (net, inputs) = build_nu_join_drain(k, false);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_nu_join_drain/{k}/100"), |b| {
            b.iter(|| {
                let marking = seed_drain_marking(&inputs, 100);
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
            })
        });
    }
}

fn owned_plain_join_drain(c: &mut Criterion) {
    for &depth in &[10, 50, 100, 200, 500] {
        let (net, inputs) = build_plain_join_drain();
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_plain_join_drain/2/{depth}"), |b| {
            b.iter(|| {
                let marking = seed_drain_marking(&inputs, depth);
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
            })
        });
    }
}

fn owned_nu_join_drain_guarded(c: &mut Criterion) {
    for &depth in &[10, 50, 100, 200, 500] {
        let (net, inputs) = build_nu_join_drain(2, true);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_nu_join_drain_guarded/2/{depth}"), |b| {
            b.iter(|| {
                let marking = seed_drain_marking(&inputs, depth);
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
            })
        });
    }
}

fn owned_nu_scatter_gather(c: &mut Criterion) {
    for &groups in &[10, 50, 100] {
        let (net, source, _budget) = build_nu_scatter_gather(false);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_nu_scatter_gather/{groups}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                for _ in 0..groups {
                    marking.add(&source, Token::at(0, 0));
                }
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
            })
        });
    }
}

fn owned_nu_scatter_gather_budgeted(c: &mut Criterion) {
    for &groups in &[10, 50, 100] {
        let (net, source, budget) = build_nu_scatter_gather(true);
        let owned = OwnedPrecompiledNet::compile(&net);
        c.bench_function(&format!("owned_nu_scatter_gather_budgeted/{groups}"), |b| {
            b.iter(|| {
                let mut marking = Marking::new();
                for _ in 0..groups {
                    marking.add(&source, Token::at(0, 0));
                }
                marking.add(&budget, Token::at(0, 0));
                let result = owned.run_sync::<NoopEventStore>(marking);
                black_box(result.count("merged"));
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
    owned_nu_join_drain,
    owned_plain_join_drain,
    owned_nu_join_drain_guarded,
    owned_nu_scatter_gather,
    owned_nu_scatter_gather_budgeted,
);
criterion_main!(benches);
