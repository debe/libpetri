//! State-class graph construction, the verification hot path: every successor clones a
//! marking, edits it, and keys the new class by it. `MarkingState` is a name-sorted vector
//! of shared names because of this loop; these benches are the regression check for it.
//!
//! The net is `workers` independent three-stage workers plus two places every step reads,
//! so each class marks `workers + 2` places and the graph closes at `3^workers` classes.
//! The initial marking is built in reverse name order, so the builder's order is kept too.

use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use libpetri::verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri::verification::state_class_graph::StateClassGraph;
use libpetri::*;

fn interleaving(workers: usize) -> (PetriNet, MarkingState) {
    let config = Place::<()>::new("shared/config");
    let lease = Place::<()>::new("shared/lease");
    let mut transitions = Vec::new();
    let mut marking = MarkingStateBuilder::new();
    for w in (0..workers).rev() {
        let stages: Vec<Place<()>> = (0..3).map(|s| Place::new(format!("worker{w:02}/stage{s}"))).collect();
        for s in 0..2 {
            transitions.push(
                Transition::builder(format!("worker{w:02}/advance{s}"))
                    .input(one(&stages[s]))
                    .read(read(if s == 0 { &config } else { &lease }))
                    .output(out_place(&stages[s + 1]))
                    .action(fork())
                    .build(),
            );
        }
        marking = marking.tokens(stages[0].name(), 1);
    }
    let marking = marking.tokens(lease.name(), 1).tokens(config.name(), 1).build();
    (PetriNet::builder("interleaving").transitions(transitions).build(), marking)
}

fn state_class_graph_interleaving(c: &mut Criterion) {
    let mut group = c.benchmark_group("state_class_graph_interleaving");
    group.sample_size(10);
    for workers in [6usize, 8] {
        let (net, marking) = interleaving(workers);
        let classes = 3usize.pow(workers as u32);
        group.bench_function(format!("{workers}_workers_{classes}_classes"), |b| {
            b.iter(|| {
                let graph = StateClassGraph::build(&net, &marking, classes + 1);
                assert_eq!(graph.class_count(), classes);
                black_box(graph.edge_count());
            })
        });
    }
    group.finish();
}

criterion_group!(benches, state_class_graph_interleaving);
criterion_main!(benches);
