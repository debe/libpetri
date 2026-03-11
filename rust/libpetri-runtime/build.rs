use libpetri_docgen::*;
use libpetri_docgen::export::graph::RankDir;
use libpetri_docgen::export::mapper::DotConfig;

fn main() {
    // Fork/join with timing and priority
    generate_executor_example();

    // Linear chain showing what PrecompiledNet optimizes
    generate_precompiled_example();
}

fn generate_executor_example() {
    let start = Place::<i32>::new("start");
    let branch_a = Place::<i32>::new("branch_a");
    let branch_b = Place::<i32>::new("branch_b");
    let join_place = Place::<i32>::new("join");
    let done = Place::<i32>::new("done");

    let branch_a_ref = branch_a.as_ref();
    let branch_b_ref = branch_b.as_ref();

    let fork_t = Transition::builder("fork")
        .input(one(&start))
        .output(and_places(&[&branch_a_ref, &branch_b_ref]))
        .timing(immediate())
        .priority(5)
        .action(fork())
        .build();

    let process_a = Transition::builder("process_a")
        .input(one(&branch_a))
        .output(out_place(&join_place))
        .timing(delayed(100))
        .action(fork())
        .build();

    let process_b = Transition::builder("process_b")
        .input(one(&branch_b))
        .output(out_place(&join_place))
        .timing(deadline(5000))
        .action(fork())
        .build();

    let complete = Transition::builder("complete")
        .input(exactly(2, &join_place))
        .output(out_place(&done))
        .timing(immediate())
        .action(fork())
        .build();

    let net = PetriNet::builder("ExecutorExample")
        .transition(fork_t)
        .transition(process_a)
        .transition(process_b)
        .transition(complete)
        .build();

    SvgGenerator::new()
        .config(DotConfig {
            direction: RankDir::TopToBottom,
            show_intervals: true,
            show_priority: true,
            ..DotConfig::default()
        })
        .generate("executor_example", &net);
}

fn generate_precompiled_example() {
    let p0 = Place::<i32>::new("p0");
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");
    let p4 = Place::<i32>::new("p4");
    let p5 = Place::<i32>::new("p5");

    let step_1 = Transition::builder("step_1")
        .input(one(&p0))
        .output(out_place(&p1))
        .timing(immediate())
        .action(fork())
        .build();

    let step_2 = Transition::builder("step_2")
        .input(one(&p1))
        .output(out_place(&p2))
        .timing(immediate())
        .action(fork())
        .build();

    let step_3 = Transition::builder("step_3")
        .input(one(&p2))
        .output(out_place(&p3))
        .timing(immediate())
        .action(fork())
        .build();

    let step_4 = Transition::builder("step_4")
        .input(one(&p3))
        .output(out_place(&p4))
        .timing(immediate())
        .action(fork())
        .build();

    let step_5 = Transition::builder("step_5")
        .input(one(&p4))
        .output(out_place(&p5))
        .timing(immediate())
        .action(fork())
        .build();

    let net = PetriNet::builder("PrecompiledExample")
        .transition(step_1)
        .transition(step_2)
        .transition(step_3)
        .transition(step_4)
        .transition(step_5)
        .build();

    SvgGenerator::new()
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            show_types: false,
            show_intervals: false,
            show_priority: false,
            ..DotConfig::default()
        })
        .generate("precompiled_example", &net);
}
