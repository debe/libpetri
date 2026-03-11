use libpetri_docgen::*;
use libpetri_docgen::export::graph::RankDir;
use libpetri_docgen::export::mapper::DotConfig;

fn main() {
    generate_mutex_example();
}

/// Classic mutual exclusion net: two processes competing for a shared mutex.
fn generate_mutex_example() {
    let idle_a = Place::<()>::new("idle_a");
    let critical_a = Place::<()>::new("critical_a");
    let idle_b = Place::<()>::new("idle_b");
    let critical_b = Place::<()>::new("critical_b");
    let mutex = Place::<()>::new("mutex");

    let idle_a_ref = idle_a.as_ref();
    let idle_b_ref = idle_b.as_ref();
    let mutex_ref = mutex.as_ref();

    let enter_a = Transition::builder("enter_a")
        .input(one(&idle_a))
        .input(one(&mutex))
        .output(out_place(&critical_a))
        .action(fork())
        .build();

    let exit_a = Transition::builder("exit_a")
        .input(one(&critical_a))
        .output(and_places(&[&idle_a_ref, &mutex_ref]))
        .action(fork())
        .build();

    let enter_b = Transition::builder("enter_b")
        .input(one(&idle_b))
        .input(one(&mutex))
        .output(out_place(&critical_b))
        .action(fork())
        .build();

    let exit_b = Transition::builder("exit_b")
        .input(one(&critical_b))
        .output(and_places(&[&idle_b_ref, &mutex_ref]))
        .action(fork())
        .build();

    let net = PetriNet::builder("MutualExclusion")
        .transition(enter_a)
        .transition(exit_a)
        .transition(enter_b)
        .transition(exit_b)
        .build();

    SvgGenerator::new()
        .config(DotConfig {
            direction: RankDir::TopToBottom,
            show_types: false,
            ..DotConfig::default()
        })
        .generate("mutex_example", &net);
}
