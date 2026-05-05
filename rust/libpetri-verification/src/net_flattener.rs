use std::collections::HashMap;

use libpetri_core::input::{self, In};
use libpetri_core::output::{self};
use libpetri_core::petri_net::PetriNet;

/// A flattened transition with pre/post vectors.
#[derive(Debug, Clone)]
pub struct FlatTransition {
    pub name: String,
    pub pre: Vec<i64>,
    pub post: Vec<i64>,
    pub inhibitor_places: Vec<usize>,
    pub read_places: Vec<usize>,
    pub reset_places: Vec<usize>,
    pub consume_all: Vec<usize>,
}

/// A flattened net ready for matrix computation and SMT encoding.
#[derive(Debug, Clone)]
pub struct FlatNet {
    pub places: Vec<String>,
    pub place_index: HashMap<String, usize>,
    pub place_count: usize,
    pub transitions: Vec<FlatTransition>,
}

/// Flattens a PetriNet: XOR branches are expanded into separate flat transitions.
pub fn flatten(net: &PetriNet) -> FlatNet {
    // Collect and sort places for stable indexing
    let mut places: Vec<String> = net.places().iter().map(|p| p.name().to_string()).collect();
    places.sort();
    places.dedup();

    let place_count = places.len();
    let place_index: HashMap<String, usize> = places
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), i))
        .collect();

    let mut flat_transitions = Vec::new();

    for t in net.transitions() {
        // Build pre vector from input specs
        let mut base_pre = vec![0i64; place_count];
        let mut consume_all_places = Vec::new();

        for spec in t.input_specs() {
            let pid = place_index[spec.place_name()];
            let required = input::required_count(spec) as i64;
            base_pre[pid] += required;
            if matches!(spec, In::All { .. } | In::AtLeast { .. }) {
                consume_all_places.push(pid);
            }
        }

        // Inhibitor places
        let inhibitor_places: Vec<usize> = t
            .inhibitors()
            .iter()
            .map(|inh| place_index[inh.place.name()])
            .collect();

        // Read places
        let read_places: Vec<usize> = t
            .reads()
            .iter()
            .map(|r| place_index[r.place.name()])
            .collect();

        // Reset places
        let reset_places: Vec<usize> = t
            .resets()
            .iter()
            .map(|r| place_index[r.place.name()])
            .collect();

        // Build post vectors: XOR branches expand into separate transitions.
        // Counts come from Out::One=1 / Out::Exactly=N / AND-collisions already
        // canonicalized inside enumerate_branches.
        if let Some(out_spec) = t.output_spec() {
            let branches = output::enumerate_branches(out_spec);
            if branches.len() <= 1 {
                // No XOR or single branch
                let mut post = vec![0i64; place_count];
                if let Some(branch) = branches.first() {
                    for (place, count) in branch {
                        let pid = place_index[place.name()];
                        post[pid] = *count as i64;
                    }
                }
                flat_transitions.push(FlatTransition {
                    name: t.name().to_string(),
                    pre: base_pre,
                    post,
                    inhibitor_places: inhibitor_places.clone(),
                    read_places: read_places.clone(),
                    reset_places: reset_places.clone(),
                    consume_all: consume_all_places.clone(),
                });
            } else {
                // XOR: one flat transition per branch
                for (bi, branch) in branches.iter().enumerate() {
                    let mut post = vec![0i64; place_count];
                    for (place, count) in branch {
                        let pid = place_index[place.name()];
                        post[pid] = *count as i64;
                    }
                    flat_transitions.push(FlatTransition {
                        name: format!("{}_b{}", t.name(), bi),
                        pre: base_pre.clone(),
                        post,
                        inhibitor_places: inhibitor_places.clone(),
                        read_places: read_places.clone(),
                        reset_places: reset_places.clone(),
                        consume_all: consume_all_places.clone(),
                    });
                }
            }
        } else {
            // No output spec
            flat_transitions.push(FlatTransition {
                name: t.name().to_string(),
                pre: base_pre,
                post: vec![0i64; place_count],
                inhibitor_places,
                read_places,
                reset_places,
                consume_all: consume_all_places,
            });
        }
    }

    FlatNet {
        places,
        place_index,
        place_count,
        transitions: flat_transitions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::{out_one, xor};
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn flatten_simple() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_one(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.place_count, 2);
        assert_eq!(flat.transitions.len(), 1);
        assert_eq!(flat.transitions[0].name, "t1");
    }

    #[test]
    fn flatten_xor_expands() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(xor(vec![out_one(&a), out_one(&b)]))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions.len(), 2);
        assert_eq!(flat.transitions[0].name, "t1_b0");
        assert_eq!(flat.transitions[1].name, "t1_b1");
    }

    // ==================== Multiplicity (IO-018, IO-019) ====================

    #[test]
    fn flatten_and_repeated_place_post_vector_is_three() {
        use libpetri_core::output::and;
        let input = Place::<i32>::new("input");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("triple")
            .input(one(&input))
            .output(and(vec![out_one(&output), out_one(&output), out_one(&output)]))
            .build();
        let net = PetriNet::builder("repeated_and").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions.len(), 1);
        let pid = flat.place_index["output"];
        assert_eq!(
            flat.transitions[0].post[pid], 3,
            "out_one(P) repeated three times under AND must produce post=3"
        );
    }

    #[test]
    fn flatten_exactly_post_vector_equals_count() {
        use libpetri_core::output::out_exactly;
        let input = Place::<i32>::new("input");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("five")
            .input(one(&input))
            .output(out_exactly(5, &output))
            .build();
        let net = PetriNet::builder("exactly").transition(t).build();

        let flat = flatten(&net);
        let pid = flat.place_index["output"];
        assert_eq!(flat.transitions[0].post[pid], 5);
    }

    #[test]
    fn flatten_and_two_exactly_sum() {
        use libpetri_core::output::{and, out_exactly};
        let input = Place::<i32>::new("input");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("sum")
            .input(one(&input))
            .output(and(vec![out_exactly(2, &output), out_exactly(3, &output)]))
            .build();
        let net = PetriNet::builder("sum").transition(t).build();

        let flat = flatten(&net);
        let pid = flat.place_index["output"];
        assert_eq!(
            flat.transitions[0].post[pid], 5,
            "AND of two Exactly(_, _) must sum counts on shared keys"
        );
    }

    #[test]
    fn flatten_xor_different_counts_per_branch() {
        use libpetri_core::output::out_exactly;
        let input = Place::<i32>::new("input");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("choice")
            .input(one(&input))
            .output(xor(vec![out_one(&output), out_exactly(3, &output)]))
            .build();
        let net = PetriNet::builder("xor_counts").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions.len(), 2);
        let pid = flat.place_index["output"];
        assert_eq!(flat.transitions[0].post[pid], 1);
        assert_eq!(flat.transitions[1].post[pid], 3);
    }
}
